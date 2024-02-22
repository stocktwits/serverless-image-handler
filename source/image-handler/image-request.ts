// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

import S3 from "aws-sdk/clients/s3";
import { createHmac } from "crypto";
import sharp, { Metadata } from "sharp";
import axios from 'axios';

import {
  ContentTypes,
  DefaultImageRequest,
  Headers,
  ImageEdits,
  ImageFormatTypes,
  ImageHandlerError,
  ImageHandlerEvent,
  ImageRequestInfo,
  RequestTypes,
  StatusCodes,
} from "./lib";
import { SecretProvider } from "./secret-provider";
import { ThumborMapper } from "./thumbor-mapper";

import https from 'https';
import http from 'http';
import { URL } from "url";

const chromium = require('@sparticuz/chromium');
const puppeteer = require('puppeteer-extra');
const StealthPlugin = require('puppeteer-extra-plugin-stealth');
puppeteer.use(StealthPlugin());

//This will be true unless source bucket is ST-avatars or if SOURCE_BUCKETS is not set
const COMPRESS_GIF = process.env.SOURCE_BUCKETS !== 'st-avatars' || process.env.SOURCE_BUCKETS === undefined;
const MAX_PERCENTAGE = parseInt(process.env.MAX_PERCENTAGE, 10) || 75
const MIN_PERCENTAGE = parseInt(process.env.MIN_PERCENTAGE, 10) || 25
const MAX_IMAGE_SIZE = 6 * 1024 * 1024; //6 MB
const ALLOWED_CONTENT_TYPES = [
  'image/jpeg',
  'image/tiff',
  'image/png',
  'image/gif',
  'image/webp',
  'image/svg+xml',
  'binary/octet-stream',
  'application/octet-stream'
];
const MAX_REDIRECTS = 3;
const TIMEOUT = 10000; // 10 seconds timeout

type OriginalImageInfo = Partial<{
  contentType: string;
  expires: string;
  lastModified: string;
  cacheControl: string;
  originalImage: Buffer;
}>;

export class ImageRequest {
  private static readonly DEFAULT_EFFORT = 4;

  constructor(private readonly s3Client: S3, private readonly secretProvider: SecretProvider) {}

  /**
   * Determines the output format of an image
   * @param imageRequestInfo Initialized image request information
   * @param event Lambda requrest body
   */
  private determineOutputFormat(imageRequestInfo: ImageRequestInfo, event: ImageHandlerEvent): void {
    const outputFormat = this.getOutputFormat(event, imageRequestInfo.requestType);
    // if webp check reduction effort, if invalid value, use 4 (default in sharp)
    if (outputFormat === ImageFormatTypes.WEBP && imageRequestInfo.requestType === RequestTypes.DEFAULT) {
      const decoded = this.decodeRequest(event);
      if (typeof decoded.effort !== "undefined") {
        const effort = Math.trunc(decoded.effort);
        const isValid = !isNaN(effort) && effort >= 0 && effort <= 6;
        imageRequestInfo.effort = isValid ? effort : ImageRequest.DEFAULT_EFFORT;
      }
    }
    if (imageRequestInfo.edits && imageRequestInfo.edits.toFormat) {
      imageRequestInfo.outputFormat = imageRequestInfo.edits.toFormat;
    } else if (outputFormat) {
      imageRequestInfo.outputFormat = outputFormat;
    }
  }

  /**
   * Fix quality for Thumbor and Custom request type if outputFormat is different from quality type.
   * @param imageRequestInfo Initialized image request information
   */
  private fixQuality(imageRequestInfo: ImageRequestInfo): void {
    if (imageRequestInfo.outputFormat) {
      const requestType = [RequestTypes.CUSTOM, RequestTypes.THUMBOR];
      const acceptedValues = [
        ImageFormatTypes.JPEG,
        ImageFormatTypes.PNG,
        ImageFormatTypes.WEBP,
        ImageFormatTypes.TIFF,
        ImageFormatTypes.HEIF,
        ImageFormatTypes.GIF,
        ImageFormatTypes.AVIF
      ];

      imageRequestInfo.contentType = `image/${imageRequestInfo.outputFormat}`;
      if (
        requestType.includes(imageRequestInfo.requestType) &&
        acceptedValues.includes(imageRequestInfo.outputFormat)
      ) {
        const qualityKey = Object.keys(imageRequestInfo.edits).filter((key) =>
          acceptedValues.includes(key as ImageFormatTypes)
        )[0];

        if (qualityKey && qualityKey !== imageRequestInfo.outputFormat) {
          imageRequestInfo.edits[imageRequestInfo.outputFormat] = imageRequestInfo.edits[qualityKey];
          delete imageRequestInfo.edits[qualityKey];
        }
      } 
      
    }

    if (imageRequestInfo.contentType === ContentTypes.GIF  && COMPRESS_GIF === true && imageRequestInfo?.edits?.gif) {
      //Gif quality as per sharp doc can be controlled by adding interframe error 
      //between 0 to 32 .After doing a bit of experimentation adding the below compression
      //reduces the chance for 413 excpeption by a good margin and looks almost the same
      let gifQuality = imageRequestInfo.edits.gif.quality;
      if(gifQuality >= 70){
          imageRequestInfo.edits.gif.interFrameMaxError = 16;
      } else if(gifQuality >= 50 && gifQuality < 70) {
          imageRequestInfo.edits.gif.interFrameMaxError = 24;
      } else {
          imageRequestInfo.edits.gif.interFrameMaxError = 32;
      }
  }

}

  /**
   * Initializer function for creating a new image request, used by the image handler to perform image modifications.
   * @param event Lambda request body.
   * @returns Initialized image request information.
   */
  public async setup(event: ImageHandlerEvent): Promise<ImageRequestInfo> {
    try {
      await this.validateRequestSignature(event);

      let imageRequestInfo: ImageRequestInfo = <ImageRequestInfo>{};

      imageRequestInfo.requestType = this.parseRequestType(event);
      imageRequestInfo.bucket = this.parseImageBucket(event, imageRequestInfo.requestType);
      imageRequestInfo.key = this.parseImageKey(event, imageRequestInfo.requestType);
      imageRequestInfo.edits = this.parseImageEdits(event, imageRequestInfo.requestType);

      const originalImage = await this.getOriginalImage(imageRequestInfo.bucket, imageRequestInfo.key);
      imageRequestInfo = { ...imageRequestInfo, ...originalImage };

      imageRequestInfo.headers = this.parseImageHeaders(event, imageRequestInfo.requestType);

      await this.setResizeDimensionsforGifIfRequired(originalImage, imageRequestInfo);

      // If the original image is SVG file and it has any edits but no output format, change the format to PNG.
      if (
        imageRequestInfo.contentType === ContentTypes.SVG &&
        imageRequestInfo.edits &&
        Object.keys(imageRequestInfo.edits).length > 0 &&
        !imageRequestInfo.edits.toFormat
      ) {
        imageRequestInfo.outputFormat = ImageFormatTypes.PNG;
      }

      /* Decide the output format of the image.
       * 1) If the format is provided, the output format is the provided format.
       * 2) If headers contain "Accept: image/webp", the output format is webp.
       * 3) Use the default image format for the rest of cases.
       */
      if (
        imageRequestInfo.contentType !== ContentTypes.SVG ||
        imageRequestInfo.edits.toFormat ||
        imageRequestInfo.outputFormat
      ) {
        this.determineOutputFormat(imageRequestInfo, event);
      }

      // Fix quality for Thumbor and Custom request type if outputFormat is different from quality type.
      this.fixQuality(imageRequestInfo);

      return imageRequestInfo;
    } catch (error) {
      console.error(error);

      throw error;
    }
  }

  public isValidURL(str: string) {
    try {
      new URL(str);
      return true;
    } catch (_) {
      return false;
    }
  }

  public async getImageBytes(url: string, depth: number) {
    return new Promise((resolve, reject) => {
      const preset_headers = {
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
        'Accept-Encoding': 'gzip, deflate, br',
        'Accept-Language': 'en-IN,en-GB;q=0.9,en-US;q=0.8,en;q=0.7',
        'Sec-Ch-Ua': '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"',
        'Sec-Ch-Ua-Mobile': '?0',
        'Sec-Ch-Ua-Platform': '"macOS"',
        'Sec-Fetch-Dest': 'document',
        'Sec-Fetch-Mode': 'navigate',
        'Sec-Fetch-Site': 'none',
        'referrer': 'www.google.com',
        'Sec-Fetch-User': '?1',
        'Upgrade-Insecure-Requests': '1',
        'Host': new URL(url).hostname,
        'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.0.3 Safari/605.1.15'
      }; 
      const protocol = url.startsWith('https') ? https : http;
      protocol.get(url, {headers: preset_headers}, response => {
        if (depth > MAX_REDIRECTS) {
          reject(new Error(`Failed to get the image: too many redirects`));
          return;
        }
        if ([301, 302, 303, 307, 308].includes(response.statusCode)) {
          const redirectUrl = response.headers.location;
          return resolve(this.getImageBytes(redirectUrl, depth + 1));
        }
        if (response.statusCode !== 200) {
          reject(new Error(`Failed to get the image at ${url}. Status code: ${response.statusCode}` ));
          return;
        }
        const contentType = response.headers['content-type'].split(';')[0];
        if (!ALLOWED_CONTENT_TYPES.includes(contentType)) {
          reject(new Error(`Invalid content type, only the following content types are allowed: ${ALLOWED_CONTENT_TYPES.join(', ')}`));
          return;
        }
        let chunks = [];
        let currentSize = 0;
        response.on('data', (chunk: any) => {
          chunks.push(chunk);
          currentSize += chunk.length;
          if (currentSize > MAX_IMAGE_SIZE) {
            console.log('here', currentSize)
            reject(new Error(`The image is too large, the maximum allowed size is ${MAX_IMAGE_SIZE} bytes`));
            response.destroy();  
          }
        });
        response.on('end', () => {
          resolve(Buffer.concat(chunks));
        });
      })
      .on('error', error => {
        reject(error);
      });
    });
  }

  /**
   * This function is used to get the image bytes from the url using the axios library.
   * @param url 
   * @param depth 
   * @returns buffer
   */
  public async getImageBytesUsingAxios(url: string, depth: number = 0): Promise<Buffer> {
    const headers = {
      'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
      'Accept-Encoding': 'gzip, deflate, br',
      'Accept-Language': 'en-IN,en-GB;q=0.9,en-US;q=0.8,en;q=0.7',
      'Sec-Ch-Ua': '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"',
      'Sec-Ch-Ua-Mobile': '?0',
      'Sec-Ch-Ua-Platform': '"macOS"',
      'Sec-Fetch-Dest': 'document',
      'Sec-Fetch-Mode': 'navigate',
      'Sec-Fetch-Site': 'none',
      'referrer': 'www.google.com',
      'Sec-Fetch-User': '?1',
      'Upgrade-Insecure-Requests': '1',
      'Host': new URL(url).hostname,
      'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.0.3 Safari/605.1.15'
    }; 

    try {
        const response = await axios.get(url, {
            headers: headers,
            timeout: TIMEOUT,
            maxRedirects: MAX_REDIRECTS,
            responseType: 'arraybuffer'
        });

        const contentType = response.headers['content-type']?.split(';')[0];
        if (!contentType || !ALLOWED_CONTENT_TYPES.includes(contentType)) {
            throw new Error(`Invalid content type, only the following content types are allowed: ${ALLOWED_CONTENT_TYPES.join(', ')}`);
        }

        if (response.data.byteLength > MAX_IMAGE_SIZE) {
            throw new Error(`The image is too large, the maximum allowed size is ${MAX_IMAGE_SIZE} bytes`);
        }

        return Buffer.from(response.data);

    } catch (error) {
        if (error.response) {
            // Request made and server responded
            throw new Error(`Failed to get the image at ${url}. Status code: ${error.response.status}`);
        } else if (error.request) {
            // The request was made but no response was received
            throw new Error(`No response received for ${url}.`);
        } else {
            // Something happened in setting up the request that triggered an Error
            throw error;
        }
    }
}

    
public async fetchImage(url: string) {
  const depth = 0; // Assuming depth is used for internal logic
  try {
      // Try fetching with the first method
      return await this.getImageBytes(url, depth);
  } catch (error) {
      console.error('Error in getImageBytes:', error.message);
      // The first method failed, try the second method
      try {
          return await this.getImageBytesUsingAxios(url, depth);
      } catch (error) {
          console.error('Error in getImageBytesUsingAxios:', error.message);
          // The second method also failed, try the third method
          try {
              return await this.getImageBytesUsingPuppeteer(url);
          } catch (error) {
              console.error('Error in getImageBytesUsingPuppeteer:', error.message);
              // All methods failed, throw an error
              throw new Error('All methods failed to fetch the image');
          }
      }
  }
}

public async getImageBytesUsingPuppeteer(imageUrl) {
  let browser = null;
  console.log(`Trying to launch browser with: ${JSON.stringify(chromium.args)}`);

  try {
      // Launching the browser with chrome-aws-lambda
      browser = await puppeteer.launch({
          args: ['--no-sandbox', '--disable-setuid-sandbox', ...chromium.args],
          executablePath: await chromium.executablePath(),
          headless: true,
          defaultViewport: chromium.defaultViewport,
      });

      const page = await browser.newPage();
      await page.setUserAgent('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/58.0.3029.110 Safari/537.36');
      const headers = {
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
        'Accept-Encoding': 'gzip, deflate, br',
        'Accept-Language': 'en-IN,en-GB;q=0.9,en-US;q=0.8,en;q=0.7',
        'Sec-Ch-Ua': '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"',
        'Sec-Ch-Ua-Mobile': '?0',
        'Sec-Ch-Ua-Platform': '"macOS"',
        'Sec-Fetch-Dest': 'document',
        'Sec-Fetch-Mode': 'navigate',
        'Sec-Fetch-Site': 'none',
        'Sec-Fetch-User': '?1',
        'Upgrade-Insecure-Requests': '1'
      };

     await page.setExtraHTTPHeaders(headers);
      
      // Navigate directly to the image URL
      const response = await page.goto(imageUrl, { waitUntil: 'networkidle2' });
      
      if(response.status() !== 200) {
        await browser.close();
        throw new Error(`Failed to get the image at ${imageUrl}. Status code: ${response.status()}` );
      }

      const buffer = await response.buffer();

      await browser.close();
      return buffer;
  } catch (error) {
      if (browser !== null) {
          await browser.close();
      }
      throw error;
  }
}




  /**
   * Gets the original image from an Amazon S3 bucket.
   * @param bucket The name of the bucket containing the image.
   * @param key The key name corresponding to the image.
   * @returns The original image or an error.
   */
  public async getOriginalImage(bucket: string, key: string): Promise<OriginalImageInfo> {
    let decodedURL = decodeURIComponent(key);
    try {
      const result: OriginalImageInfo = {};

      const imageLocation = { Bucket: bucket, Key: key };
      let imageBuffer: Buffer;
      if (this.isValidURL(decodedURL)) {
        let imgBytes = await this.fetchImage(decodedURL);
        imageBuffer = Buffer.from(imgBytes as Uint8Array);

        result.contentType = this.inferImageType(imageBuffer);
      } else {
        const originalImage = await this.s3Client.getObject(imageLocation).promise();
        imageBuffer = Buffer.from(originalImage.Body as Uint8Array);

        if (originalImage.ContentType) {
          // If using default S3 ContentType infer from hex headers
          if (["binary/octet-stream", "application/octet-stream"].includes(originalImage.ContentType)) {
            result.contentType = this.inferImageType(imageBuffer);
          } else {
            result.contentType = originalImage.ContentType;
          }
        } else {
          result.contentType = "image";
        }
  
        if (originalImage.Expires) {
          result.expires = new Date(originalImage.Expires).toUTCString();
        }
  
        if (originalImage.LastModified) {
          result.lastModified = new Date(originalImage.LastModified).toUTCString();
        }
        
      }
      
      result.cacheControl = "max-age=31536000,public";
      result.originalImage = imageBuffer;

      return result;
    } catch (error) {
      let status = StatusCodes.INTERNAL_SERVER_ERROR;
      if(error.message.includes('403')) {
        status = StatusCodes.FORBIDDEN
      }
      else if(error.message.includes('404')) {
        status = StatusCodes.NOT_FOUND
      }
      else if(error.message.includes('401')) {
        status = StatusCodes.UNAUTHORIZED
      }
      let message = error.message;
      if (error.code === "NoSuchKey") {
        status = StatusCodes.NOT_FOUND;
        message = `The image ${decodedURL} does not exist or the request may not be base64 encoded properly.`;
      }
      throw new ImageHandlerError(status, error.code, message);
    }
  }

  /**
   * Parses the name of the appropriate Amazon S3 bucket to source the original image from.
   * @param event Lambda request body.
   * @param requestType Image handler request type.
   * @returns The name of the appropriate Amazon S3 bucket.
   */
  public parseImageBucket(event: ImageHandlerEvent, requestType: RequestTypes): string {
    if (requestType === RequestTypes.DEFAULT) {
      // Decode the image request
      const request = this.decodeRequest(event);

      if (request.bucket !== undefined) {
        // Check the provided bucket against the allowed list
        const sourceBuckets = this.getAllowedSourceBuckets();

        if (sourceBuckets.includes(request.bucket) || request.bucket.match(new RegExp("^" + sourceBuckets[0] + "$"))) {
          return request.bucket;
        } else {
          throw new ImageHandlerError(
            StatusCodes.FORBIDDEN,
            "ImageBucket::CannotAccessBucket",
            "The bucket you specified could not be accessed. Please check that the bucket is specified in your SOURCE_BUCKETS."
          );
        }
      } else {
        // Try to use the default image source bucket env var
        const sourceBuckets = this.getAllowedSourceBuckets();
        return sourceBuckets[0];
      }
    } else if (requestType === RequestTypes.THUMBOR || requestType === RequestTypes.CUSTOM || requestType === RequestTypes.EXTERNAL) {
      // Use the default image source bucket env var
      const sourceBuckets = this.getAllowedSourceBuckets();
      return sourceBuckets[0];
    } else {
      throw new ImageHandlerError(
        StatusCodes.NOT_FOUND,
        "ImageBucket::CannotFindBucket",
        "The bucket you specified could not be found. Please check the spelling of the bucket name in your request."
      );
    }
  }

  /**
   * Parses the edits to be made to the original image.
   * @param event Lambda request body.
   * @param requestType Image handler request type.
   * @returns The edits to be made to the original image.
   */
  public parseImageEdits(event: ImageHandlerEvent, requestType: RequestTypes): ImageEdits {
    if (requestType === RequestTypes.DEFAULT) {
      const decoded = this.decodeRequest(event);
      return decoded.edits;
    } else if (requestType === RequestTypes.THUMBOR || requestType == RequestTypes.EXTERNAL) {
      const thumborMapping = new ThumborMapper();
      return thumborMapping.mapPathToEdits(event.path);
    } else if (requestType === RequestTypes.CUSTOM) {
      const thumborMapping = new ThumborMapper();
      const parsedPath = thumborMapping.parseCustomPath(event.path);
      return thumborMapping.mapPathToEdits(parsedPath);
    } else {
      throw new ImageHandlerError(
        StatusCodes.BAD_REQUEST,
        "ImageEdits::CannotParseEdits",
        "The edits you provided could not be parsed. Please check the syntax of your request and refer to the documentation for additional guidance."
      );
    }
  }

  /**
   * Parses the name of the appropriate Amazon S3 key corresponding to the original image.
   * @param event Lambda request body.
   * @param requestType Type of the request.
   * @returns The name of the appropriate Amazon S3 key.
   */
  public parseImageKey(event: ImageHandlerEvent, requestType: RequestTypes): string {
    if (requestType === RequestTypes.DEFAULT || requestType === RequestTypes.EXTERNAL) {
      // Decode the image request and return the image key
      const { key } = this.decodeRequest(event);
     
      return key;
    }

    if (requestType === RequestTypes.THUMBOR || requestType === RequestTypes.CUSTOM) {
      let { path } = event;

      if (requestType === RequestTypes.CUSTOM) {
        const { REWRITE_MATCH_PATTERN, REWRITE_SUBSTITUTION } = process.env;

        if (typeof REWRITE_MATCH_PATTERN === "string") {
          const patternStrings = REWRITE_MATCH_PATTERN.split("/");
          const flags = patternStrings.pop();
          const parsedPatternString = REWRITE_MATCH_PATTERN.slice(1, REWRITE_MATCH_PATTERN.length - 1 - flags.length);
          const regExp = new RegExp(parsedPatternString, flags);

          path = path.replace(regExp, REWRITE_SUBSTITUTION);
        } else {
          path = path.replace(REWRITE_MATCH_PATTERN, REWRITE_SUBSTITUTION);
        }
      }

      return decodeURIComponent(
        path.replace(/\/\d+x\d+:\d+x\d+\/|(?<=\/)\d+x\d+\/|filters:[^/]+|\/fit-in(?=\/)|^\/+/g, "").replace(/^\/+/, "")
      );
    }

    // Return an error for all other conditions
    throw new ImageHandlerError(
      StatusCodes.NOT_FOUND,
      "ImageEdits::CannotFindImage",
      "The image you specified could not be found. Please check your request syntax as well as the bucket you specified to ensure it exists."
    );
  }

  /**
   * Determines how to handle the request being made based on the URL path prefix to the image request.
   * Categorizes a request as either "image" (uses the Sharp library), "thumbor" (uses Thumbor mapping), or "custom" (uses the rewrite function).
   * @param event Lambda request body.
   * @returns The request type.
   */
  public parseRequestType(event: ImageHandlerEvent): RequestTypes {
    const { path } = event;
    const matchDefault = /^(\/?)([0-9a-zA-Z+/]{4})*(([0-9a-zA-Z+/]{2}==)|([0-9a-zA-Z+/]{3}=))?$/;
    const matchThumbor =
      /^(\/?)((fit-in)?|(filters:.+\(.?\))?|(unsafe)?)(((.(?!(\.[^.\\/]+$)))*$)|.*(\.jpg$|\.jpeg$|.\.png$|\.webp$|\.tiff$|\.tif$|\.svg$|\.gif$))/i;
    const matchURL = / |,|\.|\*|\+|\#|&|%|\$|\^/i;
    const { REWRITE_MATCH_PATTERN, REWRITE_SUBSTITUTION } = process.env;
    const definedEnvironmentVariables =
      REWRITE_MATCH_PATTERN !== "" &&
      REWRITE_SUBSTITUTION !== "" &&
      REWRITE_MATCH_PATTERN !== undefined &&
      REWRITE_SUBSTITUTION !== undefined;

    // Check if path is base 64 encoded
    let isBase64Encoded = true;
    try {
      this.decodeRequest(event);
    } catch (error) {
      console.info("Path is not base64 encoded.");
      isBase64Encoded = false;
    }


    if(path.toLowerCase().includes("http")){
      return RequestTypes.EXTERNAL;
    }
    else if (matchDefault.test(path) && isBase64Encoded) {
      // use sharp
      return RequestTypes.DEFAULT;
    } else if (definedEnvironmentVariables) {
      // use rewrite function then thumbor mappings
      return RequestTypes.CUSTOM;
    } else if (matchThumbor.test(path)) {
      // use thumbor mappings
      return RequestTypes.THUMBOR;
    } else if (matchURL.test(path)) {
      return RequestTypes.THUMBOR;
    } else {
      throw new ImageHandlerError(
        StatusCodes.BAD_REQUEST,
        "RequestTypeError",
        "The type of request you are making could not be processed. Please ensure that your original image is of a supported file type (jpg, png, tiff, webp, svg, gif) and that your image request is provided in the correct syntax. Refer to the documentation for additional guidance on forming image requests."
      );
    }
  }

  // eslint-disable-next-line jsdoc/require-returns-check
  /**
   * Parses the headers to be sent with the response.
   * @param event Lambda request body.
   * @param requestType Image handler request type.
   * @returns (optional) The headers to be sent with the response.
   */
  public parseImageHeaders(event: ImageHandlerEvent, requestType: RequestTypes): Headers {
    if (requestType === RequestTypes.DEFAULT) {
      const { headers } = this.decodeRequest(event);
      if (headers) {
        return headers;
      }
    }
  }

  /**
   * Decodes the base64-encoded image request path associated with default image requests.
   * Provides error handling for invalid or undefined path values.
   * @param event Lambda request body.
   * @returns The decoded from base-64 image request.
   *
  public decodeRequest(event: ImageHandlerEvent): DefaultImageRequest {
    const { path } = event;

    if (path) {
      const encoded = path.charAt(0) === "/" ? path.slice(1) : path;
      const toBuffer = Buffer.from(encoded, "base64");
      try {
        // To support European characters, 'ascii' was removed.
        return JSON.parse(toBuffer.toString());
      } catch (error) {
        throw new ImageHandlerError(
          StatusCodes.BAD_REQUEST,
          "DecodeRequest::CannotDecodeRequest",
          "The image request you provided could not be decoded. Please check that your request is base64 encoded properly and refer to the documentation for additional guidance."
        );
      }
    } else {
      throw new ImageHandlerError(
        StatusCodes.BAD_REQUEST,
        "DecodeRequest::CannotReadPath",
        "The URL path you provided could not be read. Please ensure that it is properly formed according to the solution documentation."
      );
    }
  }*/
  public decodeRequest(event: ImageHandlerEvent): DefaultImageRequest {
    const { path } = event;
    console.log("path is " + path);

    if (path) {
      // Find the index where 'http' starts
      const httpIndex = path.indexOf('http');
      console.log("httpIndex " + httpIndex);
      
      if (httpIndex !== -1) {
        // Extract URL from the point where 'http' is found
        const key = path.substring(httpIndex);
        console.log("key " + key);
        // Return an object of type DefaultImageRequest with the URL as the key
        return { key: key }; // 'key' is the required property of DefaultImageRequest
      } else {
        // Handle paths without 'http' (non-URL paths)
        const encoded = path.charAt(0) === "/" ? path.slice(1) : path;
        const toBuffer = Buffer.from(encoded, "base64");
        try {
          return JSON.parse(toBuffer.toString());
        } catch (error) {
          throw new ImageHandlerError(
            StatusCodes.BAD_REQUEST,
            "DecodeRequest::CannotDecodeRequest",
            "The image request you provided could not be decoded. Please check that your request is base64 encoded properly and refer to the documentation for additional guidance."
          );
        }
      }
    } else {
      throw new ImageHandlerError(
        StatusCodes.BAD_REQUEST,
        "DecodeRequest::CannotReadPath",
        "The URL path you provided could not be read. Please ensure that it is properly formed according to the solution documentation."
      );
    }
}




  /**
   * Returns a formatted image source bucket allowed list as specified in the SOURCE_BUCKETS environment variable of the image handler Lambda function.
   * Provides error handling for missing/invalid values.
   * @returns A formatted image source bucket.
   */
  public getAllowedSourceBuckets(): string[] {
    const { SOURCE_BUCKETS } = process.env;

    if (SOURCE_BUCKETS === undefined) {
      throw new ImageHandlerError(
        StatusCodes.BAD_REQUEST,
        "GetAllowedSourceBuckets::NoSourceBuckets",
        "The SOURCE_BUCKETS variable could not be read. Please check that it is not empty and contains at least one source bucket, or multiple buckets separated by commas. Spaces can be provided between commas and bucket names, these will be automatically parsed out when decoding."
      );
    } else {
      return SOURCE_BUCKETS.replace(/\s+/g, "").split(",");
    }
  }

  /**
   * Return the output format depending on the accepts headers and request type.
   * @param event Lambda request body.
   * @param requestType The request type.
   * @returns The output format.
   */
  public getOutputFormat(event: ImageHandlerEvent, requestType: RequestTypes = undefined): ImageFormatTypes {
    const { AUTO_WEBP } = process.env;

    if (AUTO_WEBP === "Yes" && event.headers.Accept && event.headers.Accept.includes(ContentTypes.WEBP)) {
      return ImageFormatTypes.WEBP;
    } else if (requestType === RequestTypes.DEFAULT) {
      const decoded = this.decodeRequest(event);
      return decoded.outputFormat;
    }

    return null;
  }

  /**
   * Return the output format depending on first four hex values of an image file.
   * @param imageBuffer Image buffer.
   * @returns The output format.
   */
  public inferImageType(imageBuffer: Buffer): string {
    const imageSignature = imageBuffer.slice(0, 4).toString("hex").toUpperCase();
    switch (imageSignature) {
        case "89504E47":
            return ContentTypes.PNG;
        case "FFD8FFDB":
        case "FFD8FFE0":
        case "FFD8FFED":
        case "FFD8FFEE":
        case "FFD8FFE1":
            return ContentTypes.JPEG;
        case "52494646":
            return ContentTypes.WEBP;
        case "49492A00":
        case "4D4D002A":
            return ContentTypes.TIFF;
        case "47494638":
            return ContentTypes.GIF;
        // No default case here to allow further checks after the switch
    }

    // Now, check for AVIF after the switch and before throwing an error
    if (this.isAVIF(imageBuffer)) {
        return ContentTypes.AVIF;
    }

    // If no known signature or AVIF is detected, throw an error
    throw new ImageHandlerError(
        StatusCodes.INTERNAL_SERVER_ERROR,
        "RequestTypeError",
        "The file does not have an extension and the file type could not be inferred. Please ensure that your original image is of a supported file type (jpg, png, tiff, webp, svg, avif). Refer to the documentation for additional guidance on forming image requests."
    );
}

  private  isAVIF(imageBuffer: Buffer): boolean {
    // Quick check for "ftypavif" in the beginning of the buffer
    const extendedSignature = imageBuffer.subarray(0, 12).toString("hex").toUpperCase();
    if (extendedSignature.includes("6674797061766966")) { // "ftypavif" in hexadecimal
        return true; // Quick detection of AVIF
    }

    // Detailed parsing to find the 'ftyp' box and check for 'avif' major brand
    let offset = 0; // Start at the beginning of the buffer

    while (offset < imageBuffer.length) {
        // Ensure there's enough buffer left to read the size and type
        if (offset + 8 > imageBuffer.length) break;

        // Read the box size and type
        const size = imageBuffer.readUInt32BE(offset); // Box size
        if(size < 8) { // Ensure that size is realistic to prevent infinite loops
            break;
        }
        const type = imageBuffer.toString('ascii', offset + 4, offset + 8); // Box type

        if (type === 'ftyp') {
            // Ensure there's enough buffer to read the major brand
            if (offset + 12 > imageBuffer.length) break;

            const majorBrand = imageBuffer.toString('ascii', offset + 8, offset + 12);
            if (majorBrand === 'avif') {
                return true; // Found 'ftyp' box with 'avif' major brand
            }
            break; // Found 'ftyp' but not 'avif', no need to continue
        }

        // Move to the next box
        offset += size;
    }

    return false; // 'ftyp' box with 'avif' major brand not found
}


  /**
   * Validates the request's signature.
   * @param event Lambda request body.
   * @returns A promise.
   * @throws Throws the error if validation is enabled and the provided signature is invalid.
   */
  private async validateRequestSignature(event: ImageHandlerEvent): Promise<void> {
    const { ENABLE_SIGNATURE, SECRETS_MANAGER, SECRET_KEY } = process.env;

    // Checks signature enabled
    if (ENABLE_SIGNATURE === "Yes") {
      const { path, queryStringParameters } = event;

      if (!queryStringParameters?.signature) {
        throw new ImageHandlerError(
          StatusCodes.BAD_REQUEST,
          "AuthorizationQueryParametersError",
          "Query-string requires the signature parameter."
        );
      }

      try {
        const { signature } = queryStringParameters;
        const secret = JSON.parse(await this.secretProvider.getSecret(SECRETS_MANAGER));
        const key = secret[SECRET_KEY];
        const hash = createHmac("sha256", key).update(path).digest("hex");

        // Signature should be made with the full path.
        if (signature !== hash) {
          throw new ImageHandlerError(StatusCodes.FORBIDDEN, "SignatureDoesNotMatch", "Signature does not match.");
        }
      } catch (error) {
        if (error.code === "SignatureDoesNotMatch") {
          throw error;
        }

        console.error("Error occurred while checking signature.", error);
        throw new ImageHandlerError(
          StatusCodes.INTERNAL_SERVER_ERROR,
          "SignatureValidationFailure",
          "Signature validation failed."
        );
      }
    }
  }

  /**
   * Checks Gif Resize dimensions and resets to original dimension if any of it exceeds the original size
   * @param event ImageRequestInfo, ImageMetadata
   * @returns A promise.
   */
  private async setResizeDimensionsforGifIfRequired(originalImage: OriginalImageInfo,imageRequestInfo: ImageRequestInfo): Promise<void> {
    //If the original image is GIF file end edit diemsions exceeds original then use original
      if (
        imageRequestInfo.contentType === ContentTypes.GIF &&
        imageRequestInfo.edits &&
        Object.keys(imageRequestInfo.edits).length > 0 && imageRequestInfo.edits.resize) {
          const metadata = await sharp(originalImage.originalImage).metadata();
          let resize = imageRequestInfo.edits.resize
              if(resize.width || resize.height){
                if(this.shouldResize(resize.width, metadata.width)){
                  imageRequestInfo.edits.resize.width = metadata.width
                }
                if(this.shouldResize(resize.height,metadata.height)){
                  imageRequestInfo.edits.resize.height = metadata.height
                }
           } 
      }
   }

  /**
    * When resize params are near to original dimensions it mostly leads to greater size gif  after resizing
    * hence when params are near to original dimensions or zero  we should not resize
    * @param number
    * @param reference
    * @returns boolean based on condition
    */

  private  shouldResize(number: number, reference: number): boolean {
    if(number === 0 || number === null) return true
    if(number > reference) return true
    const percentage = (number / reference) * 100;
    return percentage >= MAX_PERCENTAGE || percentage <= MIN_PERCENTAGE;
  }
}
