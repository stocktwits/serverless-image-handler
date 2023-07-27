// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

import Rekognition from "aws-sdk/clients/rekognition";
import S3 from "aws-sdk/clients/s3";
import SecretsManager from "aws-sdk/clients/secretsmanager";

import { getOptions } from "../solution-utils/get-options";
import { isNullOrWhiteSpace } from "../solution-utils/helpers";
import { ImageHandler } from "./image-handler";
import { ImageRequest } from "./image-request";
import { Headers, ImageHandlerEvent, ImageHandlerExecutionResult, StatusCodes } from "./lib";
import { SecretProvider } from "./secret-provider";

const awsSdkOptions = getOptions();
const s3Client = new S3(awsSdkOptions);
const rekognitionClient = new Rekognition(awsSdkOptions);
const secretsManagerClient = new SecretsManager(awsSdkOptions);
const secretProvider = new SecretProvider(secretsManagerClient);

/**
 * Image handler Lambda handler.
 * @param event The image handler request event.
 * @returns Processed request response.
 */
export async function handler(event: ImageHandlerEvent): Promise<ImageHandlerExecutionResult> {
  event.path = transformCdnUrls(event.path);
  console.info("Received event:", JSON.stringify(event, null, 2));

  const imageRequest = new ImageRequest(s3Client, secretProvider);
  const imageHandler = new ImageHandler(s3Client, rekognitionClient);
  const isAlb = event.requestContext && Object.prototype.hasOwnProperty.call(event.requestContext, "elb");

  try {
    const imageRequestInfo = await imageRequest.setup(event);
    console.info(imageRequestInfo);

    const processedRequest = await imageHandler.process(imageRequestInfo);

    let headers = getResponseHeaders(false, isAlb);
    headers["Content-Type"] = imageRequestInfo.contentType;
    // eslint-disable-next-line dot-notation
    headers["Expires"] = imageRequestInfo.expires;
    headers["Last-Modified"] = imageRequestInfo.lastModified;
    headers["Cache-Control"] = imageRequestInfo.cacheControl;

    // Apply the custom headers overwriting any that may need overwriting
    if (imageRequestInfo.headers) {
      headers = { ...headers, ...imageRequestInfo.headers };
    }

    return {
      statusCode: StatusCodes.OK,
      isBase64Encoded: true,
      headers,
      body: processedRequest,
    };
  } catch (error) {
    console.error(error);
    //log the path for debugging
    console.error("Error occurred for path ", event.path);
    // Default fallback image
    const { ENABLE_DEFAULT_FALLBACK_IMAGE, DEFAULT_FALLBACK_IMAGE_BUCKET, DEFAULT_FALLBACK_IMAGE_KEY } = process.env;
    if (
      ENABLE_DEFAULT_FALLBACK_IMAGE === "Yes" &&
      !isNullOrWhiteSpace(DEFAULT_FALLBACK_IMAGE_BUCKET) &&
      !isNullOrWhiteSpace(DEFAULT_FALLBACK_IMAGE_KEY)
    ) {
      try {
        const defaultFallbackImage = await s3Client
          .getObject({
            Bucket: DEFAULT_FALLBACK_IMAGE_BUCKET,
            Key: DEFAULT_FALLBACK_IMAGE_KEY,
          })
          .promise();

        const headers = getResponseHeaders(false, isAlb);
        headers["Content-Type"] = defaultFallbackImage.ContentType;
        headers["Last-Modified"] = defaultFallbackImage.LastModified;
        headers["Cache-Control"] = "max-age=31536000,public";

        return {
          statusCode: error.status ? error.status : StatusCodes.INTERNAL_SERVER_ERROR,
          isBase64Encoded: true,
          headers,
          body: defaultFallbackImage.Body.toString("base64"),
        };
      } catch (error) {
        console.error("Error occurred while getting the default fallback image.", error);
      }
    }

    if (error.status) {
      return {
        statusCode: error.status,
        isBase64Encoded: false,
        headers: getResponseHeaders(true, isAlb),
        body: JSON.stringify(error),
      };
    } else {
      return {
        statusCode: StatusCodes.INTERNAL_SERVER_ERROR,
        isBase64Encoded: false,
        headers: getResponseHeaders(true, isAlb),
        body: JSON.stringify({
          message: "Internal error. Please contact the system administrator.",
          code: "InternalError",
          status: StatusCodes.INTERNAL_SERVER_ERROR,
        }),
      };
    }
  }
}

/**
 * Generates the appropriate set of response headers based on a success or error condition.
 * @param isError Has an error been thrown.
 * @param isAlb Is the request from ALB.
 * @returns Headers.
 */
function getResponseHeaders(isError: boolean = false, isAlb: boolean = false): Headers {
  const { CORS_ENABLED, CORS_ORIGIN } = process.env;
  const corsEnabled = CORS_ENABLED === "Yes";
  const headers: Headers = {
    "Access-Control-Allow-Methods": "GET",
    "Access-Control-Allow-Headers": "Content-Type, Authorization",
  };

  if (!isAlb) {
    headers["Access-Control-Allow-Credentials"] = true;
  }

  if (corsEnabled) {
    headers["Access-Control-Allow-Origin"] = CORS_ORIGIN;
  }

  if (isError) {
    headers["Content-Type"] = "application/json";
  }

  return headers;
}

/**
 * Transorm CDN URLs to the format expected by the image handler.
 * @param url
 * @returns Transformed URL.
 */
function transformCdnUrls(url: string): string {
  const oldCdnurls = /\/cdn-cgi\/image\/fit=contain,width=\d+,height=\d+/;
  const cloudflareUrlformat = /\/cdn-cgi\/image\/([^/]*)\/(.*)/;
  const paramFormat = /(fit|format|width|height|quality)=([^,]*)/g;
  // Check if the URL matches the existing pattern
  if (oldCdnurls.test(url)) {
      // Replace the matched part of the URL with an empty string, effectively removing it
      return url.replace(oldCdnurls, '');
  }
  // If the existing pattern is not matched, check for the new pattern
  else if (cloudflareUrlformat.test(url)) {
    let match = url.match(cloudflareUrlformat);
    if (match) {
      let paramsString = match[1];
      let remainder = match[2];
      
      let width = '0';
      let height = '0';
      let quality = '70';
      
      let paramMatch;
      while ((paramMatch = paramFormat.exec(paramsString)) !== null) {
        switch (paramMatch[1]) {
          case 'width':
            width = paramMatch[2];
            break;
          case 'height':
            height = paramMatch[2];
            break;
          case 'quality':
            quality = paramMatch[2];
            break;
        }
      }
      
      return `/fit-in/${width}x${height}/filters:quality(${quality})/${remainder}`;
    }
  }

  // If the URL does not match any pattern, return it unchanged
  return url;
}