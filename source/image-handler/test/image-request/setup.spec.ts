// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


jest.mock('sharp'); //must be before sharp import

import { mockAwsS3, mockAwsSecretManager } from "../mock";

import S3 from "aws-sdk/clients/s3";
import SecretsManager from "aws-sdk/clients/secretsmanager";

import { ImageRequest } from "../../image-request";
import { ImageHandlerError, RequestTypes, StatusCodes } from "../../lib";
import { SecretProvider } from "../../secret-provider";
import sharp, { Sharp } from 'sharp';
import fs from "fs";


describe("setup", () => {
  const OLD_ENV = process.env;
  const s3Client = new S3();
  const secretsManager = new SecretsManager();
  let secretProvider = new SecretProvider(secretsManager);

  beforeEach(() => {
    jest.resetAllMocks();
    process.env = { ...OLD_ENV };
  });

  afterEach(() => {
    jest.clearAllMocks();
    secretProvider = new SecretProvider(secretsManager); // need to re-create the provider to make sure the secret is not cached
    process.env = OLD_ENV;
  });

  it("Should pass when a default image request is provided and populate the ImageRequest object with the proper values", async () => {
    // Arrange
    const event = {
      path: "/eyJidWNrZXQiOiJ2YWxpZEJ1Y2tldCIsImtleSI6InZhbGlkS2V5IiwiZWRpdHMiOnsiZ3JheXNjYWxlIjp0cnVlfSwib3V0cHV0Rm9ybWF0IjoianBlZyJ9",
    };
    process.env.SOURCE_BUCKETS = "validBucket, validBucket2";

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: "Default",
      bucket: "validBucket",
      key: "validKey",
      edits: { grayscale: true },
      outputFormat: "jpeg",
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      contentType: "image/jpeg",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "validBucket",
      Key: "validKey",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  it("Should pass when a default image request is provided and populate the ImageRequest object with the proper values with UTF-8 key", async () => {
    // Arrange
    const event = {
      path: "eyJidWNrZXQiOiJ2YWxpZEJ1Y2tldCIsImtleSI6IuS4reaWhyIsImVkaXRzIjp7ImdyYXlzY2FsZSI6dHJ1ZX0sIm91dHB1dEZvcm1hdCI6ImpwZWcifQ==",
    };
    process.env = { SOURCE_BUCKETS: "validBucket, validBucket2" };

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: "Default",
      bucket: "validBucket",
      key: "中文",
      edits: { grayscale: true },
      outputFormat: "jpeg",
      originalImage: Buffer.from("SampleImageContent\n"),
      contentType: "image/jpeg",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "validBucket",
      Key: "中文",
    });
    expect(imageRequestInfo).toMatchObject(expectedResult);
  });

  it("Should pass when a default image request is provided and populate the ImageRequest object with the proper values", async () => {
    // Arrange
    const event = {
      path: "/eyJidWNrZXQiOiJ2YWxpZEJ1Y2tldCIsImtleSI6InZhbGlkS2V5IiwiZWRpdHMiOnsidG9Gb3JtYXQiOiJwbmcifX0=",
    };
    process.env.SOURCE_BUCKETS = "validBucket, validBucket2";

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: "Default",
      bucket: "validBucket",
      key: "validKey",
      edits: { toFormat: "png" },
      outputFormat: "png",
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      contentType: "image/png",
    };
    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "validBucket",
      Key: "validKey",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  it("Should pass when a thumbor image request is provided and populate the ImageRequest object with the proper values", async () => {
    // Arrange
    const event = { path: "/filters:grayscale()/test-image-001.jpg" };
    process.env.SOURCE_BUCKETS = "allowedBucket001, allowedBucket002";

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: "Thumbor",
      bucket: "allowedBucket001",
      key: "test-image-001.jpg",
      edits: { grayscale: true },
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      contentType: "image",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "allowedBucket001",
      Key: "test-image-001.jpg",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  it("Should pass when a thumbor image request is provided and populate the ImageRequest object with the proper values", async () => {
    // Arrange
    const event = {
      path: "/filters:format(png)/filters:quality(50)/test-image-001.jpg",
    };
    process.env.SOURCE_BUCKETS = "allowedBucket001, allowedBucket002";

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: "Thumbor",
      bucket: "allowedBucket001",
      key: "test-image-001.jpg",
      edits: {
        toFormat: "png",
        png: { quality: 50 },
      },
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      outputFormat: "png",
      contentType: "image/png",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "allowedBucket001",
      Key: "test-image-001.jpg",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  it("Should pass when a custom image request is provided and populate the ImageRequest object with the proper values", async () => {
    // Arrange
    const event = {
      path: "/filters-rotate(90)/filters-grayscale()/custom-image.jpg",
    };
    process.env = {
      SOURCE_BUCKETS: "allowedBucket001, allowedBucket002",
      REWRITE_MATCH_PATTERN: "/(filters-)/gm",
      REWRITE_SUBSTITUTION: "filters:",
    };

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({
          cacheControl: "max-age=31536000,public",
          ContentType: "custom-type",
          Expires: "Tue, 24 Dec 2019 13:46:28 GMT",
          LastModified: "Sat, 19 Dec 2009 16:30:47 GMT",
          Body: Buffer.from("SampleImageContent\n"),
        });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: RequestTypes.CUSTOM,
      bucket: "allowedBucket001",
      key: "custom-image.jpg",
      edits: {
        grayscale: true,
        rotate: 90,
      },
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      contentType: "custom-type",
      expires: "Tue, 24 Dec 2019 13:46:28 GMT",
      lastModified: "Sat, 19 Dec 2009 16:30:47 GMT",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "allowedBucket001",
      Key: "custom-image.jpg",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  it("Should pass when a custom image request is provided and populate the ImageRequest object with the proper values and no file extension", async () => {
    // Arrange
    const event = {
      path: "/filters-rotate(90)/filters-grayscale()/custom-image",
    };
    process.env = {
      SOURCE_BUCKETS: "allowedBucket001, allowedBucket002",
      REWRITE_MATCH_PATTERN: "/(filters-)/gm",
      REWRITE_SUBSTITUTION: "filters:",
    };

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({
          CacheControl: "max-age=300,public",
          ContentType: "custom-type",
          Expires: "Tue, 24 Dec 2019 13:46:28 GMT",
          LastModified: "Sat, 19 Dec 2009 16:30:47 GMT",
          Body: Buffer.from("SampleImageContent\n"),
        });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: RequestTypes.CUSTOM,
      bucket: "allowedBucket001",
      key: "custom-image",
      edits: {
        grayscale: true,
        rotate: 90,
      },
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      contentType: "custom-type",
      expires: "Tue, 24 Dec 2019 13:46:28 GMT",
      lastModified: "Sat, 19 Dec 2009 16:30:47 GMT",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "allowedBucket001",
      Key: "custom-image",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  it("Should pass when an error is caught", async () => {
    // Arrange
    const event = {
      path: "/eyJidWNrZXQiOiJ2YWxpZEJ1Y2tldCIsImtleSI6InZhbGlkS2V5IiwiZWRpdHMiOnsiZ3JheXNjYWxlIjp0cnVlfX0=",
    };
    process.env.SOURCE_BUCKETS = "allowedBucket001, allowedBucket002";

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);

    // Assert
    try {
      await imageRequest.setup(event);
    } catch (error) {
      expect(error.code).toEqual("ImageBucket::CannotAccessBucket");
    }
  });

  describe("enableSignature", () => {
    beforeAll(() => {
      process.env.ENABLE_SIGNATURE = "Yes";
      process.env.SECRETS_MANAGER = "serverless-image-handler";
      process.env.SECRET_KEY = "signatureKey";
      process.env.SOURCE_BUCKETS = "validBucket";
    });

    it("Should pass when the image signature is correct", async () => {
      // Arrange
      const event = {
        path: "/eyJidWNrZXQiOiJ2YWxpZEJ1Y2tldCIsImtleSI6InZhbGlkS2V5IiwiZWRpdHMiOnsidG9Gb3JtYXQiOiJwbmcifX0=",
        queryStringParameters: {
          signature: "4d41311006641a56de7bca8abdbda91af254506107a2c7b338a13ca2fa95eac3",
        },
      };

      // Mock
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
        },
      }));
      mockAwsSecretManager.getSecretValue.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            SecretString: JSON.stringify({
              [process.env.SECRET_KEY]: "secret",
            }),
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Default",
        bucket: "validBucket",
        key: "validKey",
        edits: { toFormat: "png" },
        outputFormat: "png",
        originalImage: Buffer.from("SampleImageContent\n"),
        cacheControl: "max-age=31536000,public",
        contentType: "image/png",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "validKey",
      });
      expect(mockAwsSecretManager.getSecretValue).toHaveBeenCalledWith({
        SecretId: process.env.SECRETS_MANAGER,
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });

    it("Should throw an error when queryStringParameters are missing", async () => {
      // Arrange
      const event = {
        path: "/eyJidWNrZXQiOiJ2YWxpZEJ1Y2tldCIsImtleSI6InZhbGlkS2V5IiwiZWRpdHMiOnsidG9Gb3JtYXQiOiJwbmcifX0=",
      };

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      try {
        await imageRequest.setup(event);
      } catch (error) {
        // Assert
        expect(error).toMatchObject({
          status: StatusCodes.BAD_REQUEST,
          code: "AuthorizationQueryParametersError",
          message: "Query-string requires the signature parameter.",
        });
      }
    });

    it("Should throw an error when the image signature query parameter is missing", async () => {
      // Arrange
      const event = {
        path: "/eyJidWNrZXQiOiJ2YWxpZEJ1Y2tldCIsImtleSI6InZhbGlkS2V5IiwiZWRpdHMiOnsidG9Gb3JtYXQiOiJwbmcifX0=",
        queryStringParameters: null,
      };

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      try {
        await imageRequest.setup(event);
      } catch (error) {
        // Assert
        expect(error).toMatchObject({
          status: StatusCodes.BAD_REQUEST,
          message: "Query-string requires the signature parameter.",
          code: "AuthorizationQueryParametersError",
        });
      }
    });

    it("Should throw an error when signature does not match", async () => {
      // Arrange
      const event = {
        path: "/eyJidWNrZXQiOiJ2YWxpZEJ1Y2tldCIsImtleSI6InZhbGlkS2V5IiwiZWRpdHMiOnsidG9Gb3JtYXQiOiJwbmcifX0=",
        queryStringParameters: {
          signature: "invalid",
        },
      };

      // Mock
      mockAwsSecretManager.getSecretValue.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            SecretString: JSON.stringify({
              [process.env.SECRET_KEY]: "secret",
            }),
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      try {
        await imageRequest.setup(event);
      } catch (error) {
        // Assert
        expect(mockAwsSecretManager.getSecretValue).toHaveBeenCalledWith({
          SecretId: process.env.SECRETS_MANAGER,
        });
        expect(error).toMatchObject({
          status: 403,
          message: "Signature does not match.",
          code: "SignatureDoesNotMatch",
        });
      }
    });

    it("Should throw an error when any other error occurs", async () => {
      // Arrange
      const event = {
        path: "/eyJidWNrZXQiOiJ2YWxpZEJ1Y2tldCIsImtleSI6InZhbGlkS2V5IiwiZWRpdHMiOnsidG9Gb3JtYXQiOiJwbmcifX0=",
        queryStringParameters: {
          signature: "4d41311006641a56de7bca8abdbda91af254506107a2c7b338a13ca2fa95eac3",
        },
      };

      // Mock
      mockAwsSecretManager.getSecretValue.mockImplementationOnce(() => ({
        promise() {
          return Promise.reject(
            new ImageHandlerError(StatusCodes.INTERNAL_SERVER_ERROR, "InternalServerError", "SimulatedError")
          );
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      try {
        await imageRequest.setup(event);
      } catch (error) {
        // Assert
        expect(mockAwsSecretManager.getSecretValue).toHaveBeenCalledWith({
          SecretId: process.env.SECRETS_MANAGER,
        });
        expect(error).toMatchObject({
          status: StatusCodes.INTERNAL_SERVER_ERROR,
          message: "Signature validation failed.",
          code: "SignatureValidationFailure",
        });
      }
    });
  });

  describe("SVGSupport", () => {
    beforeAll(() => {
      process.env.ENABLE_SIGNATURE = "No";
      process.env.SOURCE_BUCKETS = "validBucket";
    });

    it("Should return SVG image when no edit is provided for the SVG image", async () => {
      // Arrange
      const event = {
        path: "/image.svg",
      };

      // Mock
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/svg+xml",
            Body: Buffer.from("SampleImageContent\n"),
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.svg",
        edits: {},
        originalImage: Buffer.from("SampleImageContent\n"),
        cacheControl: "max-age=31536000,public",
        contentType: "image/svg+xml",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.svg",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });

    it("Should return WebP image when there are any edits and no output is specified for the SVG image", async () => {
      // Arrange
      const event = {
        path: "/100x100/image.svg",
      };

      // Mock
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/svg+xml",
            Body: Buffer.from("SampleImageContent\n"),
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.svg",
        edits: { resize: { width: 100, height: 100 } },
        outputFormat: "png",
        originalImage: Buffer.from("SampleImageContent\n"),
        cacheControl: "max-age=31536000,public",
        contentType: "image/png",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.svg",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });

    it("Should return JPG image when output is specified to JPG for the SVG image", async () => {
      // Arrange
      const event = {
        path: "/filters:format(jpg)/image.svg",
      };

      // Mock
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/svg+xml",
            Body: Buffer.from("SampleImageContent\n"),
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.svg",
        edits: { toFormat: "jpeg" },
        outputFormat: "jpeg",
        originalImage: Buffer.from("SampleImageContent\n"),
        cacheControl: "max-age=31536000,public",
        contentType: "image/jpeg",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.svg",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
  });

  it("Should pass and return the customer headers if custom headers are provided", async () => {
    // Arrange
    const event = {
      path: "/eyJidWNrZXQiOiJ2YWxpZEJ1Y2tldCIsImtleSI6InZhbGlkS2V5IiwiaGVhZGVycyI6eyJDYWNoZS1Db250cm9sIjoibWF4LWFnZT0zMTUzNjAwMCxwdWJsaWMifSwib3V0cHV0Rm9ybWF0IjoianBlZyJ9",
    };
    process.env.SOURCE_BUCKETS = "validBucket, validBucket2";

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: "Default",
      bucket: "validBucket",
      key: "validKey",
      headers: { "Cache-Control": "max-age=31536000,public" },
      outputFormat: "jpeg",
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      contentType: "image/jpeg",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "validBucket",
      Key: "validKey",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  it("Should pass when valid reduction effort is provided and output is webp", async () => {
    const event = {
      path: "/eyJidWNrZXQiOiJ0ZXN0Iiwia2V5IjoidGVzdC5wbmciLCJvdXRwdXRGb3JtYXQiOiJ3ZWJwIiwicmVkdWN0aW9uRWZmb3J0IjozfQ==",
    };
    process.env.SOURCE_BUCKETS = "test, validBucket, validBucket2";

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: "Default",
      bucket: "test",
      key: "test.png",
      edits: undefined,
      headers: undefined,
      outputFormat: "webp",
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      contentType: "image/webp",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "test",
      Key: "test.png",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  it("Should pass and use default reduction effort if it is invalid type and output is webp", async () => {
    const event = {
      path: "/eyJidWNrZXQiOiJ0ZXN0Iiwia2V5IjoidGVzdC5wbmciLCJvdXRwdXRGb3JtYXQiOiJ3ZWJwIiwicmVkdWN0aW9uRWZmb3J0IjoidGVzdCJ9",
    };
    process.env.SOURCE_BUCKETS = "test, validBucket, validBucket2";

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: "Default",
      bucket: "test",
      key: "test.png",
      edits: undefined,
      headers: undefined,
      outputFormat: "webp",
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      contentType: "image/webp",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "test",
      Key: "test.png",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  it("Should pass and use default reduction effort if it is out of range and output is webp", async () => {
    const event = {
      path: "/eyJidWNrZXQiOiJ0ZXN0Iiwia2V5IjoidGVzdC5wbmciLCJvdXRwdXRGb3JtYXQiOiJ3ZWJwIiwicmVkdWN0aW9uRWZmb3J0IjoxMH0=",
    };
    process.env.SOURCE_BUCKETS = "test, validBucket, validBucket2";

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: "Default",
      bucket: "test",
      key: "test.png",
      edits: undefined,
      headers: undefined,
      outputFormat: "webp",
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      contentType: "image/webp",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "test",
      Key: "test.png",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  it("Should pass and not use reductionEffort if it is not provided and output is webp", async () => {
    const event = {
      path: "/eyJidWNrZXQiOiJ0ZXN0Iiwia2V5IjoidGVzdC5wbmciLCJvdXRwdXRGb3JtYXQiOiJ3ZWJwIn0=",
    };
    process.env.SOURCE_BUCKETS = "test, validBucket, validBucket2";

    // Mock
    mockAwsS3.getObject.mockImplementationOnce(() => ({
      promise() {
        return Promise.resolve({ Body: Buffer.from("SampleImageContent\n") });
      },
    }));

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const imageRequestInfo = await imageRequest.setup(event);
    const expectedResult = {
      requestType: "Default",
      bucket: "test",
      key: "test.png",
      edits: undefined,
      headers: undefined,
      outputFormat: "webp",
      originalImage: Buffer.from("SampleImageContent\n"),
      cacheControl: "max-age=31536000,public",
      contentType: "image/webp",
    };

    // Assert
    expect(mockAwsS3.getObject).toHaveBeenCalledWith({
      Bucket: "test",
      Key: "test.png",
    });
    expect(imageRequestInfo).toEqual(expectedResult);
  });

  describe("Restricted Gif Resizing", () => {
    beforeAll(() => {
      process.env.ENABLE_SIGNATURE = "No";
      process.env.SOURCE_BUCKETS = "validBucket";
    });
    it("Should match width if width exceeds the original GIF dimension and height is within range and gif is < 4mb", async () => {
      // Arrange
      const event = {
        path: "/fit-in/500x250/filters:quality(70)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 700, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 16, quality:70},
          resize: {
            width: 500,
            height: 250,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("Should match height if height exceeds the original GIF dimension but width is within range and gif is < 4mb", async () => {
      // Arrange
      const event = {
        path: "/fit-in/300x700/filters:quality(70)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 16,quality:70},
          resize: {
            width: 300,
            height: 400,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("Should match height if height =0 the original GIF dimension but width is within range", async () => {
      // Arrange
      const event = {
        path: "/fit-in/300x0/filters:quality(70)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 16, quality:70},
          resize: {
            width: 300,
            height: 400,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("Should match width if width = 0 exceeds the original GIF dimension but height is within range", async () => {
      // Arrange
      const event = {
        path: "/fit-in/0x200/filters:quality(70)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 16, quality:70},
          resize: {
            width: 500,
            height: 200,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("Should match width height if both exceeds and gif is > 4mb", async () => {
      // Arrange
      const event = {
        path: "/fit-in/700x700/filters:quality(70)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 4.1 *1024 *1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 16, quality:70},
          resize: {
            width: 500,
            height: 400,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("Should match height if height is less than 25 percent and width is within range", async () => {
      // Arrange
      const event = {
        path: "/fit-in/300x70/filters:quality(70)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 16, quality:70},
          resize: {
            width: 300,
            height: 400,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("Should match height if height is greater than 75 percent and width is within range", async () => {
      // Arrange
      const event = {
        path: "/fit-in/300x350/filters:quality(70)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: {interFrameMaxError: 16, quality:70},
          resize: {
            width: 300,
            height: 400,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("Should match width if width is less than 25 percent and height is within range", async () => {
      // Arrange
      const event = {
        path: "/fit-in/100x250/filters:quality(70)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 16,quality:70},
          resize: {
            width: 500,
            height: 250,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("Should match width if width is > than 75 percent and height is within range", async () => {
      // Arrange
      const event = {
        path: "/fit-in/450x250/filters:quality(70)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 16,quality:70},
          resize: {
            width: 500,
            height: 250,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("quality is 70 or more then interFrameMaxError 16", async () => {
      // Arrange
      const event = {
        path: "/fit-in/450x250/filters:quality(70)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 16,quality:70},
          resize: {
            width: 500,
            height: 250,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("quality is 50 or more  and less than 70  then interFrameMaxError 24", async () => {
      // Arrange
      const event = {
        path: "/fit-in/450x250/filters:quality(51)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 24,quality:51},
          resize: {
            width: 500,
            height: 250,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
    it("quality is less than 50 interFrameMaxError is 32", async () => {
      // Arrange
      const event = {
        path: "/fit-in/450x250/filters:quality(49)/image.gif",
      };
      const image = fs.readFileSync("./test/image/25x15.png");
      const sharpInstance: Partial<Sharp> = {
        metadata: jest.fn().mockResolvedValue({ width: 500, height: 400, size: 1024 }),
      };
    
      ((sharp as unknown) as jest.Mock).mockReturnValue(sharpInstance);
      
      mockAwsS3.getObject.mockImplementationOnce(() => ({
        promise() {
          return Promise.resolve({
            ContentType: "image/gif",
            Body: image,
          });
        },
      }));

      // Act
      const imageRequest = new ImageRequest(s3Client, secretProvider);
      const imageRequestInfo = await imageRequest.setup(event);
      const expectedResult = {
        requestType: "Thumbor",
        bucket: "validBucket",
        key: "image.gif",
        edits: {
          gif: { interFrameMaxError: 32,quality:49},
          resize: {
            width: 500,
            height: 250,
            fit: "inside",
        }},
        headers: undefined,
        originalImage: image,
        cacheControl: "max-age=31536000,public",
        contentType: "image/gif",
      };

      // Assert
      expect(mockAwsS3.getObject).toHaveBeenCalledWith({
        Bucket: "validBucket",
        Key: "image.gif",
      });
      expect(imageRequestInfo).toEqual(expectedResult);
    });
  });
});
