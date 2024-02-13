// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

import { consoleInfoSpy } from "../mock";

import S3 from "aws-sdk/clients/s3";
import SecretsManager from "aws-sdk/clients/secretsmanager";

import { ImageRequest } from "../../image-request";
import { RequestTypes, StatusCodes } from "../../lib";
import { SecretProvider } from "../../secret-provider";

describe("parseRequestType", () => {
  const s3Client = new S3();
  const secretsManager = new SecretsManager();
  const secretProvider = new SecretProvider(secretsManager);
  const OLD_ENV = process.env;

  beforeEach(() => {
    process.env = { ...OLD_ENV };
  });

  afterAll(() => {
    process.env = OLD_ENV;
  });

  it("Should pass if the method detects a default request", () => {
    // Arrange
    const event = {
      path: "/eyJidWNrZXQiOiJteS1zYW1wbGUtYnVja2V0Iiwia2V5IjoibXktc2FtcGxlLWtleSIsImVkaXRzIjp7ImdyYXlzY2FsZSI6dHJ1ZX19",
    };
    process.env = {};

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const result = imageRequest.parseRequestType(event);

    // Assert
    const expectedResult = RequestTypes.DEFAULT;
    expect(result).toEqual(expectedResult);
  });

  it("Should detetct external if path contains http", () => {
    // Arrange
    const event = {
      path: "/unsafe/filters:brightness(10):contrast(30)/http://upload.wikimedia.org/wikipedia/commons/thumb/7/79/Coffee_berries_1.jpg/1200px-Coffee_berries_1.jpg",
    };
    process.env = {};

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const result = imageRequest.parseRequestType(event);

    // Assert
    expect(result).toEqual(RequestTypes.EXTERNAL);
  });

  it("Should detetct external if path contains https", () => {
    // Arrange
    const event = {
      path: "/unsafe/filters:brightness(10):contrast(30)/https://upload.wikimedia.org/wikipedia/commons/thumb/7/79/Coffee_berries_1.jpg/1200px-Coffee_berries_1.jpg",
    };
    process.env = {};

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const result = imageRequest.parseRequestType(event);

    // Assert
    expect(result).toEqual(RequestTypes.EXTERNAL);
  });

  it("Should pass if get a request with supported image extension", () => {
    // Arrange
    const events = [".jpg", ".jpeg", ".png", ".webp", ".tiff", ".tif", ".svg"].map((extension) => ({
      path: `image${extension}`,
    }));
    process.env = {};

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const results = events.map((event) => imageRequest.parseRequestType(event));

    // Assert
    expect(results).toEqual(new Array(events.length).fill(RequestTypes.THUMBOR));
  });

  it("Should pass if the method detects a custom request", () => {
    // Arrange
    const event = { path: "/additionalImageRequestParameters/image.jpg" };
    process.env = {
      REWRITE_MATCH_PATTERN: "matchPattern",
      REWRITE_SUBSTITUTION: "substitutionString",
    };

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);
    const result = imageRequest.parseRequestType(event);

    // Assert
    const expectedResult = RequestTypes.CUSTOM;
    expect(result).toEqual(expectedResult);
  });

  it("Should throw an error if the method cannot determine the request type based on the three groups given", () => {
    // Arrange
    const event = { path: "12x12e24d234r2ewxsad123d34r.bmp" };

    process.env = {};

    // Act
    const imageRequest = new ImageRequest(s3Client, secretProvider);

    // Assert
    try {
      imageRequest.parseRequestType(event);
    } catch (error) {
      expect(error).toMatchObject({
        status: StatusCodes.BAD_REQUEST,
        code: "RequestTypeError",
        message:
          "The type of request you are making could not be processed. Please ensure that your original image is of a supported file type (jpg, png, tiff, webp, svg, gif) and that your image request is provided in the correct syntax. Refer to the documentation for additional guidance on forming image requests.",
      });
    }
  });
});
