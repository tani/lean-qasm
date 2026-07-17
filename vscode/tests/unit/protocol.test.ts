import { describe, expect, test } from "vitest";
import { isWebviewMessage } from "../../src/protocol";

describe("webview protocol", () => {
  test.each(["ready", "undo", "redo", "openSource"])("accepts %s", (type) => {
    expect(isWebviewMessage({ type })).toBe(true);
  });

  test("validates document replacement payloads", () => {
    expect(
      isWebviewMessage({ type: "replaceDocument", requestId: "1", baseVersion: 2, text: "qasm" }),
    ).toBe(true);
    expect(
      isWebviewMessage({ type: "replaceDocument", requestId: "1", baseVersion: "2", text: "qasm" }),
    ).toBe(false);
    expect(isWebviewMessage({ type: "unknown" })).toBe(false);
    expect(isWebviewMessage(null)).toBe(false);
  });
});
