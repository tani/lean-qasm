import type { CircuitParseResult } from "./circuit/parser";

export type HostToWebviewMessage =
  | {
      type: "documentChanged";
      version: number;
      text: string;
      parsed: CircuitParseResult;
      requestId?: string;
    }
  | { type: "editRejected"; requestId: string; message: string }
  | { type: "focusOperation"; operationId: string };

export type WebviewToHostMessage =
  | { type: "ready" }
  | { type: "replaceDocument"; requestId: string; baseVersion: number; text: string }
  | { type: "undo" }
  | { type: "redo" }
  | { type: "openSource" };

export function isWebviewMessage(value: unknown): value is WebviewToHostMessage {
  if (!value || typeof value !== "object" || !("type" in value)) return false;
  const message = value as Record<string, unknown>;
  if (
    message.type === "ready" ||
    message.type === "undo" ||
    message.type === "redo" ||
    message.type === "openSource"
  )
    return true;
  return (
    message.type === "replaceDocument" &&
    typeof message.requestId === "string" &&
    typeof message.baseVersion === "number" &&
    typeof message.text === "string"
  );
}
