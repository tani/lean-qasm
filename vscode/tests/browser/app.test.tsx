import { act, cleanup, render } from "@testing-library/react";
import { afterEach, describe, expect, test } from "vitest";
import { page } from "vitest/browser";
import { parseCircuit } from "../../src/circuit/parser";
import type { HostToWebviewMessage, WebviewToHostMessage } from "../../src/protocol";
import { CircuitEditorApp, type EditorBridge } from "../../src/webview/App";
import "../../src/webview/styles.css";

const parsed = parseCircuit(`OPENQASM 3.0;
include "stdgates.inc";
qubit[2] q;
bit[2] c;
h q[0];
cx q[0], q[1];
`);
if (!parsed.ok) throw new Error(parsed.message);

class TestBridge implements EditorBridge {
  readonly messages: WebviewToHostMessage[] = [];
  private listener: ((message: HostToWebviewMessage) => void) | undefined;

  postMessage(message: WebviewToHostMessage) {
    this.messages.push(message);
  }

  subscribe(listener: (message: HostToWebviewMessage) => void) {
    this.listener = listener;
    return () => {
      this.listener = undefined;
    };
  }

  emit(message: HostToWebviewMessage) {
    this.listener?.(message);
  }
}

afterEach(cleanup);

describe("custom editor bridge", () => {
  test("announces readiness while the source is loading", () => {
    const bridge = new TestBridge();
    render(<CircuitEditorApp bridge={bridge} />);
    expect(bridge.messages).toEqual([{ type: "ready" }]);
    expect(page.getByText("Resolving circuit topology…")).toBeVisible();
  });

  test("renders host source and routes source-editor requests", async () => {
    const bridge = new TestBridge();
    render(<CircuitEditorApp bridge={bridge} />);
    act(() => bridge.emit({ type: "documentChanged", version: 4, text: "", parsed }));
    expect(page.getByRole("heading", { name: "Circuit workbench" })).toBeVisible();
    await page.getByRole("button", { name: "Source" }).click();
    expect(bridge.messages.at(-1)).toEqual({ type: "openSource" });
  });

  test("keeps unsupported programs read-only and explains the boundary", async () => {
    const bridge = new TestBridge();
    render(<CircuitEditorApp bridge={bridge} />);
    act(() =>
      bridge.emit({
        type: "documentChanged",
        version: 8,
        text: "if (true) {}",
        parsed: {
          ok: false,
          category: "unsupported",
          message: "Control-flow statements are outside the graphical subset.",
        },
      }),
    );
    expect(page.getByRole("heading", { name: "This source is safer in text mode." })).toBeVisible();
    await page.getByRole("button", { name: "Open source editor" }).click();
    expect(bridge.messages.at(-1)).toEqual({ type: "openSource" });
  });

  test("sends canonical OpenQASM edits with the current document version", async () => {
    const bridge = new TestBridge();
    render(<CircuitEditorApp bridge={bridge} />);
    act(() => bridge.emit({ type: "documentChanged", version: 12, text: "", parsed }));
    await page.getByPlaceholder("Filter gates").fill("Pauli Y");
    await page.getByRole("button", { name: "Y 1q" }).click();
    const edit = bridge.messages.at(-1);
    expect(edit).toMatchObject({ type: "replaceDocument", baseVersion: 12 });
    if (edit?.type !== "replaceDocument") throw new Error("expected a source replacement");
    expect(edit.text).toContain("y q[0];");
  });

  test("queues rapid edits and rebases the latest circuit after each host acknowledgement", async () => {
    const bridge = new TestBridge();
    render(<CircuitEditorApp bridge={bridge} />);
    act(() => bridge.emit({ type: "documentChanged", version: 12, text: "", parsed }));

    await page.getByPlaceholder("Filter gates").fill("Pauli Y");
    await page.getByRole("button", { name: "Y 1q" }).click();
    const firstEdit = bridge.messages.at(-1);
    if (firstEdit?.type !== "replaceDocument") throw new Error("expected the first edit");

    await page.getByPlaceholder("Filter gates").fill("Pauli Z");
    await page.getByRole("button", { name: "Z 1q" }).click();
    expect(bridge.messages.filter((message) => message.type === "replaceDocument")).toHaveLength(1);

    const firstParsed = parseCircuit(firstEdit.text);
    act(() =>
      bridge.emit({
        type: "documentChanged",
        version: 13,
        text: firstEdit.text,
        parsed: firstParsed,
        requestId: firstEdit.requestId,
      }),
    );
    const secondEdit = bridge.messages.at(-1);
    expect(secondEdit).toMatchObject({ type: "replaceDocument", baseVersion: 13 });
    if (secondEdit?.type !== "replaceDocument") throw new Error("expected the queued edit");
    expect(secondEdit.text).toContain("y q[0];");
    expect(secondEdit.text).toContain("z q[0];");

    const secondParsed = parseCircuit(secondEdit.text);
    act(() =>
      bridge.emit({
        type: "documentChanged",
        version: 14,
        text: secondEdit.text,
        parsed: secondParsed,
        requestId: secondEdit.requestId,
      }),
    );
    expect(page.getByText("Circuit is structurally valid.")).toBeVisible();
  });

  test("does not send source replacements for semantic no-op edits", async () => {
    const bridge = new TestBridge();
    render(<CircuitEditorApp bridge={bridge} />);
    act(() => bridge.emit({ type: "documentChanged", version: 12, text: "", parsed }));
    await page.getByRole("button", { name: "h gate on q[0]" }).click();
    await page.getByRole("button", { name: "Move operation left" }).click();
    expect(bridge.messages).toEqual([{ type: "ready" }]);
  });

  test("rolls back an optimistic edit when the host rejects it", async () => {
    const bridge = new TestBridge();
    render(<CircuitEditorApp bridge={bridge} />);
    act(() => bridge.emit({ type: "documentChanged", version: 12, text: "", parsed }));
    await page.getByPlaceholder("Filter gates").fill("Pauli Y");
    await page.getByRole("button", { name: "Y 1q" }).click();
    const edit = bridge.messages.at(-1);
    if (edit?.type !== "replaceDocument") throw new Error("expected a source replacement");

    act(() =>
      bridge.emit({
        type: "editRejected",
        requestId: edit.requestId,
        message: "VS Code could not apply the circuit edit.",
      }),
    );
    expect(page.getByText("VS Code could not apply the circuit edit.")).toBeVisible();
    expect(page.getByText("2 ordered steps")).toBeVisible();
  });

  test("preserves gate DOM identity when the host reparses a reordered commit", async () => {
    await page.viewport(1440, 900);
    const bridge = new TestBridge();
    render(<CircuitEditorApp bridge={bridge} />);
    act(() => bridge.emit({ type: "documentChanged", version: 20, text: "", parsed }));
    const cx = page.getByRole("button", { name: "cx gate on q[0], q[1]" });
    const cxNode = cx.element().closest<HTMLElement>(".operation-node");
    const leftMutations: string[] = [];
    const observer = new MutationObserver((records) => {
      for (const record of records) {
        const left = record.oldValue?.match(/left:\s*([^;]+)/)?.[1];
        if (left) leftMutations.push(left);
      }
    });
    if (cxNode) {
      observer.observe(cxNode, {
        attributes: true,
        attributeFilter: ["style"],
        attributeOldValue: true,
      });
    }
    await cx.dropTo(page.getByRole("button", { name: "Insert operation at step 1" }));
    const edit = bridge.messages.at(-1);
    expect(edit?.type).toBe("replaceDocument");
    if (edit?.type !== "replaceDocument") throw new Error("expected a source replacement");
    const reparsed = parseCircuit(edit.text);
    expect(reparsed.ok).toBe(true);
    act(() =>
      bridge.emit({
        type: "documentChanged",
        version: 21,
        text: edit.text,
        parsed: reparsed,
        requestId: edit.requestId,
      }),
    );
    await new Promise<void>((resolve) => requestAnimationFrame(() => resolve()));
    observer.disconnect();
    const acknowledgedCxNode = page
      .getByRole("button", { name: "cx gate on q[0], q[1]" })
      .element()
      .closest<HTMLElement>(".operation-node");
    expect(acknowledgedCxNode).toBe(cxNode);
    expect(leftMutations).toHaveLength(1);
  });
});
