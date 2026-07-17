import { cleanup, fireEvent, render } from "@testing-library/react";
import axe from "axe-core";
import { StrictMode, useState } from "react";
import { afterEach, beforeEach, describe, expect, test, vi } from "vitest";
import { page, server, userEvent } from "vitest/browser";
import type { CircuitDocument } from "../../src/circuit/model";
import { parseCircuit } from "../../src/circuit/parser";
import { CircuitWorkbench } from "../../src/webview/CircuitWorkbench";
import "../../src/webview/styles.css";

const parsed = parseCircuit(`OPENQASM 3.0;
include "stdgates.inc";
qubit[2] q;
bit[2] c;
h q[0];
cx q[0], q[1];
`);
if (!parsed.ok) throw new Error(parsed.message);
const bellDocument = parsed.document;

function circuit(source: string): CircuitDocument {
  const result = parseCircuit(source);
  if (!result.ok) throw new Error(result.message);
  return result.document;
}

afterEach(cleanup);

beforeEach(async () => {
  await page.viewport(1440, 900);
});

function setup(document: CircuitDocument = bellDocument) {
  const onChange = vi.fn();
  render(
    <CircuitWorkbench
      document={document}
      onChange={onChange}
      onUndo={vi.fn()}
      onRedo={vi.fn()}
      onOpenSource={vi.fn()}
    />,
  );
  return { onChange };
}

function StatefulWorkbench({ initialDocument }: { initialDocument: CircuitDocument }) {
  const [document, setDocument] = useState(initialDocument);
  return (
    <CircuitWorkbench
      document={document}
      onChange={setDocument}
      onUndo={vi.fn()}
      onRedo={vi.fn()}
      onOpenSource={vi.fn()}
    />
  );
}

function setupStateful(document: CircuitDocument = bellDocument) {
  render(
    <StrictMode>
      <StatefulWorkbench initialDocument={document} />
    </StrictMode>,
  );
}

describe("circuit workbench", () => {
  test("adds a gate from the searchable palette", async () => {
    const { onChange } = setup();
    const search = page.getByPlaceholder("Filter gates");
    await userEvent.fill(search, "Pauli Y");
    await page.getByRole("button", { name: "Y 1q" }).click();
    expect(onChange).toHaveBeenCalledOnce();
    expect(onChange.mock.calls[0]?.[0].operations).toHaveLength(3);
  });

  test("places a dragged gate into a specific statement slot", async () => {
    const { onChange } = setup();
    await page
      .getByRole("button", { name: "Y 1q" })
      .dropTo(page.getByRole("button", { name: "Insert operation at step 2" }));
    expect(onChange).toHaveBeenCalledOnce();
    const changed = onChange.mock.calls[0]?.[0] as CircuitDocument;
    expect(changed.operations.map((operation) => operation.kind)).toEqual(["gate", "gate", "gate"]);
    expect(changed.operations[1]).toMatchObject({ kind: "gate", gate: "y" });
  });

  test("places a dragged effect into a specific statement slot", async () => {
    const { onChange } = setup();
    await page
      .getByRole("button", { name: "Measure" })
      .dropTo(page.getByRole("button", { name: "Insert operation at step 2" }));
    expect(onChange).toHaveBeenCalledOnce();
    const changed = onChange.mock.calls[0]?.[0] as CircuitDocument;
    expect(changed.operations[1]).toMatchObject({
      kind: "measurement",
      source: { register: "q", index: 0 },
      target: { register: "c", index: 0 },
    });
  });

  test("reorders an existing operation by dragging it between steps", async () => {
    const { onChange } = setup();
    await page
      .getByRole("button", { name: "cx gate on q[0], q[1]" })
      .dropTo(page.getByRole("button", { name: "Insert operation at step 1" }));
    expect(onChange).toHaveBeenCalledOnce();
    const changed = onChange.mock.calls[0]?.[0] as CircuitDocument;
    expect(changed.operations.map((operation) => operation.id)).toEqual([
      bellDocument.operations[1]?.id,
      bellDocument.operations[0]?.id,
    ]);
    const h = page.getByRole("button", { name: "h gate on q[0]" }).element();
    const cx = page.getByRole("button", { name: "cx gate on q[0], q[1]" }).element();
    const hNode = h.closest<HTMLElement>(".operation-node");
    const cxNode = cx.closest<HTMLElement>(".operation-node");
    expect(Number.parseFloat(cxNode?.style.left ?? "0")).toBeLessThan(
      Number.parseFloat(hNode?.style.left ?? "0"),
    );
    expect(cx.querySelector(".step-index")?.textContent).toBe("01");
    expect(h.querySelector(".step-index")?.textContent).toBe("02");
  });

  test("previews reordered columns before the dragged operation is dropped", () => {
    const { onChange } = setup();
    const h = page.getByRole("button", { name: "h gate on q[0]" }).element();
    const cx = page.getByRole("button", { name: "cx gate on q[0], q[1]" }).element();
    const firstSlot = page.getByRole("button", { name: "Insert operation at step 1" }).element();
    const dataTransfer = new DataTransfer();
    fireEvent.dragStart(cx, { dataTransfer });
    fireEvent.dragOver(firstSlot, { dataTransfer });
    const hNode = h.closest<HTMLElement>(".operation-node");
    const cxNode = cx.closest<HTMLElement>(".operation-node");
    expect(Number.parseFloat(cxNode?.style.left ?? "0")).toBeLessThan(
      Number.parseFloat(hNode?.style.left ?? "0"),
    );
    expect(cx.querySelector(".step-index")?.textContent).toBe("01");
    expect(h.querySelector(".step-index")?.textContent).toBe("02");
    expect(onChange).not.toHaveBeenCalled();
    fireEvent.dragEnd(cx, { dataTransfer });
  });

  test("keeps previewed gate nodes stable when the drop is committed", async () => {
    setupStateful();
    const track = page.getByLabelText("Ordered OpenQASM circuit").element();
    const before = Array.from(track.querySelectorAll<HTMLElement>(".operation-body"));
    const draggedNode = page
      .getByRole("button", { name: "cx gate on q[0], q[1]" })
      .element()
      .closest<HTMLElement>(".operation-node");
    const leftMutations: string[] = [];
    const observer = new MutationObserver((records) => {
      for (const record of records) {
        const left = record.oldValue?.match(/left:\s*([^;]+)/)?.[1];
        if (left) leftMutations.push(left);
      }
    });
    if (draggedNode) {
      observer.observe(draggedNode, {
        attributes: true,
        attributeFilter: ["style"],
        attributeOldValue: true,
      });
    }
    await page
      .getByRole("button", { name: "cx gate on q[0], q[1]" })
      .dropTo(page.getByRole("button", { name: "Insert operation at step 1" }));
    await new Promise<void>((resolve) => requestAnimationFrame(() => resolve()));
    observer.disconnect();
    const after = Array.from(track.querySelectorAll<HTMLElement>(".operation-body"));
    expect(after[0]).toBe(before[0]);
    expect(after[1]).toBe(before[1]);
    const hNode = page
      .getByRole("button", { name: "h gate on q[0]" })
      .element()
      .closest<HTMLElement>(".operation-node");
    const cxNode = page
      .getByRole("button", { name: "cx gate on q[0], q[1]" })
      .element()
      .closest<HTMLElement>(".operation-node");
    expect(Number.parseFloat(cxNode?.style.left ?? "0")).toBeLessThan(
      Number.parseFloat(hNode?.style.left ?? "0"),
    );
    expect(leftMutations).toHaveLength(1);
  });

  test("swaps the vertical roles of a controlled gate by dragging it to another wire", async () => {
    const { onChange } = setup();
    await page
      .getByRole("button", { name: "cx gate on q[0], q[1]" })
      .dropTo(page.getByRole("button", { name: "Drop operations on q[1]" }));
    expect(onChange).toHaveBeenCalledOnce();
    const changed = onChange.mock.calls[0]?.[0] as CircuitDocument;
    expect(changed.operations[1]).toMatchObject({
      kind: "gate",
      gate: "cx",
      operands: [
        { register: "q", index: 1 },
        { register: "q", index: 0 },
      ],
    });
  });

  test("moves one controlled-gate endpoint without moving the other endpoint", async () => {
    const document = circuit(`OPENQASM 3.0;
include "stdgates.inc";
qubit[3] q;
cx q[0], q[1];
`);
    const { onChange } = setup(document);
    await page
      .getByRole("button", { name: "Move cx operand 1 from q[0]" })
      .dropTo(page.getByRole("button", { name: "Drop operations on q[2]" }));
    expect(onChange).toHaveBeenCalledOnce();
    const changed = onChange.mock.calls[0]?.[0] as CircuitDocument;
    expect(changed.operations[0]).toMatchObject({
      operands: [
        { register: "q", index: 2 },
        { register: "q", index: 1 },
      ],
    });
  });

  test("swaps endpoints when one endpoint is dropped on the occupied wire", async () => {
    const { onChange } = setup();
    await page
      .getByRole("button", { name: "Move cx operand 1 from q[0]" })
      .dropTo(page.getByRole("button", { name: "Drop operations on q[1]" }));
    expect(onChange).toHaveBeenCalledOnce();
    const changed = onChange.mock.calls[0]?.[0] as CircuitDocument;
    expect(changed.operations[1]).toMatchObject({
      operands: [
        { register: "q", index: 1 },
        { register: "q", index: 0 },
      ],
    });
  });

  test("moves only the classical endpoint of a measurement to another bit wire", async () => {
    const document = circuit(`OPENQASM 3.0;
qubit[1] q;
bit[2] c;
c[0] = measure q[0];
`);
    const { onChange } = setup(document);
    await page
      .getByRole("button", { name: "Move measurement classical target from c[0]" })
      .dropTo(page.getByRole("button", { name: "Drop operations on c[1]" }));
    expect(onChange).toHaveBeenCalledOnce();
    const changed = onChange.mock.calls[0]?.[0] as CircuitDocument;
    expect(changed.operations[0]).toMatchObject({
      kind: "measurement",
      source: { register: "q", index: 0 },
      target: { register: "c", index: 1 },
    });
  });

  test("deletes an existing operation by dragging it to Discard", async () => {
    const { onChange } = setup();
    await page
      .getByRole("button", { name: "h gate on q[0]" })
      .dropTo(page.getByRole("button", { name: "Drop operation to delete" }));
    expect(onChange).toHaveBeenCalledOnce();
    const changed = onChange.mock.calls[0]?.[0] as CircuitDocument;
    expect(changed.operations).toHaveLength(1);
    expect(changed.operations[0]).toMatchObject({ kind: "gate", gate: "cx" });
  });

  test("selects, duplicates, and deletes an operation", async () => {
    const { onChange } = setup();
    await page.getByRole("button", { name: "h gate on q[0]" }).click();
    await page.getByRole("button", { name: "Duplicate" }).click();
    expect(onChange).toHaveBeenCalledOnce();
    expect(onChange.mock.calls[0]?.[0].operations).toHaveLength(3);
    await page.getByRole("button", { name: "Delete", exact: true }).click();
    expect(onChange).toHaveBeenCalledTimes(2);
  });

  test("adds a register from the inspector", async () => {
    const { onChange } = setup();
    await page.getByRole("button", { name: "+ Qubit register" }).click();
    expect(onChange).toHaveBeenCalledOnce();
    expect(onChange.mock.calls[0]?.[0].registers).toHaveLength(3);
  });

  test("adds quantum and classical wires from the canvas", async () => {
    const { onChange } = setup();
    await page.getByRole("button", { name: "Add quantum wire" }).click();
    await page.getByRole("button", { name: "Add classical wire" }).click();
    expect(onChange).toHaveBeenCalledTimes(2);
    expect(onChange.mock.calls[0]?.[0].registers[0]?.size).toBe(3);
    expect(onChange.mock.calls[1]?.[0].registers[1]?.size).toBe(3);
  });

  test("deletes an unused wire from the canvas", async () => {
    const document = circuit(`OPENQASM 3.0;
include "stdgates.inc";
qubit[3] q;
h q[0];
`);
    const { onChange } = setup(document);
    await page.getByRole("button", { name: "Delete wire q[1]" }).click();
    expect(onChange).toHaveBeenCalledOnce();
    const changed = onChange.mock.calls[0]?.[0] as CircuitDocument;
    expect(changed.registers[0]?.size).toBe(2);
  });

  test("explains why a referenced wire cannot be deleted", async () => {
    const { onChange } = setup();
    await page.getByRole("button", { name: "Delete wire q[0]" }).click();
    expect(onChange).not.toHaveBeenCalled();
    expect(page.getByText("Remove operations on 'q[0]' before deleting this wire.")).toBeVisible();
  });

  test("renames a register through the topology inspector", async () => {
    const { onChange } = setup();
    const registerName = page.getByLabelText("Register name").first();
    await registerName.fill("data");
    await userEvent.tab();
    expect(onChange).toHaveBeenCalledOnce();
    const changed = onChange.mock.calls[0]?.[0] as CircuitDocument;
    expect(changed.registers[0]?.name).toBe("data");
    const firstOperation = changed.operations[0];
    expect(firstOperation?.kind).toBe("gate");
    if (firstOperation?.kind !== "gate") throw new Error("expected a gate operation");
    expect(firstOperation.operands[0]?.register).toBe("data");
  });

  test("commits literal gate parameter expressions", async () => {
    const document = circuit(`OPENQASM 3.0;
include "stdgates.inc";
qubit[1] q;
rx(pi / 2) q[0];
`);
    const { onChange } = setup(document);
    await page.getByRole("button", { name: "rx gate on q[0]" }).click();
    const parameter = page.getByLabelText("Parameter 1");
    await parameter.fill("-pi/4");
    await userEvent.tab();
    expect(onChange).toHaveBeenCalledOnce();
    const operation = onChange.mock.calls[0]?.[0].operations[0];
    expect(operation?.kind).toBe("gate");
    if (operation?.kind !== "gate") throw new Error("expected a gate operation");
    expect(operation.parameters[0]).toMatchObject({
      kind: "binary",
      operator: "/",
    });
  });

  test("supports keyboard deletion of the selected statement", async () => {
    const { onChange } = setup();
    const operation = page.getByRole("button", { name: "h gate on q[0]" });
    await operation.click();
    if (server.browser === "webkit") fireEvent.keyDown(operation.element(), { key: "Delete" });
    else await userEvent.keyboard("{Delete}");
    expect(onChange).toHaveBeenCalledOnce();
    expect(onChange.mock.calls[0]?.[0].operations).toHaveLength(1);
  });

  test("updates the visual zoom without changing source", async () => {
    const { onChange } = setup();
    await page.getByRole("slider", { name: "Circuit zoom" }).fill("140");
    expect(page.getByText("140%")).toBeVisible();
    expect(onChange).not.toHaveBeenCalled();
  });

  test("keeps the editor controls available at a narrow viewport", async () => {
    await page.viewport(760, 780);
    setup();
    expect(page.getByRole("main")).toBeVisible();
    expect(page.getByRole("complementary", { name: "Gate palette" })).toBeVisible();
    expect(page.getByRole("complementary", { name: "Circuit inspector" })).toBeVisible();
    expect(page.getByRole("button", { name: "Source" })).toBeVisible();
  });

  test("has no automatically detectable accessibility violations", async () => {
    setup();
    const results = await axe.run(document.body, {
      rules: { "color-contrast": { enabled: false } },
    });
    expect(results.violations).toEqual([]);
  });

  test("matches the Bell workbench visual baseline", async () => {
    if (server.browser !== "chromium") return;
    setup();
    const workbench = page.getByRole("main");
    await page.getByLabelText("Ordered OpenQASM circuit").hover({ position: { x: 600, y: 20 } });
    await expect(workbench).toMatchScreenshot("bell-workbench.png");
  });
});
