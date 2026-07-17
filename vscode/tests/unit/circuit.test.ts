import { describe, expect, test } from "vitest";
import {
  addGate,
  addWire,
  duplicateOperation,
  moveOperation,
  placeMeasurementTarget,
  placeOperation,
  placeOperationOperand,
  removeRegister,
  removeWire,
  updateRegister,
} from "../../src/circuit/edit";
import {
  parseParameterExpression,
  serializeParameterExpression,
} from "../../src/circuit/expression";
import { reconcileCircuitIdentity } from "../../src/circuit/identity";
import { type CircuitDocument, EMPTY_CIRCUIT, GATE_DEFINITIONS } from "../../src/circuit/model";
import { parseCircuit } from "../../src/circuit/parser";
import { serializeCircuit } from "../../src/circuit/serializer";
import { validateCircuit } from "../../src/circuit/validation";

const bell = `OPENQASM 3.0;
include "stdgates.inc";

qubit[2] q;
bit[2] c;

h q[0];
cx q[0], q[1];
c[0] = measure q[0];
`;

describe("parameter expressions", () => {
  test.each([
    ["pi / 2", "pi / 2"],
    ["-(pi + 0.5) / 2", "-(pi + 0.5) / 2"],
    ["1 + 2 * 3", "1 + 2 * 3"],
    ["π/4", "pi / 4"],
  ])("normalizes %s", (source, expected) => {
    expect(serializeParameterExpression(parseParameterExpression(source))).toBe(expected);
  });

  test.each(["", "theta", "sin(pi)", "pi ** 2", "1 % 2"])("rejects %s", (source) => {
    expect(() => parseParameterExpression(source)).toThrow();
  });
});

describe("OpenQASM circuit adapter", () => {
  test("parses and canonically round trips a Bell circuit", () => {
    const parsed = parseCircuit(bell);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    expect(parsed.document.registers).toHaveLength(2);
    expect(parsed.document.operations.map((operation) => operation.kind)).toEqual([
      "gate",
      "gate",
      "measurement",
    ]);
    const reparsed = parseCircuit(serializeCircuit(parsed.document));
    expect(reparsed).toEqual(parsed);
  });

  test("normalizes comments, arrow measurement, reset, and barrier", () => {
    const parsed = parseCircuit(`OPENQASM 3.0;
      include "stdgates.inc"; // library
      qubit[2] q; bit[1] c;
      /* effects */ measure q[0] -> c[0]; reset q[1]; barrier q[0], q[1];`);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    expect(serializeCircuit(parsed.document)).toContain(
      "c[0] = measure q[0];\nreset q[1];\nbarrier q[0], q[1];",
    );
  });

  test("supports every gate in the editable catalog", () => {
    let document: CircuitDocument = {
      version: "3.0",
      includesStdGates: true,
      registers: [{ id: "register-0", kind: "qubit", name: "q", size: 3 }],
      operations: [],
    };
    for (const gate of GATE_DEFINITIONS) {
      const operands = Array.from({ length: gate.operandCount }, (_, index) => ({
        register: "q",
        index,
      }));
      const result = addGate(document, gate.name, operands);
      expect(result.ok, gate.name).toBe(true);
      if (result.ok) document = result.document;
    }
    const reparsed = parseCircuit(serializeCircuit(document));
    expect(reparsed.ok).toBe(true);
    if (reparsed.ok) expect(reparsed.document.operations).toHaveLength(GATE_DEFINITIONS.length);
  });

  test.each([
    ["wrong version", "OPENQASM 2.0; qreg q[1];"],
    ["dynamic index", 'OPENQASM 3.0; include "stdgates.inc"; qubit[2] q; h q[i];'],
    ["control flow", "OPENQASM 3.0; qubit[1] q; if (true) { reset q[0]; }"],
    ["whole register", 'OPENQASM 3.0; include "stdgates.inc"; qubit[1] q; h q;'],
    ["custom gate", "OPENQASM 3.0; qubit[1] q; custom q[0];"],
    ["late declaration", "OPENQASM 3.0; qubit[1] q; reset q[0]; bit[1] c;"],
    ["bad reference", 'OPENQASM 3.0; include "stdgates.inc"; qubit[1] q; cx q[0], q[1];'],
  ])("rejects %s", (_label, source) => {
    expect(parseCircuit(source).ok).toBe(false);
  });
});

describe("circuit editing", () => {
  test("renames a register and all references atomically", () => {
    const parsed = parseCircuit(bell);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    const result = updateRegister(parsed.document, "register-0", { name: "data", size: 2 });
    expect(result.ok).toBe(true);
    if (!result.ok) return;
    expect(serializeCircuit(result.document)).toContain("h data[0];");
    expect(serializeCircuit(result.document)).toContain("cx data[0], data[1];");
  });

  test("blocks destructive register changes", () => {
    const parsed = parseCircuit(bell);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    expect(updateRegister(parsed.document, "register-0", { name: "q", size: 1 }).ok).toBe(false);
    expect(removeRegister(parsed.document, "register-0").ok).toBe(false);
  });

  test("duplicates and reorders operations", () => {
    const parsed = parseCircuit(bell);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    const duplicated = duplicateOperation(parsed.document, "operation-0");
    expect(duplicated.ok).toBe(true);
    if (!duplicated.ok) return;
    expect(duplicated.document.operations).toHaveLength(4);
    const moved = moveOperation(
      duplicated.document,
      duplicated.document.operations[1]?.id ?? "",
      4,
    );
    expect(moved.ok).toBe(true);
    if (moved.ok) expect(moved.document.operations.at(-1)?.kind).toBe("gate");
  });

  test("clamps insertion positions to the circuit boundaries", () => {
    const parsed = parseCircuit(bell);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    const prepended = addGate(parsed.document, "x", [{ register: "q", index: 0 }], -100);
    expect(prepended.ok).toBe(true);
    if (!prepended.ok) return;
    expect(prepended.document.operations[0]).toMatchObject({ kind: "gate", gate: "x" });
    const appended = addGate(parsed.document, "z", [{ register: "q", index: 0 }], 100);
    expect(appended.ok).toBe(true);
    if (appended.ok) {
      expect(appended.document.operations.at(-1)).toMatchObject({ kind: "gate", gate: "z" });
    }
  });

  test("rejects duplicate editor identities before they reach React keys", () => {
    const parsed = parseCircuit(bell);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    const duplicate = structuredClone(parsed.document);
    const second = duplicate.operations[1];
    if (!second) throw new Error("expected a second operation");
    second.id = duplicate.operations[0]?.id ?? "";
    expect(validateCircuit(duplicate)).toContain("Duplicate operation id 'operation-0'.");
  });

  test("preserves operation identities across a reordered serialize-parse round trip", () => {
    const parsed = parseCircuit(bell);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    const moved = moveOperation(parsed.document, "operation-1", 0);
    expect(moved.ok).toBe(true);
    if (!moved.ok) return;
    const reparsed = parseCircuit(serializeCircuit(moved.document));
    expect(reparsed.ok).toBe(true);
    if (!reparsed.ok) return;
    expect(reparsed.document.operations.map((operation) => operation.id)).toEqual([
      "operation-0",
      "operation-1",
      "operation-2",
    ]);
    const reconciled = reconcileCircuitIdentity(moved.document, reparsed.document);
    expect(reconciled).toBe(moved.document);
    expect(reconciled.operations.map((operation) => operation.id)).toEqual([
      "operation-1",
      "operation-0",
      "operation-2",
    ]);
  });

  test("places a controlled gate on another wire and swaps operand roles", () => {
    const parsed = parseCircuit(bell);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    const placed = placeOperation(parsed.document, "operation-1", 2, {
      register: "q",
      index: 1,
    });
    expect(placed.ok).toBe(true);
    if (!placed.ok) return;
    expect(placed.document.operations[1]).toMatchObject({
      kind: "gate",
      gate: "cx",
      operands: [
        { register: "q", index: 1 },
        { register: "q", index: 0 },
      ],
    });
  });

  test("moves controlled-gate endpoints independently and swaps occupied endpoints", () => {
    const parsed = parseCircuit(`OPENQASM 3.0;
include "stdgates.inc";
qubit[3] q;
cx q[0], q[1];
`);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    const moved = placeOperationOperand(parsed.document, "operation-0", 0, {
      register: "q",
      index: 2,
    });
    expect(moved.ok).toBe(true);
    if (!moved.ok) return;
    expect(moved.document.operations[0]).toMatchObject({
      operands: [
        { register: "q", index: 2 },
        { register: "q", index: 1 },
      ],
    });
    const swapped = placeOperationOperand(parsed.document, "operation-0", 0, {
      register: "q",
      index: 1,
    });
    expect(swapped.ok).toBe(true);
    if (swapped.ok) {
      expect(swapped.document.operations[0]).toMatchObject({
        operands: [
          { register: "q", index: 1 },
          { register: "q", index: 0 },
        ],
      });
    }
  });

  test("moves a measurement's classical endpoint without changing its quantum source", () => {
    const parsed = parseCircuit(`OPENQASM 3.0;
qubit[1] q;
bit[2] c;
c[0] = measure q[0];
`);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    const moved = placeMeasurementTarget(parsed.document, "operation-0", {
      register: "c",
      index: 1,
    });
    expect(moved.ok).toBe(true);
    if (!moved.ok) return;
    expect(moved.document.operations[0]).toMatchObject({
      kind: "measurement",
      source: { register: "q", index: 0 },
      target: { register: "c", index: 1 },
    });
  });

  test("adds wires and compacts references after deleting an unused wire", () => {
    const parsed = parseCircuit(`OPENQASM 3.0;
include "stdgates.inc";
qubit[3] q;
cx q[1], q[2];
`);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    const removed = removeWire(parsed.document, "register-0", 0);
    expect(removed.ok).toBe(true);
    if (!removed.ok) return;
    expect(removed.document.registers[0]?.size).toBe(2);
    expect(removed.document.operations[0]).toMatchObject({
      operands: [
        { register: "q", index: 0 },
        { register: "q", index: 1 },
      ],
    });
    const added = addWire(removed.document, "qubit");
    expect(added.ok).toBe(true);
    if (added.ok) expect(added.document.registers[0]?.size).toBe(3);
  });

  test("does not delete a wire while an operation references it", () => {
    const parsed = parseCircuit(bell);
    expect(parsed.ok).toBe(true);
    if (!parsed.ok) return;
    expect(removeWire(parsed.document, "register-0", 0)).toMatchObject({
      ok: false,
      message: "Remove operations on 'q[0]' before deleting this wire.",
    });
  });

  test("serializes a clean empty circuit template", () => {
    expect(serializeCircuit(EMPTY_CIRCUIT)).toBe(`OPENQASM 3.0;
include "stdgates.inc";

qubit[2] q;
bit[2] c;
`);
  });
});
