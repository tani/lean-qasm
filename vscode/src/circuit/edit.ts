import { parseParameterExpression } from "./expression";
import {
  type CircuitDocument,
  type CircuitOperation,
  type CircuitRegister,
  GATE_BY_NAME,
  type GateName,
  type RegisterRef,
} from "./model";
import { isRegisterReferenced, validateCircuit } from "./validation";

export type EditResult = { ok: true; document: CircuitDocument } | { ok: false; message: string };
export type CircuitOperationInput = CircuitOperation extends infer Operation
  ? Operation extends { id: string }
    ? Omit<Operation, "id">
    : never
  : never;

function nextId(prefix: string, ids: string[]): string {
  let index = 0;
  while (ids.includes(`${prefix}-${index}`)) index += 1;
  return `${prefix}-${index}`;
}

function clampInsertionIndex(index: number, length: number): number {
  if (!Number.isFinite(index)) return length;
  return Math.max(0, Math.min(Math.trunc(index), length));
}

export function nextOperationId(document: CircuitDocument): string {
  return nextId(
    "operation",
    document.operations.map((operation) => operation.id),
  );
}

export function nextRegisterId(document: CircuitDocument): string {
  return nextId(
    "register",
    document.registers.map((register) => register.id),
  );
}

export function addGate(
  document: CircuitDocument,
  gate: GateName,
  operands: RegisterRef[],
  insertionIndex = document.operations.length,
): EditResult {
  const definition = GATE_BY_NAME.get(gate);
  if (!definition) return { ok: false, message: `Unsupported gate '${gate}'.` };
  const operation: CircuitOperation = {
    id: nextOperationId(document),
    kind: "gate",
    gate,
    parameters: definition.defaultParameters.map(parseParameterExpression),
    operands,
  };
  const operations = [...document.operations];
  operations.splice(clampInsertionIndex(insertionIndex, operations.length), 0, operation);
  return validateEdit({ ...document, operations });
}

export function addOperation(
  document: CircuitDocument,
  operation: CircuitOperationInput,
  insertionIndex = document.operations.length,
): EditResult {
  const value = { ...operation, id: nextOperationId(document) } as CircuitOperation;
  const operations = [...document.operations];
  operations.splice(clampInsertionIndex(insertionIndex, operations.length), 0, value);
  return validateEdit({ ...document, operations });
}

export function updateOperation(
  document: CircuitDocument,
  operationId: string,
  operation: CircuitOperation,
): EditResult {
  const index = document.operations.findIndex((candidate) => candidate.id === operationId);
  if (index < 0) return { ok: false, message: "The selected operation no longer exists." };
  const operations = [...document.operations];
  operations[index] = { ...operation, id: operationId };
  return validateEdit({ ...document, operations });
}

export function removeOperation(document: CircuitDocument, operationId: string): CircuitDocument {
  return {
    ...document,
    operations: document.operations.filter((operation) => operation.id !== operationId),
  };
}

export function duplicateOperation(document: CircuitDocument, operationId: string): EditResult {
  const index = document.operations.findIndex((operation) => operation.id === operationId);
  const source = document.operations[index];
  if (!source) return { ok: false, message: "The selected operation no longer exists." };
  const clone = structuredClone(source);
  clone.id = nextOperationId(document);
  const operations = [...document.operations];
  operations.splice(index + 1, 0, clone);
  return validateEdit({ ...document, operations });
}

export function moveOperation(
  document: CircuitDocument,
  operationId: string,
  insertionIndex: number,
): EditResult {
  const sourceIndex = document.operations.findIndex((operation) => operation.id === operationId);
  const source = document.operations[sourceIndex];
  if (!source) return { ok: false, message: "The selected operation no longer exists." };
  const operations = document.operations.filter((operation) => operation.id !== operationId);
  const target = clampInsertionIndex(
    insertionIndex > sourceIndex ? insertionIndex - 1 : insertionIndex,
    operations.length,
  );
  operations.splice(target, 0, source);
  return { ok: true, document: { ...document, operations } };
}

export function placeOperation(
  document: CircuitDocument,
  operationId: string,
  insertionIndex: number,
  preferredQubit?: RegisterRef,
): EditResult {
  const source = document.operations.find((operation) => operation.id === operationId);
  if (!source) return { ok: false, message: "The selected operation no longer exists." };

  const moveToFront = (references: RegisterRef[]): RegisterRef[] => {
    if (!preferredQubit || references.length === 0) return references;
    return [
      preferredQubit,
      ...references.filter(
        (reference) =>
          reference.register !== preferredQubit.register ||
          reference.index !== preferredQubit.index,
      ),
    ].slice(0, references.length);
  };

  const operation: CircuitOperation = !preferredQubit
    ? source
    : source.kind === "gate"
      ? { ...source, operands: moveToFront(source.operands) }
      : source.kind === "measurement"
        ? { ...source, source: preferredQubit }
        : source.kind === "reset"
          ? { ...source, target: preferredQubit }
          : { ...source, targets: moveToFront(source.targets) };
  const operations = document.operations.map((candidate) =>
    candidate.id === operationId ? operation : candidate,
  );
  const validated = validateEdit({ ...document, operations });
  return validated.ok ? moveOperation(validated.document, operationId, insertionIndex) : validated;
}

export function placeOperationOperand(
  document: CircuitDocument,
  operationId: string,
  operandIndex: number,
  target: RegisterRef,
): EditResult {
  const operation = document.operations.find((candidate) => candidate.id === operationId);
  if (!operation) return { ok: false, message: "The selected operation no longer exists." };
  if (operation.kind !== "gate") {
    return { ok: false, message: "Only gate operands can be moved independently." };
  }
  const previous = operation.operands[operandIndex];
  if (!previous) return { ok: false, message: "The selected gate endpoint no longer exists." };

  const operands = [...operation.operands];
  const occupiedIndex = operands.findIndex(
    (operand, index) =>
      index !== operandIndex &&
      operand.register === target.register &&
      operand.index === target.index,
  );
  if (occupiedIndex >= 0) operands[occupiedIndex] = previous;
  operands[operandIndex] = target;
  return updateOperation(document, operationId, { ...operation, operands });
}

export function placeMeasurementTarget(
  document: CircuitDocument,
  operationId: string,
  target: RegisterRef,
): EditResult {
  const operation = document.operations.find((candidate) => candidate.id === operationId);
  if (!operation) return { ok: false, message: "The selected operation no longer exists." };
  if (operation.kind !== "measurement") {
    return { ok: false, message: "Only measurement results can target a classical wire." };
  }
  return updateOperation(document, operationId, { ...operation, target });
}

export function addRegister(document: CircuitDocument, kind: "qubit" | "bit"): EditResult {
  const base = kind === "qubit" ? "q" : "c";
  let index = 0;
  let name = base;
  while (document.registers.some((register) => register.name === name)) {
    index += 1;
    name = `${base}${index}`;
  }
  const register: CircuitRegister = { id: nextRegisterId(document), kind, name, size: 1 };
  return validateEdit({ ...document, registers: [...document.registers, register] });
}

export function addWire(document: CircuitDocument, kind: "qubit" | "bit"): EditResult {
  const register = document.registers.find((candidate) => candidate.kind === kind);
  return register
    ? updateRegister(document, register.id, { name: register.name, size: register.size + 1 })
    : addRegister(document, kind);
}

export function updateRegister(
  document: CircuitDocument,
  registerId: string,
  next: Pick<CircuitRegister, "name" | "size">,
): EditResult {
  const previous = document.registers.find((register) => register.id === registerId);
  if (!previous) return { ok: false, message: "The register no longer exists." };
  if (next.size < previous.size) {
    const invalid = document.operations.some((operation) =>
      operationReferences(operation).some(
        (reference) => reference.register === previous.name && reference.index >= next.size,
      ),
    );
    if (invalid)
      return {
        ok: false,
        message: "Remove operations on truncated wires before shrinking this register.",
      };
  }
  const replaceReference = (reference: RegisterRef): RegisterRef =>
    reference.register === previous.name ? { ...reference, register: next.name } : reference;
  const operations = document.operations.map((operation): CircuitOperation => {
    if (operation.kind === "gate")
      return { ...operation, operands: operation.operands.map(replaceReference) };
    if (operation.kind === "measurement")
      return {
        ...operation,
        source: replaceReference(operation.source),
        ...(operation.target ? { target: replaceReference(operation.target) } : {}),
      };
    if (operation.kind === "reset")
      return { ...operation, target: replaceReference(operation.target) };
    return { ...operation, targets: operation.targets.map(replaceReference) };
  });
  const registers = document.registers.map((register) =>
    register.id === registerId ? { ...register, name: next.name, size: next.size } : register,
  );
  return validateEdit({ ...document, registers, operations });
}

export function removeRegister(document: CircuitDocument, registerId: string): EditResult {
  const register = document.registers.find((candidate) => candidate.id === registerId);
  if (!register) return { ok: false, message: "The register no longer exists." };
  if (isRegisterReferenced(document, register.name)) {
    return { ok: false, message: `Remove operations that reference '${register.name}' first.` };
  }
  return {
    ok: true,
    document: {
      ...document,
      registers: document.registers.filter((candidate) => candidate.id !== registerId),
    },
  };
}

export function removeWire(
  document: CircuitDocument,
  registerId: string,
  wireIndex: number,
): EditResult {
  const register = document.registers.find((candidate) => candidate.id === registerId);
  if (!register) return { ok: false, message: "The register no longer exists." };
  if (wireIndex < 0 || wireIndex >= register.size) {
    return { ok: false, message: "The selected wire no longer exists." };
  }
  const referenced = document.operations.some((operation) =>
    operationReferences(operation).some(
      (reference) => reference.register === register.name && reference.index === wireIndex,
    ),
  );
  if (referenced) {
    return {
      ok: false,
      message: `Remove operations on '${register.name}[${wireIndex}]' before deleting this wire.`,
    };
  }
  if (register.size === 1) return removeRegister(document, registerId);

  const compactReference = (reference: RegisterRef): RegisterRef =>
    reference.register === register.name && reference.index > wireIndex
      ? { ...reference, index: reference.index - 1 }
      : reference;
  const operations = document.operations.map((operation): CircuitOperation => {
    if (operation.kind === "gate")
      return { ...operation, operands: operation.operands.map(compactReference) };
    if (operation.kind === "measurement")
      return {
        ...operation,
        source: compactReference(operation.source),
        ...(operation.target ? { target: compactReference(operation.target) } : {}),
      };
    if (operation.kind === "reset")
      return { ...operation, target: compactReference(operation.target) };
    return { ...operation, targets: operation.targets.map(compactReference) };
  });
  const registers = document.registers.map((candidate) =>
    candidate.id === registerId ? { ...candidate, size: candidate.size - 1 } : candidate,
  );
  return validateEdit({ ...document, registers, operations });
}

export function operationReferences(operation: CircuitOperation): RegisterRef[] {
  if (operation.kind === "gate") return operation.operands;
  if (operation.kind === "measurement")
    return operation.target ? [operation.source, operation.target] : [operation.source];
  if (operation.kind === "reset") return [operation.target];
  return operation.targets;
}

function validateEdit(document: CircuitDocument): EditResult {
  const errors = validateCircuit(document);
  return errors.length === 0
    ? { ok: true, document }
    : { ok: false, message: errors[0] ?? "Invalid circuit edit." };
}
