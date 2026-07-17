import {
  type CircuitDocument,
  type CircuitOperation,
  GATE_BY_NAME,
  type RegisterRef,
  refKey,
} from "./model";

const IDENTIFIER = /^[A-Za-z_][A-Za-z0-9_]*$/;
const RESERVED = new Set([
  "OPENQASM",
  "include",
  "qubit",
  "bit",
  "measure",
  "reset",
  "barrier",
  "gate",
  "def",
  "extern",
  "if",
  "else",
  "for",
  "while",
  "switch",
  "case",
  "default",
  "input",
  "output",
  "const",
  "let",
  "return",
  "break",
  "continue",
  "cal",
  "defcal",
]);

export function validateRegisterName(name: string): string | undefined {
  if (!IDENTIFIER.test(name))
    return "Names must start with a letter or underscore and contain only letters, digits, or underscores.";
  if (RESERVED.has(name)) return `'${name}' is reserved by OpenQASM.`;
  return undefined;
}

function validateReference(
  document: CircuitDocument,
  reference: RegisterRef,
  expected: "qubit" | "bit",
): string | undefined {
  const register = document.registers.find((candidate) => candidate.name === reference.register);
  if (!register) return `Unknown register '${reference.register}'.`;
  if (register.kind !== expected)
    return `${refKey(reference)} must refer to a ${expected} register.`;
  if (
    !Number.isInteger(reference.index) ||
    reference.index < 0 ||
    reference.index >= register.size
  ) {
    return `${refKey(reference)} is outside ${reference.register}[0:${register.size - 1}].`;
  }
  return undefined;
}

export function validateOperation(
  document: CircuitDocument,
  operation: CircuitOperation,
): string[] {
  const errors: string[] = [];
  if (operation.kind === "gate") {
    const definition = GATE_BY_NAME.get(operation.gate);
    if (!definition) return [`Unsupported gate '${operation.gate}'.`];
    if (operation.parameters.length !== definition.parameterCount) {
      errors.push(`${operation.gate} expects ${definition.parameterCount} parameter(s).`);
    }
    if (operation.operands.length !== definition.operandCount) {
      errors.push(`${operation.gate} expects ${definition.operandCount} qubit operand(s).`);
    }
    for (const operand of operation.operands) {
      const error = validateReference(document, operand, "qubit");
      if (error) errors.push(error);
    }
    const unique = new Set(operation.operands.map(refKey));
    if (unique.size !== operation.operands.length)
      errors.push("Gate operands must be distinct qubits.");
  } else if (operation.kind === "measurement") {
    const sourceError = validateReference(document, operation.source, "qubit");
    if (sourceError) errors.push(sourceError);
    if (operation.target) {
      const targetError = validateReference(document, operation.target, "bit");
      if (targetError) errors.push(targetError);
    }
  } else if (operation.kind === "reset") {
    const error = validateReference(document, operation.target, "qubit");
    if (error) errors.push(error);
  } else {
    if (operation.targets.length === 0) errors.push("A barrier requires at least one qubit.");
    for (const target of operation.targets) {
      const error = validateReference(document, target, "qubit");
      if (error) errors.push(error);
    }
    if (new Set(operation.targets.map(refKey)).size !== operation.targets.length) {
      errors.push("Barrier targets must be distinct qubits.");
    }
  }
  return errors;
}

export function validateCircuit(document: CircuitDocument): string[] {
  const errors: string[] = [];
  const names = new Set<string>();
  const registerIds = new Set<string>();
  for (const register of document.registers) {
    if (registerIds.has(register.id)) errors.push(`Duplicate register id '${register.id}'.`);
    registerIds.add(register.id);
    const nameError = validateRegisterName(register.name);
    if (nameError) errors.push(nameError);
    if (names.has(register.name)) errors.push(`Duplicate register '${register.name}'.`);
    names.add(register.name);
    if (!Number.isInteger(register.size) || register.size <= 0) {
      errors.push(`${register.name} must have a positive integer size.`);
    }
  }
  const operationIds = new Set<string>();
  for (const operation of document.operations) {
    if (operationIds.has(operation.id)) errors.push(`Duplicate operation id '${operation.id}'.`);
    operationIds.add(operation.id);
    errors.push(...validateOperation(document, operation));
  }
  return errors;
}

export function isRegisterReferenced(document: CircuitDocument, registerName: string): boolean {
  return document.operations.some((operation) => {
    if (operation.kind === "gate")
      return operation.operands.some((ref) => ref.register === registerName);
    if (operation.kind === "measurement") {
      return (
        operation.source.register === registerName || operation.target?.register === registerName
      );
    }
    if (operation.kind === "reset") return operation.target.register === registerName;
    return operation.targets.some((ref) => ref.register === registerName);
  });
}
