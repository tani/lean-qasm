import { serializeParameterExpression } from "./expression";
import { type CircuitDocument, type CircuitOperation, type CircuitRegister, refKey } from "./model";

function registerSignature(register: CircuitRegister): string {
  return JSON.stringify([register.kind, register.name, register.size]);
}

function operationSignature(operation: CircuitOperation): string {
  if (operation.kind === "gate") {
    return JSON.stringify([
      operation.kind,
      operation.gate,
      operation.parameters.map(serializeParameterExpression),
      operation.operands.map(refKey),
    ]);
  }
  if (operation.kind === "measurement") {
    return JSON.stringify([
      operation.kind,
      refKey(operation.source),
      operation.target ? refKey(operation.target) : null,
    ]);
  }
  if (operation.kind === "reset") {
    return JSON.stringify([operation.kind, refKey(operation.target)]);
  }
  return JSON.stringify([operation.kind, operation.targets.map(refKey)]);
}

function reconcileIds<Item extends { id: string }>(
  previous: Item[],
  incoming: Item[],
  signature: (item: Item) => string,
  prefix: string,
): Item[] {
  const available = new Map<string, Item[]>();
  for (const item of previous) {
    const key = signature(item);
    available.set(key, [...(available.get(key) ?? []), item]);
  }
  const matches = incoming.map((item) => available.get(signature(item))?.shift()?.id);
  const reserved = new Set(matches.filter((id): id is string => id !== undefined));
  const used = new Set<string>();
  let nextIndex = 0;
  const freshId = () => {
    while (reserved.has(`${prefix}-${nextIndex}`) || used.has(`${prefix}-${nextIndex}`)) {
      nextIndex += 1;
    }
    const id = `${prefix}-${nextIndex}`;
    nextIndex += 1;
    return id;
  };
  return incoming.map((item, index) => {
    const matched = matches[index];
    const id = matched ?? (!reserved.has(item.id) && !used.has(item.id) ? item.id : freshId());
    used.add(id);
    return item.id === id ? item : { ...item, id };
  });
}

function documentsEqual(left: CircuitDocument, right: CircuitDocument): boolean {
  return (
    left.version === right.version &&
    left.includesStdGates === right.includesStdGates &&
    left.registers.length === right.registers.length &&
    left.operations.length === right.operations.length &&
    left.registers.every(
      (register, index) =>
        register.id === right.registers[index]?.id &&
        registerSignature(register) ===
          registerSignature(right.registers[index] as CircuitRegister),
    ) &&
    left.operations.every(
      (operation, index) =>
        operation.id === right.operations[index]?.id &&
        operationSignature(operation) ===
          operationSignature(right.operations[index] as CircuitOperation),
    )
  );
}

export function reconcileCircuitIdentity(
  previous: CircuitDocument,
  incoming: CircuitDocument,
): CircuitDocument {
  const reconciled: CircuitDocument = {
    ...incoming,
    registers: reconcileIds(previous.registers, incoming.registers, registerSignature, "register"),
    operations: reconcileIds(
      previous.operations,
      incoming.operations,
      operationSignature,
      "operation",
    ),
  };
  return documentsEqual(previous, reconciled) ? previous : reconciled;
}
