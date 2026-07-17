import { serializeParameterExpression } from "./expression";
import { type CircuitDocument, GATE_BY_NAME, type RegisterRef } from "./model";
import { validateCircuit } from "./validation";

function serializeReference(reference: RegisterRef): string {
  return `${reference.register}[${reference.index}]`;
}

export function serializeCircuit(document: CircuitDocument): string {
  const errors = validateCircuit(document);
  if (errors.length > 0) throw new Error(errors.join("\n"));

  const lines = ["OPENQASM 3.0;"];
  const needsStdGates = document.operations.some(
    (operation) => operation.kind === "gate" && !["U", "gphase"].includes(operation.gate),
  );
  if (document.includesStdGates || needsStdGates) lines.push('include "stdgates.inc";');
  if (document.registers.length > 0) lines.push("");
  for (const register of document.registers) {
    lines.push(`${register.kind}[${register.size}] ${register.name};`);
  }
  if (document.operations.length > 0) lines.push("");
  for (const operation of document.operations) {
    if (operation.kind === "gate") {
      const definition = GATE_BY_NAME.get(operation.gate);
      if (!definition) throw new Error(`Unsupported gate '${operation.gate}'.`);
      const parameters =
        operation.parameters.length > 0
          ? `(${operation.parameters.map((value) => serializeParameterExpression(value)).join(", ")})`
          : "";
      const operands = operation.operands.map(serializeReference).join(", ");
      lines.push(`${operation.gate}${parameters}${operands ? ` ${operands}` : ""};`);
    } else if (operation.kind === "measurement") {
      const source = serializeReference(operation.source);
      lines.push(
        operation.target
          ? `${serializeReference(operation.target)} = measure ${source};`
          : `measure ${source};`,
      );
    } else if (operation.kind === "reset") {
      lines.push(`reset ${serializeReference(operation.target)};`);
    } else {
      lines.push(`barrier ${operation.targets.map(serializeReference).join(", ")};`);
    }
  }
  return `${lines.join("\n")}\n`;
}
