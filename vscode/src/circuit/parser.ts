import { lex } from "qasm-ts/dist/lexer.js";
import { parse } from "qasm-ts/dist/parser.js";
import { parseParameterExpression } from "./expression";
import {
  type CircuitDocument,
  type CircuitOperation,
  type CircuitRegister,
  GATE_BY_NAME,
  type GateName,
  type RegisterRef,
} from "./model";
import { validateCircuit } from "./validation";

export type CircuitParseResult =
  | { ok: true; document: CircuitDocument }
  | { ok: false; message: string; category: "syntax" | "unsupported" | "invalid" };

function messageOf(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}

function stripComments(source: string): string {
  let result = "";
  let index = 0;
  let quote = false;
  while (index < source.length) {
    const char = source[index];
    const next = source[index + 1];
    if (quote) {
      result += char;
      if (char === "\\" && next) {
        result += next;
        index += 2;
        continue;
      }
      if (char === '"') quote = false;
      index += 1;
      continue;
    }
    if (char === '"') {
      quote = true;
      result += char;
      index += 1;
      continue;
    }
    if (char === "/" && next === "/") {
      index += 2;
      while (index < source.length && source[index] !== "\n") index += 1;
      result += "\n";
      continue;
    }
    if (char === "/" && next === "*") {
      index += 2;
      while (index < source.length && !(source[index] === "*" && source[index + 1] === "/")) {
        result += source[index] === "\n" ? "\n" : " ";
        index += 1;
      }
      index += 2;
      continue;
    }
    result += char;
    index += 1;
  }
  return result;
}

function splitTopLevel(source: string): string[] {
  const values: string[] = [];
  let depth = 0;
  let start = 0;
  for (let index = 0; index < source.length; index += 1) {
    const char = source[index];
    if (char === "(") depth += 1;
    else if (char === ")") depth -= 1;
    else if (char === "," && depth === 0) {
      values.push(source.slice(start, index).trim());
      start = index + 1;
    }
  }
  values.push(source.slice(start).trim());
  return values.filter(Boolean);
}

function parseReference(source: string): RegisterRef {
  const match = /^([A-Za-z_][A-Za-z0-9_]*)\s*\[\s*(\d+)\s*\]$/.exec(source.trim());
  if (!match?.[1] || match[2] === undefined) {
    throw new Error(`'${source.trim()}' is not an explicit indexed register reference.`);
  }
  return { register: match[1], index: Number(match[2]) };
}

function parseGate(statement: string, id: string): CircuitOperation | undefined {
  const match = /^([A-Za-z_][A-Za-z0-9_]*)(?:\s*\((.*)\))?(?:\s+(.+))?$/.exec(statement);
  if (!match?.[1] || !GATE_BY_NAME.has(match[1] as GateName)) return undefined;
  const gate = match[1] as GateName;
  const definition = GATE_BY_NAME.get(gate);
  if (!definition) return undefined;
  const parameters =
    match[2] === undefined ? [] : splitTopLevel(match[2]).map(parseParameterExpression);
  const operands = match[3] === undefined ? [] : splitTopLevel(match[3]).map(parseReference);
  return { id, kind: "gate", gate, parameters, operands };
}

export function parseCircuit(source: string): CircuitParseResult {
  try {
    parse(lex(source, undefined, 3), 3);
  } catch (error) {
    return { ok: false, category: "syntax", message: messageOf(error) };
  }

  try {
    const normalized = stripComments(source).trim();
    if (/[{}]/.test(normalized)) {
      return {
        ok: false,
        category: "unsupported",
        message:
          "Control flow, scopes, and gate definitions are not editable in the circuit subset.",
      };
    }
    const statements = normalized
      .split(";")
      .map((statement) => statement.trim())
      .filter(Boolean);
    if (statements.shift() !== "OPENQASM 3.0") {
      return {
        ok: false,
        category: "unsupported",
        message: "The circuit editor requires an exact OPENQASM 3.0 header.",
      };
    }

    let includesStdGates = false;
    const registers: CircuitRegister[] = [];
    const operations: CircuitOperation[] = [];
    let declarationsClosed = false;

    for (const statement of statements) {
      if (/^include\b/.test(statement)) {
        if (
          statement !== 'include "stdgates.inc"' ||
          registers.length > 0 ||
          operations.length > 0 ||
          includesStdGates
        ) {
          throw new Error('Only one include "stdgates.inc" before declarations is supported.');
        }
        includesStdGates = true;
        continue;
      }
      const declaration = /^(qubit|bit)\s*\[\s*(\d+)\s*\]\s+([A-Za-z_][A-Za-z0-9_]*)$/.exec(
        statement,
      );
      if (declaration?.[1] && declaration[2] && declaration[3]) {
        if (declarationsClosed)
          throw new Error("All register declarations must precede circuit operations.");
        registers.push({
          id: `register-${registers.length}`,
          kind: declaration[1] as "qubit" | "bit",
          size: Number(declaration[2]),
          name: declaration[3],
        });
        continue;
      }
      declarationsClosed = true;
      const id = `operation-${operations.length}`;
      const assignmentMeasurement = /^(.+?)\s*=\s*measure\s+(.+)$/.exec(statement);
      if (assignmentMeasurement?.[1] && assignmentMeasurement[2]) {
        operations.push({
          id,
          kind: "measurement",
          target: parseReference(assignmentMeasurement[1]),
          source: parseReference(assignmentMeasurement[2]),
        });
        continue;
      }
      const arrowMeasurement = /^measure\s+(.+?)(?:\s*->\s*(.+))?$/.exec(statement);
      if (arrowMeasurement?.[1]) {
        const target = arrowMeasurement[2] ? parseReference(arrowMeasurement[2]) : undefined;
        operations.push({
          id,
          kind: "measurement",
          source: parseReference(arrowMeasurement[1]),
          ...(target ? { target } : {}),
        });
        continue;
      }
      const reset = /^reset\s+(.+)$/.exec(statement);
      if (reset?.[1]) {
        operations.push({ id, kind: "reset", target: parseReference(reset[1]) });
        continue;
      }
      const barrier = /^barrier\s+(.+)$/.exec(statement);
      if (barrier?.[1]) {
        operations.push({
          id,
          kind: "barrier",
          targets: splitTopLevel(barrier[1]).map(parseReference),
        });
        continue;
      }
      const gate = parseGate(statement, id);
      if (gate) {
        operations.push(gate);
        continue;
      }
      throw new Error(`'${statement.slice(0, 64)}' is outside the editable circuit subset.`);
    }

    const document: CircuitDocument = { version: "3.0", includesStdGates, registers, operations };
    const errors = validateCircuit(document);
    if (errors.length > 0) return { ok: false, category: "invalid", message: errors.join("\n") };
    return { ok: true, document };
  } catch (error) {
    return { ok: false, category: "unsupported", message: messageOf(error) };
  }
}
