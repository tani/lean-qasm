export type RegisterKind = "qubit" | "bit";

export interface CircuitRegister {
  id: string;
  name: string;
  kind: RegisterKind;
  size: number;
}

export interface RegisterRef {
  register: string;
  index: number;
}

export type ParameterExpression =
  | { kind: "number"; value: string }
  | { kind: "pi" }
  | { kind: "unary"; operator: "+" | "-"; operand: ParameterExpression }
  | {
      kind: "binary";
      operator: "+" | "-" | "*" | "/";
      left: ParameterExpression;
      right: ParameterExpression;
    };

export interface GateOperation {
  id: string;
  kind: "gate";
  gate: GateName;
  parameters: ParameterExpression[];
  operands: RegisterRef[];
}

export interface MeasurementOperation {
  id: string;
  kind: "measurement";
  source: RegisterRef;
  target?: RegisterRef;
}

export interface ResetOperation {
  id: string;
  kind: "reset";
  target: RegisterRef;
}

export interface BarrierOperation {
  id: string;
  kind: "barrier";
  targets: RegisterRef[];
}

export type CircuitOperation =
  | GateOperation
  | MeasurementOperation
  | ResetOperation
  | BarrierOperation;

export interface CircuitDocument {
  version: "3.0";
  includesStdGates: boolean;
  registers: CircuitRegister[];
  operations: CircuitOperation[];
}

export interface GateDefinition {
  name: GateName;
  label: string;
  category: "single" | "rotation" | "controlled" | "swap" | "universal" | "legacy";
  parameterCount: number;
  operandCount: number;
  defaultParameters: string[];
  description: string;
}

export const GATE_DEFINITIONS = [
  {
    name: "x",
    label: "X",
    category: "single",
    parameterCount: 0,
    operandCount: 1,
    defaultParameters: [],
    description: "Pauli X",
  },
  {
    name: "y",
    label: "Y",
    category: "single",
    parameterCount: 0,
    operandCount: 1,
    defaultParameters: [],
    description: "Pauli Y",
  },
  {
    name: "z",
    label: "Z",
    category: "single",
    parameterCount: 0,
    operandCount: 1,
    defaultParameters: [],
    description: "Pauli Z",
  },
  {
    name: "h",
    label: "H",
    category: "single",
    parameterCount: 0,
    operandCount: 1,
    defaultParameters: [],
    description: "Hadamard",
  },
  {
    name: "s",
    label: "S",
    category: "single",
    parameterCount: 0,
    operandCount: 1,
    defaultParameters: [],
    description: "S phase",
  },
  {
    name: "sdg",
    label: "S†",
    category: "single",
    parameterCount: 0,
    operandCount: 1,
    defaultParameters: [],
    description: "Inverse S",
  },
  {
    name: "t",
    label: "T",
    category: "single",
    parameterCount: 0,
    operandCount: 1,
    defaultParameters: [],
    description: "T phase",
  },
  {
    name: "tdg",
    label: "T†",
    category: "single",
    parameterCount: 0,
    operandCount: 1,
    defaultParameters: [],
    description: "Inverse T",
  },
  {
    name: "sx",
    label: "√X",
    category: "single",
    parameterCount: 0,
    operandCount: 1,
    defaultParameters: [],
    description: "Square-root X",
  },
  {
    name: "id",
    label: "I",
    category: "legacy",
    parameterCount: 0,
    operandCount: 1,
    defaultParameters: [],
    description: "Identity",
  },
  {
    name: "p",
    label: "P",
    category: "rotation",
    parameterCount: 1,
    operandCount: 1,
    defaultParameters: ["pi / 2"],
    description: "Phase rotation",
  },
  {
    name: "rx",
    label: "RX",
    category: "rotation",
    parameterCount: 1,
    operandCount: 1,
    defaultParameters: ["pi / 2"],
    description: "X-axis rotation",
  },
  {
    name: "ry",
    label: "RY",
    category: "rotation",
    parameterCount: 1,
    operandCount: 1,
    defaultParameters: ["pi / 2"],
    description: "Y-axis rotation",
  },
  {
    name: "rz",
    label: "RZ",
    category: "rotation",
    parameterCount: 1,
    operandCount: 1,
    defaultParameters: ["pi / 2"],
    description: "Z-axis rotation",
  },
  {
    name: "cx",
    label: "CX",
    category: "controlled",
    parameterCount: 0,
    operandCount: 2,
    defaultParameters: [],
    description: "Controlled X",
  },
  {
    name: "cy",
    label: "CY",
    category: "controlled",
    parameterCount: 0,
    operandCount: 2,
    defaultParameters: [],
    description: "Controlled Y",
  },
  {
    name: "cz",
    label: "CZ",
    category: "controlled",
    parameterCount: 0,
    operandCount: 2,
    defaultParameters: [],
    description: "Controlled Z",
  },
  {
    name: "ch",
    label: "CH",
    category: "controlled",
    parameterCount: 0,
    operandCount: 2,
    defaultParameters: [],
    description: "Controlled H",
  },
  {
    name: "cp",
    label: "CP",
    category: "controlled",
    parameterCount: 1,
    operandCount: 2,
    defaultParameters: ["pi / 2"],
    description: "Controlled phase",
  },
  {
    name: "crx",
    label: "CRX",
    category: "controlled",
    parameterCount: 1,
    operandCount: 2,
    defaultParameters: ["pi / 2"],
    description: "Controlled RX",
  },
  {
    name: "cry",
    label: "CRY",
    category: "controlled",
    parameterCount: 1,
    operandCount: 2,
    defaultParameters: ["pi / 2"],
    description: "Controlled RY",
  },
  {
    name: "crz",
    label: "CRZ",
    category: "controlled",
    parameterCount: 1,
    operandCount: 2,
    defaultParameters: ["pi / 2"],
    description: "Controlled RZ",
  },
  {
    name: "swap",
    label: "SWAP",
    category: "swap",
    parameterCount: 0,
    operandCount: 2,
    defaultParameters: [],
    description: "Swap two qubits",
  },
  {
    name: "ccx",
    label: "CCX",
    category: "controlled",
    parameterCount: 0,
    operandCount: 3,
    defaultParameters: [],
    description: "Toffoli",
  },
  {
    name: "cswap",
    label: "CSWAP",
    category: "swap",
    parameterCount: 0,
    operandCount: 3,
    defaultParameters: [],
    description: "Controlled swap",
  },
  {
    name: "U",
    label: "U",
    category: "universal",
    parameterCount: 3,
    operandCount: 1,
    defaultParameters: ["pi / 2", "0", "pi"],
    description: "Universal single-qubit gate",
  },
  {
    name: "cu",
    label: "CU",
    category: "universal",
    parameterCount: 4,
    operandCount: 2,
    defaultParameters: ["pi / 2", "0", "pi", "0"],
    description: "Controlled universal gate",
  },
  {
    name: "gphase",
    label: "GΦ",
    category: "universal",
    parameterCount: 1,
    operandCount: 0,
    defaultParameters: ["pi / 2"],
    description: "Global phase",
  },
  {
    name: "CX",
    label: "CX",
    category: "legacy",
    parameterCount: 0,
    operandCount: 2,
    defaultParameters: [],
    description: "OpenQASM 2 CNOT alias",
  },
  {
    name: "phase",
    label: "PHASE",
    category: "legacy",
    parameterCount: 1,
    operandCount: 1,
    defaultParameters: ["pi / 2"],
    description: "Legacy phase",
  },
  {
    name: "cphase",
    label: "CPHASE",
    category: "legacy",
    parameterCount: 1,
    operandCount: 2,
    defaultParameters: ["pi / 2"],
    description: "Legacy controlled phase",
  },
  {
    name: "u1",
    label: "U1",
    category: "legacy",
    parameterCount: 1,
    operandCount: 1,
    defaultParameters: ["pi / 2"],
    description: "Legacy U1",
  },
  {
    name: "u2",
    label: "U2",
    category: "legacy",
    parameterCount: 2,
    operandCount: 1,
    defaultParameters: ["0", "pi"],
    description: "Legacy U2",
  },
  {
    name: "u3",
    label: "U3",
    category: "legacy",
    parameterCount: 3,
    operandCount: 1,
    defaultParameters: ["pi / 2", "0", "pi"],
    description: "Legacy U3",
  },
] as const satisfies readonly GateDefinition[];

export type GateName =
  | "x"
  | "y"
  | "z"
  | "h"
  | "s"
  | "sdg"
  | "t"
  | "tdg"
  | "sx"
  | "id"
  | "p"
  | "rx"
  | "ry"
  | "rz"
  | "cx"
  | "cy"
  | "cz"
  | "ch"
  | "cp"
  | "crx"
  | "cry"
  | "crz"
  | "swap"
  | "ccx"
  | "cswap"
  | "U"
  | "cu"
  | "gphase"
  | "CX"
  | "phase"
  | "cphase"
  | "u1"
  | "u2"
  | "u3";

export const GATE_BY_NAME = new Map<GateName, GateDefinition>(
  GATE_DEFINITIONS.map((gate) => [gate.name, gate]),
);

export const EMPTY_CIRCUIT: CircuitDocument = {
  version: "3.0",
  includesStdGates: true,
  registers: [
    { id: "register-0", name: "q", kind: "qubit", size: 2 },
    { id: "register-1", name: "c", kind: "bit", size: 2 },
  ],
  operations: [],
};

export function getRegister(document: CircuitDocument, reference: RegisterRef) {
  return document.registers.find((register) => register.name === reference.register);
}

export function refKey(reference: RegisterRef): string {
  return `${reference.register}[${reference.index}]`;
}
