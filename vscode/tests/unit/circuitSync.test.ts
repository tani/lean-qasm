import { describe, expect, test } from "vitest";
import { addGate } from "../../src/circuit/edit";
import type { CircuitDocument, GateName } from "../../src/circuit/model";
import { parseCircuit } from "../../src/circuit/parser";
import { serializeCircuit } from "../../src/circuit/serializer";
import type { HostToWebviewMessage } from "../../src/protocol";
import {
  type CircuitSyncState,
  circuitSyncReducer,
  INITIAL_CIRCUIT_SYNC_STATE,
} from "../../src/webview/useCircuitSync";

const source = `OPENQASM 3.0;
include "stdgates.inc";
qubit[2] q;
bit[2] c;
h q[0];
cx q[0], q[1];
`;

const parsed = parseCircuit(source);
if (!parsed.ok) throw new Error(parsed.message);
const initialDocument = parsed.document;

type DocumentChangedMessage = Extract<HostToWebviewMessage, { type: "documentChanged" }>;

function appendGate(document: CircuitDocument, gate: GateName): CircuitDocument {
  const result = addGate(document, gate, [{ register: "q", index: 0 }]);
  if (!result.ok) throw new Error(result.message);
  return result.document;
}

function hostMessage(
  document: CircuitDocument,
  version: number,
  requestId?: string,
): DocumentChangedMessage {
  const text = serializeCircuit(document);
  const result = parseCircuit(text);
  return {
    type: "documentChanged",
    version,
    text,
    parsed: result,
    ...(requestId ? { requestId } : {}),
  };
}

function receiveHost(
  state: CircuitSyncState,
  document: CircuitDocument,
  version: number,
  requestId?: string,
  nextRequestId = "next-request",
): CircuitSyncState {
  return circuitSyncReducer(state, {
    type: "hostDocument",
    message: hostMessage(document, version, requestId),
    nextRequestId,
  });
}

function initialState(): CircuitSyncState {
  return receiveHost(INITIAL_CIRCUIT_SYNC_STATE, initialDocument, 12);
}

describe("circuit synchronization reducer", () => {
  test("accepts the initial host document and ignores semantic no-op edits", () => {
    const state = initialState();
    expect(state.visible).toMatchObject({ version: 12, parsed: { ok: true } });
    expect(state.confirmed).toBe(state.visible);

    const unchanged = circuitSyncReducer(state, {
      type: "localEdit",
      document: initialDocument,
      requestId: "request-1",
    });
    expect(unchanged).toBe(state);

    const staleRejection = circuitSyncReducer(state, {
      type: "editRejected",
      requestId: "stale-request",
      message: "stale",
    });
    expect(staleRejection).toBe(state);
  });

  test("coalesces rapid edits and rebases the latest document after acknowledgement", () => {
    const firstDocument = appendGate(initialDocument, "y");
    const secondDocument = appendGate(firstDocument, "z");
    const firstEdit = circuitSyncReducer(initialState(), {
      type: "localEdit",
      document: firstDocument,
      requestId: "request-1",
    });
    expect(firstEdit.inFlight).toMatchObject({ requestId: "request-1", baseVersion: 12 });

    const queued = circuitSyncReducer(firstEdit, {
      type: "localEdit",
      document: secondDocument,
      requestId: "unused-request",
    });
    expect(queued.inFlight).toBe(firstEdit.inFlight);
    expect(queued.queued).toBe(secondDocument);
    expect(queued.visible?.parsed).toMatchObject({ ok: true, document: secondDocument });

    const rebased = receiveHost(queued, firstDocument, 13, "request-1", "request-2");
    expect(rebased.queued).toBeUndefined();
    expect(rebased.inFlight).toMatchObject({
      requestId: "request-2",
      baseVersion: 13,
      document: secondDocument,
    });
    expect(rebased.visible?.parsed).toMatchObject({ ok: true, document: secondDocument });

    const settled = receiveHost(rebased, secondDocument, 14, "request-2");
    expect(settled.inFlight).toBeUndefined();
    expect(settled.queued).toBeUndefined();
    expect(settled.visible).toMatchObject({
      version: 14,
      parsed: { ok: true, document: secondDocument },
    });
  });

  test("keeps external source as the rollback point while an optimistic edit is pending", () => {
    const optimistic = appendGate(initialDocument, "y");
    const queuedDocument = appendGate(optimistic, "z");
    const externalDocument = appendGate(initialDocument, "x");
    const firstEdit = circuitSyncReducer(initialState(), {
      type: "localEdit",
      document: optimistic,
      requestId: "request-1",
    });
    const queued = circuitSyncReducer(firstEdit, {
      type: "localEdit",
      document: queuedDocument,
      requestId: "unused-request",
    });
    const externallyChanged = receiveHost(queued, externalDocument, 13);
    expect(externallyChanged.visible?.parsed).toMatchObject({
      ok: true,
      document: queuedDocument,
    });
    expect(externallyChanged.confirmed).toMatchObject({ version: 13 });

    const rejected = circuitSyncReducer(externallyChanged, {
      type: "editRejected",
      requestId: "request-1",
      message: "The edit was rejected.",
    });
    expect(rejected.inFlight).toBeUndefined();
    expect(rejected.queued).toBeUndefined();
    expect(rejected.visible).toBe(rejected.confirmed);
    expect(rejected.notice).toBe("The edit was rejected.");
    if (!rejected.visible?.parsed.ok) throw new Error("expected a valid rollback document");
    expect(serializeCircuit(rejected.visible.parsed.document)).toContain("x q[0];");
    expect(serializeCircuit(rejected.visible.parsed.document)).not.toContain("y q[0];");
  });
});
