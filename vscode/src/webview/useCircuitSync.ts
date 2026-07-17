import { useCallback, useEffect, useReducer, useRef } from "react";
import { reconcileCircuitIdentity } from "../circuit/identity";
import type { CircuitDocument } from "../circuit/model";
import type { CircuitParseResult } from "../circuit/parser";
import { serializeCircuit } from "../circuit/serializer";
import type { HostToWebviewMessage, WebviewToHostMessage } from "../protocol";

export interface EditorBridge {
  postMessage(message: WebviewToHostMessage): void;
  subscribe(listener: (message: HostToWebviewMessage) => void): () => void;
}

export interface EditorState {
  version: number;
  parsed: CircuitParseResult;
}

export interface PendingEdit {
  requestId: string;
  baseVersion: number;
  document: CircuitDocument;
  text: string;
}

export interface CircuitSyncState {
  visible?: EditorState;
  confirmed?: EditorState;
  inFlight?: PendingEdit;
  queued?: CircuitDocument;
  notice?: string;
}

type DocumentChangedMessage = Extract<HostToWebviewMessage, { type: "documentChanged" }>;

export type CircuitSyncAction =
  | { type: "localEdit"; document: CircuitDocument; requestId: string }
  | { type: "hostDocument"; message: DocumentChangedMessage; nextRequestId: string }
  | { type: "editRejected"; requestId: string; message: string };

export const INITIAL_CIRCUIT_SYNC_STATE: CircuitSyncState = {};

function pendingEdit(
  document: CircuitDocument,
  baseVersion: number,
  requestId: string,
): PendingEdit {
  return { requestId, baseVersion, document, text: serializeCircuit(document) };
}

function reconcileHostDocument(
  state: CircuitSyncState,
  message: DocumentChangedMessage,
): EditorState {
  const currentParsed = state.visible?.parsed;
  const identitySource =
    state.inFlight?.document ?? (currentParsed?.ok ? currentParsed.document : undefined);
  const parsed =
    identitySource && message.parsed.ok
      ? {
          ok: true as const,
          document: reconcileCircuitIdentity(identitySource, message.parsed.document),
        }
      : message.parsed;
  return { version: message.version, parsed };
}

export function circuitSyncReducer(
  state: CircuitSyncState,
  action: CircuitSyncAction,
): CircuitSyncState {
  if (action.type === "localEdit") {
    if (!state.visible?.parsed.ok) return state;
    if (serializeCircuit(state.visible.parsed.document) === serializeCircuit(action.document)) {
      return state;
    }

    const visible: EditorState = {
      ...state.visible,
      parsed: { ok: true, document: action.document },
    };
    return state.inFlight
      ? { ...state, visible, queued: action.document }
      : {
          ...state,
          visible,
          inFlight: pendingEdit(action.document, state.visible.version, action.requestId),
        };
  }

  if (action.type === "editRejected") {
    if (action.requestId !== state.inFlight?.requestId) return state;
    const visible = state.confirmed ?? state.visible;
    return {
      ...(visible ? { visible } : {}),
      ...(state.confirmed ? { confirmed: state.confirmed } : {}),
      notice: action.message,
    };
  }

  const confirmed = reconcileHostDocument(state, action.message);
  const acknowledgesPending =
    Boolean(action.message.requestId) && action.message.requestId === state.inFlight?.requestId;

  if (acknowledgesPending) {
    if (state.queued && confirmed.parsed.ok) {
      return {
        visible: {
          version: action.message.version,
          parsed: { ok: true, document: state.queued },
        },
        confirmed,
        inFlight: pendingEdit(state.queued, action.message.version, action.nextRequestId),
      };
    }
    return { visible: confirmed, confirmed };
  }

  return state.inFlight ? { ...state, confirmed } : { visible: confirmed, confirmed };
}

function createRequestId(): string {
  return globalThis.crypto?.randomUUID?.() ?? `${Date.now()}-${Math.random()}`;
}

export function useCircuitSync(bridge: EditorBridge) {
  const [sync, dispatch] = useReducer(circuitSyncReducer, INITIAL_CIRCUIT_SYNC_STATE);
  const sentEditRef = useRef<{ bridge: EditorBridge; requestId: string } | undefined>(undefined);

  useEffect(() => {
    const edit = sync.inFlight;
    if (
      !edit ||
      (sentEditRef.current?.bridge === bridge && sentEditRef.current.requestId === edit.requestId)
    ) {
      return;
    }
    sentEditRef.current = { bridge, requestId: edit.requestId };
    bridge.postMessage({
      type: "replaceDocument",
      requestId: edit.requestId,
      baseVersion: edit.baseVersion,
      text: edit.text,
    });
  }, [bridge, sync.inFlight]);

  useEffect(() => {
    const unsubscribe = bridge.subscribe((message) => {
      if (message.type === "documentChanged") {
        dispatch({ type: "hostDocument", message, nextRequestId: createRequestId() });
      } else if (message.type === "editRejected") {
        dispatch({
          type: "editRejected",
          requestId: message.requestId,
          message: message.message,
        });
      }
    });
    bridge.postMessage({ type: "ready" });
    return unsubscribe;
  }, [bridge]);

  const commit = useCallback((document: CircuitDocument) => {
    dispatch({ type: "localEdit", document, requestId: createRequestId() });
  }, []);

  return {
    state: sync.visible,
    pending: Boolean(sync.inFlight),
    notice: sync.notice,
    commit,
  };
}
