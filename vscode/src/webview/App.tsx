import { useCallback, useEffect, useRef, useState } from "react";
import { reconcileCircuitIdentity } from "../circuit/identity";
import type { CircuitDocument } from "../circuit/model";
import type { CircuitParseResult } from "../circuit/parser";
import { serializeCircuit } from "../circuit/serializer";
import type { HostToWebviewMessage, WebviewToHostMessage } from "../protocol";
import { CircuitWorkbench } from "./CircuitWorkbench";

export interface EditorBridge {
  postMessage(message: WebviewToHostMessage): void;
  subscribe(listener: (message: HostToWebviewMessage) => void): () => void;
}

interface EditorState {
  version: number;
  parsed: CircuitParseResult;
}

interface PendingEdit {
  requestId: string;
  document: CircuitDocument;
}

export function CircuitEditorApp({ bridge }: { bridge: EditorBridge }) {
  const [state, setState] = useState<EditorState>();
  const [pending, setPending] = useState(false);
  const [notice, setNotice] = useState<string>();
  const stateRef = useRef<EditorState | undefined>(undefined);
  const confirmedStateRef = useRef<EditorState | undefined>(undefined);
  const pendingEditRef = useRef<PendingEdit | undefined>(undefined);
  const queuedDocumentRef = useRef<CircuitDocument | undefined>(undefined);

  const updateState = useCallback((next: EditorState) => {
    stateRef.current = next;
    setState(next);
  }, []);

  const submit = useCallback(
    (document: CircuitDocument, baseVersion: number) => {
      const text = serializeCircuit(document);
      const requestId = globalThis.crypto?.randomUUID?.() ?? `${Date.now()}-${Math.random()}`;
      pendingEditRef.current = { requestId, document };
      setPending(true);
      bridge.postMessage({ type: "replaceDocument", requestId, baseVersion, text });
    },
    [bridge],
  );

  useEffect(() => {
    const unsubscribe = bridge.subscribe((message) => {
      if (message.type === "documentChanged") {
        const pendingEdit = pendingEditRef.current;
        const currentParsed = stateRef.current?.parsed;
        const identitySource =
          pendingEdit?.document ?? (currentParsed?.ok ? currentParsed.document : undefined);
        const parsed =
          identitySource && message.parsed.ok
            ? {
                ok: true as const,
                document: reconcileCircuitIdentity(identitySource, message.parsed.document),
              }
            : message.parsed;
        const confirmed = { version: message.version, parsed };
        confirmedStateRef.current = confirmed;

        if (message.requestId && message.requestId === pendingEdit?.requestId) {
          pendingEditRef.current = undefined;
          const queued = queuedDocumentRef.current;
          queuedDocumentRef.current = undefined;
          if (queued && parsed.ok) {
            updateState({ version: message.version, parsed: { ok: true, document: queued } });
            submit(queued, message.version);
          } else {
            updateState(confirmed);
            setPending(false);
          }
          setNotice(undefined);
        } else if (!pendingEdit) {
          updateState(confirmed);
          setPending(false);
          setNotice(undefined);
        }
      } else if (message.type === "editRejected") {
        if (message.requestId !== pendingEditRef.current?.requestId) return;
        pendingEditRef.current = undefined;
        queuedDocumentRef.current = undefined;
        if (confirmedStateRef.current) updateState(confirmedStateRef.current);
        setPending(false);
        setNotice(message.message);
      }
    });
    bridge.postMessage({ type: "ready" });
    return unsubscribe;
  }, [bridge, submit, updateState]);

  const commit = useCallback(
    (document: CircuitDocument) => {
      const current = stateRef.current;
      if (!current?.parsed.ok) return;
      if (serializeCircuit(current.parsed.document) === serializeCircuit(document)) return;

      updateState({ ...current, parsed: { ok: true, document } });
      if (pendingEditRef.current) {
        queuedDocumentRef.current = document;
        return;
      }
      submit(document, current.version);
    },
    [submit, updateState],
  );

  if (!state) {
    return (
      <main className="loading-state" aria-live="polite">
        <span className="loading-orbit" aria-hidden="true" />
        <p>Resolving circuit topology…</p>
      </main>
    );
  }

  if (!state.parsed.ok) {
    return (
      <main className="unsupported-state">
        <div className="unsupported-mark" aria-hidden="true">
          Q!
        </div>
        <p className="eyebrow">Circuit boundary</p>
        <h1>This source is safer in text mode.</h1>
        <p>{state.parsed.message}</p>
        <p className="muted">
          The graphical editor accepts linear OpenQASM 3.0 circuits with fixed registers and
          explicit indexed operands.
        </p>
        <button
          className="primary-button"
          type="button"
          onClick={() => bridge.postMessage({ type: "openSource" })}
        >
          Open source editor
        </button>
      </main>
    );
  }

  return (
    <CircuitWorkbench
      document={state.parsed.document}
      onChange={commit}
      onUndo={() => bridge.postMessage({ type: "undo" })}
      onRedo={() => bridge.postMessage({ type: "redo" })}
      onOpenSource={() => bridge.postMessage({ type: "openSource" })}
      pending={pending}
      externalNotice={notice}
    />
  );
}
