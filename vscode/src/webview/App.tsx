import { CircuitWorkbench } from "./CircuitWorkbench";
import { type EditorBridge, useCircuitSync } from "./useCircuitSync";

export type { EditorBridge } from "./useCircuitSync";

export function CircuitEditorApp({ bridge }: { bridge: EditorBridge }) {
  const { state, pending, notice, commit } = useCircuitSync(bridge);

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
