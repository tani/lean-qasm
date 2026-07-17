import type { CSSProperties, DragEvent, KeyboardEvent } from "react";
import { useEffect, useMemo, useRef, useState } from "react";
import {
  addGate,
  addOperation,
  addRegister,
  addWire,
  duplicateOperation,
  type EditResult,
  moveOperation,
  operationReferences,
  placeMeasurementTarget,
  placeOperation,
  placeOperationOperand,
  removeOperation,
  removeRegister,
  removeWire,
  updateOperation,
  updateRegister,
} from "../circuit/edit";
import { parseParameterExpression, serializeParameterExpression } from "../circuit/expression";
import {
  type CircuitDocument,
  type CircuitOperation,
  type CircuitRegister,
  GATE_BY_NAME,
  GATE_DEFINITIONS,
  type GateName,
  type RegisterRef,
  refKey,
} from "../circuit/model";

const ROW_HEIGHT = 52;
const TOP = 46;
const LABEL_WIDTH = 132;
const COLUMN_WIDTH = 88;
const DRAG_MIME = "application/x-leanqasm";

type EffectKind = "measurement" | "reset" | "barrier";

interface ReorderSession {
  operationId: string;
  status: "dragging" | "committed";
  visualOrder: string[];
}

function isEndpointPayload(payload: string | undefined): boolean {
  return Boolean(payload?.startsWith("operand:") || payload?.startsWith("measurement-target:"));
}

function isMovePayload(payload: string | undefined): boolean {
  return Boolean(payload?.startsWith("operation:") || isEndpointPayload(payload));
}

interface Lane {
  key: string;
  label: string;
  kind: "qubit" | "bit";
  reference: RegisterRef;
}

interface WorkbenchProps {
  document: CircuitDocument;
  onChange(document: CircuitDocument): void;
  onUndo(): void;
  onRedo(): void;
  onOpenSource(): void;
  pending?: boolean;
  externalNotice?: string | undefined;
}

function lanesOf(document: CircuitDocument): Lane[] {
  return document.registers.flatMap((register) =>
    Array.from({ length: register.size }, (_, index) => ({
      key: `${register.name}-${index}`,
      label: `${register.name}[${index}]`,
      kind: register.kind,
      reference: { register: register.name, index },
    })),
  );
}

function description(operation: CircuitOperation): string {
  if (operation.kind === "gate") {
    return `${operation.gate} gate on ${operation.operands.map(refKey).join(", ") || "global phase"}`;
  }
  if (operation.kind === "measurement") {
    return `Measure ${refKey(operation.source)}${operation.target ? ` into ${refKey(operation.target)}` : ""}`;
  }
  if (operation.kind === "reset") return `Reset ${refKey(operation.target)}`;
  return `Barrier on ${operation.targets.map(refKey).join(", ")}`;
}

function resultDocument(result: EditResult, setNotice: (notice: string | undefined) => void) {
  if (!result.ok) {
    setNotice(result.message);
    return undefined;
  }
  setNotice(undefined);
  return result.document;
}

export function CircuitWorkbench({
  document,
  onChange,
  onUndo,
  onRedo,
  onOpenSource,
  pending = false,
  externalNotice,
}: WorkbenchProps) {
  const [selectedId, setSelectedId] = useState<string>();
  const [search, setSearch] = useState("");
  const [zoom, setZoom] = useState(100);
  const [notice, setNotice] = useState<string>();
  const [dragPayload, setDragPayload] = useState<string>();
  const [activeDropIndex, setActiveDropIndex] = useState<number>();
  const [activeLaneKey, setActiveLaneKey] = useState<string>();
  const [discardActive, setDiscardActive] = useState(false);
  const [reorderSession, setReorderSession] = useState<ReorderSession>();
  const [renderOperationIds, setRenderOperationIds] = useState(() =>
    document.operations.map((operation) => operation.id),
  );
  const canvasRef = useRef<HTMLElement>(null);
  const lanes = useMemo(() => lanesOf(document), [document]);
  const qubits = lanes.filter((lane) => lane.kind === "qubit");
  const bits = lanes.filter((lane) => lane.kind === "bit");
  const selected = document.operations.find((operation) => operation.id === selectedId);
  const visibleGates = GATE_DEFINITIONS.filter((gate) =>
    `${gate.name} ${gate.description} ${gate.category}`
      .toLowerCase()
      .includes(search.toLowerCase()),
  );
  const canvasWidth = LABEL_WIDTH + Math.max(2, document.operations.length + 1) * COLUMN_WIDTH + 36;
  const canvasHeight = TOP + Math.max(1, lanes.length) * ROW_HEIGHT + 30;
  const documentOperationIds = document.operations.map((operation) => operation.id);
  const stableRenderIds = [
    ...renderOperationIds.filter((id) => documentOperationIds.includes(id)),
    ...documentOperationIds.filter((id) => !renderOperationIds.includes(id)),
  ];
  const operationById = new Map(
    document.operations.map((operation) => [operation.id, operation] as const),
  );
  const visualOrder = reorderSession?.visualOrder ?? documentOperationIds;

  useEffect(() => {
    if (selectedId && !document.operations.some((operation) => operation.id === selectedId)) {
      setSelectedId(undefined);
    }
  }, [document.operations, selectedId]);

  useEffect(() => {
    const operationIds = document.operations.map((operation) => operation.id);
    setRenderOperationIds((current) => {
      const next = [
        ...current.filter((id) => operationIds.includes(id)),
        ...operationIds.filter((id) => !current.includes(id)),
      ];
      return current.length === next.length && current.every((id, index) => id === next[index])
        ? current
        : next;
    });
    setReorderSession((current) =>
      current?.status === "committed" &&
      current.visualOrder.length === operationIds.length &&
      current.visualOrder.every((id, index) => id === operationIds[index])
        ? undefined
        : current,
    );
  }, [document.operations]);

  const apply = (result: EditResult) => {
    const next = resultDocument(result, setNotice);
    if (next) onChange(next);
  };

  const beginDrag = (
    event: DragEvent<HTMLButtonElement>,
    payload: string,
    effect: "copy" | "move",
  ) => {
    event.dataTransfer.setData(DRAG_MIME, payload);
    event.dataTransfer.setData("text/plain", payload);
    event.dataTransfer.effectAllowed = effect;
    setDragPayload(payload);
    setReorderSession(
      payload.startsWith("operation:")
        ? {
            operationId: payload.slice("operation:".length),
            status: "dragging",
            visualOrder: document.operations.map((operation) => operation.id),
          }
        : undefined,
    );
    setNotice(
      payload.startsWith("measurement-target:")
        ? "Drop the measurement result on another classical wire."
        : payload.startsWith("operand:")
          ? "Drop this endpoint on another quantum wire. Dropping on the other endpoint swaps them."
          : payload.startsWith("operation:")
            ? "Drop on a wire to change placement, between steps to reorder, or on Discard to delete."
            : "Drop on a wire between steps to place the operation.",
    );
  };

  const clearDragState = () => {
    setDragPayload(undefined);
    setActiveDropIndex(undefined);
    setActiveLaneKey(undefined);
    setDiscardActive(false);
  };

  const endDrag = () => {
    clearDragState();
    setReorderSession((current) => (current?.status === "committed" ? current : undefined));
  };

  const readDragPayload = (event: DragEvent<HTMLElement>) =>
    event.dataTransfer.getData(DRAG_MIME) || event.dataTransfer.getData("text/plain");

  const defaultOperands = (count: number, preferred?: RegisterRef): RegisterRef[] => {
    const ordered = preferred
      ? [
          preferred,
          ...qubits
            .map((lane) => lane.reference)
            .filter((ref) => refKey(ref) !== refKey(preferred)),
        ]
      : qubits.map((lane) => lane.reference);
    return ordered.slice(0, count);
  };

  const insertGate = (
    gate: GateName,
    index = document.operations.length,
    preferred?: RegisterRef,
  ) => {
    const definition = GATE_BY_NAME.get(gate);
    if (!definition) return;
    const operands = defaultOperands(definition.operandCount, preferred);
    if (operands.length !== definition.operandCount) {
      setNotice(`${definition.label} needs ${definition.operandCount} distinct qubits.`);
      return;
    }
    const result = addGate(document, gate, operands, index);
    const next = resultDocument(result, setNotice);
    if (next) {
      onChange(next);
      setSelectedId(next.operations[index]?.id);
    }
  };

  const insertEffect = (
    effect: EffectKind,
    index = document.operations.length,
    preferred?: RegisterRef,
  ) => {
    const source = preferred ?? qubits[0]?.reference;
    if (!source) return setNotice("Add a qubit register before measuring.");
    const operation =
      effect === "measurement"
        ? {
            kind: "measurement" as const,
            source,
            ...(bits[0]?.reference ? { target: bits[0].reference } : {}),
          }
        : effect === "reset"
          ? { kind: "reset" as const, target: source }
          : { kind: "barrier" as const, targets: [source] };
    const result = addOperation(document, operation, index);
    const next = resultDocument(result, setNotice);
    if (next) {
      onChange(next);
      setSelectedId(next.operations[index]?.id);
    }
  };

  const laneAt = (clientY: number) => {
    const track = canvasRef.current?.getBoundingClientRect();
    const scaledRow = ROW_HEIGHT * (zoom / 100);
    const laneIndex = track
      ? Math.round((clientY - track.top - TOP * (zoom / 100)) / scaledRow)
      : 0;
    return lanes[Math.max(0, Math.min(laneIndex, lanes.length - 1))];
  };

  const insertionIndexAt = (clientX: number) => {
    const track = canvasRef.current?.getBoundingClientRect();
    if (!track) return document.operations.length;
    const scale = zoom / 100;
    const column = Math.round(
      (clientX - track.left - LABEL_WIDTH * scale) / (COLUMN_WIDTH * scale),
    );
    return Math.max(0, Math.min(column, document.operations.length));
  };

  const previewReorder = (insertionIndex: number) => {
    if (reorderSession?.status !== "dragging") return;
    const result = moveOperation(document, reorderSession.operationId, insertionIndex);
    if (!result.ok) return;
    const next = result.document.operations.map((operation) => operation.id);
    setReorderSession((current) =>
      current?.status === "dragging" &&
      (current.visualOrder.length !== next.length ||
        current.visualOrder.some((id, index) => id !== next[index]))
        ? { ...current, visualOrder: next }
        : current,
    );
  };

  const handleDrop = (
    event: DragEvent<HTMLElement>,
    insertionIndex: number,
    preferredReference?: RegisterRef,
  ) => {
    event.preventDefault();
    event.stopPropagation();
    const payload = readDragPayload(event);
    const preferredLane = preferredReference
      ? lanes.find((lane) => refKey(lane.reference) === refKey(preferredReference))
      : laneAt(event.clientY);
    const preferredQubit = preferredLane?.kind === "qubit" ? preferredLane.reference : undefined;
    const preferredBit = preferredLane?.kind === "bit" ? preferredLane.reference : undefined;
    if (payload.startsWith("measurement-target:")) {
      clearDragState();
      const operationId = payload.slice("measurement-target:".length);
      if (!operationId || !preferredBit) {
        setNotice("Drop measurement results on a classical wire.");
        return;
      }
      apply(placeMeasurementTarget(document, operationId, preferredBit));
      setSelectedId(operationId);
      return;
    }
    if (payload.startsWith("operand:")) {
      clearDragState();
      const [, operationId, operandIndex] = payload.split(":");
      if (!operationId || operandIndex === undefined || !preferredQubit) {
        setNotice("Drop gate endpoints on a quantum wire.");
        return;
      }
      apply(placeOperationOperand(document, operationId, Number(operandIndex), preferredQubit));
      setSelectedId(operationId);
      return;
    }
    if (payload.startsWith("operation:")) {
      const operationId = payload.slice("operation:".length);
      const next = resultDocument(
        placeOperation(document, operationId, insertionIndex, preferredQubit),
        setNotice,
      );
      if (next) {
        setReorderSession({
          operationId,
          status: "committed",
          visualOrder: next.operations.map((operation) => operation.id),
        });
        clearDragState();
        onChange(next);
        setSelectedId(operationId);
      } else {
        setReorderSession(undefined);
        clearDragState();
      }
      return;
    }
    if (payload.startsWith("gate:")) {
      clearDragState();
      insertGate(payload.slice("gate:".length) as GateName, insertionIndex, preferredQubit);
      return;
    }
    if (payload.startsWith("effect:")) {
      clearDragState();
      insertEffect(payload.slice("effect:".length) as EffectKind, insertionIndex, preferredQubit);
      return;
    }
    clearDragState();
  };

  const handleTrackDragOver = (event: DragEvent<HTMLElement>) => {
    event.preventDefault();
    event.dataTransfer.dropEffect = isMovePayload(dragPayload) ? "move" : "copy";
    const insertionIndex = insertionIndexAt(event.clientX);
    setActiveDropIndex(isEndpointPayload(dragPayload) ? undefined : insertionIndex);
    previewReorder(insertionIndex);
    const lane = laneAt(event.clientY);
    const expectedKind = dragPayload?.startsWith("measurement-target:") ? "bit" : "qubit";
    setActiveLaneKey(lane?.kind === expectedKind ? lane.key : undefined);
  };

  const deleteOperation = (operationId: string) => {
    const index = document.operations.findIndex((operation) => operation.id === operationId);
    if (index < 0) return setNotice("The dragged operation no longer exists.");
    onChange(removeOperation(document, operationId));
    if (selectedId === operationId) setSelectedId(undefined);
    setNotice(`Removed step ${index + 1}.`);
  };

  const handleDiscardDrop = (event: DragEvent<HTMLButtonElement>) => {
    event.preventDefault();
    const payload = readDragPayload(event);
    endDrag();
    if (!payload.startsWith("operation:")) {
      setNotice("Only existing circuit steps can be discarded.");
      return;
    }
    deleteOperation(payload.slice("operation:".length));
  };

  const moveSelected = (delta: number) => {
    if (!selected) return;
    const index = document.operations.findIndex((operation) => operation.id === selected.id);
    apply(moveOperation(document, selected.id, index + (delta < 0 ? -1 : 2)));
  };

  const handleKeys = (event: KeyboardEvent<HTMLElement>) => {
    if (event.target instanceof HTMLInputElement || event.target instanceof HTMLSelectElement)
      return;
    const modifier = event.metaKey || event.ctrlKey;
    if (modifier && event.key.toLowerCase() === "z") {
      event.preventDefault();
      event.shiftKey ? onRedo() : onUndo();
    } else if (modifier && event.key.toLowerCase() === "d" && selected) {
      event.preventDefault();
      apply(duplicateOperation(document, selected.id));
    } else if ((event.key === "Delete" || event.key === "Backspace") && selected) {
      event.preventDefault();
      deleteOperation(selected.id);
    } else if (event.altKey && event.key === "ArrowLeft") {
      event.preventDefault();
      moveSelected(-1);
    } else if (event.altKey && event.key === "ArrowRight") {
      event.preventDefault();
      moveSelected(1);
    } else if (event.key === "ArrowLeft" || event.key === "ArrowRight") {
      const index = selected
        ? document.operations.findIndex((operation) => operation.id === selected.id)
        : -1;
      const next =
        event.key === "ArrowLeft"
          ? Math.max(0, index - 1)
          : Math.min(document.operations.length - 1, index + 1);
      setSelectedId(document.operations[next]?.id);
    } else if (event.key === "Enter" && selected) {
      window.document.getElementById("operation-inspector")?.focus();
    } else if (event.key === "Escape") {
      setSelectedId(undefined);
    }
  };

  return (
    <main className="workbench" onKeyDown={handleKeys}>
      <header className="topbar">
        <div className="brand-block">
          <span className="brand-sigil" aria-hidden="true">
            <i />
            <i />
          </span>
          <div>
            <p className="eyebrow">QASM Editor / OpenQASM 3.0</p>
            <h1>Circuit workbench</h1>
          </div>
        </div>
        <nav className="toolbar" aria-label="Document controls">
          <button type="button" onClick={onUndo} aria-label="Undo">
            ↶
          </button>
          <button type="button" onClick={onRedo} aria-label="Redo">
            ↷
          </button>
          <span className="toolbar-rule" />
          <label className="zoom-control">
            <span>Zoom</span>
            <input
              aria-label="Circuit zoom"
              type="range"
              min="60"
              max="160"
              step="10"
              value={zoom}
              onChange={(event) => setZoom(Number(event.target.value))}
            />
            <output>{zoom}%</output>
          </label>
          <button type="button" onClick={onOpenSource}>
            Source
          </button>
        </nav>
      </header>

      <aside className="palette-panel" aria-label="Gate palette">
        <div className="panel-heading">
          <p className="eyebrow">Operations</p>
          <span>{visibleGates.length}</span>
        </div>
        <label className="search-field">
          <span className="sr-only">Search gates</span>
          <span aria-hidden="true">⌕</span>
          <input
            value={search}
            onChange={(event) => setSearch(event.target.value)}
            placeholder="Filter gates"
          />
        </label>
        <div className="gate-palette">
          {visibleGates.map((gate) => (
            <button
              key={gate.name}
              className={`palette-gate category-${gate.category}`}
              type="button"
              draggable
              onDragStart={(event) => beginDrag(event, `gate:${gate.name}`, "copy")}
              onDragEnd={endDrag}
              onClick={() => insertGate(gate.name)}
              title={`${gate.description}. Drag to place or click to append.`}
            >
              <strong>{gate.label}</strong>
              <small>{gate.operandCount === 0 ? "global" : `${gate.operandCount}q`}</small>
            </button>
          ))}
        </div>
        <section className="effect-palette" aria-label="Quantum effects">
          <button
            type="button"
            draggable
            onDragStart={(event) => beginDrag(event, "effect:measurement", "copy")}
            onDragEnd={endDrag}
            onClick={() => insertEffect("measurement")}
            title="Drag to place or click to append."
          >
            <span>M</span>Measure
          </button>
          <button
            type="button"
            draggable
            onDragStart={(event) => beginDrag(event, "effect:reset", "copy")}
            onDragEnd={endDrag}
            onClick={() => insertEffect("reset")}
            title="Drag to place or click to append."
          >
            <span>↺</span>Reset
          </button>
          <button
            type="button"
            draggable
            onDragStart={(event) => beginDrag(event, "effect:barrier", "copy")}
            onDragEnd={endDrag}
            onClick={() => insertEffect("barrier")}
            title="Drag to place or click to append."
          >
            <span>╫</span>Barrier
          </button>
        </section>
      </aside>

      <section className="canvas-panel" aria-label="Quantum circuit canvas">
        <div className="canvas-ruler">
          <span>{document.operations.length} ordered steps</span>
          <div className="canvas-ruler-actions">
            <span>
              {qubits.length} quantum · {bits.length} classical wires
            </span>
            <fieldset className="wire-tools">
              <legend className="sr-only">Wire controls</legend>
              <button
                type="button"
                onClick={() => apply(addWire(document, "qubit"))}
                aria-label="Add quantum wire"
                title="Add quantum wire"
              >
                +Q
              </button>
              <button
                type="button"
                onClick={() => apply(addWire(document, "bit"))}
                aria-label="Add classical wire"
                title="Add classical wire"
              >
                +C
              </button>
            </fieldset>
            <button
              type="button"
              className={`discard-target${dragPayload?.startsWith("operation:") ? " drag-ready" : ""}${discardActive ? " drop-active" : ""}`}
              aria-label="Drop operation to delete"
              onClick={() =>
                selected
                  ? deleteOperation(selected.id)
                  : setNotice("Select or drag a circuit step to discard it.")
              }
              onDragEnter={(event) => {
                event.preventDefault();
                if (dragPayload?.startsWith("operation:")) setDiscardActive(true);
              }}
              onDragOver={(event) => {
                event.preventDefault();
                event.dataTransfer.dropEffect = "move";
                if (dragPayload?.startsWith("operation:")) setDiscardActive(true);
              }}
              onDragLeave={() => setDiscardActive(false)}
              onDrop={handleDiscardDrop}
            >
              <span aria-hidden="true">×</span>
              Discard
            </button>
          </div>
        </div>
        <div className="canvas-scroll">
          <section
            ref={canvasRef}
            className={`circuit-track${dragPayload ? " dragging" : ""}${dragPayload?.startsWith("operation:") ? " reorder-preview" : ""}`}
            style={
              {
                width: canvasWidth,
                height: canvasHeight,
                "--circuit-zoom": zoom / 100,
              } as CSSProperties
            }
            aria-label="Ordered OpenQASM circuit"
            onDragOver={handleTrackDragOver}
            onDrop={(event) => handleDrop(event, insertionIndexAt(event.clientX))}
          >
            {lanes.map((lane, index) => {
              const register = document.registers.find(
                (candidate) => candidate.name === lane.reference.register,
              );
              return (
                <div
                  key={lane.key}
                  className={`wire-row wire-${lane.kind}${activeLaneKey === lane.key ? " drop-active" : ""}`}
                  style={{ top: TOP + index * ROW_HEIGHT }}
                >
                  <span className="wire-label">{lane.label}</span>
                  <button
                    type="button"
                    className="wire-drop-target"
                    aria-label={`Drop operations on ${lane.label}`}
                    onClick={() =>
                      setNotice(`Drag an operation here to place it on ${lane.label}.`)
                    }
                    onDragEnter={() =>
                      setActiveLaneKey(
                        lane.kind ===
                          (dragPayload?.startsWith("measurement-target:") ? "bit" : "qubit")
                          ? lane.key
                          : undefined,
                      )
                    }
                    onDragOver={(event) => {
                      event.preventDefault();
                      event.dataTransfer.dropEffect = isMovePayload(dragPayload) ? "move" : "copy";
                      const expectedKind = dragPayload?.startsWith("measurement-target:")
                        ? "bit"
                        : "qubit";
                      setActiveLaneKey(lane.kind === expectedKind ? lane.key : undefined);
                      const insertionIndex = insertionIndexAt(event.clientX);
                      setActiveDropIndex(
                        isEndpointPayload(dragPayload) ? undefined : insertionIndex,
                      );
                      previewReorder(insertionIndex);
                    }}
                    onDrop={(event) =>
                      handleDrop(event, insertionIndexAt(event.clientX), lane.reference)
                    }
                  />
                  <button
                    type="button"
                    className="wire-delete"
                    aria-label={`Delete wire ${lane.label}`}
                    title={`Delete ${lane.label}`}
                    onClick={() => {
                      if (register) apply(removeWire(document, register.id, lane.reference.index));
                    }}
                  >
                    ×
                  </button>
                  <span className="wire-line" />
                </div>
              );
            })}
            {stableRenderIds.map((operationId) => {
              const operation = operationById.get(operationId);
              if (!operation) return null;
              const documentIndex = document.operations.findIndex(
                (candidate) => candidate.id === operationId,
              );
              const visualIndex = visualOrder.indexOf(operation.id);
              return (
                <OperationButton
                  key={operation.id}
                  operation={operation}
                  index={visualIndex >= 0 ? visualIndex : documentIndex}
                  lanes={lanes}
                  selected={operation.id === selectedId}
                  dragging={dragPayload === `operation:${operation.id}`}
                  draggingEndpoint={
                    dragPayload?.startsWith(`operand:${operation.id}:`) ||
                    dragPayload === `measurement-target:${operation.id}`
                      ? dragPayload
                      : undefined
                  }
                  onSelect={() => setSelectedId(operation.id)}
                  onDragStart={(event) => beginDrag(event, `operation:${operation.id}`, "move")}
                  onEndpointDragStart={(event, operandIndex) =>
                    beginDrag(event, `operand:${operation.id}:${operandIndex}`, "move")
                  }
                  onClassicalTargetDragStart={(event) =>
                    beginDrag(event, `measurement-target:${operation.id}`, "move")
                  }
                  onDragEnd={endDrag}
                />
              );
            })}
            {Array.from({ length: document.operations.length + 1 }, (_, index) => (
              <button
                key={
                  index === 0
                    ? "slot-start"
                    : `slot-after-${document.operations[index - 1]?.id ?? "end"}`
                }
                className={`insertion-slot${dragPayload && !isEndpointPayload(dragPayload) ? " drag-ready" : ""}${activeDropIndex === index ? " drop-active" : ""}`}
                style={{
                  left: LABEL_WIDTH + index * COLUMN_WIDTH - 13,
                  top: 20,
                  height: canvasHeight - 32,
                }}
                type="button"
                aria-label={`Insert operation at step ${index + 1}`}
                onDragOver={(event) => {
                  event.preventDefault();
                  event.dataTransfer.dropEffect = isMovePayload(dragPayload) ? "move" : "copy";
                  setActiveDropIndex(isEndpointPayload(dragPayload) ? undefined : index);
                  previewReorder(index);
                }}
                onDragEnter={() => {
                  setActiveDropIndex(isEndpointPayload(dragPayload) ? undefined : index);
                  previewReorder(index);
                }}
                onDragLeave={() =>
                  setActiveDropIndex((current) => (current === index ? undefined : current))
                }
                onDrop={(event) => handleDrop(event, index)}
              >
                <span>+</span>
              </button>
            ))}
          </section>
        </div>
      </section>

      <aside className="inspector-panel" aria-label="Circuit inspector">
        {selected ? (
          <OperationInspector
            key={selected.id}
            operation={selected}
            document={document}
            onUpdate={(operation) => apply(updateOperation(document, selected.id, operation))}
            onDelete={() => deleteOperation(selected.id)}
            onDuplicate={() => apply(duplicateOperation(document, selected.id))}
            onMove={moveSelected}
            onNotice={setNotice}
          />
        ) : (
          <RegisterInspector document={document} onChange={onChange} onNotice={setNotice} />
        )}
      </aside>

      <footer className="statusbar" aria-live="polite">
        <span className={pending ? "status-pulse active" : "status-pulse"} aria-hidden="true" />
        <span>
          {pending
            ? "Writing canonical OpenQASM…"
            : (externalNotice ?? notice ?? "Circuit is structurally valid.")}
        </span>
        <span className="status-spacer" />
        <span>OPENQASM 3.0</span>
      </footer>
    </main>
  );
}

function OperationButton({
  operation,
  index,
  lanes,
  selected,
  dragging,
  draggingEndpoint,
  onSelect,
  onDragStart,
  onEndpointDragStart,
  onClassicalTargetDragStart,
  onDragEnd,
}: {
  operation: CircuitOperation;
  index: number;
  lanes: Lane[];
  selected: boolean;
  dragging: boolean;
  draggingEndpoint: string | undefined;
  onSelect(): void;
  onDragStart(event: DragEvent<HTMLButtonElement>): void;
  onEndpointDragStart(event: DragEvent<HTMLButtonElement>, operandIndex: number): void;
  onClassicalTargetDragStart(event: DragEvent<HTMLButtonElement>): void;
  onDragEnd(): void;
}) {
  const refs = operationReferences(operation);
  const positions = refs
    .map((reference) => lanes.findIndex((lane) => refKey(lane.reference) === refKey(reference)))
    .filter((value) => value >= 0);
  const minimum = positions.length > 0 ? Math.min(...positions) : 0;
  const maximum = positions.length > 0 ? Math.max(...positions) : minimum;
  const height = Math.max(36, (maximum - minimum) * ROW_HEIGHT + 36);
  const left = LABEL_WIDTH + index * COLUMN_WIDTH + 10;
  const top =
    operation.kind === "gate" && operation.operands.length === 0
      ? 4
      : TOP + minimum * ROW_HEIGHT - 18;
  const endpointPositions = operation.kind === "gate" ? positions : [];
  return (
    <div
      className={`operation-node operation-${operation.kind}${selected ? " selected" : ""}${dragging ? " dragging" : ""}`}
      style={{ left, top, width: 68, height }}
    >
      <button
        type="button"
        className="operation-body"
        aria-label={description(operation)}
        aria-pressed={selected}
        draggable
        onDragStart={onDragStart}
        onDragEnd={onDragEnd}
        onClick={onSelect}
      >
        <OperationGlyph
          operation={operation}
          positions={positions.map((position) => position - minimum)}
        />
        <span className="step-index">{String(index + 1).padStart(2, "0")}</span>
      </button>
      {operation.kind === "gate" && operation.operands.length > 1
        ? endpointPositions.map((position, operandIndex) => {
            const operand = operation.operands[operandIndex];
            if (!operand) return null;
            const payload = `operand:${operation.id}:${operandIndex}`;
            return (
              <button
                key={`${operation.id}-endpoint-${refKey(operand)}`}
                type="button"
                className={`endpoint-handle${draggingEndpoint === payload ? " dragging" : ""}`}
                style={{ top: 18 + (position - minimum) * ROW_HEIGHT - 18 }}
                aria-label={`Move ${operation.gate} operand ${operandIndex + 1} from ${refKey(operand)}`}
                draggable
                onClick={(event) => {
                  event.stopPropagation();
                  onSelect();
                }}
                onDragStart={(event) => {
                  event.stopPropagation();
                  onEndpointDragStart(event, operandIndex);
                }}
                onDragEnd={onDragEnd}
                title={`Drag endpoint ${operandIndex + 1} from ${refKey(operand)}`}
              >
                <span aria-hidden="true">{operandIndex + 1}</span>
              </button>
            );
          })
        : null}
      {operation.kind === "measurement" && operation.target && positions[1] !== undefined ? (
        <button
          type="button"
          className={`endpoint-handle classical-endpoint${draggingEndpoint === `measurement-target:${operation.id}` ? " dragging" : ""}`}
          style={{ top: 18 + ((positions[1] ?? minimum) - minimum) * ROW_HEIGHT - 18 }}
          aria-label={`Move measurement classical target from ${refKey(operation.target)}`}
          draggable
          onClick={(event) => {
            event.stopPropagation();
            onSelect();
          }}
          onDragStart={(event) => {
            event.stopPropagation();
            onClassicalTargetDragStart(event);
          }}
          onDragEnd={onDragEnd}
          title={`Drag classical result from ${refKey(operation.target)}`}
        >
          <span aria-hidden="true">C</span>
        </button>
      ) : null}
    </div>
  );
}

function OperationGlyph({
  operation,
  positions,
}: {
  operation: CircuitOperation;
  positions: number[];
}) {
  const y = (position: number) => 18 + position * ROW_HEIGHT;
  const bottom = Math.max(18, ...positions.map(y));
  const top = Math.min(18, ...positions.map(y));
  if (operation.kind === "barrier") {
    return (
      <svg viewBox={`0 0 68 ${bottom + 18}`} aria-hidden="true">
        <path className="barrier-glyph" d={`M28 ${top}V${bottom}M39 ${top}V${bottom}`} />
      </svg>
    );
  }
  if (operation.kind === "measurement") {
    const sourceY = y(positions[0] ?? 0);
    const targetY = positions[1] === undefined ? sourceY : y(positions[1]);
    return (
      <svg viewBox={`0 0 68 ${bottom + 18}`} aria-hidden="true">
        <path className="connector" d={`M34 ${sourceY}V${targetY}`} />
        <rect
          className="gate-box measure-box"
          x="14"
          y={sourceY - 15}
          width="40"
          height="30"
          rx="8"
        />
        <path
          className="measure-arc"
          d={`M23 ${sourceY + 7}a12 12 0 0 1 22 0M34 ${sourceY + 4}l8-9`}
        />
        {positions[1] !== undefined && (
          <path className="classical-mark" d={`M27 ${targetY - 3}l7 7 7-7`} />
        )}
      </svg>
    );
  }
  if (operation.kind === "reset") {
    return (
      <svg viewBox="0 0 68 36" aria-hidden="true">
        <circle className="reset-ring" cx="34" cy="18" r="14" />
        <path className="reset-arrow" d="M25 20a10 10 0 0 1 16-8l2-5m0 0-6 1" />
      </svg>
    );
  }
  const definition = GATE_BY_NAME.get(operation.gate);
  if (!definition) return null;
  if (positions.length === 0) return <span className="global-phase">GΦ</span>;
  const controlled =
    definition.category === "controlled" || ["CX", "cphase", "cu"].includes(operation.gate);
  const swap = operation.gate === "swap" || operation.gate === "cswap";
  return (
    <svg viewBox={`0 0 68 ${bottom + 18}`} aria-hidden="true">
      {positions.length > 1 && <path className="connector" d={`M34 ${top}V${bottom}`} />}
      {positions.map((position, operandIndex) => {
        const center = y(position);
        const isControl =
          controlled &&
          operandIndex < positions.length - 1 &&
          !(operation.gate === "cswap" && operandIndex > 0);
        const isSwap = swap && (!controlled || operandIndex > 0);
        if (isControl)
          return <circle key={position} className="control-dot" cx="34" cy={center} r="5" />;
        if (isSwap)
          return (
            <path key={position} className="swap-mark" d={`M26 ${center - 8}l16 16m0-16-16 16`} />
          );
        return (
          <g key={position}>
            <rect className="gate-box" x="12" y={center - 16} width="44" height="32" rx="8" />
            <text className="gate-label" x="34" y={center + 4}>
              {controlled &&
              operandIndex === positions.length - 1 &&
              operation.gate.toLowerCase().endsWith("x")
                ? "⊕"
                : definition.label}
            </text>
          </g>
        );
      })}
    </svg>
  );
}

function OperationInspector({
  operation,
  document,
  onUpdate,
  onDelete,
  onDuplicate,
  onMove,
  onNotice,
}: {
  operation: CircuitOperation;
  document: CircuitDocument;
  onUpdate(operation: CircuitOperation): void;
  onDelete(): void;
  onDuplicate(): void;
  onMove(delta: number): void;
  onNotice(message: string | undefined): void;
}) {
  const qubits = lanesOf(document).filter((lane) => lane.kind === "qubit");
  const bits = lanesOf(document).filter((lane) => lane.kind === "bit");
  const [parameters, setParameters] = useState(
    operation.kind === "gate" ? operation.parameters.map(serializeParameterExpression) : [],
  );
  const updateRef = (reference: string) => {
    const lane = [...qubits, ...bits].find(
      (candidate) => refKey(candidate.reference) === reference,
    );
    return lane?.reference;
  };
  const commitParameter = (index: number) => {
    if (operation.kind !== "gate") return;
    try {
      const next = [...operation.parameters];
      next[index] = parseParameterExpression(parameters[index] ?? "");
      onNotice(undefined);
      onUpdate({ ...operation, parameters: next });
    } catch (error) {
      onNotice(error instanceof Error ? error.message : String(error));
    }
  };
  return (
    <div className="inspector-content" id="operation-inspector" tabIndex={-1}>
      <div className="panel-heading">
        <p className="eyebrow">Selected step</p>
        <span>{operation.id.replace("operation-", "#")}</span>
      </div>
      <h2>
        {operation.kind === "gate" ? GATE_BY_NAME.get(operation.gate)?.description : operation.kind}
      </h2>
      <p className="muted inspector-description">{description(operation)}</p>
      {operation.kind === "gate" && (
        <>
          {operation.parameters.map((_, index) => (
            // biome-ignore lint/suspicious/noArrayIndexKey: parameter positions are fixed by each OpenQASM gate signature
            <label className="field" key={`parameter-${index}`}>
              <span>Parameter {index + 1}</span>
              <input
                value={parameters[index] ?? ""}
                onChange={(event) =>
                  setParameters(
                    parameters.map((value, candidate) =>
                      candidate === index ? event.target.value : value,
                    ),
                  )
                }
                onBlur={() => commitParameter(index)}
                onKeyDown={(event) => event.key === "Enter" && event.currentTarget.blur()}
              />
            </label>
          ))}
          {operation.operands.map((operand, index) => (
            <label className="field" key={refKey(operand)}>
              <span>Qubit {index + 1}</span>
              <select
                value={refKey(operand)}
                onChange={(event) => {
                  const reference = updateRef(event.target.value);
                  if (!reference) return;
                  const operands = [...operation.operands];
                  operands[index] = reference;
                  onUpdate({ ...operation, operands });
                }}
              >
                {qubits.map((lane) => (
                  <option key={lane.key} value={refKey(lane.reference)}>
                    {lane.label}
                  </option>
                ))}
              </select>
            </label>
          ))}
        </>
      )}
      {operation.kind === "measurement" && (
        <>
          <ReferenceSelect
            label="Source qubit"
            value={operation.source}
            lanes={qubits}
            onChange={(source) => onUpdate({ ...operation, source })}
          />
          <label className="field">
            <span>Classical target</span>
            <select
              value={operation.target ? refKey(operation.target) : ""}
              onChange={(event) => {
                const target = updateRef(event.target.value);
                onUpdate(
                  target
                    ? { ...operation, target }
                    : { id: operation.id, kind: "measurement", source: operation.source },
                );
              }}
            >
              <option value="">Discard result</option>
              {bits.map((lane) => (
                <option key={lane.key} value={refKey(lane.reference)}>
                  {lane.label}
                </option>
              ))}
            </select>
          </label>
        </>
      )}
      {operation.kind === "reset" && (
        <ReferenceSelect
          label="Reset qubit"
          value={operation.target}
          lanes={qubits}
          onChange={(target) => onUpdate({ ...operation, target })}
        />
      )}
      {operation.kind === "barrier" && (
        <fieldset className="target-fieldset">
          <legend>Barrier targets</legend>
          {qubits.map((lane) => {
            const checked = operation.targets.some(
              (target) => refKey(target) === refKey(lane.reference),
            );
            return (
              <label key={lane.key}>
                <input
                  type="checkbox"
                  checked={checked}
                  onChange={() => {
                    const targets = checked
                      ? operation.targets.filter(
                          (target) => refKey(target) !== refKey(lane.reference),
                        )
                      : [...operation.targets, lane.reference];
                    if (targets.length === 0)
                      return onNotice("A barrier requires at least one qubit.");
                    onUpdate({ ...operation, targets });
                  }}
                />
                {lane.label}
              </label>
            );
          })}
        </fieldset>
      )}
      <div className="inspector-actions">
        <button type="button" onClick={() => onMove(-1)} aria-label="Move operation left">
          ←
        </button>
        <button type="button" onClick={() => onMove(1)} aria-label="Move operation right">
          →
        </button>
        <button type="button" onClick={onDuplicate}>
          Duplicate
        </button>
        <button className="danger-button" type="button" onClick={onDelete}>
          Delete
        </button>
      </div>
    </div>
  );
}

function ReferenceSelect({
  label,
  value,
  lanes,
  onChange,
}: {
  label: string;
  value: RegisterRef;
  lanes: Lane[];
  onChange(reference: RegisterRef): void;
}) {
  return (
    <label className="field">
      <span>{label}</span>
      <select
        value={refKey(value)}
        onChange={(event) => {
          const reference = lanes.find(
            (lane) => refKey(lane.reference) === event.target.value,
          )?.reference;
          if (reference) onChange(reference);
        }}
      >
        {lanes.map((lane) => (
          <option key={lane.key} value={refKey(lane.reference)}>
            {lane.label}
          </option>
        ))}
      </select>
    </label>
  );
}

function RegisterInspector({
  document,
  onChange,
  onNotice,
}: {
  document: CircuitDocument;
  onChange(document: CircuitDocument): void;
  onNotice(message: string | undefined): void;
}) {
  const apply = (result: EditResult) => {
    const next = resultDocument(result, onNotice);
    if (next) onChange(next);
  };
  return (
    <div className="inspector-content">
      <div className="panel-heading">
        <p className="eyebrow">Registers</p>
        <span>{document.registers.length}</span>
      </div>
      <h2>Wire topology</h2>
      <p className="muted inspector-description">
        Register edits update every indexed operand atomically.
      </p>
      <div className="register-list">
        {document.registers.map((register) => (
          <RegisterRow
            key={register.id}
            register={register}
            onCommit={(next) => apply(updateRegister(document, register.id, next))}
            onDelete={() => apply(removeRegister(document, register.id))}
          />
        ))}
      </div>
      <div className="register-add">
        <button type="button" onClick={() => apply(addRegister(document, "qubit"))}>
          + Qubit register
        </button>
        <button type="button" onClick={() => apply(addRegister(document, "bit"))}>
          + Bit register
        </button>
      </div>
      <div className="shortcut-card">
        <p className="eyebrow">Keyboard</p>
        <dl>
          <div>
            <dt>⌘/Ctrl D</dt>
            <dd>Duplicate</dd>
          </div>
          <div>
            <dt>⌥ ← →</dt>
            <dd>Reorder</dd>
          </div>
          <div>
            <dt>Delete</dt>
            <dd>Remove</dd>
          </div>
        </dl>
      </div>
    </div>
  );
}

function RegisterRow({
  register,
  onCommit,
  onDelete,
}: {
  register: CircuitRegister;
  onCommit(value: Pick<CircuitRegister, "name" | "size">): void;
  onDelete(): void;
}) {
  const [name, setName] = useState(register.name);
  const [size, setSize] = useState(String(register.size));
  const commit = () => onCommit({ name: name.trim(), size: Number(size) });
  return (
    <div className={`register-row register-${register.kind}`}>
      <span className="register-kind">{register.kind === "qubit" ? "Q" : "C"}</span>
      <label>
        <span className="sr-only">Register name</span>
        <input
          value={name}
          onChange={(event) => setName(event.target.value)}
          onBlur={commit}
          onKeyDown={(event) => event.key === "Enter" && event.currentTarget.blur()}
        />
      </label>
      <label className="size-field">
        <span>×</span>
        <input
          aria-label={`${register.name} size`}
          type="number"
          min="1"
          value={size}
          onChange={(event) => setSize(event.target.value)}
          onBlur={commit}
          onKeyDown={(event) => event.key === "Enter" && event.currentTarget.blur()}
        />
      </label>
      <button type="button" onClick={onDelete} aria-label={`Delete ${register.name}`}>
        ×
      </button>
    </div>
  );
}
