import React from "react";
import { createRoot } from "react-dom/client";
import { CircuitEditorApp, type EditorBridge } from "./App";
import "./styles.css";

declare function acquireVsCodeApi(): {
  postMessage(message: unknown): void;
  getState(): unknown;
  setState(state: unknown): void;
};

const api = acquireVsCodeApi();
const bridge: EditorBridge = {
  postMessage: (message) => api.postMessage(message),
  subscribe: (listener) => {
    const handler = (event: MessageEvent) => listener(event.data);
    window.addEventListener("message", handler);
    return () => window.removeEventListener("message", handler);
  },
};

const root = document.getElementById("root");
if (!root) throw new Error("Missing QASM Editor webview root.");
createRoot(root).render(
  <React.StrictMode>
    <CircuitEditorApp bridge={bridge} />
  </React.StrictMode>,
);
