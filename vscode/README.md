# QASM Editor

A graphical, source-backed OpenQASM 3.0 circuit editor for VS Code desktop and the web. The canvas keeps one OpenQASM statement per column, while the text document remains the source of truth for undo, redo, save, and external edits.

## Use the editor

Open a `.qasm` file, then run **QASM Editor: Open as Circuit** from the Command Palette or choose **Reopen Editor With… → QASM Editor**. Use **QASM Editor: New Quantum Circuit** to create a new source file.

The workbench supports palette clicks and drag/drop, operation reordering, register edits, gate parameters, measurements, reset, barriers, zoom, and keyboard commands. The **Source** button returns to the normal text editor.

## Editable OpenQASM subset

The graphical editor intentionally accepts a portable linear subset:

- `OPENQASM 3.0` and `include "stdgates.inc"`;
- fixed `qubit` and `bit` registers;
- explicit indexed operands such as `q[0]`;
- standard gates, `U`, and `gphase` with literal `pi` arithmetic;
- measurement assignment or arrow syntax, reset, and barrier.

Control flow, timing, calibration, custom definitions, dynamic operands, and other non-linear constructs open as an explained read-only boundary instead of being rewritten. Graphical edits serialize to deterministic canonical OpenQASM, so comments and whitespace are normalized after a canvas edit.

## Development

The project uses TypeScript 7, React 19, Vite 8, Vitest 4, Biome 2, and Open Props. It requires the Node version recorded in `.node-version`.

```sh
npm install
npm run check
```

Useful focused commands:

```sh
npm run typecheck
npm run lint
npm run launch
npm run test:unit
npm run test:browser
npm run test:extension:web
npm run test:extension:desktop
npm run package
```

`npm run launch` builds the project and opens `tests/fixtures/workspace/bell.qasm` with the
graphical editor in a new Extension Development Host. Set `VSCODE_CLI_PATH` when the VS Code CLI
is not named `code`.

The automated suite covers the parser/serializer and editing invariants, host/webview protocol validation, React interactions, drag/drop, keyboard behavior, responsive layout, automated accessibility checks, a reviewed Chromium visual baseline, Chromium/Firefox/WebKit execution, and VS Code custom-editor activation.

## Architecture

`src/circuit` contains the self-contained circuit model, subset parser, validator, edit operations, expression parser, and canonical serializer. `src/extension.ts` owns VS Code document synchronization and rejects stale or invalid webview writes. `src/webview` contains the React workbench. The extension bundle is worker-compatible CommonJS for desktop and web extension hosts; the webview remains an ESM Vite application protected by a restrictive content security policy.
