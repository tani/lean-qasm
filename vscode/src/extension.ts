import * as vscode from "vscode";
import { EMPTY_CIRCUIT } from "./circuit/model";
import { parseCircuit } from "./circuit/parser";
import { serializeCircuit } from "./circuit/serializer";
import { type HostToWebviewMessage, isWebviewMessage } from "./protocol";

const VIEW_TYPE = "tani.qasm-editor.circuit";

class CircuitEditorProvider implements vscode.CustomTextEditorProvider {
  constructor(private readonly context: vscode.ExtensionContext) {}

  async resolveCustomTextEditor(
    document: vscode.TextDocument,
    panel: vscode.WebviewPanel,
  ): Promise<void> {
    panel.webview.options = {
      enableScripts: true,
      localResourceRoots: [vscode.Uri.joinPath(this.context.extensionUri, "dist", "webview")],
    };
    panel.webview.html = this.webviewHtml(panel.webview);

    const sendDocument = (requestId?: string) => {
      const text = document.getText();
      const message: HostToWebviewMessage = {
        type: "documentChanged",
        version: document.version,
        text,
        parsed: parseCircuit(text),
        ...(requestId ? { requestId } : {}),
      };
      return panel.webview.postMessage(message);
    };

    const changeSubscription = vscode.workspace.onDidChangeTextDocument((event) => {
      if (event.document.uri.toString() === document.uri.toString()) void sendDocument();
    });

    const messageSubscription = panel.webview.onDidReceiveMessage(async (value: unknown) => {
      if (!isWebviewMessage(value)) return;
      if (value.type === "ready") {
        await sendDocument();
        return;
      }
      if (value.type === "openSource") {
        await vscode.commands.executeCommand("vscode.openWith", document.uri, "default");
        return;
      }
      if (value.type === "undo" || value.type === "redo") {
        await vscode.commands.executeCommand(value.type);
        return;
      }
      if (value.baseVersion !== document.version) {
        await sendDocument();
        await panel.webview.postMessage({
          type: "editRejected",
          requestId: value.requestId,
          message:
            "The source changed before this edit was applied. The circuit has been refreshed.",
        } satisfies HostToWebviewMessage);
        return;
      }
      const parsed = parseCircuit(value.text);
      if (!parsed.ok) {
        await sendDocument();
        await panel.webview.postMessage({
          type: "editRejected",
          requestId: value.requestId,
          message: parsed.message,
        } satisfies HostToWebviewMessage);
        return;
      }
      if (value.text === document.getText()) {
        await sendDocument(value.requestId);
        return;
      }
      const range = new vscode.Range(
        document.positionAt(0),
        document.positionAt(document.getText().length),
      );
      const edit = new vscode.WorkspaceEdit();
      edit.replace(document.uri, range, value.text);
      if (await vscode.workspace.applyEdit(edit)) {
        await sendDocument(value.requestId);
      } else {
        await sendDocument();
        await panel.webview.postMessage({
          type: "editRejected",
          requestId: value.requestId,
          message: "VS Code could not apply the circuit edit.",
        } satisfies HostToWebviewMessage);
      }
    });

    panel.onDidDispose(() => {
      changeSubscription.dispose();
      messageSubscription.dispose();
    });
  }

  private webviewHtml(webview: vscode.Webview): string {
    const script = webview.asWebviewUri(
      vscode.Uri.joinPath(this.context.extensionUri, "dist", "webview", "webview.js"),
    );
    const styles = webview.asWebviewUri(
      vscode.Uri.joinPath(this.context.extensionUri, "dist", "webview", "assets", "webview.css"),
    );
    const nonce = createNonce();
    return `<!doctype html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <meta http-equiv="Content-Security-Policy" content="default-src 'none'; img-src ${webview.cspSource} data:; style-src ${webview.cspSource} 'unsafe-inline'; font-src ${webview.cspSource} data:; script-src 'nonce-${nonce}';" />
    <link rel="stylesheet" href="${styles}" />
    <title>QASM Editor</title>
  </head>
  <body>
    <div id="root"></div>
    <script type="module" nonce="${nonce}" src="${script}"></script>
  </body>
</html>`;
  }
}

function createNonce(): string {
  const bytes = new Uint8Array(18);
  crypto.getRandomValues(bytes);
  return Array.from(bytes, (byte) => byte.toString(36)).join("");
}

function activeResource(resource?: vscode.Uri): vscode.Uri | undefined {
  if (resource) return resource;
  const input = vscode.window.tabGroups.activeTabGroup.activeTab?.input;
  if (input instanceof vscode.TabInputText || input instanceof vscode.TabInputCustom)
    return input.uri;
  return vscode.window.activeTextEditor?.document.uri;
}

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  const provider = new CircuitEditorProvider(context);
  context.subscriptions.push(
    vscode.window.registerCustomEditorProvider(VIEW_TYPE, provider, {
      webviewOptions: { retainContextWhenHidden: false },
      supportsMultipleEditorsPerDocument: true,
    }),
    vscode.commands.registerCommand("tani.qasm-editor.newCircuit", async () => {
      const folder = vscode.workspace.workspaceFolders?.[0]?.uri;
      const uri = await vscode.window.showSaveDialog({
        ...(folder ? { defaultUri: vscode.Uri.joinPath(folder, "circuit.qasm") } : {}),
        filters: { "OpenQASM 3.0": ["qasm"] },
        saveLabel: "Create Circuit",
      });
      if (!uri) return;
      await vscode.workspace.fs.writeFile(
        uri,
        new TextEncoder().encode(serializeCircuit(EMPTY_CIRCUIT)),
      );
      await vscode.commands.executeCommand("vscode.openWith", uri, VIEW_TYPE);
    }),
    vscode.commands.registerCommand(
      "tani.qasm-editor.openCircuit",
      async (resource?: vscode.Uri) => {
        const uri = activeResource(resource);
        if (uri) await vscode.commands.executeCommand("vscode.openWith", uri, VIEW_TYPE);
      },
    ),
    vscode.commands.registerCommand(
      "tani.qasm-editor.openSource",
      async (resource?: vscode.Uri) => {
        const uri = activeResource(resource);
        if (uri) await vscode.commands.executeCommand("vscode.openWith", uri, "default");
      },
    ),
  );

  if (context.extensionMode === vscode.ExtensionMode.Development) {
    const active = activeResource();
    const resource = active?.path.toLowerCase().endsWith(".qasm")
      ? active
      : (await vscode.workspace.findFiles("**/*.qasm", "**/node_modules/**", 1))[0];
    if (resource) await vscode.commands.executeCommand("vscode.openWith", resource, VIEW_TYPE);
  }
}

export function deactivate(): void {}
