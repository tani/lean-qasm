import * as vscode from "vscode";

function assert(condition: unknown, message: string): asserts condition {
  if (!condition) throw new Error(message);
}

export async function run(): Promise<void> {
  const extension = vscode.extensions.getExtension("tani.qasm-editor");
  assert(extension, "QASM Editor extension was not discovered.");
  await extension.activate();
  assert(extension.isActive, "QASM Editor extension did not activate.");

  const commands = await vscode.commands.getCommands(true);
  for (const command of [
    "tani.qasm-editor.newCircuit",
    "tani.qasm-editor.openCircuit",
    "tani.qasm-editor.openSource",
  ]) {
    assert(commands.includes(command), `Missing command ${command}.`);
  }

  const fixture = vscode.Uri.joinPath(
    vscode.workspace.workspaceFolders?.[0]?.uri ?? vscode.Uri.file("."),
    "bell.qasm",
  );
  await vscode.commands.executeCommand("vscode.openWith", fixture, "tani.qasm-editor.circuit");
  await new Promise((resolve) => setTimeout(resolve, 250));
  const input = vscode.window.tabGroups.activeTabGroup.activeTab?.input;
  assert(
    input instanceof vscode.TabInputCustom,
    "Circuit fixture did not open as a custom editor.",
  );
  assert(input.viewType === "tani.qasm-editor.circuit", "Unexpected custom editor view type.");
  await vscode.commands.executeCommand("workbench.action.closeActiveEditor");
}
