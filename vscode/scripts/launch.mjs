import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("..", import.meta.url));
const workspace = fileURLToPath(new URL("../tests/fixtures/workspace", import.meta.url));
const circuit = fileURLToPath(new URL("../tests/fixtures/workspace/bell.qasm", import.meta.url));
const executable = process.env.VSCODE_CLI_PATH || "code";
const args = ["--new-window", `--extensionDevelopmentPath=${root}`, workspace, circuit];

if (process.argv.includes("--dry-run")) {
  console.log([executable, ...args].join(" "));
} else {
  execFileSync(executable, args, { stdio: "inherit" });
}
