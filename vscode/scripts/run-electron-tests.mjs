import { fileURLToPath } from "node:url";
import { runTests } from "@vscode/test-electron";

const root = fileURLToPath(new URL("..", import.meta.url));
const workspace = fileURLToPath(new URL("../tests/fixtures/workspace", import.meta.url));
const extensionTestsPath = fileURLToPath(new URL("../dist/test/suite/index.cjs", import.meta.url));

try {
  await runTests({
    extensionDevelopmentPath: root,
    extensionTestsPath,
    launchArgs: [workspace, "--disable-extensions"],
  });
} catch (error) {
  console.error("VS Code desktop integration tests failed.", error);
  process.exitCode = 1;
}
