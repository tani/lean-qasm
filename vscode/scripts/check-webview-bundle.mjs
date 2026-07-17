import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";

const bundle = fileURLToPath(new URL("../dist/webview/webview.js", import.meta.url));
const source = await readFile(bundle, "utf8");

if (/\bprocess\.env\b/.test(source)) {
  throw new Error("The webview bundle contains process.env and will crash in VS Code.");
}

if (!source.includes("acquireVsCodeApi")) {
  throw new Error("The webview bundle does not contain the VS Code bridge.");
}

console.log("Verified the production webview bundle is browser-safe.");
