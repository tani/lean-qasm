import { fileURLToPath, URL } from "node:url";
import react from "@vitejs/plugin-react";
import { defineConfig } from "vite";

export default defineConfig(({ mode }) => {
  const extension = mode === "extension";
  const extensionTest = mode === "extension-test";
  const entry = fileURLToPath(
    new URL(
      extension
        ? "./src/extension.ts"
        : extensionTest
          ? "./src/test/suite/index.ts"
          : "./src/webview/main.tsx",
      import.meta.url,
    ),
  );

  return {
    plugins: extension || extensionTest ? [] : [react()],
    define:
      extension || extensionTest
        ? {}
        : {
            "process.env.NODE_ENV": JSON.stringify("production"),
          },
    build: {
      target: "es2022",
      outDir: extension ? "dist/extension" : extensionTest ? "dist/test/suite" : "dist/webview",
      emptyOutDir: true,
      sourcemap: true,
      minify: true,
      lib: {
        entry,
        formats: extension || extensionTest ? ["cjs"] : ["es"],
        fileName: () => (extension ? "extension.cjs" : extensionTest ? "index.cjs" : "webview.js"),
        cssFileName: "webview",
      },
      rollupOptions: {
        external: extension || extensionTest ? ["vscode"] : [],
        output: {
          assetFileNames: "assets/[name][extname]",
        },
      },
    },
  };
});
