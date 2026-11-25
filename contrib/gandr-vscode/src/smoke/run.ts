// The end-to-end smoke's runner: VS Code at the extension's declared floor,
// downloaded once into the user's cache, starts without a display on a
// scratch workspace holding one corpus source, with the extension under
// development and nothing else, and plays `scene.ts` in its extension host.
// The `gandr` on `PATH` serves it; `mise run check:vscode-smoke` puts the
// workspace's build first. VS Code keeps the runner's environment rather
// than resolving the login shell's, which on macOS replaces `PATH` and so
// the `gandr` that serves. VS Code's own log is printed only when the scene
// fails.

import { runTests } from "@vscode/test-electron";
import { copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync } from "node:fs";
import { homedir, tmpdir } from "node:os";
import { basename, join, resolve } from "node:path";
import { PassThrough } from "node:stream";

// `dist/src/smoke` lies three directories under the extension's root.
const extension = resolve(__dirname, "../../..");
const source = resolve(extension, "../../corpus/model/basics/definitions.gandr");

// The oldest VS Code the manifest admits, so the smoke holds the floor the
// extension declares rather than whichever release is newest.
function floor(): string {
  const manifest: unknown = JSON.parse(readFileSync(join(extension, "package.json"), "utf8"));
  const range =
    typeof manifest === "object" && manifest !== null && "engines" in manifest
      ? (manifest.engines as { vscode?: unknown }).vscode
      : undefined;
  if (typeof range !== "string" || !/^\^\d+\.\d+\.\d+$/u.test(range)) {
    throw new Error(`the manifest's engines.vscode is not a caret range: ${String(range)}`);
  }
  return range.slice(1);
}

async function main(): Promise<void> {
  const version = floor();
  const scratch = mkdtempSync(join(tmpdir(), "gandr-vscode-smoke-"));
  const log = new PassThrough();
  const lines: Buffer[] = [];
  log.on("data", (chunk: Buffer) => lines.push(chunk));
  try {
    const workspace = join(scratch, "workspace");
    mkdirSync(workspace);
    const opened = join(workspace, basename(source));
    copyFileSync(source, opened);
    await runTests({
      version,
      cachePath: join(
        process.env["XDG_CACHE_HOME"] ?? join(homedir(), ".cache"),
        "gandr",
        "vscode",
      ),
      extensionDevelopmentPath: extension,
      extensionTestsPath: join(__dirname, "scene.js"),
      extensionTestsEnv: { GANDR_SMOKE_SOURCE: opened },
      launchArgs: [
        workspace,
        "--ozone-platform=headless",
        "--disable-extensions",
        "--disable-workspace-trust",
        "--force-disable-user-env",
        `--user-data-dir=${join(scratch, "user")}`,
        `--extensions-dir=${join(scratch, "extensions")}`,
      ],
      stdout: log,
      stderr: log,
    });
  } catch (error: unknown) {
    process.stderr.write(Buffer.concat(lines));
    throw error;
  } finally {
    rmSync(scratch, { recursive: true, force: true });
  }
  process.stdout.write(
    `vscode smoke OK: VS Code ${version} activated the extension, typed into ${basename(source)} and was answered one HTML hover\n`,
  );
}

// A failure rejects, and Node ends with the error and a nonzero status.
void main();
