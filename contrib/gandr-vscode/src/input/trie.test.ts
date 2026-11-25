import assert from "node:assert/strict";
import { test } from "node:test";

import { entries } from "./table";
import { build, commandAt, continuations, walk } from "./trie";

const commands = entries();
const root = build(commands);

void test("every command in the table reaches the glyphs it offers", () => {
  for (const [command, glyphs] of commands) {
    assert.deepEqual(walk(root, command)?.glyphs, glyphs, command);
  }
});

void test("\\to offers → first", () => {
  assert.equal(walk(root, "\\to")?.glyphs[0], "→");
});

void test("\\r forks, and its continuations reach \\rightarrowtail one fork at a time", () => {
  const r = walk(root, "\\r");
  assert.ok(r !== undefined);
  assert.equal(r.glyphs[0], "→", "\\r offers its own arrows");
  let command = "\\r";
  let node = r;
  const steps: string[] = [];
  while (command !== "\\rightarrowtail") {
    const next = continuations(node, command).find((c) => "\\rightarrowtail".startsWith(c.command));
    assert.ok(next !== undefined, `a continuation of ${command} leads on`);
    assert.ok(next.command.length > command.length);
    command = next.command;
    steps.push(command);
    const reached = walk(root, command);
    assert.ok(reached !== undefined);
    node = reached;
  }
  assert.ok(steps.length > 1, `\\r reaches \\rightarrowtail through forks: ${steps.join(" ")}`);
  assert.deepEqual(node.glyphs, ["↣"]);
});

void test("a continuation counts and samples the glyphs it leads to", () => {
  const r = walk(root, "\\r");
  assert.ok(r !== undefined);
  for (const continuation of continuations(r, "\\r")) {
    const reached = walk(root, continuation.command);
    assert.ok(reached !== undefined, continuation.command);
    assert.equal(continuation.reachable, reached.reachable);
    assert.ok(continuation.sample.length > 0 && continuation.sample.length <= 6);
  }
});

void test("the command at a line's end is read from its first backslash that begins one", () => {
  assert.deepEqual(pick("def f = \\to"), { start: 8, command: "\\to" });
  assert.deepEqual(
    pick("x\\_\\be"),
    { start: 1, command: "\\_\\be" },
    "a command holding a backslash is read whole",
  );
  assert.deepEqual(
    pick("\\to \\l"),
    { start: 4, command: "\\l" },
    "only the last run without whitespace",
  );
  assert.equal(pick("\\to "), undefined, "a space ends the command");
  assert.equal(pick("\\zzzz"), undefined, "no command begins so");
  assert.equal(pick("plain"), undefined);
});

function pick(line: string): { start: number; command: string } | undefined {
  const found = commandAt(root, line);
  return found === undefined ? undefined : { start: found.start, command: found.command };
}
