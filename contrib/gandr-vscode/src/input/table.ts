// The commands of the generated table, `table.json`, each with its glyphs.
// `scripts/input-table.mts` writes the table from its pinned sources; the
// table names them and their licences.

import type { Entry } from "./trie";

import table from "./table.json";

export function entries(): Entry[] {
  return table.commands.map((entry: unknown): Entry => {
    if (!Array.isArray(entry) || entry.length !== 2) {
      throw new Error("an input table entry is not a pair");
    }
    const [command, glyphs]: unknown[] = entry;
    if (
      typeof command !== "string" ||
      !Array.isArray(glyphs) ||
      !glyphs.every((g) => typeof g === "string")
    ) {
      throw new Error("an input table entry is not a command and its glyphs");
    }
    return [command, glyphs as string[]];
  });
}
