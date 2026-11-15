// The input method's commands as a trie of code points: a command is a walk
// from the root, the node it reaches holds the glyphs the command offers, and
// a node's children continue it. Built once from the table; a lookup walks the
// command's length.

export interface Node {
  // The glyphs the command ending here offers, in the table's order.
  readonly glyphs: readonly string[];
  // The commands continuing this one, by their next code point.
  readonly next: ReadonlyMap<string, Node>;
  // How many glyphs this command and every command continuing it offer.
  readonly reachable: number;
}

interface Building {
  readonly glyphs: string[];
  readonly next: Map<string, Building>;
  reachable: number;
}

// A command the table offers, with its glyphs.
export type Entry = readonly [command: string, glyphs: readonly string[]];

export function build(entries: Iterable<Entry>): Node {
  const root: Building = { glyphs: [], next: new Map(), reachable: 0 };
  for (const [command, glyphs] of entries) {
    let node = root;
    for (const point of command) {
      let child = node.next.get(point);
      if (child === undefined) {
        child = { glyphs: [], next: new Map(), reachable: 0 };
        node.next.set(point, child);
      }
      node = child;
    }
    node.glyphs.push(...glyphs);
  }
  const tally = (node: Building): number => {
    node.reachable = node.glyphs.length;
    for (const child of node.next.values()) node.reachable += tally(child);
    return node.reachable;
  };
  tally(root);
  return root;
}

// The node `command` reaches, or none when no command begins with it.
export function walk(root: Node, command: string): Node | undefined {
  let node: Node | undefined = root;
  for (const point of command) {
    node = node.next.get(point);
    if (node === undefined) return undefined;
  }
  return node;
}

// The command being written at the end of `line`: from the first `\` of the
// line's last run without whitespace whose rest every command could begin
// with, so a command holding a `\` (`\_\beta`) is read whole.
export function commandAt(
  root: Node,
  line: string,
): { start: number; command: string; node: Node } | undefined {
  let run = line.length;
  while (run > 0 && !/\s/.test(line[run - 1] ?? "")) run--;
  for (let start = line.indexOf("\\", run); start >= 0; start = line.indexOf("\\", start + 1)) {
    const command = line.slice(start);
    const node = walk(root, command);
    if (node !== undefined) return { start, command, node };
  }
  return undefined;
}

// A command that continues the one written, to the next point where the trie
// forks or offers a glyph.
export interface Continuation {
  readonly command: string;
  // How many glyphs the commands it begins offer.
  readonly reachable: number;
  // The first of those glyphs, at most `SAMPLE`.
  readonly sample: readonly string[];
}

export const SAMPLE = 6;

// The continuations of `command`, which reaches `node`, in code-unit order.
export function continuations(node: Node, command: string): Continuation[] {
  const found: Continuation[] = [];
  for (const point of [...node.next.keys()].sort()) {
    let path = point;
    let reached = node.next.get(point);
    while (reached !== undefined && reached.glyphs.length === 0 && reached.next.size === 1) {
      const [only] = reached.next;
      if (only === undefined) break;
      path += only[0];
      reached = only[1];
    }
    if (reached === undefined) continue;
    found.push({ command: command + path, reachable: reached.reachable, sample: sample(reached) });
  }
  return found;
}

function sample(node: Node): string[] {
  const found: string[] = [];
  const visit = (at: Node): void => {
    for (const glyph of at.glyphs) {
      if (found.length === SAMPLE) return;
      found.push(glyph);
    }
    for (const point of [...at.next.keys()].sort()) {
      if (found.length === SAMPLE) return;
      const child = at.next.get(point);
      if (child !== undefined) visit(child);
    }
  };
  visit(node);
  return found;
}
