// mend applies unified diffs, SEARCH/REPLACE blocks, V4A patches and JSON edits.
// Node 22, standard library only: node main.ts [options] [PATCH]. See SPEC.md.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import {
  accessSync, chmodSync, constants, lstatSync, mkdirSync, readdirSync, readFileSync,
  renameSync, rmSync, rmdirSync, statSync, unlinkSync, writeFileSync, writeSync,
} from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';
const trimSpaces = (s: string): string => s.replace(/^ +| +$/g, '');

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly events: ({ kind: 'move'; from: string; to: string } | { kind: 'reset'; path: string })[] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
  blocked(p: string): boolean {
    for (let parent = dirname(p); parent !== '.'; parent = dirname(parent)) {
      if (this.get(parent) !== null) return true;
    }
    const prefix = `${p}/`;
    for (const [path, text] of this.now) {
      if (text !== null && path.startsWith(prefix)) return true;
    }
    if (!diskEntry(p)?.isDirectory()) return false;
    const pending = [p];
    while (pending.length > 0) {
      const directory = pending.pop()!;
      for (const entry of readdirSync(directory, { withFileTypes: true })) {
        const child = `${directory}/${entry.name}`;
        if (entry.isDirectory()) pending.push(child);
        else if (this.get(child) !== null) return true;
      }
    }
    return false;
  }
  set(p: string, text: string | null): void {
    const existenceChanged = (this.get(p) === null) !== (text === null);
    this.now.set(p, text);
    if (existenceChanged) this.events.push({ kind: 'reset', path: p });
  }
  move(from: string, to: string, text: string): void {
    this.now.set(from, null);
    this.now.set(to, text);
    this.events.push({ kind: 'move', from, to });
  }
  moveRows(): { sources: Set<string>; destinations: Map<string, string> } {
    type Chain = { origin: string; dest: string; alive: boolean; preOrigin: boolean };
    const chains: Chain[] = [];
    const endingAt = new Map<string, Chain>();
    const tainted = new Set<string>();
    for (const event of this.events) {
      if (event.kind === 'reset') {
        tainted.add(event.path);
        const chain = endingAt.get(event.path);
        if (chain !== undefined) chain.alive = false;
        endingAt.delete(event.path);
        continue;
      }
      const { from, to } = event;
      const chain = endingAt.get(from);
      if (chain !== undefined) {
        endingAt.delete(from);
        chain.dest = to;
        endingAt.set(to, chain);
      } else {
        const next = { origin: from, dest: to, alive: true, preOrigin: this.original(from) !== null && !tainted.has(from) };
        chains.push(next);
        endingAt.set(to, next);
      }
    }
    const sources = new Set<string>();
    const destinations = new Map<string, string>();
    for (const { origin, dest, alive, preOrigin } of chains) {
      if (!alive || !preOrigin) continue;
      if (sources.has(origin) || destinations.has(dest)) continue;
      if (this.original(origin) === null || this.get(origin) !== null) continue;
      if (this.original(dest) !== null || this.get(dest) === null) continue;
      sources.add(origin);
      destinations.set(dest, origin);
    }
    return { sources, destinations };
  }
}

type Edit = (tree: Tree) => void;

function parseError(index: number): never {
  throw new Exit2(`error: parse ${index + 1}`);
}

function requireSafe(...paths: (string | null)[]): void {
  for (const path of paths) {
    if (path !== null && !safe(path)) throw new Fail('unsafe', path);
  }
}

function requireFile(tree: Tree, path: string): string {
  const text = tree.get(path);
  if (text === null) throw new Fail('missing', path);
  return text;
}

function requireAbsent(tree: Tree, path: string): void {
  if (tree.get(path) !== null || tree.blocked(path)) throw new Fail('exists', path);
}

type LineFile = { lines: string[]; br: '\n' | '\r\n'; finalBreak: boolean };

function readLines(text: string): LineFile {
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const finalBreak = text.endsWith(br);
  const lines = text === '' ? [] : text.split(br);
  if (finalBreak) lines.pop();
  return { lines, br, finalBreak };
}

function writeLines({ lines, br, finalBreak }: LineFile): string {
  return lines.length === 0 ? '' : lines.join(br) + (finalBreak ? br : '');
}

function newFile(lines: string[], finalBreak = true): string {
  return writeLines({ lines, br: '\n', finalBreak });
}

const leadingIndent = (line: string): string => /^[ \t]*/.exec(line)![0];
const normalizers = [
  (line: string) => line,
  (line: string) => line.replace(/[ \t]+$/, ''),
  (line: string) => line.replace(/^[ \t]+|[ \t]+$/g, ''),
];

/** Match in linear time at each tier, including overlapping occurrences. */
function findTier(lines: string[], old: string[], strict: boolean, from = 0) {
  if (old.length > lines.length - from) return null;
  for (let tier = 0; tier < (strict ? 1 : normalizers.length); tier++) {
    const normalize = normalizers[tier]!;
    const pattern = old.map(normalize);
    // After a mismatch, keep the longest prefix that is also a suffix of the match so far.
    const fallback = new Uint32Array(pattern.length);
    for (let i = 1, prefix = 0; i < pattern.length; i++) {
      while (prefix > 0 && pattern[i] !== pattern[prefix]) prefix = fallback[prefix - 1]!;
      if (pattern[i] === pattern[prefix]) prefix++;
      fallback[i] = prefix;
    }
    const positions: number[] = [];
    for (let i = from, prefix = 0; i < lines.length; i++) {
      const line = normalize(lines[i]!);
      while (prefix > 0 && line !== pattern[prefix]) prefix = fallback[prefix - 1]!;
      if (line === pattern[prefix]) prefix++;
      if (prefix === pattern.length) {
        positions.push(i + 1 - prefix);
        prefix = fallback[prefix - 1]!;
      }
    }
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}

type NewLine = { text: string; context?: number };
type Replacement = { old: string[]; next: NewLine[] };

function replacement(body: string[]): Replacement {
  const old: string[] = [];
  const next: NewLine[] = [];
  for (const line of body) {
    const text = line.slice(1);
    if (line[0] === '-') old.push(text);
    else if (line[0] === '+') next.push({ text });
    else if (line[0] !== '\\') {
      next.push({ text, context: old.length });
      old.push(text);
    }
  }
  return { old, next };
}

function replaceLines(file: LineFile, { old, next }: Replacement, at: number, tier: number): void {
  const matched = file.lines;
  const from = tier === 2 ? leadingIndent(old[0]!) : '';
  const to = tier === 2 ? leadingIndent(matched[at]!) : '';
  const written = next.map(({ text, context }) => {
    if (context !== undefined) return matched[at + context]!;
    if (tier === 2 && !blank(text) && text.startsWith(from)) return to + text.slice(from.length);
    return text;
  });
  file.lines = matched.slice(0, at).concat(written, matched.slice(at + old.length));
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

type UnifiedHunk = Replacement & { start: number; noFinalBreak: boolean; additions: string[]; noCreationBreak: boolean };
type PathPair = { old: string | null; next: string | null };
type UnifiedSection = {
  git?: PathPair;
  header?: PathPair;
  renameFrom?: string;
  renameTo?: string;
  create?: boolean;
  remove?: boolean;
  hunks: UnifiedHunk[];
};

function headerPath(line: string): string | null {
  const path = trimSpaces(line.slice(4).split('\t', 1)[0]!);
  return path === '/dev/null' ? null : path.replace(/^[ab]\//, '');
}

function unifiedHunk(start: number, body: string[]): UnifiedHunk {
  const additions: string[] = [];
  let lastNew = -1;
  let lastAddition = -1;
  for (let i = 0; i < body.length; i++) {
    const line = body[i]!;
    if (line.startsWith('+')) {
      additions.push(line.slice(1));
      lastAddition = i;
    }
    if (line === '' || line.startsWith(' ') || line.startsWith('+')) lastNew = i;
  }
  const marked = (i: number) => i >= 0 && (body[i + 1] ?? '').startsWith('\\');
  return { ...replacement(body), start, additions, noFinalBreak: marked(lastNew), noCreationBreak: marked(lastAddition) };
}

function unifiedEdit(section: UnifiedSection, strict: boolean): Edit {
  const { old, next } = section.header ?? {
    old: section.renameFrom ?? section.git!.old,
    next: section.renameTo ?? section.git!.next,
  };
  const { hunks } = section;
  return (tree) => {
    requireSafe(old, next);
    if (old === null || section.create) {
      const path = next ?? '';
      requireSafe(path);
      requireAbsent(tree, path);
      const additions = hunks.flatMap((h) => h.additions);
      const last = hunks.findLast((h) => h.additions.length > 0);
      tree.set(path, newFile(additions, !last?.noCreationBreak));
      return;
    }
    const original = requireFile(tree, old);
    if (next === null || section.remove) {
      tree.set(old, null);
      return;
    }
    if (next !== old) requireAbsent(tree, next);
    const file = readLines(original);
    let delta = 0;
    const clamp = (at: number) => Math.min(file.lines.length, Math.max(0, at));
    for (const hunk of hunks) {
      let at: number;
      let tier = 0;
      if (hunk.old.length === 0) at = clamp(hunk.start + delta);
      else {
        const match = findTier(file.lines, hunk.old, strict);
        if (match === null) throw new Fail('no-match', old);
        const target = clamp(hunk.start - 1 + delta);
        at = match.positions[0]!;
        for (const candidate of match.positions) {
          if (Math.abs(candidate - target) < Math.abs(at - target)) at = candidate;
        }
        tier = match.tier;
      }
      if (at + hunk.old.length === file.lines.length) file.finalBreak = !hunk.noFinalBreak;
      replaceLines(file, hunk, at, tier);
      delta += hunk.next.length - hunk.old.length;
    }
    const text = writeLines(file);
    if (next !== old) tree.move(old, next, text);
    else tree.set(old, text);
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let section: UnifiedSection | undefined;
  const flush = () => { if (section !== undefined) edits.push(unifiedEdit(section, strict)); };
  const gitLine = (line: string) => /^diff --git(?:[ \t]|$)/.test(line);
  const pairAt = (i: number) => lines[i]?.startsWith('--- ') && lines[i + 1]?.startsWith('+++ ');
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!;
    if (gitLine(line)) {
      // Patch lines are split only at LF; other UTF-8 line separator characters can be part of a path.
      const match = /^diff --git a\/(.*?) b\/(.*)$/s.exec(line);
      if (match === null) parseError(i);
      flush();
      section = { git: { old: match[1]!, next: match[2]! }, hunks: [] };
    } else if (pairAt(i)) {
      if (!section || section.header || section.hunks.length > 0) {
        flush();
        section = { hunks: [] };
      }
      section.header = { old: headerPath(line), next: headerPath(lines[++i]!) };
    } else if (line.startsWith('@@')) {
      const match = /^@@ -(\d+)(?:,\d+)? \+\d+(?:,\d+)? @@/.exec(line);
      if (match === null || !section) parseError(i);
      let end = i + 1;
      while (end < lines.length && !pairAt(end) && (lines[end] === '' || /^[ +\\-]/.test(lines[end]!))) end++;
      const body = lines.slice(i + 1, end);
      while (body.at(-1) === '') body.pop();
      section.hunks.push(unifiedHunk(Number(match[1]), body));
      i = end - 1;
    } else if (section && section.hunks.length === 0) {
      if (line.startsWith('--- ')) parseError(i + 1);
      if (line.startsWith('rename from ')) section.renameFrom = line.slice(12);
      else if (line.startsWith('rename to ')) section.renameTo = line.slice(10);
      else if (/^new file mode(?: |$)/.test(line)) section.create = true;
      else if (/^deleted file mode(?: |$)/.test(line)) section.remove = true;
    }
  }
  flush();
  return edits;
}

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let outside = 0;
  let previousPath: string | undefined;
  const markers = lines.map((line) => line.trimEnd());
  for (let i = 0; i < lines.length; i++) {
    if (markers[i] !== '<<<<<<< SEARCH') continue;
    let path = previousPath;
    for (let j = i - 1; j >= outside; j--) {
      const candidate = lines[j]!.trim();
      if (candidate === '' || candidate.startsWith('```')) continue;
      path = candidate;
      break;
    }
    const middle = markers.indexOf('=======', i + 1);
    const end = middle < 0 ? -1 : markers.indexOf('>>>>>>> REPLACE', middle + 1);
    if (path === undefined || end < 0) parseError(i);
    const p = path;
    const old = lines.slice(i + 1, middle);
    const added = lines.slice(middle + 1, end);
    const change = { old, next: added.map((text) => ({ text })) };
    edits.push((tree) => {
      requireSafe(p);
      if (old.length === 0) {
        requireAbsent(tree, p);
        tree.set(p, newFile(added));
        return;
      }
      const file = readLines(requireFile(tree, p));
      const match = findTier(file.lines, old, strict);
      if (match === null) throw new Fail('no-match', p);
      if (match.positions.length > 1) throw new Fail('ambiguous', p);
      replaceLines(file, change, match.positions[0]!, match.tier);
      tree.set(p, writeLines(file));
    });
    previousPath = path;
    outside = end + 1;
    i = end;
  }
  return edits;
}

type V4AChunk = Replacement & { anchor: string; eof: boolean };

function v4aUpdate(lines: string[], start: number, end: number, path: string, strict: boolean): Edit {
  let i = start + 1;
  let destination: string | null = null;
  if (i < end && lines[i]!.startsWith('*** Move to: ')) destination = lines[i++]!.slice(13).trim();
  const chunks: V4AChunk[] = [];
  const isBody = (line: string) => line === '' || /^[ +\-]/.test(line);
  while (i < end) {
    let anchor = '';
    if (lines[i]!.startsWith('@@')) anchor = trimSpaces(lines[i++]!.slice(2));
    else if (chunks.length > 0 || !isBody(lines[i]!)) parseError(i);
    const bodyStart = i;
    while (i < end && isBody(lines[i]!)) i++;
    const body = lines.slice(bodyStart, i);
    const eof = i < end && lines[i] === '*** End of File';
    if (eof) i++;
    chunks.push({ ...replacement(body), anchor, eof });
  }
  if (chunks.length === 0 && destination === null) parseError(start);
  return (tree) => {
    requireSafe(path, destination);
    const file = readLines(requireFile(tree, path));
    if (destination !== null) requireAbsent(tree, destination);
    let cursor = 0;
    for (const chunk of chunks) {
      if (chunk.anchor !== '') {
        const anchor = findTier(file.lines, [chunk.anchor], strict, cursor);
        if (anchor === null) throw new Fail('no-match', path);
        cursor = anchor.positions[0]! + 1;
      }
      let at = chunk.eof ? file.lines.length : cursor;
      let tier = 0;
      if (chunk.old.length > 0) {
        const from = chunk.eof ? Math.max(cursor, file.lines.length - chunk.old.length) : cursor;
        const match = findTier(file.lines, chunk.old, strict, from);
        if (match === null) throw new Fail('no-match', path);
        at = match.positions[0]!;
        tier = match.tier;
      }
      replaceLines(file, chunk, at, tier);
      cursor = at + chunk.next.length;
    }
    const text = writeLines(file);
    if (destination !== null) tree.move(path, destination, text);
    else tree.set(path, text);
  };
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const begin = lines.findIndex((line) => !blank(line));
  if (begin < 0) parseError(0);
  if (lines[begin]!.trim() !== '*** Begin Patch') parseError(begin);
  const end = lines.findLastIndex((line) => !blank(line));
  if (lines[end]!.trim() !== '*** End Patch') parseError(lines.length);

  const edits: Edit[] = [];
  const header = /^\*\*\* (Add|Delete|Update) File: (.*)$/s;
  for (let i = begin + 1; i < end;) {
    if (blank(lines[i]!)) { i++; continue; }
    const match = header.exec(lines[i]!);
    if (match === null) parseError(i);
    const path = trimSpaces(match[2]!);
    let next = i + 1;
    while (next < end && !header.test(lines[next]!)) next++;
    let bodyEnd = next;
    while (bodyEnd > i + 1 && blank(lines[bodyEnd - 1]!)) bodyEnd--;
    if (match[1] === 'Add') {
      const added: string[] = [];
      for (let j = i + 1; j < bodyEnd; j++) {
        const line = lines[j]!;
        if (line !== '' && !line.startsWith('+')) parseError(j);
        added.push(line.slice(1));
      }
      edits.push((tree) => {
        requireSafe(path);
        requireAbsent(tree, path);
        tree.set(path, newFile(added));
      });
    } else if (match[1] === 'Delete') {
      if (i + 1 < bodyEnd) parseError(i + 1);
      edits.push((tree) => {
        requireSafe(path);
        requireFile(tree, path);
        tree.set(path, null);
      });
    } else edits.push(v4aUpdate(lines, i, bodyEnd, path, strict));
    i = next;
  }
  return edits;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      requireAbsent(tree, p);
      tree.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const file = readLines(before);
      const { lines } = file;
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      file.lines = lines.slice(0, line).concat(add, lines.slice(line));
      tree.set(p, writeLines(file));
    };
  }
  return null;
}

const nonIntegerToken = Symbol('non-integer JSON number');

function parseJsonEdits(text: string): unknown {
  return JSON.parse(text, (key: string, value: unknown, context?: { source: string }) => {
    // Node 22 exposes the token even when its numeric value has already rounded.
    if (key === 'insert_line' && typeof value === 'number') {
      if (!Number.isFinite(value)) return nonIntegerToken;
      const [, whole, fraction = '', exponent = '0'] = /^-?(\d+)(?:\.(\d+))?(?:[eE]([+-]?\d+))?$/.exec(context!.source)!;
      const digits = (whole + fraction).replace(/^0+/, '');
      if (digits !== '') {
        const shift = parseInt(exponent, 10) - fraction.length;
        if (shift < 0) {
          let end = digits.length;
          while (digits[end - 1] === '0') end--;
          if (digits.length - end < -shift) return nonIntegerToken;
        }
      }
    }
    return value;
  });
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = parseJsonEdits(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(parseJsonEdits(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

type Write = { path: string; text: string; mode?: number };
type CommitPlan = {
  backups: { path: string; directory: boolean }[];
  directories: string[];
  writes: Write[];
};

function diskEntry(path: string) {
  try {
    return lstatSync(path, { throwIfNoEntry: false });
  } catch (e) {
    if ((e as NodeJS.ErrnoException).code === 'ENOTDIR') return undefined;
    throw e;
  }
}

/** Plan from the final tree, so both --check and real runs detect path conflicts. */
function planCommit(changes: Map<string, string | null>): CommitPlan {
  const backups: CommitPlan['backups'] = [];
  const make = new Set<string>();
  const checked = new Set<string>();
  const writes: Write[] = [];
  const removable = (path: string) => changes.get(path) === null;

  function clearDirectory(path: string): void {
    for (const name of readdirSync(path).sort()) {
      const child = `${path}/${name}`;
      if (removable(child)) continue; // Already scheduled for backup.
      if (!diskEntry(child)?.isDirectory()) throw new Error('directory contains a retained file');
      clearDirectory(child);
    }
    backups.push({ path, directory: true });
  }

  function ensureDirectory(path: string): void {
    if (path === '.' || checked.has(path)) return;
    if (typeof changes.get(path) === 'string') throw new Error('file conflicts with a parent directory');
    ensureDirectory(dirname(path));
    const entry = diskEntry(path);
    if (removable(path) || !entry) make.add(path);
    else if (!entry.isDirectory() && !(entry.isSymbolicLink() && statSync(path).isDirectory())) {
      throw new Error('parent path is not a directory');
    }
    checked.add(path);
  }

  for (const [path, text] of changes) {
    if (text === null) backups.push({ path, directory: false });
  }
  for (const [path, text] of changes) {
    if (text === null) continue;
    ensureDirectory(dirname(path));
    const entry = diskEntry(path);
    if (entry?.isDirectory()) clearDirectory(path);
    else if (entry) {
      if (entry.isFile()) accessSync(path, constants.W_OK);
      backups.push({ path, directory: false });
    }
    writes.push({ path, text, mode: entry?.isFile() ? entry.mode & 0o7777 : undefined });
  }

  const parents = new Set(['.']);
  for (const { path } of backups) parents.add(dirname(path));
  for (const path of make) parents.add(dirname(path));
  for (const { path } of writes) parents.add(dirname(path));
  for (const path of parents) {
    if (!make.has(path)) accessSync(path, constants.W_OK | constants.X_OK);
  }
  return { backups, directories: [...make], writes };
}

/** Keep the originals as directory entries so rollback restores bytes and metadata. */
function applyCommit({ backups, directories, writes }: CommitPlan): void {
  if (backups.length === 0 && writes.length === 0) return;
  const reserved = new Set(writes.map(({ path }) => path.split('/', 1)[0]));
  let scratch: string;
  for (let i = 0; ; i++) {
    scratch = `.mend-stage-${i}`;
    if (reserved.has(scratch)) continue;
    try {
      mkdirSync(scratch, { mode: 0o700 });
      break;
    } catch (e) {
      if ((e as NodeJS.ErrnoException).code !== 'EEXIST') throw e;
    }
  }

  const undo: (() => void)[] = [];
  try {
    for (const [i, { text, mode }] of writes.entries()) {
      const staged = `${scratch}/new-${i}`;
      writeFileSync(staged, text, { flag: 'wx' });
      if (mode !== undefined) chmodSync(staged, mode);
    }
    for (const [i, { path, directory }] of backups.entries()) {
      // Never take a directory that still contains entries (e.g. a concurrent addition).
      if (directory && readdirSync(path).length !== 0) throw new Error('directory is no longer empty');
      const saved = `${scratch}/old-${i}`;
      renameSync(path, saved);
      undo.push(() => renameSync(saved, path));
    }
    for (const path of directories) {
      mkdirSync(path);
      undo.push(() => rmdirSync(path));
    }
    for (const [i, { path }] of writes.entries()) {
      renameSync(`${scratch}/new-${i}`, path);
      undo.push(() => unlinkSync(path));
    }
  } catch (e) {
    const errors = [];
    for (const rollback of undo.reverse()) {
      try { rollback(); } catch (err) { errors.push(err); }
    }
    if (errors.length > 0) throw new AggregateError([e, ...errors], `rollback incomplete; backups at ${scratch}`);
    rmSync(scratch, { recursive: true, force: true });
    throw e;
  }
  rmSync(scratch, { recursive: true, force: true });
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, strict);
    else edits = v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const eventCount = tree.events.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.events.length = eventCount;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: string[] = [];
  const moves = tree.moveRows();
  const changes = new Map<string, string | null>();
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    changes.set(p, now);
    const from = moves.destinations.get(p);
    if (from !== undefined) rows.push(`R ${from} -> ${p}`);
    else if (!moves.sources.has(p)) rows.push(`${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`);
  }
  if (changes.size > 0) {
    try {
      const plan = planCommit(changes);
      if (!check) applyCommit(plan);
    } catch (e) {
      if (e instanceof AggregateError) throw e;
      return { code: 1, out: ['error: internal'] };
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
