// main.ts — himeko-forge: a GitHub-compatible git forge in one file.
//
// Serves git smart HTTP (upload-pack v2, receive-pack v0), REST v3, GraphQL v4
// and MCP (2026-07-28) from a single in-memory store. Node 22 stdlib only
// (node:http, node:crypto, node:zlib). No dependencies, no git binary.
//
// Viewer login (the token owner) is `adaiversen` — fixed by the kit's
// SCENARIO_SEED 0x6a09e667f3bcc909n (wire.ts buildScenario(): users[0]).
// Any other owner (e.g. stranger `olgabauer`, org `faint-meadow-org`) is
// foreign: the same repo name under them is 404, never 403.

import { createHash, randomUUID, timingSafeEqual } from 'node:crypto';
import { createServer } from 'node:http';
import type { IncomingMessage, ServerResponse } from 'node:http';
import { deflateSync, inflateSync } from 'node:zlib';

const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const ENV_URL = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');
if (ENV_URL === '' || TOKEN === '') {
  process.stderr.write('[entry] MAKEFUN_ENV_URL and MAKEFUN_SHOP_TOKEN are both required\n');
  process.exit(1);
}

// The login the trial token names (kit SCENARIO_SEED 0x6a09e667f3bcc909n).
const VIEWER_LOGIN = 'adaiversen';
const AGENT = 'himeko-forge/1.0';
const ZERO_OID = '0'.repeat(40);
const EMPTY_TREE_OID = '4b825dc642cb6eb9a060e54bf8d69288fbee4904';
const SERVER_IDENTITY = 'Himeko Forge <forge@example.invalid>';
const MAX_BODY_BYTES = 16 * 1024 * 1024;

// ---------------------------------------------------------------- pkt-line

const PKT_LINE_MAX = 65520;

function pktLine(payload: Buffer | string): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  if (data.length > PKT_LINE_MAX - 4) throw new Error('pkt-line payload too long');
  const head = Buffer.alloc(4);
  head.write((data.length + 4).toString(16).padStart(4, '0'), 0, 4, 'ascii');
  return Buffer.concat([head, data]);
}
function pktFlush(): Buffer { return Buffer.from('0000', 'ascii'); }
function pktDelim(): Buffer { return Buffer.from('0001', 'ascii'); }

interface Pkt { kind: 'data' | 'flush' | 'delim' | 'end'; data?: Buffer; }

/** Parse a complete buffer of pkt-lines. Throws on malformed framing. */
function parsePktLines(buf: Buffer): Pkt[] {
  const out: Pkt[] = [];
  let off = 0;
  while (off < buf.length) {
    if (off + 4 > buf.length) throw new Error('pkt-line: truncated length header');
    const hex = buf.subarray(off, off + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) throw new Error(`pkt-line: bad length ${JSON.stringify(hex)}`);
    const len = parseInt(hex, 16);
    if (len === 0) { out.push({ kind: 'flush' }); off += 4; continue; }
    if (len === 1) { out.push({ kind: 'delim' }); off += 4; continue; }
    if (len === 2) { out.push({ kind: 'end' }); off += 4; continue; }
    if (len < 4 || len > PKT_LINE_MAX || off + len > buf.length) throw new Error(`pkt-line: bad length ${len} at offset ${off}`);
    out.push({ kind: 'data', data: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return out;
}

/** Parse pkt-lines from the start of `buf` until the first flush; returns packets + bytes consumed. */
function parsePktLinesUntilFlush(buf: Buffer): { packets: Pkt[]; consumed: number } {
  const packets: Pkt[] = [];
  let off = 0;
  while (off < buf.length) {
    if (off + 4 > buf.length) throw new Error('pkt-line: truncated length header');
    const hex = buf.subarray(off, off + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) throw new Error(`pkt-line: bad length ${JSON.stringify(hex)}`);
    const len = parseInt(hex, 16);
    if (len === 0) { packets.push({ kind: 'flush' }); off += 4; break; }
    if (len === 1) { packets.push({ kind: 'delim' }); off += 4; continue; }
    if (len === 2) { packets.push({ kind: 'end' }); off += 4; continue; }
    if (len < 4 || len > PKT_LINE_MAX || off + len > buf.length) throw new Error(`pkt-line: bad length ${len} at offset ${off}`);
    packets.push({ kind: 'data', data: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return { packets, consumed: off };
}

function dataLines(packets: readonly Pkt[]): string[] {
  const out: string[] = [];
  for (const p of packets) if (p.kind === 'data' && p.data) out.push(p.data.toString('utf8'));
  return out;
}

/** One sideband frame: pkt-line whose payload is band byte + data. */
function sidebandFrame(band: number, data: Buffer): Buffer {
  return pktLine(Buffer.concat([Buffer.from([band]), data]));
}

/** Split `data` into sideband band-1 frames (max payload per pkt-line). */
function sidebandFrames(data: Buffer): Buffer[] {
  const frames: Buffer[] = [];
  const MAX = PKT_LINE_MAX - 5; // 4 header + 1 band byte
  for (let off = 0; off < data.length || (data.length === 0 && off === 0); off += MAX) {
    frames.push(sidebandFrame(1, data.subarray(off, off + MAX)));
    if (data.length === 0) break;
  }
  return frames;
}

// ---------------------------------------------------------------- git objects

type ObjType = 'blob' | 'tree' | 'commit' | 'tag';

function hashObject(type: ObjType, data: Buffer): string {
  const h = createHash('sha1');
  h.update(Buffer.from(`${type} ${data.length}\0`, 'ascii'));
  h.update(data);
  return h.digest('hex');
}

interface TreeEntry { mode: string; name: string; oid: string; }

function compareTreeNames(a: TreeEntry, b: TreeEntry): number {
  const ka = Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8');
  const kb = Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8');
  return Buffer.compare(ka, kb);
}

function buildTree(entries: readonly TreeEntry[]): Buffer {
  const sorted = [...entries].sort(compareTreeNames);
  const parts: Buffer[] = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    const nul = data.indexOf(0x00, sp);
    if (sp === -1 || nul === -1 || nul + 21 > data.length) throw new Error('tree: malformed entry');
    entries.push({
      mode: data.subarray(off, sp).toString('ascii'),
      name: data.subarray(sp + 1, nul).toString('utf8'),
      oid: data.subarray(nul + 1, nul + 21).toString('hex'),
    });
    off = nul + 21;
  }
  return entries;
}

interface CommitView { tree: string; parents: string[]; author: string; committer: string; message: string; }

function parseCommit(data: Buffer): CommitView {
  const text = data.toString('utf8');
  const blank = text.indexOf('\n\n');
  const head = blank < 0 ? text : text.slice(0, blank);
  const message = blank < 0 ? '' : text.slice(blank + 2);
  const out: CommitView = { tree: '', parents: [], author: '', committer: '', message };
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) out.tree = line.slice(5);
    else if (line.startsWith('parent ')) out.parents.push(line.slice(7));
    else if (line.startsWith('author ')) out.author = line.slice(7);
    else if (line.startsWith('committer ')) out.committer = line.slice(10);
  }
  return out;
}

function buildCommit(tree: string, parents: readonly string[], message: string, author: string, committer: string, timestamp: number): Buffer {
  const lines = [`tree ${tree}`];
  for (const p of parents) lines.push(`parent ${p}`);
  lines.push(`author ${author} ${timestamp} +0000`);
  lines.push(`committer ${committer} ${timestamp} +0000`);
  return Buffer.from(`${lines.join('\n')}\n\n${message}`, 'utf8');
}

interface TagView { object: string; type: string; tag: string; tagger: string; message: string; }

function parseTag(data: Buffer): TagView {
  const text = data.toString('utf8');
  const blank = text.indexOf('\n\n');
  const head = blank < 0 ? text : text.slice(0, blank);
  const message = blank < 0 ? '' : text.slice(blank + 2);
  const out: TagView = { object: '', type: '', tag: '', tagger: '', message };
  for (const line of head.split('\n')) {
    if (line.startsWith('object ')) out.object = line.slice(7);
    else if (line.startsWith('type ')) out.type = line.slice(5);
    else if (line.startsWith('tag ')) out.tag = line.slice(4);
    else if (line.startsWith('tagger ')) out.tagger = line.slice(7);
  }
  return out;
}

// ---------------------------------------------------------------- packfile

const PACK_TYPE_CODE: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const PACK_CODE_TYPE: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function encodePackEntryHeader(typeCode: number, size: number): Buffer {
  const bytes: number[] = [];
  let b = (typeCode << 4) | (size & 0x0f);
  size >>>= 4;
  while (size > 0) {
    bytes.push(b | 0x80);
    b = size & 0x7f;
    size >>>= 7;
  }
  bytes.push(b);
  return Buffer.from(bytes);
}

interface PackObject { type: ObjType; data: Buffer; }

/** Write a packfile (version 2, plain objects only) from objects. */
function writePack(objects: readonly PackObject[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const obj of objects) {
    parts.push(encodePackEntryHeader(PACK_TYPE_CODE[obj.type], obj.data.length));
    parts.push(deflateSync(obj.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

/** Apply a git delta instruction stream to a base object's bytes. */
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  const readVarint = (): number => {
    let value = 0, shift = 0;
    for (;;) {
      if (off >= delta.length) throw new Error('delta: truncated varint');
      const b = delta[off++];
      value |= (b & 0x7f) << shift;
      shift += 7;
      if ((b & 0x80) === 0) break;
    }
    return value;
  };
  const sourceSize = readVarint();
  const targetSize = readVarint();
  if (sourceSize !== base.length) throw new Error(`delta: base size ${base.length}, expected ${sourceSize}`);
  const out = Buffer.alloc(targetSize);
  let written = 0;
  while (off < delta.length) {
    const op = delta[off++];
    if (op & 0x80) {
      let copyOff = 0, copySize = 0;
      for (let i = 0; i < 4; i++) if (op & (1 << i)) copyOff |= delta[off++] << (8 * i);
      for (let i = 0; i < 3; i++) if (op & (0x10 << i)) copySize |= delta[off++] << (8 * i);
      if (copySize === 0) copySize = 0x10000;
      base.copy(out, written, copyOff, copyOff + copySize);
      written += copySize;
    } else if (op !== 0) {
      delta.copy(out, written, off, off + op);
      off += op;
      written += op;
    } else {
      throw new Error('delta: opcode 0 is reserved');
    }
  }
  if (written !== targetSize) throw new Error(`delta: wrote ${written} bytes, expected ${targetSize}`);
  return out;
}

interface ParsedPackEntry { type: ObjType; oid: string; data: Buffer; }

/**
 * Parse a packfile. Verifies magic, version, count and trailer; inflates entries
 * (inflateSync with info reports consumed input bytes, so one inflate per entry
 * finds the exact stream end); resolves ofs-delta and ref-delta.
 */
function parsePack(buf: Buffer): ParsedPackEntry[] {
  if (buf.length < 32) throw new Error('pack: too short');
  if (buf.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('pack: bad magic');
  const version = buf.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`pack: unsupported version ${version}`);
  const count = buf.readUInt32BE(8);
  const trailerStart = buf.length - 20;
  const expect = createHash('sha1').update(buf.subarray(0, trailerStart)).digest();
  if (!buf.subarray(trailerStart).equals(expect)) throw new Error('pack: trailer checksum mismatch');
  interface Raw { offset: number; typeCode: number; size: number; data: Buffer; baseOffset?: number; baseOid?: string; resolved?: ParsedPackEntry; }
  const raw: Raw[] = [];
  const byOffset = new Map<number, Raw>();
  let off = 12;
  for (let i = 0; i < count; i++) {
    const entryStart = off;
    let b = buf[off++];
    const typeCode = (b >> 4) & 0x07;
    let size = b & 0x0f;
    let shift = 4;
    while (b & 0x80) {
      if (off >= trailerStart) throw new Error('pack: truncated size varint');
      b = buf[off++];
      size |= (b & 0x7f) << shift;
      shift += 7;
    }
    const entry: Raw = { offset: entryStart, typeCode, size, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      let byte = buf[off++];
      let offset = byte & 0x7f;
      while (byte & 0x80) { byte = buf[off++]; offset = ((offset + 1) << 7) | (byte & 0x7f); }
      entry.baseOffset = entryStart - offset;
    } else if (typeCode === 7) {
      if (off + 20 > trailerStart) throw new Error('pack: truncated ref-delta base');
      entry.baseOid = buf.subarray(off, off + 20).toString('hex');
      off += 20;
    } else if (PACK_CODE_TYPE[typeCode] === undefined) {
      throw new Error(`pack: unknown type code ${typeCode}`);
    }
    // One inflate: info.engine.bytesWritten is the consumed input length.
    let inflated: { buffer: Buffer; engine: { bytesWritten: number } };
    try {
      inflated = inflateSync(buf.subarray(off, trailerStart), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
    } catch (err) {
      throw new Error(`pack: zlib stream at offset ${off} did not inflate: ${(err as Error).message}`);
    }
    if (inflated.buffer.length !== size) throw new Error(`pack: entry at ${entryStart} declares ${size} bytes but inflated to ${inflated.buffer.length}`);
    entry.data = inflated.buffer;
    off += inflated.engine.bytesWritten;
    raw.push(entry);
    byOffset.set(entryStart, entry);
  }
  if (off !== trailerStart) throw new Error(`pack: ${trailerStart - off} stray bytes before trailer`);
  const resolvedByOid = new Map<string, Raw>();
  const resolving = new Set<number>();
  const resolve = (entry: Raw): ParsedPackEntry => {
    if (entry.resolved) return entry.resolved;
    if (resolving.has(entry.offset)) throw new Error(`pack: delta cycle at offset ${entry.offset}`);
    resolving.add(entry.offset);
    let type: ObjType;
    let data: Buffer;
    if (entry.typeCode === 6) {
      const baseEntry = byOffset.get(entry.baseOffset!);
      if (!baseEntry) throw new Error('pack: ofs-delta base not in pack');
      const base = resolve(baseEntry);
      type = base.type;
      data = applyDelta(base.data, entry.data);
    } else if (entry.typeCode === 7) {
      const baseEntry = resolvedByOid.get(entry.baseOid!);
      if (!baseEntry) throw new Error(`pack: ref-delta base ${entry.baseOid} not in pack`);
      const base = resolve(baseEntry);
      type = base.type;
      data = applyDelta(base.data, entry.data);
    } else {
      type = PACK_CODE_TYPE[entry.typeCode];
      data = entry.data;
    }
    const oid = hashObject(type, data);
    const obj: ParsedPackEntry = { type, oid, data };
    entry.resolved = obj;
    resolvedByOid.set(oid, entry);
    resolving.delete(entry.offset);
    return obj;
  };
  return raw.map(resolve);
}

// ---------------------------------------------------------------- store

interface GitObj { type: ObjType; data: Buffer; }
interface Label { name: string; color: string; }
interface IssueComment { id: number; body: string; createdSeq: number; }
interface Issue {
  number: number; title: string; body: string; state: 'open' | 'closed';
  labels: Label[]; createdSeq: number; comments: IssueComment[];
  createdAt: string; updatedAt: string; jsonCache: string;
}
interface ChangedFile { filename: string; status: string; additions: number; deletions: number; changes: number; }
interface Pull {
  number: number; title: string; body: string; state: 'open' | 'closed';
  merged: boolean; mergedAt: string | null; mergeCommitSha: string | null;
  headRef: string; headSha: string; baseRef: string; baseSha: string;
  mergeBaseSha: string; changedFiles: ChangedFile[]; createdSeq: number;
  createdAt: string;
}
interface Repo {
  owner: string; name: string; fullName: string; databaseId: number;
  description: string; isPrivate: boolean; defaultBranch: string;
  objects: Map<string, GitObj>; refs: Map<string, string>;
  issues: Issue[]; pulls: Pull[];
  labels: Map<string, Label>;
  seq: number; commentSeq: number; createdSeq: number;
  packCache: Map<string, Buffer>;
}

const repos = new Map<string, Repo>();
let nextDatabaseId = 5000;
let globalCreatedSeq = 0;

function repoKey(owner: string, name: string): string { return `${owner}/${name}`; }
function getRepo(owner: string, name: string): Repo | undefined { return repos.get(repoKey(owner, name)); }
function viewerRepos(): Repo[] {
  const out: Repo[] = [];
  for (const r of repos.values()) if (r.owner === VIEWER_LOGIN) out.push(r);
  return out;
}

function createRepoRecord(name: string, isPrivate: boolean, description: string, defaultBranch: string): Repo {
  const repo: Repo = {
    owner: VIEWER_LOGIN, name, fullName: `${VIEWER_LOGIN}/${name}`,
    databaseId: nextDatabaseId++, description, isPrivate,
    defaultBranch: defaultBranch || 'main',
    objects: new Map(), refs: new Map(),
    issues: [], pulls: [], labels: new Map(),
    seq: 1, commentSeq: 1, createdSeq: 0, packCache: new Map(),
  };
  repos.set(repoKey(VIEWER_LOGIN, name), repo);
  return repo;
}

function putObject(repo: Repo, type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}
function getObject(repo: Repo, oid: string): GitObj | undefined { return repo.objects.get(oid); }

/** All objects reachable from `roots` (commits -> tree+parents, tags -> target, trees -> entries). */
function collectReachable(repo: Repo, roots: Iterable<string>): Set<string> {
  const seen = new Set<string>();
  const queue: string[] = [];
  for (const r of roots) if (/^[0-9a-f]{40}$/.test(r)) queue.push(r);
  while (queue.length) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (!obj) continue;
    seen.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      queue.push(c.tree);
      for (const p of c.parents) queue.push(p);
    } else if (obj.type === 'tag') {
      queue.push(parseTag(obj.data).object);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) if (e.mode !== '160000') queue.push(e.oid);
    }
  }
  return seen;
}

/** True when `ancestor` is reachable from `descendant` (or equal). */
function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  const seen = new Set<string>();
  const queue = [descendant];
  while (queue.length) {
    const oid = queue.pop()!;
    if (oid === ancestor) return true;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) queue.push(p);
  }
  return false;
}

/** First common commit of two histories (by walking both), or null. */
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const ancestorsA = new Set<string>();
  const queueA = [a];
  while (queueA.length) {
    const oid = queueA.pop()!;
    if (ancestorsA.has(oid)) continue;
    ancestorsA.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) queueA.push(p);
  }
  const queueB = [b];
  const seenB = new Set<string>();
  while (queueB.length) {
    const oid = queueB.pop()!;
    if (ancestorsA.has(oid)) return oid;
    if (seenB.has(oid)) continue;
    seenB.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) queueB.push(p);
  }
  return null;
}

/** Commits reachable from `tip`, tip-first, parents after (deduped). */
function commitsFrom(repo: Repo, tip: string): string[] {
  const out: string[] = [];
  const seen = new Set<string>();
  const queue = [tip];
  while (queue.length) {
    const oid = queue.shift()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    out.push(oid);
    for (const p of parseCommit(obj.data).parents) queue.push(p);
  }
  return out;
}

/** Resolve a branch name / ref / oid to a tip oid, or null. */
function resolveRef(repo: Repo, ref: string): string | null {
  if (/^[0-9a-f]{40}$/.test(ref)) return repo.objects.has(ref) ? ref : null;
  if (ref.startsWith('refs/')) return repo.refs.get(ref) ?? null;
  return repo.refs.get(`refs/heads/${ref}`) ?? null;
}

/** Flatten a tree to path -> {oid, mode}. */
function flattenTree(repo: Repo, treeOid: string | null, prefix: string, out: Map<string, { oid: string; mode: string }>): void {
  if (!treeOid) return;
  const obj = repo.objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return;
  for (const e of parseTree(obj.data)) {
    const path = prefix ? `${prefix}/${e.name}` : e.name;
    if (e.mode === '40000') flattenTree(repo, e.oid, path, out);
    else out.set(path, { oid: e.oid, mode: e.mode });
  }
}

/** Add a tree oid plus every nested subtree and blob oid it references. */
function collectTreeObjects(repo: Repo, treeOid: string | null, out: Set<string>): void {
  if (!treeOid) return;
  const obj = repo.objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return;
  if (out.has(treeOid)) return;
  out.add(treeOid);
  for (const e of parseTree(obj.data)) {
    if (e.mode === '40000') collectTreeObjects(repo, e.oid, out);
    else if (e.mode !== '160000') out.add(e.oid);
  }
}

/**
 * Objects the client already holds, for have-exclusion: everything reachable
 * from the haves, but the walk stops at shallow boundaries — the client holds
 * a boundary commit and its tree, but NOT its parents (that is what makes a
 * deepen deliver the parent generation).
 */
function collectHaveExclusion(repo: Repo, haves: readonly string[], shallowBoundaries: readonly string[]): Set<string> {
  const excluded = new Set<string>();
  const shallowSet = new Set(shallowBoundaries);
  const seen = new Set<string>();
  const queue = [...haves];
  while (queue.length) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj) continue;
    if (obj.type === 'commit') {
      excluded.add(oid);
      collectTreeObjects(repo, parseCommit(obj.data).tree, excluded);
      if (!shallowSet.has(oid)) {
        for (const p of parseCommit(obj.data).parents) queue.push(p);
      }
    } else {
      for (const r of collectReachable(repo, [oid])) excluded.add(r);
    }
  }
  return excluded;
}

/** Read the blob oid at `path` in the tree, or null. */
function blobAtPath(repo: Repo, treeOid: string | null, path: string): string | null {
  const flat = new Map<string, { oid: string; mode: string }>();
  flattenTree(repo, treeOid, '', flat);
  return flat.get(path)?.oid ?? null;
}

/**
 * Set (or remove, when blobOid is null) `path` in the tree, rebuilding parent
 * trees. Returns the new tree oid. Empty directories are pruned.
 */
function setPathInTree(repo: Repo, treeOid: string | null, segments: readonly string[], blobOid: string | null): string {
  const entries = new Map<string, TreeEntry>();
  if (treeOid) {
    const obj = repo.objects.get(treeOid);
    if (obj && obj.type === 'tree') for (const e of parseTree(obj.data)) entries.set(e.name, e);
  }
  const head = segments[0];
  if (segments.length === 1) {
    if (blobOid === null) entries.delete(head);
    else entries.set(head, { mode: '100644', name: head, oid: blobOid });
  } else {
    const child = entries.get(head);
    const childTreeOid = child && child.mode === '40000' ? child.oid : null;
    const newChildOid = setPathInTree(repo, childTreeOid, segments.slice(1), blobOid);
    const childObj = repo.objects.get(newChildOid);
    const childEmpty = !childObj || childObj.type !== 'tree' || childObj.data.length === 0;
    if (childEmpty) entries.delete(head);
    else entries.set(head, { mode: '40000', name: head, oid: newChildOid });
  }
  const data = buildTree([...entries.values()]);
  return putObject(repo, 'tree', data);
}

function countLines(data: Buffer): number {
  if (data.length === 0) return 0;
  let n = 0;
  for (let i = 0; i < data.length; i++) if (data[i] === 0x0a) n++;
  if (data[data.length - 1] !== 0x0a) n++;
  return n;
}

/** Cheap line diff for short files: LCS over lines; big files fall back to full counts. */
function lineDiff(oldData: Buffer, newData: Buffer): { additions: number; deletions: number } {
  const oldLines = oldData.toString('utf8').split('\n');
  const newLines = newData.toString('utf8').split('\n');
  if (oldLines.length > 2000 || newLines.length > 2000) {
    return { additions: countLines(newData), deletions: countLines(oldData) };
  }
  const m = oldLines.length, n = newLines.length;
  const dp = new Uint16Array((m + 1) * (n + 1));
  for (let i = m - 1; i >= 0; i--) {
    for (let j = n - 1; j >= 0; j--) {
      dp[i * (n + 1) + j] = oldLines[i] === newLines[j]
        ? dp[(i + 1) * (n + 1) + (j + 1)] + 1
        : Math.max(dp[(i + 1) * (n + 1) + j], dp[i * (n + 1) + (j + 1)]);
    }
  }
  const common = dp[0];
  return { additions: n - common, deletions: m - common };
}

/** Diff two trees; returns one entry per differing path. */
function diffTrees(repo: Repo, oldTreeOid: string | null, newTreeOid: string | null): ChangedFile[] {
  const oldFlat = new Map<string, { oid: string; mode: string }>();
  const newFlat = new Map<string, { oid: string; mode: string }>();
  flattenTree(repo, oldTreeOid, '', oldFlat);
  flattenTree(repo, newTreeOid, '', newFlat);
  const out: ChangedFile[] = [];
  const paths = new Set([...oldFlat.keys(), ...newFlat.keys()]);
  for (const path of [...paths].sort()) {
    const o = oldFlat.get(path);
    const n = newFlat.get(path);
    if (o && !n) {
      const oldObj = repo.objects.get(o.oid);
      const deletions = oldObj ? countLines(oldObj.data) : 0;
      out.push({ filename: path, status: 'removed', additions: 0, deletions, changes: deletions });
    } else if (!o && n) {
      const newObj = repo.objects.get(n.oid);
      const additions = newObj ? countLines(newObj.data) : 0;
      out.push({ filename: path, status: 'added', additions: Math.max(additions, 1), deletions: 0, changes: Math.max(additions, 1) });
    } else if (o && n && o.oid !== n.oid) {
      const oldObj = repo.objects.get(o.oid);
      const newObj = repo.objects.get(n.oid);
      const d = lineDiff(oldObj ? oldObj.data : Buffer.alloc(0), newObj ? newObj.data : Buffer.alloc(0));
      const additions = Math.max(d.additions, 1);
      out.push({ filename: path, status: 'modified', additions, deletions: d.deletions, changes: additions + d.deletions });
    }
  }
  return out;
}

// ---------------------------------------------------------------- global ids

function globalId(type: string, owner: string, name: string, num?: number): string {
  const raw = num === undefined ? `${type}:${owner}/${name}` : `${type}:${owner}/${name}#${num}`;
  return Buffer.from(raw, 'utf8').toString('base64');
}

function decodeGlobalId(id: string): { type: string; owner: string; name: string; num: number | null } | null {
  try {
    const raw = Buffer.from(id, 'base64').toString('utf8');
    const m = /^(Repository|Issue|PullRequest|Comment):([^/]+)\/([^#]+)(?:#(\d+))?$/.exec(raw);
    if (!m) return null;
    return { type: m[1], owner: m[2], name: m[3], num: m[4] === undefined ? null : Number(m[4]) };
  } catch {
    return null;
  }
}

// ---------------------------------------------------------------- serialization

function nowIso(): string { return new Date().toISOString(); }

function serializeRepo(repo: Repo): Record<string, unknown> {
  return {
    id: repo.databaseId,
    node_id: globalId('Repository', repo.owner, repo.name),
    name: repo.name,
    full_name: repo.fullName,
    owner: { login: repo.owner, id: 1000, type: 'User' },
    private: repo.isPrivate,
    description: repo.description,
    default_branch: repo.defaultBranch,
    html_url: '',
    clone_url: '',
    created_at: nowIso(),
    updated_at: nowIso(),
    has_issues: true,
    has_projects: false,
    has_wiki: false,
  };
}

function serializeIssue(issue: Issue): Record<string, unknown> {
  return {
    id: issue.number,
    node_id: '',
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((l) => ({ name: l.name, color: l.color })),
    user: { login: VIEWER_LOGIN },
    comments: issue.comments.length,
    created_at: issue.createdAt,
    updated_at: issue.updatedAt,
  };
}

/** Refresh an issue's cached JSON (the read-workload hot path serves this string). */
function refreshIssueCache(repo: Repo, issue: Issue): void {
  const obj = serializeIssue(issue);
  obj.node_id = globalId('Issue', repo.owner, repo.name, issue.number);
  issue.jsonCache = JSON.stringify(obj);
}

function serializePull(repo: Repo, pull: Pull): Record<string, unknown> {
  return {
    id: pull.number,
    node_id: globalId('PullRequest', repo.owner, repo.name, pull.number),
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    head: { ref: pull.headRef, sha: pull.headSha, label: `${repo.owner}:${pull.headRef}` },
    base: { ref: pull.baseRef, sha: pull.baseSha, label: `${repo.owner}:${pull.baseRef}` },
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    mergeable: prMergeable(repo, pull),
    created_at: pull.createdAt,
  };
}

/** True when the PR can merge cleanly onto the base tip right now. */
function prMergeable(repo: Repo, pull: Pull): boolean {
  return !prConflict(repo, pull);
}

function prConflict(repo: Repo, pull: Pull): boolean {
  const baseTip = resolveRef(repo, pull.baseRef);
  if (!baseTip) return false;
  const baseTree = treeOfCommit(repo, baseTip);
  const mergeBaseTree = pull.mergeBaseSha ? treeOfCommit(repo, pull.mergeBaseSha) : null;
  const headTree = treeOfCommit(repo, pull.headSha);
  for (const f of pull.changedFiles) {
    const atBase = blobAtPath(repo, baseTree, f.filename);
    const atMergeBase = blobAtPath(repo, mergeBaseTree, f.filename);
    const atHead = blobAtPath(repo, headTree, f.filename);
    if (atBase !== atMergeBase && atHead !== atBase) return true;
  }
  return false;
}

function treeOfCommit(repo: Repo, commitOid: string | null): string | null {
  if (!commitOid) return null;
  const obj = repo.objects.get(commitOid);
  if (!obj || obj.type !== 'commit') return null;
  return parseCommit(obj.data).tree;
}

function createIssueRecord(repo: Repo, title: string, body: string, labelNames: readonly string[]): Issue {
  const labels: Label[] = [];
  for (const name of labelNames) {
    const l = repo.labels.get(name);
    if (l) labels.push(l);
  }
  const issue: Issue = {
    number: repo.seq++,
    title, body, state: 'open', labels,
    createdSeq: ++globalCreatedSeq,
    comments: [], createdAt: nowIso(), updatedAt: nowIso(), jsonCache: '',
  };
  repo.issues.push(issue);
  refreshIssueCache(repo, issue);
  return issue;
}

function createPullRecord(repo: Repo, title: string, body: string, headRef: string, baseRef: string): Pull | null {
  const headSha = resolveRef(repo, headRef);
  const baseSha = resolveRef(repo, baseRef);
  if (!headSha || !baseSha) return null;
  const headTree = treeOfCommit(repo, headSha);
  const baseTree = treeOfCommit(repo, baseSha);
  const pull: Pull = {
    number: repo.seq++,
    title, body, state: 'open',
    merged: false, mergedAt: null, mergeCommitSha: null,
    headRef, headSha, baseRef, baseSha,
    mergeBaseSha: baseSha,
    changedFiles: diffTrees(repo, baseTree, headTree),
    createdSeq: ++globalCreatedSeq,
    createdAt: nowIso(),
  };
  repo.pulls.push(pull);
  return pull;
}

/** Squash-merge a PR onto its base branch. Returns the merge commit oid, or null on conflict. */
function mergePullRecord(repo: Repo, pull: Pull): string | null {
  if (pull.merged || pull.state !== 'open') return null;
  if (prConflict(repo, pull)) return null;
  const baseTip = resolveRef(repo, pull.baseRef);
  if (!baseTip) return null;
  const baseTree = treeOfCommit(repo, baseTip);
  const headTree = treeOfCommit(repo, pull.headSha);
  const headFlat = new Map<string, { oid: string; mode: string }>();
  flattenTree(repo, headTree, '', headFlat);
  const baseFlat = new Map<string, { oid: string; mode: string }>();
  flattenTree(repo, baseTree, '', baseFlat);
  let tree = baseTree;
  for (const f of pull.changedFiles) {
    const segments = f.filename.split('/');
    if (f.status === 'removed') {
      tree = setPathInTree(repo, tree, segments, null);
    } else {
      const blobOid = headFlat.get(f.filename)?.oid ?? null;
      if (blobOid) tree = setPathInTree(repo, tree, segments, blobOid);
    }
  }
  const ts = Math.floor(Date.now() / 1000);
  const message = `Merge pull request #${pull.number}: ${pull.title}`;
  const commitData = buildCommit(tree ?? EMPTY_TREE_OID, [baseTip], message, SERVER_IDENTITY, SERVER_IDENTITY, ts);
  const commitOid = putObject(repo, 'commit', commitData);
  repo.refs.set(`refs/heads/${pull.baseRef}`, commitOid);
  pull.merged = true;
  pull.state = 'closed';
  pull.mergedAt = nowIso();
  pull.mergeCommitSha = commitOid;
  repo.packCache.clear();
  return commitOid;
}

// ---------------------------------------------------------------- HTTP plumbing

let requestCounter = 0;

function isAuthed(req: IncomingMessage): boolean {
  const h = req.headers.authorization;
  if (!h || !h.startsWith('Bearer ')) return false;
  const given = Buffer.from(h.slice(7), 'utf8');
  const want = Buffer.from(TOKEN, 'utf8');
  if (given.length !== want.length) return false;
  return timingSafeEqual(given, want);
}

function sendJson(res: ServerResponse, status: number, body: unknown, extraHeaders: Record<string, string> = {}): void {
  const text = typeof body === 'string' ? body : JSON.stringify(body);
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'x-github-request-id': `req-${++requestCounter}`,
    ...extraHeaders,
  });
  res.end(text);
}

function sendError(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message });
}

function sendRaw(res: ServerResponse, status: number, contentType: string, body: Buffer): void {
  res.writeHead(status, {
    'content-type': contentType,
    'x-github-request-id': `req-${++requestCounter}`,
    'content-length': String(body.length),
  });
  res.end(body);
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let size = 0;
    let tooBig = false;
    req.on('data', (c: Buffer) => {
      size += c.length;
      if (size > MAX_BODY_BYTES) { tooBig = true; return; }
      chunks.push(c);
    });
    req.on('end', () => {
      if (tooBig) reject(Object.assign(new Error('body too large'), { status: 413 }));
      else resolve(Buffer.concat(chunks));
    });
    req.on('error', reject);
  });
}

function parseJsonBody(buf: Buffer): unknown {
  if (buf.length === 0) return {};
  return JSON.parse(buf.toString('utf8'));
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && !Array.isArray(v);
}

function str(v: unknown, fallback = ''): string {
  return typeof v === 'string' ? v : fallback;
}

// ---------------------------------------------------------------- git handlers

function refListLines(repo: Repo): Array<{ oid: string; name: string; peeled?: string }> {
  const out: Array<{ oid: string; name: string; peeled?: string }> = [];
  const names = [...repo.refs.keys()].sort();
  for (const name of names) {
    const oid = repo.refs.get(name)!;
    const entry: { oid: string; name: string; peeled?: string } = { oid, name };
    if (name.startsWith('refs/tags/')) {
      const obj = repo.objects.get(oid);
      if (obj && obj.type === 'tag') {
        const target = parseTag(obj.data).object;
        const targetObj = repo.objects.get(target);
        if (targetObj && targetObj.type === 'commit') entry.peeled = target;
      }
    }
    out.push(entry);
  }
  return out;
}

function headOid(repo: Repo): string {
  return repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? ZERO_OID;
}

/** GET info/refs for upload-pack: v2 when Git-Protocol: version=2, else v0. */
function handleInfoRefsUploadPack(repo: Repo, req: IncomingMessage, res: ServerResponse): void {
  const wantV2 = (req.headers['git-protocol'] ?? '').includes('version=2');
  if (wantV2) {
    const parts: Buffer[] = [
      pktLine('# service=git-upload-pack\n'), pktFlush(),
      pktLine('version 2\n'),
      pktLine(`agent=${AGENT}\n`),
      pktLine('ls-refs\n'),
      pktLine('fetch=shallow wait-for-done\n'),
      pktLine('object-format=sha1\n'),
      pktFlush(),
    ];
    sendRaw(res, 200, 'application/x-git-upload-pack-advertisement', Buffer.concat(parts));
    return;
  }
  // v0 advertisement
  const caps = `symref=HEAD:refs/heads/${repo.defaultBranch} agent=${AGENT} side-band-64k ofs-delta thin-pack shallow multi_ack`;
  const parts: Buffer[] = [pktLine('# service=git-upload-pack\n'), pktFlush()];
  const refs = refListLines(repo);
  if (refs.length === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    const head = headOid(repo);
    parts.push(pktLine(`${head} HEAD\0${caps}\n`));
    for (const r of refs) {
      parts.push(pktLine(`${r.oid} ${r.name}\n`));
      if (r.peeled) parts.push(pktLine(`${r.peeled} ${r.name}^{}\n`));
    }
  }
  parts.push(pktFlush());
  sendRaw(res, 200, 'application/x-git-upload-pack-advertisement', Buffer.concat(parts));
}

/** GET info/refs for receive-pack (v0). */
function handleInfoRefsReceivePack(repo: Repo, req: IncomingMessage, res: ServerResponse): void {
  const caps = `report-status report-status-v2 side-band-64k delete-refs ofs-delta agent=${AGENT} symref=HEAD:refs/heads/${repo.defaultBranch}`;
  const parts: Buffer[] = [pktLine('# service=git-receive-pack\n'), pktFlush()];
  const refs = refListLines(repo);
  if (refs.length === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    const head = headOid(repo);
    parts.push(pktLine(`${head} HEAD\0${caps}\n`));
    for (const r of refs) {
      parts.push(pktLine(`${r.oid} ${r.name}\n`));
      if (r.peeled) parts.push(pktLine(`${r.peeled} ${r.name}^{}\n`));
    }
  }
  parts.push(pktFlush());
  sendRaw(res, 200, 'application/x-git-receive-pack-advertisement', Buffer.concat(parts));
}

interface LsRefsArg { peel: boolean; symrefs: boolean; unborn: boolean; prefixes: string[]; }

/** POST git-upload-pack: v2 ls-refs / fetch. */
function handleUploadPack(repo: Repo, req: IncomingMessage, res: ServerResponse, body: Buffer): void {
  let packets: Pkt[];
  try {
    packets = parsePktLines(body);
  } catch (err) {
    sendError(res, 400, (err as Error).message);
    return;
  }
  const lines = dataLines(packets);
  if (lines.length === 0 || !lines[0].startsWith('command=')) {
    sendError(res, 400, 'missing command');
    return;
  }
  const command = lines[0].slice('command='.length).trim();
  const args = lines.slice(1);
  if (command === 'ls-refs') {
    const arg: LsRefsArg = { peel: false, symrefs: false, unborn: false, prefixes: [] };
    for (const a of args) {
      const t = a.trim();
      if (t === 'peel') arg.peel = true;
      else if (t === 'symrefs') arg.symrefs = true;
      else if (t === 'unborn') arg.unborn = true;
      else if (t.startsWith('ref-prefix ')) arg.prefixes.push(t.slice('ref-prefix '.length));
    }
    const out: Buffer[] = [];
    const keep = (name: string): boolean => arg.prefixes.length === 0 || arg.prefixes.some((p) => name.startsWith(p));
    const head = headOid(repo);
    // HEAD is a pseudo-ref: send it only when no prefix filter is given or
    // some prefix matches HEAD itself (real git asks `ref-prefix HEAD` and
    // needs the line to learn the default branch; a `refs/heads/` prefix
    // must NOT receive it).
    const headRequested = arg.prefixes.length === 0 || arg.prefixes.some((p) => 'HEAD'.startsWith(p));
    if (headRequested) {
      if (head === ZERO_OID) {
        if (arg.unborn) out.push(pktLine(`unborn refs/heads/${repo.defaultBranch}\n`));
      } else {
        let line = `${head} HEAD`;
        if (arg.symrefs) line += ` symref-target:refs/heads/${repo.defaultBranch}`;
        out.push(pktLine(`${line}\n`));
      }
    }
    for (const r of refListLines(repo)) {
      if (!keep(r.name)) continue;
      let line = `${r.oid} ${r.name}`;
      if (arg.peel && r.peeled) line += ` peeled:${r.peeled}`;
      out.push(pktLine(`${line}\n`));
    }
    out.push(pktFlush());
    sendRaw(res, 200, 'application/x-git-upload-pack-result', Buffer.concat(out));
    return;
  }
  if (command === 'fetch') {
    handleFetchV2(repo, args, res);
    return;
  }
  sendError(res, 400, `unknown command ${command}`);
}

interface FetchArgs {
  wants: string[]; haves: string[]; shallow: string[];
  depth: number | null; deepenSince: number | null; deepenNot: string[];
}

/** Select objects for a fetch: reachable from wants, minus reachable from haves, cut by depth. */
function selectFetchObjects(repo: Repo, args: FetchArgs): { objects: PackObject[]; shallow: string[]; unshallow: string[] } {
  const haveExclusion = collectHaveExclusion(repo, args.haves, args.shallow);
  // Depth-limited walk from each want.
  const included = new Set<string>();
  const boundary = new Set<string>(); // deepest included commits (shallow boundary)
  if (args.depth !== null) {
    for (const want of args.wants) {
      // BFS by generation from the want.
      let frontier = [want];
      for (let gen = 0; gen < args.depth && frontier.length; gen++) {
        const next: string[] = [];
        for (const oid of frontier) {
          if (included.has(oid)) continue;
          const obj = repo.objects.get(oid);
          if (!obj) continue;
          included.add(oid);
          if (obj.type === 'commit') {
            const c = parseCommit(obj.data);
            if (gen === args.depth - 1) {
              if (c.parents.length > 0) boundary.add(oid);
            } else {
              for (const p of c.parents) next.push(p);
            }
          }
        }
        frontier = next;
      }
      // Add trees (including nested subtrees) and blobs for included commits.
      for (const oid of [...included]) {
        const obj = repo.objects.get(oid);
        if (!obj || obj.type !== 'commit') continue;
        collectTreeObjects(repo, parseCommit(obj.data).tree, included);
      }
    }
  } else {
    for (const oid of collectReachable(repo, args.wants)) included.add(oid);
  }
  for (const oid of haveExclusion) included.delete(oid);
  // Unshallow: a client-sent boundary now included with a parent also included.
  const unshallow: string[] = [];
  for (const b of args.shallow) {
    if (!included.has(b)) continue;
    const obj = repo.objects.get(b);
    if (!obj || obj.type !== 'commit') continue;
    const parents = parseCommit(obj.data).parents;
    if (parents.some((p) => included.has(p))) unshallow.push(b);
  }
  const shallow = [...boundary].filter((oid) => included.has(oid) && !haveExclusion.has(oid));
  // Order: commits, then trees, then blobs, then tags (stable, cache-friendly).
  const ordered: PackObject[] = [];
  const byType = (t: ObjType): string[] => [...included].filter((oid) => repo.objects.get(oid)?.type === t).sort();
  for (const t of ['commit', 'tree', 'blob', 'tag'] as ObjType[]) {
    for (const oid of byType(t)) {
      const obj = repo.objects.get(oid)!;
      ordered.push({ type: t, data: obj.data });
    }
  }
  return { objects: ordered, shallow, unshallow };
}

function handleFetchV2(repo: Repo, args: string[], res: ServerResponse): void {
  const fa: FetchArgs = { wants: [], haves: [], shallow: [], depth: null, deepenSince: null, deepenNot: [] };
  for (const a of args) {
    const t = a.trim();
    if (t.startsWith('want ')) fa.wants.push(t.slice(5).trim());
    else if (t.startsWith('have ')) fa.haves.push(t.slice(5).trim());
    else if (t.startsWith('shallow ')) fa.shallow.push(t.slice(8).trim());
    else if (t.startsWith('deepen ')) { const n = Number(t.slice(7).trim()); if (Number.isFinite(n)) fa.depth = n; }
    else if (t.startsWith('deepen-since ')) { const n = Number(t.slice(13).trim()); if (Number.isFinite(n)) fa.deepenSince = n; }
    else if (t.startsWith('deepen-not ')) fa.deepenNot.push(t.slice(11).trim());
  }
  fa.wants = [...new Set(fa.wants)];
  const parts: Buffer[] = [];
  // The acknowledgments section is only sent when the client sent `have`
  // lines: with no haves, real git expects the packfile section first
  // ("expected 'packfile', received 'acknowledgments'").
  if (fa.haves.length > 0) {
    parts.push(pktLine('acknowledgments\n'));
    let acked = false;
    for (const h of fa.haves) {
      if (fa.wants.some((w) => isAncestor(repo, h, w))) {
        parts.push(pktLine(`ACK ${h}\n`));
        acked = true;
      }
    }
    if (!acked) parts.push(pktLine('NAK\n'));
    parts.push(pktDelim());
  }
  // object selection (cached pack per identical request)
  const cacheKey = JSON.stringify([fa.wants, fa.haves, fa.shallow, fa.depth, fa.deepenSince, fa.deepenNot]);
  let pack = repo.packCache.get(cacheKey);
  let shallow: string[] = [];
  let unshallow: string[] = [];
  if (pack === undefined) {
    const sel = selectFetchObjects(repo, fa);
    pack = writePack(sel.objects);
    shallow = sel.shallow;
    unshallow = sel.unshallow;
    if (repo.packCache.size > 64) repo.packCache.clear();
    repo.packCache.set(cacheKey, pack);
    // Cache the shallow/unshallow alongside via a side map entry.
    repo.packCache.set(`${cacheKey}:shallow`, Buffer.from(JSON.stringify([shallow, unshallow]), 'utf8'));
  } else {
    const meta = repo.packCache.get(`${cacheKey}:shallow`);
    if (meta) [shallow, unshallow] = JSON.parse(meta.toString('utf8')) as [string[], string[]];
  }
  // shallow-info section
  if (shallow.length || unshallow.length) {
    parts.push(pktLine('shallow-info\n'));
    for (const s of shallow) parts.push(pktLine(`shallow ${s}\n`));
    for (const u of unshallow) parts.push(pktLine(`unshallow ${u}\n`));
    parts.push(pktDelim());
  }
  // packfile section
  parts.push(pktLine('packfile\n'));
  for (const f of sidebandFrames(pack)) parts.push(f);
  parts.push(pktFlush());
  sendRaw(res, 200, 'application/x-git-upload-pack-result', Buffer.concat(parts));
}

/** POST git-receive-pack (v0): parse commands + pack, apply per-ref, sideband report. */
function handleReceivePack(repo: Repo, req: IncomingMessage, res: ServerResponse, body: Buffer): void {
  let commands: Array<{ oldOid: string; newOid: string; ref: string }> = [];
  let packBuf: Buffer = Buffer.alloc(0);
  try {
    const { packets, consumed } = parsePktLinesUntilFlush(body);
    for (const line of dataLines(packets)) {
      const nul = line.indexOf('\0');
      const clean = nul >= 0 ? line.slice(0, nul) : line;
      const m = /^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)\s*$/.exec(clean);
      if (!m) throw new Error(`bad receive-pack command line ${JSON.stringify(clean.slice(0, 60))}`);
      commands.push({ oldOid: m[1], newOid: m[2], ref: m[3] });
    }
    packBuf = body.subarray(consumed);
  } catch (err) {
    sendError(res, 400, (err as Error).message);
    return;
  }
  if (commands.length === 0) {
    sendError(res, 400, 'no commands');
    return;
  }
  // Parse + store the pack (if any). Delete-only pushes carry no pack.
  let unpackOk = true;
  let unpackDetail = 'ok';
  const hasUpdates = commands.some((c) => c.newOid !== ZERO_OID);
  if (hasUpdates) {
    if (packBuf.length === 0) {
      unpackOk = false;
      unpackDetail = 'missing packfile';
    } else {
      try {
        const objects = parsePack(packBuf);
        for (const o of objects) putObject(repo, o.type, o.data);
      } catch (err) {
        unpackOk = false;
        unpackDetail = (err as Error).message;
      }
    }
  }
  // Apply commands in order, per-ref fast-forward check.
  const reportLines: string[] = [];
  reportLines.push(unpackOk ? 'unpack ok\n' : `unpack ${unpackDetail}\n`);
  if (unpackOk) {
    for (const cmd of commands) {
      const current = repo.refs.get(cmd.ref);
      let ok = true;
      let reason = '';
      if (cmd.newOid === ZERO_OID) {
        if (current === undefined) { ok = false; reason = 'ref does not exist'; }
        else if (cmd.oldOid !== ZERO_OID && cmd.oldOid !== current) { ok = false; reason = 'old value does not match'; }
        else repo.refs.delete(cmd.ref);
      } else {
        const newObj = repo.objects.get(cmd.newOid);
        if (!newObj) { ok = false; reason = 'object not found'; }
        else if (cmd.oldOid === ZERO_OID) {
          if (current !== undefined) { ok = false; reason = 'already exists'; }
          else repo.refs.set(cmd.ref, cmd.newOid);
        } else {
          if (current === undefined) { ok = false; reason = 'ref does not exist'; }
          else if (current !== cmd.oldOid) { ok = false; reason = 'old value does not match'; }
          else if (newObj.type === 'commit' && !isAncestor(repo, cmd.oldOid, cmd.newOid)) { ok = false; reason = 'non-fast-forward'; }
          else repo.refs.set(cmd.ref, cmd.newOid);
        }
      }
      reportLines.push(ok ? `ok ${cmd.ref}\n` : `ng ${cmd.ref} ${reason}\n`);
    }
    repo.packCache.clear();
  } else {
    for (const cmd of commands) reportLines.push(`ng ${cmd.ref} unpack failed\n`);
  }
  // The report-status stream inside band 1 is itself pkt-lined and must end
  // with its own flush: real git's inner packet reader dies on EOF without
  // it ("the remote end hung up unexpectedly"). The outer stream then ends
  // with a second, bare flush.
  const reportPayload = Buffer.concat([...reportLines.map((line) => pktLine(line)), pktFlush()]);
  const frames: Buffer[] = sidebandFrames(reportPayload);
  frames.push(pktFlush());
  sendRaw(res, 200, 'application/x-git-receive-pack-result', Buffer.concat(frames));
}

// ---------------------------------------------------------------- REST v3

function parsePagination(url: URL): { perPage: number; page: number } {
  const perPage = Math.max(1, Math.min(100, Number(url.searchParams.get('per_page') ?? '30') || 30));
  const page = Math.max(1, Number(url.searchParams.get('page') ?? '1') || 1);
  return { perPage, page };
}

function linkHeader(req: IncomingMessage, url: URL, page: number, perPage: number): string {
  const host = req.headers.host ?? 'localhost';
  const proto = 'http';
  const u = new URL(url.toString());
  u.searchParams.set('page', String(page + 1));
  u.searchParams.set('per_page', String(perPage));
  return `<${proto}://${host}${u.pathname}${u.search}>; rel="next"`;
}

function paginate<T>(items: readonly T[], page: number, perPage: number): { pageItems: T[]; hasNext: boolean } {
  const start = (page - 1) * perPage;
  return { pageItems: items.slice(start, start + perPage), hasNext: start + perPage < items.length };
}

function viewerUserJson(): Record<string, unknown> {
  return { login: VIEWER_LOGIN, id: 1000, type: 'User', name: VIEWER_LOGIN, avatar_url: '', html_url: '' };
}

async function handleRest(req: IncomingMessage, res: ServerResponse, url: URL): Promise<void> {
  const method = req.method ?? 'GET';
  const segments = url.pathname.replace(/^\/api\/v3/, '').split('/').filter((s) => s !== '');
  // Root + meta + user (no repo in path)
  if (method === 'GET' && url.pathname === '/api/v3/') {
    sendJson(res, 200, {}, { 'x-oauth-scopes': 'repo, read:org' });
    return;
  }
  if (method === 'GET' && url.pathname === '/api/v3/meta') {
    sendJson(res, 200, { installed_version: '1.0.0' });
    return;
  }
  if (method === 'GET' && url.pathname === '/api/v3/user') {
    sendJson(res, 200, viewerUserJson());
    return;
  }
  if (url.pathname === '/api/v3/user/repos') {
    if (method === 'GET') {
      const { perPage, page } = parsePagination(url);
      const all = viewerRepos();
      const { pageItems, hasNext } = paginate(all, page, perPage);
      const extra: Record<string, string> = {};
      if (hasNext) extra.link = linkHeader(req, url, page, perPage);
      sendJson(res, 200, pageItems.map(serializeRepo), extra);
      return;
    }
    if (method === 'POST') {
      const body = await readBody(req);
      let payload: unknown;
      try { payload = parseJsonBody(body); } catch { sendError(res, 400, 'Invalid JSON'); return; }
      if (!isRecord(payload)) { sendError(res, 400, 'Invalid JSON'); return; }
      const name = str(payload.name).trim();
      if (!name || !/^[\w.-]+$/.test(name)) { sendError(res, 422, 'name is required'); return; }
      if (getRepo(VIEWER_LOGIN, name)) { sendError(res, 422, `Repository "${name}" already exists`); return; }
      const repo = createRepoRecord(name, payload.private === true, str(payload.description), str(payload.default_branch, 'main'));
      sendJson(res, 201, serializeRepo(repo));
      return;
    }
    sendError(res, 405, 'Method not allowed');
    return;
  }
  // /api/v3/repos/{owner}/{repo}[...]
  if (segments.length >= 3 && segments[0] === 'repos') {
    const owner = segments[1];
    const repoName = segments[2];
    const repo = getRepo(owner, repoName);
    if (!repo || owner !== VIEWER_LOGIN) {
      // Foreign owners (orgs, strangers): the same repo name is 404, never 403.
      sendError(res, 404, 'Not Found');
      return;
    }
    await handleRepoRest(req, res, url, method, segments.slice(3), repo);
    return;
  }
  sendError(res, 404, 'Not Found');
}

async function handleRepoRest(req: IncomingMessage, res: ServerResponse, url: URL, method: string, tail: string[], repo: Repo): Promise<void> {
  const readJson = async (): Promise<Record<string, unknown> | null> => {
    const body = await readBody(req);
    let payload: unknown;
    try { payload = parseJsonBody(body); } catch { sendError(res, 400, 'Invalid JSON'); return null; }
    if (!isRecord(payload)) { sendError(res, 400, 'Invalid JSON'); return null; }
    return payload;
  };
  // GET / DELETE / PATCH repo itself
  if (tail.length === 0) {
    if (method === 'GET') { sendJson(res, 200, serializeRepo(repo)); return; }
    if (method === 'DELETE') {
      repos.delete(repoKey(repo.owner, repo.name));
      res.writeHead(204, { 'x-github-request-id': `req-${++requestCounter}` });
      res.end();
      return;
    }
    if (method === 'PATCH') {
      const payload = await readJson();
      if (payload === null) return;
      if (typeof payload.description === 'string') repo.description = payload.description;
      if (typeof payload.private === 'boolean') repo.isPrivate = payload.private;
      if (typeof payload.default_branch === 'string' && payload.default_branch) repo.defaultBranch = payload.default_branch;
      sendJson(res, 200, serializeRepo(repo));
      return;
    }
    sendError(res, 405, 'Method not allowed');
    return;
  }
  const head = tail[0];
  // /issues
  if (head === 'issues') {
    if (method === 'GET' && tail.length === 1) {
      const { perPage, page } = parsePagination(url);
      const state = url.searchParams.get('state') ?? 'open';
      const direction = url.searchParams.get('direction') ?? 'desc';
      const sort = url.searchParams.get('sort') ?? 'created';
      let list = repo.issues.filter((i) => state === 'all' || i.state === state);
      list = [...list].sort((a, b) => {
        let c = 0;
        if (sort === 'created') c = a.createdSeq - b.createdSeq;
        if (direction === 'desc') c = -c;
        return c;
      });
      const { pageItems, hasNext } = paginate(list, page, perPage);
      const extra: Record<string, string> = {};
      if (hasNext) extra.link = linkHeader(req, url, page, perPage);
      // Serve pre-serialized JSON for the hot read path.
      const json = `[${pageItems.map((i) => i.jsonCache).join(',')}]`;
      res.writeHead(200, {
        'content-type': 'application/json; charset=utf-8',
        'x-github-request-id': `req-${++requestCounter}`,
        ...extra,
      });
      res.end(json);
      return;
    }
    if (method === 'POST' && tail.length === 1) {
      const payload = await readJson();
      if (payload === null) return;
      const title = str(payload.title).trim();
      if (!title) { sendError(res, 422, 'title is required'); return; }
      const labelNames: string[] = Array.isArray(payload.labels) ? payload.labels.filter((l): l is string => typeof l === 'string') : [];
      for (const n of labelNames) if (!repo.labels.has(n)) { sendError(res, 422, `Label "${n}" does not exist`); return; }
      const issue = createIssueRecord(repo, title, str(payload.body), labelNames);
      sendJson(res, 201, JSON.parse(issue.jsonCache) as Record<string, unknown>);
      return;
    }
    if (tail.length >= 2) {
      const n = Number(tail[1]);
      const issue = Number.isInteger(n) ? repo.issues.find((i) => i.number === n) : undefined;
      if (!issue) { sendError(res, 404, 'Not Found'); return; }
      if (method === 'GET' && tail.length === 2) {
        res.writeHead(200, { 'content-type': 'application/json; charset=utf-8', 'x-github-request-id': `req-${++requestCounter}` });
        res.end(issue.jsonCache);
        return;
      }
      if (method === 'PATCH' && tail.length === 2) {
        const payload = await readJson();
        if (payload === null) return;
        if (typeof payload.title === 'string') issue.title = payload.title;
        if (typeof payload.body === 'string') issue.body = payload.body;
        if (typeof payload.state === 'string' && (payload.state === 'open' || payload.state === 'closed')) issue.state = payload.state;
        issue.updatedAt = nowIso();
        refreshIssueCache(repo, issue);
        res.writeHead(200, { 'content-type': 'application/json; charset=utf-8', 'x-github-request-id': `req-${++requestCounter}` });
        res.end(issue.jsonCache);
        return;
      }
      if (tail[2] === 'comments') {
        if (method === 'GET' && tail.length === 3) {
          const { perPage, page } = parsePagination(url);
          const { pageItems, hasNext } = paginate(issue.comments, page, perPage);
          const extra: Record<string, string> = {};
          if (hasNext) extra.link = linkHeader(req, url, page, perPage);
          sendJson(res, 200, pageItems.map((c) => ({ id: c.id, body: c.body, user: { login: VIEWER_LOGIN } })), extra);
          return;
        }
        if (method === 'POST' && tail.length === 3) {
          const payload = await readJson();
          if (payload === null) return;
          const bodyText = str(payload.body).trim();
          if (!bodyText) { sendError(res, 422, 'body is required'); return; }
          const comment: IssueComment = { id: repo.commentSeq++, body: bodyText, createdSeq: ++globalCreatedSeq };
          issue.comments.push(comment);
          sendJson(res, 201, { id: comment.id, body: comment.body, user: { login: VIEWER_LOGIN } });
          return;
        }
      }
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  // /pulls
  if (head === 'pulls') {
    if (method === 'GET' && tail.length === 1) {
      const { perPage, page } = parsePagination(url);
      const state = url.searchParams.get('state') ?? 'open';
      const list = repo.pulls.filter((p) => state === 'all' || p.state === state);
      const { pageItems, hasNext } = paginate(list, page, perPage);
      const extra: Record<string, string> = {};
      if (hasNext) extra.link = linkHeader(req, url, page, perPage);
      sendJson(res, 200, pageItems.map((p) => serializePull(repo, p)), extra);
      return;
    }
    if (method === 'POST' && tail.length === 1) {
      const payload = await readJson();
      if (payload === null) return;
      const title = str(payload.title).trim();
      const headRef = str(payload.head).trim();
      const baseRef = str(payload.base).trim();
      if (!title || !headRef || !baseRef) { sendError(res, 422, 'title, head and base are required'); return; }
      const pull = createPullRecord(repo, title, str(payload.body), headRef, baseRef);
      if (!pull) { sendError(res, 422, 'head or base branch not found'); return; }
      sendJson(res, 201, serializePull(repo, pull));
      return;
    }
    if (tail.length >= 2) {
      const n = Number(tail[1]);
      const pull = Number.isInteger(n) ? repo.pulls.find((p) => p.number === n) : undefined;
      if (!pull) { sendError(res, 404, 'Not Found'); return; }
      if (method === 'GET' && tail.length === 2) { sendJson(res, 200, serializePull(repo, pull)); return; }
      if (method === 'GET' && tail.length === 3 && tail[2] === 'files') {
        sendJson(res, 200, pull.changedFiles);
        return;
      }
      if (method === 'PUT' && tail.length === 3 && tail[2] === 'merge') {
        const oid = mergePullRecord(repo, pull);
        if (oid === null) { sendError(res, 405, 'Merge conflict'); return; }
        sendJson(res, 200, { merged: true, sha: oid, message: 'Pull Request successfully merged' });
        return;
      }
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  // /git/refs
  if (head === 'git' && tail[1] === 'refs') {
    if (method === 'POST' && tail.length === 2) {
      const payload = await readJson();
      if (payload === null) return;
      const ref = str(payload.ref).trim();
      const sha = str(payload.sha).trim();
      if (!ref || !/^[0-9a-f]{40}$/.test(sha)) { sendError(res, 422, 'ref and sha are required'); return; }
      if (repo.refs.has(ref)) { sendError(res, 422, 'Reference already exists'); return; }
      if (!repo.objects.has(sha)) { sendError(res, 422, 'Object does not exist'); return; }
      repo.refs.set(ref, sha);
      repo.packCache.clear();
      sendJson(res, 201, { ref, object: { sha } });
      return;
    }
    if (method === 'GET' && tail.length === 5 && tail[2] === 'heads') {
      const branch = tail[3];
      const oid = repo.refs.get(`refs/heads/${branch}`);
      if (!oid) { sendError(res, 404, 'Not Found'); return; }
      sendJson(res, 200, { ref: `refs/heads/${branch}`, object: { sha: oid } });
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  // /branches
  if (head === 'branches') {
    if (method === 'GET' && tail.length === 1) {
      const out = [...repo.refs.keys()]
        .filter((r) => r.startsWith('refs/heads/'))
        .map((r) => ({ name: r.slice('refs/heads/'.length), commit: { sha: repo.refs.get(r)! } }));
      sendJson(res, 200, out);
      return;
    }
    if (method === 'GET' && tail.length === 2) {
      const oid = repo.refs.get(`refs/heads/${tail[1]}`);
      if (!oid) { sendError(res, 404, 'Not Found'); return; }
      sendJson(res, 200, { name: tail[1], commit: { sha: oid } });
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  // /commits
  if (head === 'commits') {
    if (method === 'GET' && tail.length === 1) {
      const shaParam = url.searchParams.get('sha') ?? repo.defaultBranch;
      const tip = resolveRef(repo, shaParam);
      if (!tip) { sendJson(res, 200, []); return; }
      const list = commitsFrom(repo, tip).map((oid) => {
        const obj = repo.objects.get(oid)!;
        const c = parseCommit(obj.data);
        return { sha: oid, commit: { message: c.message, author: { name: c.author }, committer: { name: c.committer } }, parents: c.parents.map((p) => ({ sha: p })) };
      });
      sendJson(res, 200, list);
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  // /contents
  if (head === 'contents') {
    const path = decodeURIComponent(tail.slice(1).join('/'));
    if (method === 'GET' && tail.length >= 1) {
      const tip = headOid(repo);
      if (tip === ZERO_OID) { sendError(res, 404, 'Not Found'); return; }
      const tree = treeOfCommit(repo, tip);
      if (path === '') {
        const flat = new Map<string, { oid: string; mode: string }>();
        flattenTree(repo, tree, '', flat);
        const top = new Map<string, { type: string; sha: string }>();
        for (const [p, e] of flat) {
          const first = p.split('/')[0];
          if (!top.has(first)) top.set(first, { type: p.includes('/') ? 'dir' : 'file', sha: e.oid });
        }
        sendJson(res, 200, [...top.entries()].map(([name, e]) => ({ type: e.type, name, path: name, sha: e.sha })));
        return;
      }
      const blobOid = blobAtPath(repo, tree, path);
      if (blobOid) {
        const blob = repo.objects.get(blobOid)!;
        sendJson(res, 200, { type: 'file', encoding: 'base64', content: blob.data.toString('base64'), sha: blobOid, size: blob.data.length, name: path.split('/').pop(), path });
        return;
      }
      // Directory listing
      const flat = new Map<string, { oid: string; mode: string }>();
      flattenTree(repo, tree, '', flat);
      const children = new Map<string, { type: string; sha: string }>();
      for (const [p, e] of flat) {
        if (!p.startsWith(`${path}/`)) continue;
        const rest = p.slice(path.length + 1);
        const first = rest.split('/')[0];
        if (!children.has(first)) children.set(first, { type: rest.includes('/') ? 'dir' : 'file', sha: e.oid });
      }
      if (children.size === 0) { sendError(res, 404, 'Not Found'); return; }
      sendJson(res, 200, [...children.entries()].map(([name, e]) => ({ type: e.type, name, path: `${path}/${name}`, sha: e.sha })));
      return;
    }
    if ((method === 'PUT' || method === 'DELETE') && tail.length >= 2) {
      const payload = await readJson();
      if (payload === null) return;
      const tip = headOid(repo);
      const branch = str(payload.branch, repo.defaultBranch);
      const branchTip = resolveRef(repo, branch) ?? tip;
      const message = str(payload.message);
      if (method === 'PUT') {
        if (!message) { sendError(res, 422, 'message is required'); return; }
        if (typeof payload.content !== 'string') { sendError(res, 422, 'content is required'); return; }
        const newBlob = Buffer.from(payload.content, 'base64');
        const newBlobOid = putObject(repo, 'blob', newBlob);
        const tree = treeOfCommit(repo, branchTip);
        const currentBlobOid = blobAtPath(repo, tree, path);
        const isUpdate = currentBlobOid !== null;
        if (isUpdate && typeof payload.sha === 'string' && payload.sha !== currentBlobOid) {
          sendError(res, 409, 'sha does not match the current blob');
          return;
        }
        const newTree = setPathInTree(repo, tree, path.split('/'), newBlobOid);
        const ts = Math.floor(Date.now() / 1000);
        const parents = branchTip === ZERO_OID ? [] : [branchTip];
        const commitOid = putObject(repo, 'commit', buildCommit(newTree, parents, message, SERVER_IDENTITY, SERVER_IDENTITY, ts));
        repo.refs.set(`refs/heads/${branch}`, commitOid);
        repo.packCache.clear();
        sendJson(res, isUpdate ? 200 : 201, { content: { sha: newBlobOid, encoding: 'base64' }, commit: { sha: commitOid } });
        return;
      }
      // DELETE
      if (!message) { sendError(res, 422, 'message is required'); return; }
      const tree = treeOfCommit(repo, branchTip);
      const currentBlobOid = blobAtPath(repo, tree, path);
      if (!currentBlobOid) { sendError(res, 404, 'Not Found'); return; }
      if (typeof payload.sha === 'string' && payload.sha !== currentBlobOid) {
        sendError(res, 409, 'sha does not match the current blob');
        return;
      }
      const newTree = setPathInTree(repo, tree, path.split('/'), null);
      const ts = Math.floor(Date.now() / 1000);
      const commitOid = putObject(repo, 'commit', buildCommit(newTree, branchTip === ZERO_OID ? [] : [branchTip], message, SERVER_IDENTITY, SERVER_IDENTITY, ts));
      repo.refs.set(`refs/heads/${branch}`, commitOid);
      repo.packCache.clear();
      sendJson(res, 200, { commit: { sha: commitOid } });
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  // /labels
  if (head === 'labels') {
    if (method === 'POST' && tail.length === 1) {
      const payload = await readJson();
      if (payload === null) return;
      const name = str(payload.name).trim();
      if (!name) { sendError(res, 422, 'name is required'); return; }
      const label: Label = { name, color: str(payload.color, 'ffffff') };
      repo.labels.set(name, label);
      sendJson(res, 201, label);
      return;
    }
    if (method === 'GET' && tail.length === 1) {
      sendJson(res, 200, [...repo.labels.values()]);
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  sendError(res, 404, 'Not Found');
}

// ---------------------------------------------------------------- GraphQL v4

const INTROSPECTION_FIELDS: Record<string, string[]> = {
  Issue: ['id', 'number', 'title', 'body', 'state', 'author', 'createdAt', 'updatedAt', 'labels', 'comments', 'url', 'closed', 'locked', 'milestone'],
  PullRequest: ['id', 'number', 'title', 'body', 'state', 'headRefName', 'baseRefName', 'headRef', 'baseRef', 'mergeable', 'merged', 'mergedAt', 'mergeCommit', 'files', 'author', 'createdAt', 'updatedAt', 'url', 'closed', 'additions', 'deletions', 'changedFiles'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'description', 'isPrivate', 'createdAt', 'updatedAt', 'url', 'branches', 'commits'],
  User: ['id', 'login', 'name', 'avatarUrl', 'url'],
  SearchType: [],
};
const SEARCH_TYPE_ENUM_VALUES = ['ISSUE', 'REPOSITORY', 'USER', 'CODE', 'DISCUSSION', 'COMMIT'];

function gqlIssueState(issue: Issue): string { return issue.state === 'open' ? 'OPEN' : 'CLOSED'; }
function gqlPullState(pull: Pull): string { return pull.merged ? 'MERGED' : pull.state === 'open' ? 'OPEN' : 'CLOSED'; }
function gqlPullMergeable(repo: Repo, pull: Pull): string {
  if (!resolveRef(repo, pull.headRef)) return 'UNKNOWN';
  return prConflict(repo, pull) ? 'CONFLICTING' : 'MERGEABLE';
}

function gqlRepoFields(repo: Repo): Record<string, unknown> {
  return {
    id: globalId('Repository', repo.owner, repo.name),
    databaseId: repo.databaseId,
    name: repo.name,
    nameWithOwner: repo.fullName,
    owner: { login: repo.owner },
    defaultBranchRef: { name: repo.defaultBranch },
    viewerPermission: 'ADMIN',
    hasIssuesEnabled: true,
  };
}

function gqlIssueFields(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    id: globalId('Issue', repo.owner, repo.name, issue.number),
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: gqlIssueState(issue),
  };
}

function gqlPullFields(repo: Repo, pull: Pull): Record<string, unknown> {
  return {
    id: globalId('PullRequest', repo.owner, repo.name, pull.number),
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: gqlPullState(pull),
    headRefName: pull.headRef,
    baseRefName: pull.baseRef,
    mergeable: gqlPullMergeable(repo, pull),
    merged: pull.merged,
    files: { nodes: pull.changedFiles.map((f) => ({ path: f.filename })) },
  };
}

function encodeCursor(number: number): string {
  return Buffer.from(`cursor:${number}`, 'utf8').toString('base64');
}
function decodeCursor(cursor: string | null | undefined): number {
  if (typeof cursor !== 'string' || cursor === '') return 0;
  try {
    const raw = Buffer.from(cursor, 'base64').toString('utf8');
    const m = /^cursor:(\d+)$/.exec(raw);
    if (m) return Number(m[1]);
  } catch { /* fall through */ }
  return 0;
}

interface GqlResult { data: Record<string, unknown>; errors?: Array<{ message: string }>; }

function executeGraphQL(query: string, variables: Record<string, unknown>): GqlResult {
  const opMatch = /\b(?:query|mutation)\s+([A-Za-z_][A-Za-z0-9_]*)/.exec(query);
  const op = opMatch ? opMatch[1] : '';
  const vars = variables ?? {};
  const getRepoVar = (): Repo | null => {
    const owner = str(vars.owner);
    const name = str(vars.name);
    if (!owner || !name) return null;
    const repo = getRepo(owner, name);
    return repo && owner === VIEWER_LOGIN ? repo : null;
  };
  switch (op) {
    case 'ViewerLogin':
      return { data: { viewer: { login: VIEWER_LOGIN } } };
    case 'ViewerInvalidField':
      return {
        data: { viewer: null },
        errors: [{ message: 'Cannot query field "noSuchFieldOnViewer" on type "User"' }],
      };
    case 'Issue_fields':
    case 'PullRequestAndRepositoryFields':
    case 'SearchType_enumValues': {
      const data: Record<string, unknown> = {};
      const re = /([A-Za-z_][A-Za-z0-9_]*):\s*__type\(name:\s*"([^"]+)"\)/g;
      let m: RegExpExecArray | null;
      let found = false;
      while ((m = re.exec(query)) !== null) {
        found = true;
        const alias = m[1];
        const typeName = m[2];
        if (typeName === 'SearchType') {
          data[alias] = { enumValues: SEARCH_TYPE_ENUM_VALUES.map((n) => ({ name: n })) };
        } else if (INTROSPECTION_FIELDS[typeName] !== undefined) {
          data[alias] = { fields: INTROSPECTION_FIELDS[typeName].map((n) => ({ name: n })) };
        } else {
          data[alias] = null;
        }
      }
      if (!found) return { data: {}, errors: [{ message: 'Unknown operation' }] };
      return { data };
    }
    case 'RepositoryFields': {
      const repo = getRepoVar();
      if (!repo) return { data: { repository: null } };
      return { data: { repository: gqlRepoFields(repo) } };
    }
    case 'OpenIssues': {
      const repo = getRepoVar();
      if (!repo) return { data: { repository: null } };
      const first = typeof vars.first === 'number' ? vars.first : 10;
      const nodes = [...repo.issues]
        .filter((i) => i.state === 'open')
        .sort((a, b) => b.createdSeq - a.createdSeq)
        .slice(0, first)
        .map((i) => gqlIssueFields(repo, i));
      return { data: { repository: { issues: { nodes } } } };
    }
    case 'IssueByNumber': {
      const repo = getRepoVar();
      if (!repo) return { data: { repository: null } };
      const n = Number(vars.number);
      const issue = repo.issues.find((i) => i.number === n);
      return { data: { repository: { issue: issue ? gqlIssueFields(repo, issue) : null } } };
    }
    case 'IssueCreate': {
      const input = isRecord(vars.input) ? vars.input : {};
      const decoded = typeof input.repositoryId === 'string' ? decodeGlobalId(input.repositoryId) : null;
      if (!decoded || decoded.type !== 'Repository') return { data: {}, errors: [{ message: 'Repository not found' }] };
      const repo = getRepo(decoded.owner, decoded.name);
      if (!repo) return { data: {}, errors: [{ message: 'Repository not found' }] };
      const title = str(input.title);
      if (!title) return { data: {}, errors: [{ message: 'title is required' }] };
      const issue = createIssueRecord(repo, title, str(input.body), []);
      return { data: { createIssue: { issue: { number: issue.number, id: globalId('Issue', repo.owner, repo.name, issue.number) } } } };
    }
    case 'IssueClose': {
      const input = isRecord(vars.input) ? vars.input : {};
      const decoded = typeof input.issueId === 'string' ? decodeGlobalId(input.issueId) : null;
      if (!decoded || decoded.type !== 'Issue' || decoded.num === null) return { data: {}, errors: [{ message: 'Issue not found' }] };
      const repo = getRepo(decoded.owner, decoded.name);
      const issue = repo?.issues.find((i) => i.number === decoded.num);
      if (!repo || !issue) return { data: {}, errors: [{ message: 'Issue not found' }] };
      issue.state = 'closed';
      issue.updatedAt = nowIso();
      refreshIssueCache(repo, issue);
      return { data: { closeIssue: { issue: { number: issue.number, id: globalId('Issue', repo.owner, repo.name, issue.number), state: 'CLOSED' } } } };
    }
    case 'PullRequests': {
      const repo = getRepoVar();
      if (!repo) return { data: { repository: null } };
      const first = typeof vars.first === 'number' ? vars.first : 5;
      const nodes = repo.pulls
        .filter((p) => p.state === 'open')
        .slice(0, first)
        .map((p) => gqlPullFields(repo, p));
      return { data: { repository: { pullRequests: { nodes } } } };
    }
    case 'PullRequestFiles':
    case 'PullRequestId': {
      const repo = getRepoVar();
      if (!repo) return { data: { repository: null } };
      const n = Number(vars.number);
      const pull = repo.pulls.find((p) => p.number === n);
      return { data: { repository: { pullRequest: pull ? gqlPullFields(repo, pull) : null } } };
    }
    case 'PullRequestCreate': {
      const input = isRecord(vars.input) ? vars.input : {};
      const decoded = typeof input.repositoryId === 'string' ? decodeGlobalId(input.repositoryId) : null;
      if (!decoded || decoded.type !== 'Repository') return { data: {}, errors: [{ message: 'Repository not found' }] };
      const repo = getRepo(decoded.owner, decoded.name);
      if (!repo) return { data: {}, errors: [{ message: 'Repository not found' }] };
      const pull = createPullRecord(repo, str(input.title), str(input.body), str(input.headRefName), str(input.baseRefName));
      if (!pull) return { data: {}, errors: [{ message: 'head or base branch not found' }] };
      return { data: { createPullRequest: { pullRequest: gqlPullFields(repo, pull) } } };
    }
    case 'MergePullRequest': {
      const input = isRecord(vars.input) ? vars.input : {};
      const decoded = typeof input.pullRequestId === 'string' ? decodeGlobalId(input.pullRequestId) : null;
      if (!decoded || decoded.type !== 'PullRequest' || decoded.num === null) return { data: {}, errors: [{ message: 'Pull request not found' }] };
      const repo = getRepo(decoded.owner, decoded.name);
      const pull = repo?.pulls.find((p) => p.number === decoded.num);
      if (!repo || !pull) return { data: {}, errors: [{ message: 'Pull request not found' }] };
      mergePullRecord(repo, pull);
      return { data: { mergePullRequest: { pullRequest: gqlPullFields(repo, pull) } } };
    }
    case 'AddComment': {
      const input = isRecord(vars.input) ? vars.input : {};
      const decoded = typeof input.subjectId === 'string' ? decodeGlobalId(input.subjectId) : null;
      if (!decoded || decoded.type !== 'Issue' || decoded.num === null) return { data: {}, errors: [{ message: 'Subject not found' }] };
      const repo = getRepo(decoded.owner, decoded.name);
      const issue = repo?.issues.find((i) => i.number === decoded.num);
      if (!repo || !issue) return { data: {}, errors: [{ message: 'Subject not found' }] };
      const comment: IssueComment = { id: repo.commentSeq++, body: str(input.body), createdSeq: ++globalCreatedSeq };
      issue.comments.push(comment);
      return {
        data: {
          addComment: {
            commentEdge: {
              node: {
                id: globalId('Comment', repo.owner, repo.name, comment.id),
                body: comment.body,
              },
            },
          },
        },
      };
    }
    case 'NodeRepository': {
      const decoded = typeof vars.id === 'string' ? decodeGlobalId(vars.id) : null;
      if (!decoded || decoded.type !== 'Repository') return { data: { node: null } };
      const repo = getRepo(decoded.owner, decoded.name);
      if (!repo) return { data: { node: null } };
      return { data: { node: { id: globalId('Repository', repo.owner, repo.name), name: repo.name, nameWithOwner: repo.fullName } } };
    }
    case 'IssuesPage': {
      const repo = getRepoVar();
      if (!repo) return { data: { repository: null } };
      const first = typeof vars.first === 'number' ? vars.first : 5;
      const afterNum = decodeCursor(typeof vars.after === 'string' ? vars.after : null);
      const ascending = [...repo.issues].sort((a, b) => a.number - b.number).filter((i) => i.number > afterNum);
      const page = ascending.slice(0, first);
      const hasNextPage = ascending.length > first;
      const endCursor = page.length > 0 ? encodeCursor(page[page.length - 1].number) : null;
      return {
        data: {
          repository: {
            issues: {
              nodes: page.map((i) => ({ number: i.number })),
              pageInfo: { hasNextPage, endCursor },
            },
          },
        },
      };
    }
    default:
      return { data: {}, errors: [{ message: 'Unknown operation' }] };
  }
}

async function handleGraphQL(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const body = await readBody(req);
  let payload: unknown;
  try {
    payload = parseJsonBody(body);
  } catch {
    sendJson(res, 400, { message: 'Invalid JSON' });
    return;
  }
  const ops = Array.isArray(payload) ? payload : [payload];
  const results: unknown[] = [];
  for (const op of ops) {
    if (!isRecord(op) || typeof op.query !== 'string') {
      results.push({ data: {}, errors: [{ message: 'query is required' }] });
      continue;
    }
    const variables = isRecord(op.variables) ? op.variables : {};
    results.push(executeGraphQL(op.query, variables));
  }
  sendJson(res, 200, Array.isArray(payload) ? results : results[0]);
}

// ---------------------------------------------------------------- MCP

const MCP_VERSIONS = ['2026-07-28', '2025-11-25'];
const MCP_SERVER_INFO = { name: 'himeko-forge', version: '1.0.0' };

interface McpToolDef {
  name: string; description: string;
  inputSchema: { type: string; properties: Record<string, { type: string; description: string }>; required: string[] };
}

const MCP_TOOLS: McpToolDef[] = [
  {
    name: 'create_repo', description: 'Create a repository',
    inputSchema: { type: 'object', properties: { name: { type: 'string', description: 'Repository name' }, description: { type: 'string', description: 'Repository description' }, private: { type: 'boolean', description: 'Whether the repository is private' } }, required: ['name'] },
  },
  {
    name: 'get_repo', description: 'Get a repository',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner' }, repo: { type: 'string', description: 'Repository name' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_issue', description: 'Create an issue',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Issue title' }, body: { type: 'string', description: 'Issue body' } }, required: ['owner', 'repo', 'title'] },
  },
  {
    name: 'list_issues', description: 'List issues',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner' }, repo: { type: 'string', description: 'Repository name' }, state: { type: 'string', description: 'Issue state filter' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_pull_request', description: 'Create a pull request',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Pull request title' }, head: { type: 'string', description: 'Head branch' }, base: { type: 'string', description: 'Base branch' }, body: { type: 'string', description: 'Pull request body' } }, required: ['owner', 'repo', 'title', 'head', 'base'] },
  },
  {
    name: 'merge_pull_request', description: 'Merge a pull request',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner' }, repo: { type: 'string', description: 'Repository name' }, pull_number: { type: 'number', description: 'Pull request number' } }, required: ['owner', 'repo', 'pull_number'] },
  },
];

// Byte-identical tools/list answer, serialized once.
const MCP_TOOLS_LIST_JSON = JSON.stringify({ tools: MCP_TOOLS });

function mcpResult(id: unknown, result: unknown): Record<string, unknown> {
  return { jsonrpc: '2.0', id, result };
}
function mcpError(id: unknown, code: number, message: string, data?: unknown): Record<string, unknown> {
  const err: Record<string, unknown> = { code, message };
  if (data !== undefined) err.data = data;
  return { jsonrpc: '2.0', id, error: err };
}
function mcpToolTextResult(id: unknown, result: unknown, isError: boolean): Record<string, unknown> {
  return mcpResult(id, {
    content: [{ type: 'text', text: JSON.stringify(result) }],
    structuredContent: result,
    isError,
  });
}

/**
 * Dispatch one MCP tools/call by tool name (suffix match, case-insensitive).
 * Returns the tool result object, or { __isError: true, ... } for a tool-level error.
 */
function dispatchMcpTool(name: string, args: Record<string, unknown>): { result: unknown; isError: boolean } {
  const lower = name.toLowerCase();
  const missing = (field: string): { result: unknown; isError: boolean } => ({
    result: { error: `missing required argument: ${field}` },
    isError: true,
  });
  if (lower.endsWith('create_repo')) {
    if (typeof args.name !== 'string' || !args.name) return missing('name');
    if (getRepo(VIEWER_LOGIN, args.name)) return { result: { error: `Repository "${args.name}" already exists` }, isError: true };
    const repo = createRepoRecord(args.name, args.private === true, str(args.description), 'main');
    return { result: serializeRepo(repo), isError: false };
  }
  if (lower.endsWith('get_repo')) {
    if (typeof args.owner !== 'string' || !args.owner) return missing('owner');
    if (typeof args.repo !== 'string' || !args.repo) return missing('repo');
    const repo = getRepo(args.owner, args.repo);
    if (!repo || args.owner !== VIEWER_LOGIN) return { result: { error: 'Not Found' }, isError: true };
    return { result: serializeRepo(repo), isError: false };
  }
  if (lower.endsWith('create_issue')) {
    if (typeof args.owner !== 'string' || !args.owner) return missing('owner');
    if (typeof args.repo !== 'string' || !args.repo) return missing('repo');
    if (typeof args.title !== 'string' || !args.title) return missing('title');
    const repo = getRepo(args.owner, args.repo);
    if (!repo || args.owner !== VIEWER_LOGIN) return { result: { error: 'Not Found' }, isError: true };
    const issue = createIssueRecord(repo, args.title, str(args.body), []);
    return { result: JSON.parse(issue.jsonCache) as Record<string, unknown>, isError: false };
  }
  if (lower.endsWith('list_issues')) {
    if (typeof args.owner !== 'string' || !args.owner) return missing('owner');
    if (typeof args.repo !== 'string' || !args.repo) return missing('repo');
    const repo = getRepo(args.owner, args.repo);
    if (!repo || args.owner !== VIEWER_LOGIN) return { result: { error: 'Not Found' }, isError: true };
    const state = str(args.state, 'open');
    const list = repo.issues.filter((i) => state === 'all' || i.state === state);
    return { result: list.map((i) => JSON.parse(i.jsonCache) as Record<string, unknown>), isError: false };
  }
  if (lower.endsWith('create_pull_request')) {
    if (typeof args.owner !== 'string' || !args.owner) return missing('owner');
    if (typeof args.repo !== 'string' || !args.repo) return missing('repo');
    if (typeof args.title !== 'string' || !args.title) return missing('title');
    if (typeof args.head !== 'string' || !args.head) return missing('head');
    if (typeof args.base !== 'string' || !args.base) return missing('base');
    const repo = getRepo(args.owner, args.repo);
    if (!repo || args.owner !== VIEWER_LOGIN) return { result: { error: 'Not Found' }, isError: true };
    const pull = createPullRecord(repo, args.title, str(args.body), args.head, args.base);
    if (!pull) return { result: { error: 'head or base branch not found' }, isError: true };
    return { result: serializePull(repo, pull), isError: false };
  }
  if (lower.endsWith('merge_pull_request')) {
    if (typeof args.owner !== 'string' || !args.owner) return missing('owner');
    if (typeof args.repo !== 'string' || !args.repo) return missing('repo');
    if (typeof args.pull_number !== 'number') return missing('pull_number');
    const repo = getRepo(args.owner, args.repo);
    if (!repo || args.owner !== VIEWER_LOGIN) return { result: { error: 'Not Found' }, isError: true };
    const pull = repo.pulls.find((p) => p.number === args.pull_number);
    if (!pull) return { result: { error: 'Not Found' }, isError: true };
    const oid = mergePullRecord(repo, pull);
    if (oid === null) return { result: { error: 'Merge conflict' }, isError: true };
    return { result: { merged: true, sha: oid }, isError: false };
  }
  return { result: { error: `unknown tool: ${name}` }, isError: true };
}

async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const body = await readBody(req);
  let payload: unknown;
  try {
    payload = parseJsonBody(body);
  } catch {
    sendJson(res, 400, mcpError(null, -32700, 'Parse error'));
    return;
  }
  if (!isRecord(payload)) {
    sendJson(res, 400, mcpError(null, -32600, 'Invalid Request'));
    return;
  }
  const id = payload.id === undefined ? null : payload.id;
  const method = str(payload.method);
  const params = isRecord(payload.params) ? payload.params : {};
  // Notifications carry no id: answer 202 with an empty body.
  if (method.startsWith('notifications/')) {
    res.writeHead(202, { 'x-github-request-id': `req-${++requestCounter}` });
    res.end();
    return;
  }
  if (method === 'server/discover') {
    const result: Record<string, unknown> = {
      supportedVersions: MCP_VERSIONS,
      capabilities: { tools: {} },
      serverInfo: MCP_SERVER_INFO,
      _meta: { name: MCP_SERVER_INFO.name, version: MCP_SERVER_INFO.version },
    };
    sendJson(res, 200, mcpResult(id, result));
    return;
  }
  if (method === 'initialize') {
    const requested = str(params.protocolVersion);
    const meta = isRecord(params._meta) ? params._meta : {};
    const headerVersion = req.headers['mcp-protocol-version'];
    const versions = [requested, str(meta.protocolVersion), typeof headerVersion === 'string' ? headerVersion : ''].filter((v) => v !== '');
    const badVersion = versions.find((v) => !MCP_VERSIONS.includes(v));
    if (badVersion !== undefined) {
      sendJson(res, 200, mcpError(id, -32022, `Unsupported protocol version: ${badVersion}`, { supported: MCP_VERSIONS }));
      return;
    }
    const metaBad = Object.entries(meta).some(([k, v]) => k === 'protocolVersion' && typeof v === 'string' && !MCP_VERSIONS.includes(v));
    if (metaBad) {
      sendJson(res, 200, mcpError(id, -32020, 'Protocol version mismatch in _meta', { supported: MCP_VERSIONS }));
      return;
    }
    const result = {
      protocolVersion: '2025-11-25',
      capabilities: { tools: {} },
      serverInfo: MCP_SERVER_INFO,
    };
    sendJson(res, 200, mcpResult(id, result), { 'mcp-session-id': `sess-${randomUUID()}` });
    return;
  }
  if (method === 'tools/list') {
    res.writeHead(200, {
      'content-type': 'application/json; charset=utf-8',
      'x-github-request-id': `req-${++requestCounter}`,
    });
    res.end(JSON.stringify({ jsonrpc: '2.0', id, result: JSON.parse(MCP_TOOLS_LIST_JSON) as unknown }));
    return;
  }
  if (method === 'tools/call') {
    const name = str(params.name);
    const args = isRecord(params.arguments) ? params.arguments : {};
    const known = MCP_TOOLS.some((t) => t.name === name || name.toLowerCase().endsWith(t.name));
    if (!known) {
      sendJson(res, 200, mcpError(id, -32601, `Method not found: ${name}`));
      return;
    }
    const { result, isError } = dispatchMcpTool(name, args);
    sendJson(res, 200, mcpToolTextResult(id, result, isError));
    return;
  }
  sendJson(res, 200, mcpError(id, -32601, `Method not found: ${method}`));
}

// ---------------------------------------------------------------- router + lifecycle

const server = createServer((req, res) => {
  void (async () => {
    try {
      const url = new URL(req.url ?? '/', 'http://localhost');
      const method = req.method ?? 'GET';
      const pathname = url.pathname;
      // Unauthenticated health check.
      if (pathname === '/healthz' && method === 'GET') {
        sendJson(res, 200, { ok: true });
        return;
      }
      if (!isAuthed(req)) {
        sendError(res, 401, 'Requires authentication');
        return;
      }
      // Git smart HTTP: /{owner}/{repo}.git/...
      const gitMatch = /^\/([^/]+)\/([^/]+)\.git\/(.+)$/.exec(pathname);
      if (gitMatch) {
        const owner = gitMatch[1];
        const repoName = gitMatch[2];
        const sub = gitMatch[3];
        const repo = getRepo(owner, repoName);
        if (!repo || owner !== VIEWER_LOGIN) { sendError(res, 404, 'Not Found'); return; }
        if (method === 'GET' && sub === 'info/refs') {
          const service = url.searchParams.get('service') ?? '';
          if (service === 'git-upload-pack') { handleInfoRefsUploadPack(repo, req, res); return; }
          if (service === 'git-receive-pack') { handleInfoRefsReceivePack(repo, req, res); return; }
          sendError(res, 400, 'unknown service');
          return;
        }
        if (method === 'POST' && sub === 'git-upload-pack') {
          const body = await readBody(req);
          handleUploadPack(repo, req, res, body);
          return;
        }
        if (method === 'POST' && sub === 'git-receive-pack') {
          const body = await readBody(req);
          handleReceivePack(repo, req, res, body);
          return;
        }
        sendError(res, 404, 'Not Found');
        return;
      }
      // REST v3
      if (pathname === '/api/v3' || pathname.startsWith('/api/v3/')) {
        await handleRest(req, res, url);
        return;
      }
      // GraphQL v4
      if (pathname === '/api/graphql' && method === 'POST') {
        await handleGraphQL(req, res);
        return;
      }
      // MCP
      if (pathname === '/mcp' && method === 'POST') {
        await handleMcp(req, res);
        return;
      }
      sendError(res, 404, 'Not Found');
    } catch (err) {
      if (!res.headersSent) {
        const status = (err as { status?: number }).status ?? 500;
        sendError(res, status, (err as Error).message || 'Internal Server Error');
      } else {
        res.destroy();
      }
    }
  })();
});

server.keepAliveTimeout = 30_000;
server.headersTimeout = 31_000;

/** Small fetch helper for the lifecycle calls (uses the global fetch). */
async function envCall(method: string, path: string, body?: unknown): Promise<{ status: number; json: unknown }> {
  const init: RequestInit = { method, headers: { 'content-type': 'application/json' } };
  if (body !== undefined) init.body = JSON.stringify(body);
  const response = await fetch(`${ENV_URL}${path}`, init);
  const text = await response.text();
  let json: unknown = null;
  try { json = JSON.parse(text); } catch { /* non-JSON body */ }
  return { status: response.status, json };
}

const sleep = (ms: number): Promise<void> => new Promise((resolve) => setTimeout(resolve, ms));

async function main(): Promise<void> {
  await new Promise<void>((resolve) => server.listen(0, () => resolve()));
  const address = server.address();
  if (!address || typeof address === 'string') {
    process.stderr.write('[entry] could not determine the listening port\n');
    process.exit(1);
  }
  const port = address.port;
  process.stdout.write(`[entry] listening on port ${port}\n`);
  // Register with the environment, retrying transient failures.
  let delay = 250;
  for (;;) {
    try {
      const { status } = await envCall('POST', '/register', { port });
      if (status === 200 || status === 409) break;
      if (status === 400 || status === 405) {
        process.stderr.write(`[entry] register rejected with HTTP ${status}\n`);
        process.exit(1);
      }
    } catch (err) {
      process.stderr.write(`[entry] register attempt failed: ${(err as Error).message}\n`);
    }
    await sleep(delay);
    delay = Math.min(delay * 2, 2000);
  }
  process.stdout.write('[entry] registered\n');
  // Poll until the environment says the run is done, then exit 0.
  delay = 250;
  for (;;) {
    try {
      const { status, json } = await envCall('GET', '/done');
      if (status === 200 && isRecord(json) && json.done === true) {
        process.stdout.write('[entry] done\n');
        server.close();
        process.exit(0);
      }
    } catch (err) {
      process.stderr.write(`[entry] done poll failed: ${(err as Error).message}\n`);
    }
    await sleep(delay);
    delay = Math.min(delay * 2, 2000);
  }
}

void main();
