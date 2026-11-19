// forge — a GitHub-compatible git forge core, from scratch.
// Node >= 22, standard library only (http, fs, zlib, crypto, path).
// Implements: git object model (SHA-1, zlib loose semantics in-memory),
// packfile read/write (incl. ofs/ref deltas), smart HTTP (clone/push,
// full + shallow), GitHub REST v3 subset, a real GraphQL subset (parser +
// executor: connections, fragments, mutations), MCP with github-mcp-server
// tool shapes, deterministic state export. No git binary, no services.
'use strict';
const http = require('node:http');
const fs = require('node:fs');
const path = require('node:path');
const zlib = require('node:zlib');
const crypto = require('node:crypto');

const ZERO_SHA = '0000000000000000000000000000000000000000';
const TYPE_NAMES = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag', 6: 'ofs-delta', 7: 'ref-delta' };
const TYPE_IDS = { commit: 1, tree: 2, blob: 3, tag: 4 };
const BASE_TIME = 1704067200; // 2024-01-01T00:00:00Z, deterministic clock base

// ---------------- util ----------------
function sha1hex(buf) { return crypto.createHash('sha1').update(buf).digest('hex'); }
function sha1buf(buf) { return crypto.createHash('sha1').update(buf).digest(); }
function isHex40(s) { return typeof s === 'string' && /^[0-9a-f]{40}$/.test(s); }
function sortKeysDeep(v) {
  if (Array.isArray(v)) return v.map(sortKeysDeep);
  if (v && typeof v === 'object') {
    const out = {};
    for (const k of Object.keys(v).sort()) out[k] = sortKeysDeep(v[k]);
    return out;
  }
  return v;
}
function canonicalJSON(v) { return JSON.stringify(sortKeysDeep(v)) + '\n'; }

// ---------------- git objects ----------------
function hashObject(type, data) {
  const header = Buffer.from(type + ' ' + data.length + '\0', 'utf8');
  return sha1hex(Buffer.concat([header, data]));
}
function parseCommit(data) {
  const text = data.toString('utf8');
  const blank = text.indexOf('\n\n');
  const head = blank >= 0 ? text.slice(0, blank) : text;
  const message = blank >= 0 ? text.slice(blank + 2) : '';
  let tree = null; const parents = [];
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
  }
  return { tree, parents, message, raw: text };
}
function parseTree(data) {
  const entries = []; let i = 0;
  while (i < data.length) {
    const sp = data.indexOf(0x20, i);
    const mode = data.toString('utf8', i, sp);
    const nul = data.indexOf(0x00, sp);
    const name = data.toString('utf8', sp + 1, nul);
    const sha = data.toString('hex', nul + 1, nul + 21);
    entries.push({ mode, name, sha });
    i = nul + 21;
  }
  return entries;
}
function serializeTree(entries) {
  const sorted = [...entries].sort((a, b) => {
    const an = a.mode === '40000' || a.mode === '040000' ? a.name + '/' : a.name;
    const bn = b.mode === '40000' || b.mode === '040000' ? b.name + '/' : b.name;
    return an < bn ? -1 : an > bn ? 1 : 0;
  });
  const parts = [];
  for (const e of sorted) {
    parts.push(Buffer.from(e.mode + ' ' + e.name + '\0', 'utf8'));
    parts.push(Buffer.from(e.sha, 'hex'));
  }
  return Buffer.concat(parts);
}
function parseTag(data) {
  const text = data.toString('utf8');
  let object = null, type = null;
  for (const line of text.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7).trim();
    else if (line.startsWith('type ')) type = line.slice(5).trim();
    else if (line === '') break;
  }
  return { object, type };
}

// ---------------- packfiles ----------------
// Find minimal prefix length that inflates (inflateSync ignores trailing
// bytes and throws "unexpected end of file" when truncated).
function inflateAt(buf, offset) {
  const remaining = buf.length - offset;
  let lo = 1, hi = 1, ok = false;
  while (true) {
    const tryLen = Math.min(hi, remaining);
    try { zlib.inflateSync(buf.subarray(offset, offset + tryLen)); ok = true; hi = tryLen; break; }
    catch (e) {
      if (!/unexpected end of file/.test(e.message)) throw e;
      if (tryLen >= remaining) break;
      hi *= 2;
    }
  }
  if (!ok) throw new Error('unexpected end of file');
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    try { zlib.inflateSync(buf.subarray(offset, offset + mid)); hi = mid; }
    catch (e) { if (!/unexpected end of file/.test(e.message)) throw e; lo = mid + 1; }
  }
  const data = zlib.inflateSync(buf.subarray(offset, offset + lo));
  return { data, consumed: lo };
}
function applyDelta(base, delta) {
  let i = 0;
  function varint() {
    let v = 0, shift = 0;
    while (true) { const b = delta[i++]; v |= (b & 0x7f) << shift; shift += 7; if (!(b & 0x80)) break; }
    return v;
  }
  const srcSize = varint(); const dstSize = varint();
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  const out = [];
  while (i < delta.length) {
    const op = delta[i++];
    if (op & 0x80) {
      let off = 0, size = 0;
      if (op & 0x01) off = delta[i++];
      if (op & 0x02) off |= delta[i++] << 8;
      if (op & 0x04) off |= delta[i++] << 16;
      if (op & 0x08) off |= delta[i++] << 24;
      if (op & 0x10) size = delta[i++];
      if (op & 0x20) size |= delta[i++] << 8;
      if (op & 0x40) size |= delta[i++] << 16;
      if (size === 0) size = 0x10000;
      out.push(base.subarray(off, off + size));
    } else if (op > 0) { out.push(delta.subarray(i, i + op)); i += op; }
    else throw new Error('delta opcode 0');
  }
  const result = Buffer.concat(out);
  if (result.length !== dstSize) throw new Error('delta result size mismatch');
  return result;
}
// Parse a pack buffer into raw entries (deltas unresolved).
function parsePack(buf) {
  if (buf.length < 12 || buf.toString('utf8', 0, 4) !== 'PACK') throw new Error('bad pack header');
  const version = buf.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error('bad pack version');
  const count = buf.readUInt32BE(8);
  let off = 12;
  const entries = []; const byOffset = new Map();
  for (let n = 0; n < count; n++) {
    const start = off;
    let b = buf[off++];
    const typeId = (b >> 4) & 0x7;
    let size = b & 0x0f; let shift = 4;
    while (b & 0x80) { b = buf[off++]; size |= (b & 0x7f) << shift; shift += 7; }
    let baseSha = null, baseOffset = null;
    if (typeId === 7) { baseSha = buf.toString('hex', off, off + 20); off += 20; }
    else if (typeId === 6) {
      let c = buf[off++]; let rel = c & 0x7f;
      while (c & 0x80) { c = buf[off++]; rel = ((rel + 1) << 7) | (c & 0x7f); }
      baseOffset = start - rel;
    }
    const { data, consumed } = inflateAt(buf, off);
    off += consumed;
    if (data.length !== size) throw new Error('pack object size mismatch');
    const entry = { typeId, data, baseSha, baseOffset, offset: start };
    entries.push(entry); byOffset.set(start, entry);
  }
  return { entries, byOffset, endOffset: off };
}
// Resolve parsed pack entries into {type, data} using a base lookup fn.
function resolvePack(parsed, lookupBase) {
  const resolved = new Map(); // entry -> {type,data}
  const byOffsetResolved = new Map();
  let progress = true;
  const pending = new Set(parsed.entries);
  let guard = 0;
  while (pending.size && progress && guard++ < 10000) {
    progress = false;
    for (const e of [...pending]) {
      if (e.typeId >= 1 && e.typeId <= 4) {
        const r = { type: TYPE_NAMES[e.typeId], data: e.data };
        resolved.set(e, r); byOffsetResolved.set(e.offset, r); pending.delete(e); progress = true;
      } else if (e.typeId === 7) {
        let base = null;
        for (const [pe, pr] of resolved) if (hashObject(pr.type, pr.data) === e.baseSha) { base = pr; break; }
        if (!base && lookupBase) base = lookupBase(e.baseSha);
        if (base) {
          const r = { type: base.type, data: applyDelta(base.data, e.data) };
          resolved.set(e, r); byOffsetResolved.set(e.offset, r); pending.delete(e); progress = true;
        }
      } else if (e.typeId === 6) {
        const base = byOffsetResolved.get(e.baseOffset);
        if (base) {
          const r = { type: base.type, data: applyDelta(base.data, e.data) };
          resolved.set(e, r); byOffsetResolved.set(e.offset, r); pending.delete(e); progress = true;
        }
      }
    }
  }
  if (pending.size) throw new Error('unresolvable delta in pack (thin pack base missing?)');
  return [...resolved.values()];
}
function packObjectHeader(typeId, size) {
  const bytes = [];
  let b = ((typeId & 0x7) << 4) | (size & 0x0f);
  size >>= 4;
  while (size > 0) { bytes.push(b | 0x80); b = size & 0x7f; size >>= 7; }
  bytes.push(b);
  return Buffer.from(bytes);
}
function buildPack(objects) { // objects: [{type, data}] — full objects, no deltas
  const parts = [];
  const head = Buffer.alloc(12);
  head.write('PACK', 0, 'utf8'); head.writeUInt32BE(2, 4); head.writeUInt32BE(objects.length, 8);
  parts.push(head);
  for (const o of objects) {
    parts.push(packObjectHeader(TYPE_IDS[o.type], o.data.length));
    parts.push(zlib.deflateSync(o.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, sha1buf(body)]);
}

// ---------------- pkt-line ----------------
function pktLine(payload) {
  if (payload === null || payload === undefined) return Buffer.from('0000');
  const b = Buffer.isBuffer(payload) ? payload : Buffer.from(String(payload), 'utf8');
  const len = b.length + 4;
  return Buffer.concat([Buffer.from(len.toString(16).padStart(4, '0'), 'ascii'), b]);
}
function readPktLines(buf, start) {
  const lines = []; let off = start || 0;
  while (off + 4 <= buf.length) {
    const lenStr = buf.toString('ascii', off, off + 4);
    if (!/^[0-9a-f]{4}$/.test(lenStr)) break;
    const len = parseInt(lenStr, 16);
    if (len === 0) { off += 4; return { lines, next: off, flushed: true }; }
    if (len < 4 || off + len > buf.length) break;
    lines.push(buf.subarray(off + 4, off + len));
    off += len;
  }
  return { lines, next: off, flushed: false };
}

// ---------------- store ----------------
const DATA_DIR = process.env.FORGE_DATA_DIR || path.join(process.cwd(), 'data');
const STATE_FILE = path.join(DATA_DIR, 'state.json');

class Repo {
  constructor(owner, name) {
    this.owner = owner; this.name = name;
    this.description = ''; this.homepage = '';
    this.isPrivate = false; this.defaultBranch = 'main';
    this.head = 'refs/heads/main';
    this.objects = new Map(); // sha -> {type, data:Buffer}
    this.refs = new Map();    // ref -> sha
    this.issues = [];         // issue objects (plain JSON)
    this.pulls = [];
    this.nextNumber = 1;
    this.createdSeq = 0;
  }
  key() { return this.owner.toLowerCase() + '/' + this.name.toLowerCase(); }
  storeObject(type, data) {
    const sha = hashObject(type, data);
    if (!this.objects.has(sha)) this.objects.set(sha, { type, data: Buffer.from(data) });
    return sha;
  }
  getObject(sha) { return this.objects.get(sha) || null; }
  headSha() { return this.refs.get(this.head) || null; }
}

const state = {
  repos: new Map(), // key -> Repo
  seq: 0,           // deterministic logical clock (never wall-clock in exports)
  nextRepoId: 1,
  nextIssueId: 1,
};
function nextSeq() { return ++state.seq; }
function fakeISO(seq) { return new Date((BASE_TIME + seq) * 1000).toISOString().replace('.000Z', 'Z'); }
function getRepo(owner, name) {
  if (!owner || !name) return null;
  return state.repos.get((owner + '/' + name).toLowerCase()) || null;
}
function createRepo(owner, name, opts) {
  let r = getRepo(owner, name);
  if (r) return r;
  r = new Repo(owner, name);
  if (opts && opts.description) r.description = String(opts.description);
  if (opts && typeof opts.private === 'boolean') r.isPrivate = opts.private;
  if (opts && opts.default_branch) { r.defaultBranch = String(opts.default_branch); r.head = 'refs/heads/' + r.defaultBranch; }
  r.createdSeq = nextSeq();
  r.id = state.nextRepoId++;
  state.repos.set(r.key(), r);
  scheduleSave();
  return r;
}
function deleteRepo(owner, name) {
  const k = (owner + '/' + name).toLowerCase();
  const had = state.repos.delete(k);
  if (had) scheduleSave();
  return had;
}

// persistence (own store on disk; export excludes volatile fields)
let saveTimer = null;
function scheduleSave() {
  if (saveTimer) return;
  saveTimer = setTimeout(() => { saveTimer = null; saveState(); }, 50);
}
let saveInFlight = false, saveDirty = false;
function saveState() {
  // Persistence uses the same shape as the export but skips the deep key
  // sort (the export endpoint canonicalises separately); writes are async
  // and coalesced so mutation bursts do not stall the event loop.
  if (saveInFlight) { saveDirty = true; return; }
  saveInFlight = true;
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    const text = JSON.stringify(stateDump());
    const tmp = STATE_FILE + '.tmp';
    fs.writeFile(tmp, text, (err) => {
      if (err) { saveInFlight = false; return; }
      fs.rename(tmp, STATE_FILE, () => {
        saveInFlight = false;
        if (saveDirty) { saveDirty = false; saveState(); }
      });
    });
  } catch (e) { saveInFlight = false; /* in-memory store is authoritative */ }
}
function stateDump() {
  const repos = [...state.repos.values()].sort((a, b) => a.key() < b.key() ? -1 : 1).map(r => {
    const objects = {};
    for (const sha of [...r.objects.keys()].sort()) {
      const o = r.objects.get(sha);
      objects[sha] = { type: o.type, data: o.data.toString('base64') };
    }
    const refs = {};
    for (const ref of [...r.refs.keys()].sort()) refs[ref] = r.refs.get(ref);
    return {
      owner: r.owner, name: r.name, id: r.id, description: r.description,
      private: r.isPrivate, default_branch: r.defaultBranch, head: r.head,
      createdSeq: r.createdSeq, nextNumber: r.nextNumber,
      refs, objects,
      issues: [...r.issues].sort((a, b) => a.number - b.number),
      pulls: [...r.pulls].sort((a, b) => a.number - b.number),
    };
  });
  return { format: 'forge-export-v1', seq: state.seq, nextRepoId: state.nextRepoId, nextIssueId: state.nextIssueId, repos };
}
function loadState() {
  try {
    if (!fs.existsSync(STATE_FILE)) return;
    const dump = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
    state.seq = dump.seq || 0; state.nextRepoId = dump.nextRepoId || 1; state.nextIssueId = dump.nextIssueId || 1;
    for (const rd of dump.repos || []) {
      const r = new Repo(rd.owner, rd.name);
      r.description = rd.description || ''; r.isPrivate = !!rd.private;
      r.defaultBranch = rd.default_branch || 'main'; r.head = rd.head || 'refs/heads/main';
      r.nextNumber = rd.nextNumber || 1; r.createdSeq = rd.createdSeq || 0; r.id = rd.id || 0;
      r.issues = rd.issues || []; r.pulls = rd.pulls || [];
      for (const [ref, sha] of Object.entries(rd.refs || {})) r.refs.set(ref, sha);
      for (const [sha, o] of Object.entries(rd.objects || {})) r.objects.set(sha, { type: o.type, data: Buffer.from(o.data, 'base64') });
      state.repos.set(r.key(), r);
    }
  } catch (e) { /* start fresh on unreadable state */ }
}
function exportState() { return sortKeysDeep(stateDump()); }

// ---------------- git graph walking ----------------
function collectClosure(repo, tips, maxDepth) {
  // Returns {objects: Map sha->{type,data}, shallow: Set<commitSha>}
  const objects = new Map(); const shallow = new Set();
  const commitDist = new Map();
  const queue = [];
  for (const t of tips) if (isHex40(t) && repo.objects.has(t)) queue.push({ sha: t, dist: 0 });
  const seenCommits = new Set();
  const addObjectDeep = (sha) => {
    if (objects.has(sha)) return;
    const o = repo.objects.get(sha); if (!o) return;
    objects.set(sha, o);
    if (o.type === 'tree') for (const e of parseTree(o.data)) addObjectDeep(e.sha);
    else if (o.type === 'tag') { const tg = parseTag(o.data); if (tg.object) addObjectDeep(tg.object); }
  };
  while (queue.length) {
    const { sha, dist } = queue.shift();
    const o = repo.objects.get(sha); if (!o) continue;
    if (o.type === 'tag') { objects.set(sha, o); const tg = parseTag(o.data); if (tg.object) queue.push({ sha: tg.object, dist }); continue; }
    if (o.type !== 'commit') { addObjectDeep(sha); continue; }
    if (seenCommits.has(sha) && commitDist.get(sha) <= dist) continue;
    seenCommits.add(sha); commitDist.set(sha, dist);
    objects.set(sha, o);
    const c = parseCommit(o.data);
    if (c.tree) addObjectDeep(c.tree);
    // deepen N: N levels including the tip; a commit at dist N-1 is the boundary
    const atBoundary = maxDepth !== undefined && maxDepth !== null && dist + 1 >= maxDepth;
    if (atBoundary) { if (c.parents.length) shallow.add(sha); continue; }
    for (const p of c.parents) queue.push({ sha: p, dist: dist + 1 });
  }
  return { objects, shallow };
}
function flattenTree(repo, treeSha, prefix, out) {
  const o = repo.objects.get(treeSha); if (!o || o.type !== 'tree') return out;
  for (const e of parseTree(o.data)) {
    const p = prefix ? prefix + '/' + e.name : e.name;
    if (e.mode === '40000' || e.mode === '040000') flattenTree(repo, e.sha, p, out);
    else out.set(p, { mode: e.mode, sha: e.sha });
  }
  return out;
}
function buildTreeFromFiles(repo, files) {
  // files: Map path -> {mode, sha}; returns tree sha
  function build(prefix) {
    const entries = []; const subdirs = new Map();
    for (const [p, f] of files) {
      if (prefix && !p.startsWith(prefix + '/')) continue;
      const rest = prefix ? p.slice(prefix.length + 1) : p;
      const slash = rest.indexOf('/');
      if (slash < 0) entries.push({ mode: f.mode, name: rest, sha: f.sha });
      else {
        const dir = rest.slice(0, slash);
        if (!subdirs.has(dir)) subdirs.set(dir, true);
      }
    }
    for (const dir of subdirs.keys()) {
      const childPrefix = prefix ? prefix + '/' + dir : dir;
      entries.push({ mode: '40000', name: dir, sha: build(childPrefix) });
    }
    return repo.storeObject('tree', serializeTree(entries));
  }
  return build('');
}
function makeCommit(repo, treeSha, parents, message) {
  const t = BASE_TIME + nextSeq();
  const ident = 'Forge Bot <forge@localhost> ' + t + ' +0000';
  let text = 'tree ' + treeSha + '\n';
  for (const p of parents) text += 'parent ' + p + '\n';
  text += 'author ' + ident + '\ncommitter ' + ident + '\n\n' + (message || '') + '\n';
  return repo.storeObject('commit', Buffer.from(text, 'utf8'));
}

// ---------------- git smart HTTP ----------------
const UPLOAD_CAPS = 'multi_ack_detailed no-done side-band side-band-64k thin-pack ofs-delta shallow deepen-since deepen-not symref=HEAD:refs/heads/main agent=forge/1.0';
const RECEIVE_CAPS = 'report-status report-status-v2 delete-refs side-band-64k ofs-delta atomic quiet agent=forge/1.0';

function advertiseRefs(repo, service) {
  const isUpload = service === 'git-upload-pack';
  const caps = isUpload ? UPLOAD_CAPS : RECEIVE_CAPS;
  const parts = [];
  parts.push(pktLine('# service=' + service + '\n'));
  parts.push(pktLine(null));
  const refs = [...repo.refs.entries()].sort((a, b) => a[0] < b[0] ? -1 : 1);
  let headSha = repo.headSha();
  let headTarget = repo.head;
  if (!headSha && refs.length) { headTarget = refs[0][0]; headSha = refs[0][1]; }
  const capsForHead = caps.replace('symref=HEAD:refs/heads/main', 'symref=HEAD:' + headTarget);
  if (!refs.length) {
    parts.push(pktLine(ZERO_SHA + ' capabilities^{}\0' + capsForHead + '\n'));
  } else {
    parts.push(pktLine(headSha + ' HEAD\0' + capsForHead + '\n'));
    for (const [ref, sha] of refs) {
      parts.push(pktLine(sha + ' ' + ref + '\n'));
      // peeled annotated tags
      const o = repo.objects.get(sha);
      if (o && o.type === 'tag') {
        const tg = parseTag(o.data);
        if (tg.object) parts.push(pktLine(tg.object + ' ' + ref + '^{}\n'));
      }
    }
  }
  parts.push(pktLine(null));
  return Buffer.concat(parts);
}

function handleUploadPack(req, res, repo, body) {
  // Parse all pkt-lines in the request (stateless RPC style).
  const wants = []; const haves = [];
  let caps = ''; let deepen = null; let done = false;
  let off = 0;
  while (off < body.length) {
    const { lines, next, flushed } = readPktLines(body, off);
    if (next === off && !flushed) break;
    off = next;
    for (const raw of lines) {
      let line = raw.toString('utf8');
      const nul = line.indexOf('\0');
      if (nul >= 0) { caps = line.slice(nul + 1).trim(); line = line.slice(0, nul); }
      line = line.replace(/\n$/, '');
      // v0 upload-pack request: capabilities follow the want sha after a space
      const wantCapsMatch = line.match(/^want [0-9a-f]{40} (.+)$/);
      if (wantCapsMatch && !caps) caps = wantCapsMatch[1].trim();
      if (line.startsWith('want ')) wants.push(line.slice(5, 45));
      else if (line.startsWith('have ')) haves.push(line.slice(5, 45));
      else if (line.startsWith('deepen ')) deepen = parseInt(line.slice(7), 10);
      else if (line.startsWith('deepen-since ')) deepen = null; // unsupported precision: serve full
      else if (line === 'done') done = true;
    }
    if (!flushed && lines.length === 0) break;
    if (off >= body.length) break;
  }
  const wantCaps = caps;
  const useSideband = /side-band-64k/.test(wantCaps) || /side-band/.test(wantCaps);
  if (!wants.length) { res.writeHead(200, { 'Content-Type': 'application/x-git-upload-pack-result' }); res.end(pktLine('NAK\n')); return; }
  if (!done && haves.length) {
    // Negotiation round: acknowledge nothing in common yet.
    res.writeHead(200, { 'Content-Type': 'application/x-git-upload-pack-result' });
    res.end(pktLine('NAK\n'));
    return;
  }
  if (!done && deepen !== null && deepen !== undefined) {
    // Stateless deepen probe round: answer with the shallow section only.
    const probe = collectClosure(repo, wants, deepen);
    const out = [];
    for (const s of [...probe.shallow].sort()) out.push(pktLine('shallow ' + s + '\n'));
    out.push(pktLine(null));
    res.writeHead(200, { 'Content-Type': 'application/x-git-upload-pack-result' });
    res.end(Buffer.concat(out));
    return;
  }
  const haveClosure = haves.length ? collectClosure(repo, haves.filter(h => repo.objects.has(h)), null).objects : new Map();
  const { objects, shallow } = collectClosure(repo, wants, deepen);
  for (const sha of haveClosure.keys()) objects.delete(sha);
  const packObjs = [...objects.entries()]
    .sort((a, b) => a[0] < b[0] ? -1 : 1)
    .map(([, o]) => ({ type: o.type, data: o.data }));
  const pack = buildPack(packObjs);
  const out = [];
  if (deepen !== null && deepen !== undefined) {
    for (const s of [...shallow].sort()) out.push(pktLine('shallow ' + s + '\n'));
    out.push(pktLine(null));
  }
  const knownHaves = haves.filter(h => repo.objects.has(h));
  if (knownHaves.length) {
    for (const h of knownHaves) out.push(pktLine('ACK ' + h + ' common\n'));
    out.push(pktLine('ACK ' + knownHaves[knownHaves.length - 1] + '\n'));
  } else {
    out.push(pktLine('NAK\n'));
  }
  if (useSideband) {
    const CH = 65500;
    for (let i = 0; i < pack.length; i += CH) {
      const chunk = Buffer.concat([Buffer.from([1]), pack.subarray(i, i + CH)]);
      out.push(pktLine(chunk));
    }
    out.push(pktLine(null));
  } else {
    out.push(pack);
  }
  res.writeHead(200, { 'Content-Type': 'application/x-git-upload-pack-result', 'Cache-Control': 'no-cache' });
  res.end(Buffer.concat(out));
}

function handleReceivePack(req, res, repo, body) {
  const { lines, next } = readPktLines(body, 0);
  let caps = '';
  const updates = [];
  for (const raw of lines) {
    let line = raw.toString('utf8');
    const nul = line.indexOf('\0');
    if (nul >= 0) { caps = line.slice(nul + 1).trim(); line = line.slice(0, nul); }
    line = line.replace(/\n$/, '');
    const m = line.match(/^([0-9a-f]{40}) ([0-9a-f]{40}) (.+)$/);
    if (m) updates.push({ oldSha: m[1], newSha: m[2], ref: m[3] });
  }
  const packBuf = body.subarray(next);
  let unpackError = null;
  if (packBuf.length >= 12) {
    try {
      const parsed = parsePack(packBuf);
      const resolved = resolvePack(parsed, (sha) => repo.objects.get(sha) || null);
      for (const o of resolved) repo.storeObject(o.type, o.data);
    } catch (e) { unpackError = e.message; }
  } else if (packBuf.length > 0) unpackError = 'short pack';
  const reportStatus = /report-status/.test(caps);
  const results = [];
  if (!unpackError) {
    for (const u of updates) {
      if (u.newSha === ZERO_SHA) {
        if ((repo.refs.get(u.ref) || ZERO_SHA) !== u.oldSha && u.oldSha !== ZERO_SHA) { results.push({ ...u, ok: false, msg: 'old value mismatch' }); continue; }
        repo.refs.delete(u.ref); results.push({ ...u, ok: true }); continue;
      }
      const obj = repo.objects.get(u.newSha);
      if (!obj) { results.push({ ...u, ok: false, msg: 'unknown object' }); continue; }
      const cur = repo.refs.get(u.ref) || ZERO_SHA;
      if (cur !== u.oldSha) { results.push({ ...u, ok: false, msg: 'old value mismatch (expected ' + cur + ')' }); continue; }
      repo.refs.set(u.ref, u.newSha);
      if (u.ref.startsWith('refs/heads/')) {
        const branch = u.ref.slice('refs/heads/'.length);
        if (!repo.refs.has(repo.head)) { repo.head = u.ref; repo.defaultBranch = branch; }
      }
      results.push({ ...u, ok: true });
    }
    if (updates.length) scheduleSave();
  } else {
    for (const u of updates) results.push({ ...u, ok: false, msg: 'unpack failed' });
  }
  res.writeHead(200, { 'Content-Type': 'application/x-git-receive-pack-result', 'Cache-Control': 'no-cache' });
  if (reportStatus) {
    // With side-band-64k/side-band requested, every report-status pkt-line
    // payload is wrapped in band 1; the terminating flush stays plain.
    const useSideband = /side-band/.test(caps);
    // Sideband receive-pack status is double-framed: the report-status
    // pkt-lines themselves are carried as band-1 payload.
    const wrap = (s) => useSideband ? pktLine(Buffer.concat([Buffer.from([1]), pktLine(s)])) : pktLine(s);
    const out = [wrap(unpackError ? 'unpack ' + unpackError + '\n' : 'unpack ok\n')];
    for (const r of results) out.push(wrap(r.ok ? 'ok ' + r.ref + '\n' : 'ng ' + r.ref + ' ' + r.msg + '\n'));
    if (useSideband) out.push(pktLine(Buffer.concat([Buffer.from([1]), pktLine(null)]))); // inner flush, band-1 wrapped
    out.push(pktLine(null));
    res.end(Buffer.concat(out));
  } else res.end();
}

// ---------------- REST v3 shapes ----------------
function baseUrl(req) { return 'http://' + (req.headers.host || 'localhost'); }
function repoJSON(req, r) {
  const b = baseUrl(req);
  return {
    id: r.id, node_id: Buffer.from('R_' + r.id).toString('base64'),
    name: r.name, full_name: r.owner + '/' + r.name,
    owner: { login: r.owner, id: 1, type: 'User' },
    private: r.isPrivate, html_url: b + '/' + r.owner + '/' + r.name,
    description: r.description, homepage: r.homepage || '',
    created_at: fakeISO(r.createdSeq), updated_at: fakeISO(r.createdSeq), pushed_at: fakeISO(r.createdSeq),
    git_url: 'git://' + (req.headers.host || 'localhost') + '/' + r.owner + '/' + r.name + '.git',
    clone_url: b + '/' + r.owner + '/' + r.name + '.git',
    ssh_url: 'git@' + (req.headers.host || 'localhost') + ':' + r.owner + '/' + r.name + '.git',
    default_branch: r.defaultBranch, size: r.objects.size,
    stargazers_count: 0, watchers_count: 0, forks_count: 0, open_issues_count: r.issues.filter(i => i.state === 'open').length,
    language: null, archived: false, disabled: false, visibility: r.isPrivate ? 'private' : 'public',
  };
}
function issueJSON(req, r, i) {
  const b = baseUrl(req);
  return {
    id: i.id, node_id: Buffer.from('I_' + i.id).toString('base64'),
    url: b + '/repos/' + r.owner + '/' + r.name + '/issues/' + i.number,
    repository_url: b + '/repos/' + r.owner + '/' + r.name,
    html_url: b + '/' + r.owner + '/' + r.name + '/issues/' + i.number,
    number: i.number, title: i.title, body: i.body || '',
    user: { login: i.user || r.owner, id: 1, type: 'User' },
    labels: (i.labels || []).map(n => ({ name: n })),
    state: i.state || 'open',
    assignees: [], comments: (i.comments || []).length,
    created_at: fakeISO(i.createdSeq), updated_at: fakeISO(i.updatedSeq || i.createdSeq), closed_at: i.state === 'closed' ? fakeISO(i.updatedSeq || i.createdSeq) : null,
    pull_request: i.isPull ? { url: b + '/repos/' + r.owner + '/' + r.name + '/pulls/' + i.number } : undefined,
    comments_list: i.comments || [],
  };
}
function pullJSON(req, r, p) {
  const b = baseUrl(req);
  const base = issueJSON(req, r, p);
  return {
    ...base,
    url: b + '/repos/' + r.owner + '/' + r.name + '/pulls/' + p.number,
    html_url: b + '/' + r.owner + '/' + r.name + '/pulls/' + p.number,
    head: { ref: p.head, sha: p.headSha || null, repo: { full_name: r.owner + '/' + r.name } },
    base: { ref: p.base, sha: p.baseSha || null, repo: { full_name: r.owner + '/' + r.name } },
    merged: !!p.merged, mergeable: true, draft: !!p.draft,
  };
}
function sendJSON(res, code, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Content-Length': Buffer.byteLength(body) });
  res.end(body);
}
function notFound(res, msg) { sendJSON(res, 404, { message: msg || 'Not Found', documentation_url: 'https://docs.github.com/rest' }); }

function paginateList(req, res, list, query) {
  // GitHub-style page/per_page; with neither param the full list is returned.
  if (!query.has('per_page') && !query.has('page')) return list;
  const per = Math.min(100, Math.max(1, parseInt(query.get('per_page') || '30', 10) || 30));
  const page = Math.max(1, parseInt(query.get('page') || '1', 10) || 1);
  const total = list.length;
  const lastPage = Math.max(1, Math.ceil(total / per));
  const base = baseUrl(req) + req.url.split('?')[0];
  const links = [];
  const mk = (p, rel) => '<' + base + '?page=' + p + '&per_page=' + per + '>; rel="' + rel + '"';
  if (page < lastPage) { links.push(mk(page + 1, 'next')); links.push(mk(lastPage, 'last')); }
  if (page > 1) { links.push(mk(1, 'first')); links.push(mk(page - 1, 'prev')); }
  if (links.length) res.setHeader('Link', links.join(', '));
  return list.slice((page - 1) * per, page * per);
}
function handleREST(req, res, seg, query, bodyObj) {
  const method = req.method;
  // seg: path segments after optional api/v3 strip
  if (seg.length === 0) { sendJSON(res, 200, { current_user_url: baseUrl(req) + '/user', repository_url: baseUrl(req) + '/repos/{owner}/{repo}' }); return true; }
  if (seg[0] === 'user' && seg[1] === 'repos') {
    if (method === 'POST') {
      const name = bodyObj && bodyObj.name; if (!name) { sendJSON(res, 422, { message: 'Validation Failed: name required' }); return true; }
      const owner = (bodyObj && bodyObj.owner) || 'forge';
      if (getRepo(owner, name)) { sendJSON(res, 422, { message: 'Repository already exists' }); return true; }
      const r = createRepo(owner, name, bodyObj);
      sendJSON(res, 201, repoJSON(req, r)); return true;
    }
    if (method === 'GET') { sendJSON(res, 200, paginateList(req, res, [...state.repos.values()], query).map(r => repoJSON(req, r))); return true; }
  }
  if (seg[0] === 'user' && seg.length === 1 && method === 'GET') { sendJSON(res, 200, { login: 'forge', id: 1, type: 'User', html_url: baseUrl(req) + '/forge' }); return true; }
  if (seg[0] === 'users' && seg.length === 2 && method === 'GET') { sendJSON(res, 200, { login: seg[1], id: 1, type: 'User', html_url: baseUrl(req) + '/' + seg[1] }); return true; }
  if (seg[0] === 'orgs' && seg[2] === 'repos' && method === 'POST') {
    const name = bodyObj && bodyObj.name; if (!name) { sendJSON(res, 422, { message: 'name required' }); return true; }
    const r = createRepo(seg[1], name, bodyObj); sendJSON(res, 201, repoJSON(req, r)); return true;
  }
  if (seg[0] === 'repos' && seg.length === 1 && method === 'POST') {
    const name = bodyObj && bodyObj.name; if (!name) { sendJSON(res, 422, { message: 'name required' }); return true; }
    const owner = (bodyObj && bodyObj.owner) || 'forge';
    if (getRepo(owner, name)) { sendJSON(res, 422, { message: 'Repository already exists' }); return true; }
    const r = createRepo(owner, name, bodyObj); sendJSON(res, 201, repoJSON(req, r)); return true;
  }
  if (seg[0] === 'users' && seg[2] === 'repos' && method === 'GET') {
    const list = [...state.repos.values()].filter(r => r.owner.toLowerCase() === seg[1].toLowerCase());
    sendJSON(res, 200, paginateList(req, res, list, query).map(r => repoJSON(req, r))); return true;
  }
  if (seg[0] === 'search' && seg[1] === 'repositories') {
    const q = (query.get('q') || '').toLowerCase();
    const items = [...state.repos.values()].filter(r => !q || r.key().includes(q)).map(r => repoJSON(req, r));
    sendJSON(res, 200, { total_count: items.length, incomplete_results: false, items }); return true;
  }
  if (seg[0] !== 'repos' || seg.length < 3) return false;
  const owner = seg[1], name = seg[2];
  const repo = getRepo(owner, name);
  if (seg.length === 3) {
    if (method === 'GET') { if (!repo) { notFound(res); return true; } sendJSON(res, 200, repoJSON(req, repo)); return true; }
    if (method === 'DELETE') { if (!repo) { notFound(res); return true; } deleteRepo(owner, name); res.writeHead(204); res.end(); return true; }
    if (method === 'PATCH') {
      if (!repo) { notFound(res); return true; }
      if (bodyObj) { if (bodyObj.description !== undefined) repo.description = String(bodyObj.description); if (bodyObj.private !== undefined) repo.isPrivate = !!bodyObj.private; if (bodyObj.default_branch) repo.defaultBranch = String(bodyObj.default_branch); }
      scheduleSave(); sendJSON(res, 200, repoJSON(req, repo)); return true;
    }
    return false;
  }
  if (!repo) { notFound(res); return true; }
  const sub = seg[3];
  // issues & pulls share the number sequence, as on GitHub
  if (sub === 'issues' || sub === 'pulls') {
    const isPull = sub === 'pulls';
    const coll = isPull ? repo.pulls : repo.issues;
    if (seg.length === 4) {
      if (method === 'GET') {
        const st = query.get('state');
        let list = isPull ? coll : coll; // issues endpoint also lists PRs on GitHub; keep separate + pull entries flagged
        if (!isPull) list = [...repo.issues, ...repo.pulls];
        if (st && st !== 'all') list = list.filter(i => (i.state || 'open') === st);
        const dirParam = (query.get('direction') || 'desc').toLowerCase();
        list = [...list].sort((a, b) => (dirParam === 'asc' ? 1 : -1) * (a.number - b.number));
        sendJSON(res, 200, paginateList(req, res, list, query).map(i => (i.isPull ? pullJSON(req, repo, i) : issueJSON(req, repo, i)))); return true;
      }
      if (method === 'POST') {
        if (!bodyObj || !bodyObj.title) { sendJSON(res, 422, { message: 'Validation Failed: title required' }); return true; }
        const item = {
          id: state.nextIssueId++, number: repo.nextNumber++,
          title: String(bodyObj.title), body: bodyObj.body ? String(bodyObj.body) : '',
          state: 'open', user: bodyObj.user || owner, labels: Array.isArray(bodyObj.labels) ? bodyObj.labels.map(l => typeof l === 'string' ? l : l.name) : [],
          comments: [], createdSeq: nextSeq(), updatedSeq: 0, isPull,
        };
        if (isPull) {
          item.head = bodyObj.head ? String(bodyObj.head) : ''; item.base = bodyObj.base ? String(bodyObj.base) : repo.defaultBranch;
          item.headSha = resolveRef(repo, item.head); item.baseSha = resolveRef(repo, item.base);
          item.draft = !!bodyObj.draft; item.merged = false;
          repo.pulls.push(item);
        } else repo.issues.push(item);
        scheduleSave();
        sendJSON(res, 201, isPull ? pullJSON(req, repo, item) : issueJSON(req, repo, item)); return true;
      }
    }
    if (seg.length === 5) {
      const num = parseInt(seg[4], 10);
      const item = coll.find(i => i.number === num) || (!isPull ? repo.pulls.find(i => i.number === num) : null);
      if (!item) { notFound(res); return true; }
      if (method === 'GET') { sendJSON(res, 200, item.isPull ? pullJSON(req, repo, item) : issueJSON(req, repo, item)); return true; }
      if (method === 'PATCH' || method === 'PUT') {
        if (bodyObj) {
          if (bodyObj.title !== undefined) item.title = String(bodyObj.title);
          if (bodyObj.body !== undefined) item.body = String(bodyObj.body);
          if (bodyObj.state !== undefined) item.state = String(bodyObj.state);
          if (bodyObj.labels !== undefined) item.labels = bodyObj.labels.map(l => typeof l === 'string' ? l : l.name);
          item.updatedSeq = nextSeq();
        }
        scheduleSave(); sendJSON(res, 200, item.isPull ? pullJSON(req, repo, item) : issueJSON(req, repo, item)); return true;
      }
      if (method === 'DELETE') { const ix = coll.indexOf(item); if (ix >= 0) coll.splice(ix, 1); scheduleSave(); res.writeHead(204); res.end(); return true; }
    }
    if (seg.length === 6 && seg[5] === 'comments' && seg[3] === 'issues') {
      const num = parseInt(seg[4], 10);
      const item = repo.issues.find(i => i.number === num) || repo.pulls.find(i => i.number === num);
      if (!item) { notFound(res); return true; }
      if (method === 'GET') { sendJSON(res, 200, item.comments || []); return true; }
      if (method === 'POST') {
        const c = { id: (item.comments.length + 1), body: bodyObj && bodyObj.body ? String(bodyObj.body) : '', user: { login: owner }, createdSeq: nextSeq() };
        item.comments.push(c); scheduleSave(); sendJSON(res, 201, c); return true;
      }
    }
    if (seg.length === 6 && sub === 'pulls') {
      const num = parseInt(seg[4], 10);
      const item = repo.pulls.find(i => i.number === num);
      if (!item) { notFound(res); return true; }
      if (seg[5] === 'merge') {
        if (method === 'GET') { if (item.merged) { res.writeHead(204); res.end(); } else notFound(res, 'Pull Request is not merged'); return true; }
        if (method === 'PUT') { item.merged = true; item.state = 'closed'; item.updatedSeq = nextSeq(); scheduleSave(); sendJSON(res, 200, { sha: item.headSha || '', merged: true, message: 'Pull Request successfully merged' }); return true; }
      }
      if (seg[5] === 'files' && method === 'GET') {
        const files = gqlChangedFiles(repo, item).map(f => ({ filename: f.path, status: f.changeType === 'ADDED' ? 'added' : f.changeType === 'DELETED' ? 'removed' : 'modified', additions: 0, deletions: 0, changes: 0, sha: '' }));
        sendJSON(res, 200, paginateList(req, res, files, query)); return true;
      }
    }
    return true;
  }
  if (sub === 'labels' && method === 'GET') {
    const names = new Set();
    for (const i of [...repo.issues, ...repo.pulls]) for (const l of i.labels || []) names.add(l);
    sendJSON(res, 200, [...names].sort().map(n => ({ name: n, color: 'ededed', default: false, description: null }))); return true;
  }
  if (sub === 'contents') {
    const filePath = seg.slice(4).map(decodeURIComponent).join('/');
    if (method === 'GET') {
      const refName = query.get('ref') || repo.defaultBranch;
      const content = getContents(repo, refName, filePath);
      if (!content) { notFound(res, 'Not Found'); return true; }
      sendJSON(res, 200, content); return true;
    }
    if (method === 'PUT') {
      if (!bodyObj || bodyObj.content === undefined) { sendJSON(res, 422, { message: 'content required' }); return true; }
      const branch = bodyObj.branch || repo.defaultBranch;
      const result = putContents(repo, branch, filePath, Buffer.from(String(bodyObj.content).replace(/\s/g, ''), 'base64'), bodyObj.message || ('Update ' + filePath), bodyObj.sha);
      if (result.error) { sendJSON(res, result.code || 422, { message: result.error }); return true; }
      sendJSON(res, result.created ? 201 : 200, result.payload); return true;
    }
    if (method === 'DELETE') {
      const branch = (bodyObj && bodyObj.branch) || repo.defaultBranch;
      const result = deleteContents(repo, branch, filePath, (bodyObj && bodyObj.message) || ('Delete ' + filePath), bodyObj && bodyObj.sha);
      if (result.error) { sendJSON(res, result.code || 422, { message: result.error }); return true; }
      sendJSON(res, 200, result.payload); return true;
    }
    return true;
  }
  if (sub === 'branches' && method === 'GET') {
    const list = [...repo.refs.entries()].filter(([r]) => r.startsWith('refs/heads/')).map(([r, sha]) => ({ name: r.slice(11), commit: { sha }, protected: false }));
    sendJSON(res, 200, list); return true;
  }
  if (sub === 'tags' && method === 'GET') {
    const list = [...repo.refs.entries()].filter(([r]) => r.startsWith('refs/tags/')).map(([r, sha]) => ({ name: r.slice(10), commit: { sha } }));
    sendJSON(res, 200, list); return true;
  }
  if (sub === 'git' && seg[4] === 'refs' && method === 'GET') {
    const list = [...repo.refs.entries()].map(([r, sha]) => ({ ref: r, object: { sha, type: (repo.objects.get(sha) || {}).type || 'commit' } }));
    sendJSON(res, 200, list); return true;
  }
  if (sub === 'commits' && method === 'GET' && seg.length === 4) {
    const tip = repo.headSha(); const list = [];
    if (tip) {
      const { objects } = collectClosure(repo, [tip], null);
      for (const [sha, o] of objects) if (o.type === 'commit') { const c = parseCommit(o.data); list.push({ sha, commit: { message: c.message, tree: { sha: c.tree } }, parents: c.parents.map(p => ({ sha: p })) }); }
    }
    sendJSON(res, 200, list); return true;
  }
  return false;
}
function resolveRef(repo, ref) {
  if (!ref) return null;
  if (isHex40(ref)) return ref;
  if (repo.refs.has(ref)) return repo.refs.get(ref);
  if (repo.refs.has('refs/heads/' + ref)) return repo.refs.get('refs/heads/' + ref);
  if (repo.refs.has('refs/tags/' + ref)) return repo.refs.get('refs/tags/' + ref);
  if (ref === 'HEAD') return repo.headSha();
  return null;
}
function treeOfRef(repo, refName) {
  const sha = resolveRef(repo, refName || repo.defaultBranch);
  if (!sha) return null;
  let o = repo.objects.get(sha); if (!o) return null;
  if (o.type === 'tag') { const tg = parseTag(o.data); o = repo.objects.get(tg.object); if (!o) return null; }
  if (o.type === 'commit') { const c = parseCommit(o.data); return { commitSha: sha, treeSha: c.tree }; }
  if (o.type === 'tree') return { commitSha: null, treeSha: sha };
  return null;
}
function getContents(repo, refName, filePath) {
  const t = treeOfRef(repo, refName); if (!t) return null;
  if (!filePath) {
    const entries = parseTree(repo.objects.get(t.treeSha).data);
    return entries.map(e => ({ name: e.name, path: e.name, sha: e.sha, type: (e.mode === '40000' || e.mode === '040000') ? 'dir' : 'file', size: 0 }));
  }
  const files = flattenTree(repo, t.treeSha, '', new Map());
  const hit = files.get(filePath);
  if (hit) {
    const blob = repo.objects.get(hit.sha);
    return { name: filePath.split('/').pop(), path: filePath, sha: hit.sha, size: blob.data.length, type: 'file', encoding: 'base64', content: blob.data.toString('base64') };
  }
  // directory?
  const prefix = filePath.replace(/\/$/, '') + '/';
  const children = new Map();
  for (const p of files.keys()) if (p.startsWith(prefix)) { const rest = p.slice(prefix.length); const first = rest.split('/')[0]; children.set(first, rest.includes('/') ? 'dir' : 'file'); }
  if (children.size) return [...children.entries()].map(([name, type]) => ({ name, path: prefix + name, type, sha: ZERO_SHA, size: 0 }));
  return null;
}
function putContents(repo, branch, filePath, contentBuf, message, expectedSha) {
  const ref = 'refs/heads/' + branch;
  const parentSha = repo.refs.get(ref) || null;
  let files = new Map();
  if (parentSha) { const t = treeOfRef(repo, ref); if (t) files = flattenTree(repo, t.treeSha, '', new Map()); }
  const existing = files.get(filePath);
  if (expectedSha && existing && existing.sha !== expectedSha) return { error: 'sha mismatch', code: 409 };
  if (!expectedSha && existing) return { error: 'sha was not supplied', code: 422 };
  if (expectedSha && !existing) return { error: 'not found', code: 404 };
  const blobSha = repo.storeObject('blob', contentBuf);
  files.set(filePath, { mode: '100644', sha: blobSha });
  const treeSha = buildTreeFromFiles(repo, files);
  const commitSha = makeCommit(repo, treeSha, parentSha ? [parentSha] : [], message);
  repo.refs.set(ref, commitSha);
  if (!repo.refs.has(repo.head) || branch === repo.defaultBranch) { /* keep head */ }
  scheduleSave();
  return { created: !existing, payload: { content: { name: filePath.split('/').pop(), path: filePath, sha: blobSha, size: contentBuf.length, type: 'file' }, commit: { sha: commitSha, message } } };
}
function deleteContents(repo, branch, filePath, message, expectedSha) {
  const ref = 'refs/heads/' + branch;
  const parentSha = repo.refs.get(ref); if (!parentSha) return { error: 'branch not found', code: 404 };
  const t = treeOfRef(repo, ref); const files = flattenTree(repo, t.treeSha, '', new Map());
  const existing = files.get(filePath); if (!existing) return { error: 'not found', code: 404 };
  if (expectedSha && existing.sha !== expectedSha) return { error: 'sha mismatch', code: 409 };
  files.delete(filePath);
  const treeSha = buildTreeFromFiles(repo, files);
  const commitSha = makeCommit(repo, treeSha, [parentSha], message);
  repo.refs.set(ref, commitSha); scheduleSave();
  return { payload: { content: null, commit: { sha: commitSha, message } } };
}

// ---------------- GraphQL (real subset: parser + executor) ----------------
// A small but genuine GraphQL implementation: lexer, parser (operations,
// variable definitions, fragments, directives, all value types) and a
// schema-driven executor over the forge's data model. Covers the query and
// mutation shapes gh and github-mcp-server send: repository / viewer / user /
// organization / search / rateLimit, connections with cursor pagination,
// issue & pull-request fields, git objects (Commit/Tree/Blob/Ref), and the
// common mutations (createIssue, addComment, createPullRequest,
// mergePullRequest, label mutations, createRepository, ...).
// Deterministic: every timestamp comes from the logical clock (fakeISO),
// cursors are pure functions of position, ordering is stable.

function gqlNid(prefix, val) { return Buffer.from(prefix + '_' + val, 'utf8').toString('base64'); }
function gqlDecodeNid(id) {
  try {
    const s = Buffer.from(String(id), 'base64').toString('utf8');
    const ix = s.indexOf('_');
    if (ix < 0) return null;
    return { prefix: s.slice(0, ix), val: s.slice(ix + 1) };
  } catch (e) { return null; }
}
function findRepoById(id) {
  const d = gqlDecodeNid(id); if (!d || d.prefix !== 'R') return null;
  const rid = parseInt(d.val, 10);
  for (const r of state.repos.values()) if (r.id === rid) return r;
  return null;
}
function findIssueByNid(id) {
  const d = gqlDecodeNid(id); if (!d || d.prefix !== 'I') return null;
  const iid = parseInt(d.val, 10);
  for (const r of state.repos.values()) {
    for (const i of r.issues) if (i.id === iid) return { r, i };
    for (const p of r.pulls) if (p.id === iid) return { r, i: p };
  }
  return null;
}

// ----- lexer -----
function gqlLex(src) {
  const toks = []; let i = 0, line = 1, col = 1;
  const err = (m) => { const e = new Error(m); e.line = line; e.col = col; throw e; };
  while (i < src.length) {
    const c = src[i];
    if (c === '\n') { line++; col = 1; i++; continue; }
    if (c === ' ' || c === '\t' || c === '\r' || c === ',' ) { col++; i++; continue; }
    if (c === '#') { while (i < src.length && src[i] !== '\n') i++; continue; }
    const startLine = line, startCol = col;
    if (src.startsWith('...', i)) { toks.push({ t: '...', line: startLine, col: startCol }); i += 3; col += 3; continue; }
    if ('!$():=@[]{}|&'.includes(c)) { toks.push({ t: c, line: startLine, col: startCol }); i++; col++; continue; }
    if (c === '"') {
      if (src.startsWith('"""', i)) {
        const end = src.indexOf('"""', i + 3); if (end < 0) err('unterminated block string');
        let v = src.slice(i + 3, end);
        v = v.replace(/\\"""/g, '"""');
        const raw = src.slice(i, end + 3);
        toks.push({ t: 'String', v, line: startLine, col: startCol });
        for (const ch of raw) { if (ch === '\n') { line++; col = 1; } else col++; }
        i = end + 3; continue;
      }
      let j = i + 1, v = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\n') err('unterminated string');
        if (src[j] === '\\') {
          const e = src[j + 1];
          if (e === 'u') { v += String.fromCharCode(parseInt(src.slice(j + 2, j + 6), 16)); j += 6; }
          else { v += ({ '"': '"', '\\': '\\', '/': '/', b: '\b', f: '\f', n: '\n', r: '\r', t: '\t' })[e] || e; j += 2; }
        } else { v += src[j]; j++; }
      }
      if (j >= src.length) err('unterminated string');
      toks.push({ t: 'String', v, line: startLine, col: startCol });
      col += (j - i + 1); i = j + 1; continue;
    }
    if (/[0-9-]/.test(c)) {
      let j = i, isFloat = false;
      if (src[j] === '-') j++;
      while (j < src.length && /[0-9]/.test(src[j])) j++;
      if (src[j] === '.') { isFloat = true; j++; while (j < src.length && /[0-9]/.test(src[j])) j++; }
      if (src[j] === 'e' || src[j] === 'E') { isFloat = true; j++; if (src[j] === '+' || src[j] === '-') j++; while (j < src.length && /[0-9]/.test(src[j])) j++; }
      const txt = src.slice(i, j);
      toks.push({ t: isFloat ? 'Float' : 'Int', v: isFloat ? parseFloat(txt) : parseInt(txt, 10), line: startLine, col: startCol });
      col += (j - i); i = j; continue;
    }
    if (/[_A-Za-z]/.test(c)) {
      let j = i; while (j < src.length && /[_0-9A-Za-z]/.test(src[j])) j++;
      toks.push({ t: 'Name', v: src.slice(i, j), line: startLine, col: startCol });
      col += (j - i); i = j; continue;
    }
    err('unexpected character ' + JSON.stringify(c));
  }
  toks.push({ t: 'EOF', line, col });
  return toks;
}

// ----- parser -----
function gqlParse(src) {
  const toks = gqlLex(src); let pos = 0;
  const peek = () => toks[pos];
  const next = () => toks[pos++];
  const expect = (t) => { const tk = next(); if (tk.t !== t) { const e = new Error('expected ' + t + ', got ' + tk.t); e.line = tk.line; e.col = tk.col; throw e; } return tk; };
  const skip = (t) => { if (peek().t === t) { pos++; return true; } return false; };
  function parseValue() {
    const tk = peek();
    if (tk.t === '$') { next(); return { kind: 'var', name: expect('Name').v }; }
    if (tk.t === 'Int' || tk.t === 'Float' || tk.t === 'String') { next(); return { kind: 'lit', value: tk.v }; }
    if (tk.t === 'Name') { next(); if (tk.v === 'true') return { kind: 'lit', value: true }; if (tk.v === 'false') return { kind: 'lit', value: false }; if (tk.v === 'null') return { kind: 'lit', value: null }; return { kind: 'enum', value: tk.v }; }
    if (tk.t === '[') { next(); const vals = []; while (peek().t !== ']') vals.push(parseValue()); expect(']'); return { kind: 'list', values: vals }; }
    if (tk.t === '{') { next(); const fields = {}; while (peek().t !== '}') { const n = expect('Name').v; expect(':'); fields[n] = parseValue(); } expect('}'); return { kind: 'object', fields }; }
    const e = new Error('unexpected value token ' + tk.t); e.line = tk.line; e.col = tk.col; throw e;
  }
  function parseType() {
    let t;
    if (skip('[')) { const inner = parseType(); expect(']'); t = { list: inner }; }
    else t = { name: expect('Name').v };
    if (skip('!')) t = { nonNull: t };
    return t;
  }
  function parseDirectives() {
    const dirs = [];
    while (peek().t === '@') { next(); const name = expect('Name').v; const args = {}; if (skip('(')) { while (peek().t !== ')') { const n = expect('Name').v; expect(':'); args[n] = parseValue(); } expect(')'); } dirs.push({ name, args }); }
    return dirs;
  }
  function parseSelectionSet() {
    expect('{'); const sels = [];
    while (peek().t !== '}') sels.push(parseSelection());
    expect('}'); return sels;
  }
  function parseSelection() {
    if (peek().t === '...') {
      next();
      if (peek().t === 'Name' && peek().v === 'on') { next(); const cond = expect('Name').v; const dirs = parseDirectives(); const sels = parseSelectionSet(); return { kind: 'inline', typeCondition: cond, directives: dirs, selections: sels }; }
      const nameTok = expect('Name'); const dirs = parseDirectives();
      return { kind: 'spread', name: nameTok.v, directives: dirs };
    }
    const first = expect('Name'); let alias = null, name = first.v;
    if (skip(':')) { alias = name; name = expect('Name').v; }
    const args = {};
    if (skip('(')) { while (peek().t !== ')') { const n = expect('Name').v; expect(':'); args[n] = parseValue(); } expect(')'); }
    const dirs = parseDirectives();
    let sels = null;
    if (peek().t === '{') sels = parseSelectionSet();
    return { kind: 'field', name, alias, args, directives: dirs, selections: sels, line: first.line, col: first.col };
  }
  function parseOperation() {
    if (peek().t === '{') return { op: 'query', name: null, varDefs: [], directives: [], selections: parseSelectionSet() };
    const kw = expect('Name').v;
    if (kw !== 'query' && kw !== 'mutation' && kw !== 'subscription') { const e = new Error('unexpected definition ' + kw); throw e; }
    let name = null;
    if (peek().t === 'Name') name = next().v;
    const varDefs = [];
    if (skip('(')) {
      while (peek().t !== ')') {
        expect('$'); const vn = expect('Name').v; expect(':'); const ty = parseType();
        let def = undefined;
        if (skip('=')) def = parseValue();
        parseDirectives();
        varDefs.push({ name: vn, type: ty, default: def });
      }
      expect(')');
    }
    const dirs = parseDirectives();
    return { op: kw, name, varDefs, directives: dirs, selections: parseSelectionSet() };
  }
  const operations = []; const fragments = {};
  while (peek().t !== 'EOF') {
    if (peek().t === 'Name' && peek().v === 'fragment') {
      next(); const fname = expect('Name').v; const onKw = expect('Name'); if (onKw.v !== 'on') throw new Error('expected "on" in fragment');
      const cond = expect('Name').v; parseDirectives(); const sels = parseSelectionSet();
      fragments[fname] = { typeCondition: cond, selections: sels };
    } else operations.push(parseOperation());
  }
  return { operations, fragments };
}
function gqlValue(node, vars) {
  if (!node) return undefined;
  switch (node.kind) {
    case 'lit': case 'enum': return node.value;
    case 'var': return vars ? vars[node.name] : undefined;
    case 'list': return node.values.map(v => gqlValue(v, vars));
    case 'object': { const o = {}; for (const k of Object.keys(node.fields)) o[k] = gqlValue(node.fields[k], vars); return o; }
  }
  return undefined;
}
function gqlDirsOk(dirs, vars) {
  for (const d of dirs || []) {
    if (d.name === 'skip' && gqlValue(d.args.if, vars) === true) return false;
    if (d.name === 'include' && gqlValue(d.args.if, vars) === false) return false;
  }
  return true;
}

// ----- wrappers over the data model -----
function gqlUser(login) { return { __typename: 'User', login: String(login || 'forge') }; }
function gqlOrg(login) { return { __typename: 'Organization', login: String(login || 'forge') }; }
function gqlRepo(r) { return { __typename: 'Repository', r }; }
function gqlIssue(r, i) { return { __typename: 'Issue', r, i }; }
function gqlPull(r, p) { return { __typename: 'PullRequest', r, i: p }; }
function gqlComment(r, i, c) { return { __typename: 'IssueComment', r, i, c }; }
function gqlLabel(name) { return { __typename: 'Label', name: String(name) }; }
function gqlRef(r, refName, sha) { return { __typename: 'Ref', r, refName, sha }; }
function gqlGitObject(r, sha) {
  const o = r.objects.get(sha); if (!o) return null;
  const tn = { commit: 'Commit', tree: 'Tree', blob: 'Blob', tag: 'Tag' }[o.type];
  if (!tn) return null;
  return { __typename: tn, r, sha, o };
}
function gqlActorFromIdent(text) {
  const m = /^(.*?) <(.*?)> (\d+) ([+-]\d{4})$/.exec(text || '');
  if (!m) return { name: 'Forge Bot', email: 'forge@localhost', date: fakeISO(0) };
  return { name: m[1], email: m[2], date: new Date(parseInt(m[3], 10) * 1000).toISOString().replace('.000Z', 'Z') };
}
function gqlCommitIdents(r, sha) {
  const o = r.objects.get(sha);
  let author = null, committer = null;
  if (o) for (const line of o.data.toString('utf8').split('\n')) {
    if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
    else if (line === '') break;
  }
  return { author: gqlActorFromIdent(author), committer: gqlActorFromIdent(committer || author) };
}
function gqlAncestors(r, tipSha, limit) {
  // commits reachable from tip, newest first by embedded timestamp then sha
  const seen = new Set(); const out = []; const queue = [tipSha];
  while (queue.length && out.length < (limit || 1000)) {
    const sha = queue.shift();
    if (!sha || seen.has(sha)) continue; seen.add(sha);
    const o = r.objects.get(sha); if (!o || o.type !== 'commit') continue;
    const c = parseCommit(o.data);
    let ts = 0; const m = /> (\d+) [+-]\d{4}/.exec(o.data.toString('utf8')); if (m) ts = parseInt(m[1], 10);
    out.push({ sha, c, ts });
    for (const p of c.parents) queue.push(p);
  }
  out.sort((a, b) => (b.ts - a.ts) || (a.sha < b.sha ? -1 : 1));
  return out;
}
const GQL_INTERFACES = {
  Node: ['User', 'Organization', 'Repository', 'Issue', 'PullRequest', 'IssueComment', 'Label', 'Ref', 'Commit', 'Tree', 'Blob', 'Tag'],
  Actor: ['User', 'Organization'],
  RepositoryOwner: ['User', 'Organization'],
  Labelable: ['Issue', 'PullRequest'],
  Closable: ['Issue', 'PullRequest'],
  Comment: ['IssueComment'],
  GitObject: ['Commit', 'Tree', 'Blob', 'Tag'],
  UniformResourceLocatable: ['User', 'Organization', 'Repository', 'Issue', 'PullRequest', 'IssueComment', 'Label', 'Ref', 'Commit'],
  SearchResultItem: ['Repository', 'Issue', 'PullRequest', 'User'],
};
function gqlTypeMatches(obj, cond) {
  if (!cond) return true;
  if (!obj || !obj.__typename) return false;
  if (obj.__typename === cond) return true;
  return (GQL_INTERFACES[cond] || []).includes(obj.__typename);
}
// ----- connections -----
function gqlCursor(idx) { return Buffer.from('cursor:' + idx, 'utf8').toString('base64'); }
function gqlCursorIndex(cur) {
  try { const s = Buffer.from(String(cur), 'base64').toString('utf8'); const m = /^cursor:(\d+)$/.exec(s); return m ? parseInt(m[1], 10) : null; } catch (e) { return null; }
}
function gqlConnect(typeName, items, args) {
  args = args || {};
  let start = 0, end = items.length;
  if (args.after != null) { const ix = gqlCursorIndex(args.after); if (ix != null) start = Math.max(start, ix + 1); }
  if (args.before != null) { const ix = gqlCursorIndex(args.before); if (ix != null) end = Math.min(end, ix); }
  let slice = items.slice(start, end);
  if (args.first != null) slice = slice.slice(0, Math.max(0, args.first));
  if (args.last != null) slice = slice.slice(Math.max(0, slice.length - args.last));
  const offset = items.indexOf(slice[0]);
  const edges = slice.map((node, k) => ({ __typename: typeName + 'Edge', cursor: gqlCursor((offset < 0 ? start : offset) + k), node }));
  return {
    __typename: typeName + 'Connection', totalCount: items.length, edges,
    nodes: slice,
    pageInfo: {
      __typename: 'PageInfo',
      hasNextPage: edges.length > 0 && (start + edges.length) < items.length && args.last == null,
      hasPreviousPage: start > 0,
      startCursor: edges.length ? edges[0].cursor : null,
      endCursor: edges.length ? edges[edges.length - 1].cursor : null,
    },
  };
}
function gqlEmptyConn(typeName) { return gqlConnect(typeName, [], {}); }
function gqlSortIssues(list, args) {
  const out = [...list];
  const dir = args && args.orderBy && args.orderBy.direction === 'ASC' ? 1 : -1;
  out.sort((a, b) => dir * (a.number - b.number));
  return out;
}
function gqlIssueStateFilter(list, args) {
  if (!args || !args.states) return list;
  const want = (Array.isArray(args.states) ? args.states : [args.states]).map(s => String(s).toLowerCase());
  return list.filter(i => want.includes((i.state || 'open').toLowerCase()));
}
function gqlLabelConn(item) {
  return gqlConnect('Label', (item.labels || []).map(gqlLabel), {});
}
function gqlCommentsConn(r, i, args) {
  const list = [...(i.comments || [])].sort((a, b) => a.id - b.id);
  return gqlConnect('IssueComment', list.map(c => gqlComment(r, i, c)), args);
}
function gqlChangedFiles(r, p) {
  const baseT = treeOfRef(r, p.baseSha || p.base); const headT = treeOfRef(r, p.headSha || p.head);
  const baseFiles = baseT ? flattenTree(r, baseT.treeSha, '', new Map()) : new Map();
  const headFiles = headT ? flattenTree(r, headT.treeSha, '', new Map()) : new Map();
  const files = [];
  for (const [path, f] of headFiles) {
    if (!baseFiles.has(path)) files.push({ path, changeType: 'ADDED' });
    else if (baseFiles.get(path).sha !== f.sha) files.push({ path, changeType: 'MODIFIED' });
  }
  for (const path of baseFiles.keys()) if (!headFiles.has(path)) files.push({ path, changeType: 'DELETED' });
  files.sort((a, b) => a.path < b.path ? -1 : 1);
  return files;
}
function gqlRepoIssuesConn(r, args) { return gqlConnect('Issue', gqlSortIssues(gqlIssueStateFilter([...r.issues], args), args).map(i => gqlIssue(r, i)), args); }
function gqlRepoPullsConn(r, args) { return gqlConnect('PullRequest', gqlSortIssues(gqlIssueStateFilter([...r.pulls], args), args).map(p => gqlPull(r, p)), args); }
function gqlUserReposConn(login, args) {
  const list = [...state.repos.values()].filter(r => r.owner.toLowerCase() === String(login).toLowerCase()).sort((a, b) => a.id - b.id).map(gqlRepo);
  return gqlConnect('Repository', list, args);
}

// ----- schema -----
const GQL_SCHEMA = {
  Query: {
    viewer: () => gqlUser('forge'),
    user: (o, a) => gqlUser(a.login),
    organization: (o, a) => gqlOrg(a.login),
    repositoryOwner: (o, a) => gqlUser(a.login),
    repository: (o, a) => { const r = getRepo(a.owner, a.name); return r ? gqlRepo(r) : null; },
    rateLimit: () => ({ __typename: 'RateLimit', limit: 5000, cost: 1, remaining: 5000, used: 0, resetAt: fakeISO(0), nodeCount: 0 }),
    node: (o, a) => {
      const d = gqlDecodeNid(a.id); if (!d) return null;
      if (d.prefix === 'R') { const r = findRepoById(a.id); return r ? gqlRepo(r) : null; }
      if (d.prefix === 'I') { const f = findIssueByNid(a.id); if (!f) return null; return f.i.isPull ? gqlPull(f.r, f.i) : gqlIssue(f.r, f.i); }
      if (d.prefix === 'L') return gqlLabel(d.val);
      return null;
    },
    search: (o, a, ctx) => {
      const type = String(a.type || 'REPOSITORY').toUpperCase();
      const q = String(a.query || '');
      const terms = q.split(/\s+/).filter(Boolean);
      const repoFilter = (terms.find(t => t.startsWith('repo:')) || '').slice(5);
      const kindFilter = (terms.find(t => t.startsWith('is:')) || '').slice(3);
      const textTerms = terms.filter(t => !t.includes(':')).map(t => t.toLowerCase());
      let nodes = [], issueCount = 0, repositoryCount = 0, userCount = 0;
      if (type === 'REPOSITORY') {
        const list = [...state.repos.values()].filter(r => (!repoFilter || r.key().toLowerCase() === repoFilter.toLowerCase()) && textTerms.every(t => (r.name + ' ' + r.owner + ' ' + (r.description || '')).toLowerCase().includes(t)));
        repositoryCount = list.length; nodes = list.map(gqlRepo);
      } else if (type === 'ISSUE') {
        const all = [];
        for (const r of state.repos.values()) {
          if (repoFilter && r.key().toLowerCase() !== repoFilter.toLowerCase()) continue;
          for (const i of r.issues) all.push(gqlIssue(r, i));
          for (const p of r.pulls) all.push(gqlPull(r, p));
        }
        const list = all.filter(w => {
          if (kindFilter === 'pr' && w.__typename !== 'PullRequest') return false;
          if (kindFilter === 'issue' && w.__typename !== 'Issue') return false;
          return textTerms.every(t => (w.i.title + ' ' + (w.i.body || '')).toLowerCase().includes(t));
        });
        issueCount = list.length; nodes = list;
      } else if (type === 'USER') { userCount = 1; nodes = [gqlUser('forge')]; }
      const conn = gqlConnect('SearchResultItem', nodes, a);
      conn.issueCount = issueCount; conn.repositoryCount = repositoryCount; conn.userCount = userCount;
      return conn;
    },
  },
  User: {
    id: (o) => gqlNid('U', o.login),
    login: (o) => o.login,
    name: (o) => o.login,
    url: (o, a, ctx) => baseUrl(ctx.req) + '/' + o.login,
    resourcePath: (o) => '/' + o.login,
    email: () => '',
    avatarUrl: () => '',
    isViewer: (o) => o.login === 'forge',
    isSiteAdmin: () => false,
    createdAt: () => fakeISO(1),
    updatedAt: () => fakeISO(1),
    repositories: (o, a) => gqlUserReposConn(o.login, a),
    repository: (o, a) => { const r = getRepo(o.login, a.name); return r ? gqlRepo(r) : null; },
    followers: () => gqlEmptyConn('User'),
    following: () => gqlEmptyConn('User'),
    issues: () => gqlEmptyConn('Issue'),
    pullRequests: () => gqlEmptyConn('PullRequest'),
  },
  Organization: {
    id: (o) => gqlNid('O', o.login),
    login: (o) => o.login,
    name: (o) => o.login,
    url: (o, a, ctx) => baseUrl(ctx.req) + '/' + o.login,
    resourcePath: (o) => '/' + o.login,
    email: () => '',
    avatarUrl: () => '',
    createdAt: () => fakeISO(1),
    updatedAt: () => fakeISO(1),
    repositories: (o, a) => gqlUserReposConn(o.login, a),
    repository: (o, a) => { const r = getRepo(o.login, a.name); return r ? gqlRepo(r) : null; },
    membersWithRole: () => gqlEmptyConn('User'),
    teams: () => gqlEmptyConn('Team'),
  },
  Repository: {
    id: (o) => gqlNid('R', o.r.id),
    databaseId: (o) => o.r.id,
    name: (o) => o.r.name,
    nameWithOwner: (o) => o.r.owner + '/' + o.r.name,
    owner: (o) => gqlUser(o.r.owner),
    description: (o) => o.r.description || null,
    homepageUrl: (o) => o.r.homepage || null,
    url: (o, a, ctx) => baseUrl(ctx.req) + '/' + o.r.owner + '/' + o.r.name,
    resourcePath: (o) => '/' + o.r.owner + '/' + o.r.name,
    sshUrl: (o, a, ctx) => 'git@' + (ctx.req.headers.host || 'localhost') + ':' + o.r.owner + '/' + o.r.name + '.git',
    isPrivate: (o) => o.r.isPrivate,
    visibility: (o) => o.r.isPrivate ? 'PRIVATE' : 'PUBLIC',
    isFork: () => false,
    isArchived: () => false,
    isDisabled: () => false,
    isMirror: () => false,
    isTemplate: () => false,
    isEmpty: (o) => !o.r.headSha(),
    createdAt: (o) => fakeISO(o.r.createdSeq),
    updatedAt: (o) => fakeISO(o.r.createdSeq),
    pushedAt: (o) => fakeISO(o.r.createdSeq),
    hasIssuesEnabled: () => true,
    hasWikiEnabled: () => false,
    hasProjectsEnabled: () => false,
    viewerCanAdminister: () => true,
    viewerPermission: () => 'ADMIN',
    stargazerCount: () => 0,
    forkCount: () => 0,
    diskUsage: (o) => { let n = 0; for (const ob of o.r.objects.values()) n += ob.data.length; return Math.round(n / 1024); },
    primaryLanguage: () => null,
    licenseInfo: () => null,
    languages: () => gqlEmptyConn('Language'),
    stargazers: () => gqlEmptyConn('User'),
    forks: () => gqlEmptyConn('Repository'),
    watchers: () => ({ __typename: 'UserConnection', totalCount: 0, edges: [], nodes: [], pageInfo: { __typename: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null } }),
    defaultBranchRef: (o) => { const sha = o.r.refs.get(o.r.head); return sha ? gqlRef(o.r, o.r.head, sha) : null; },
    ref: (o, a) => { const qn = String(a.qualifiedName || ''); const sha = o.r.refs.get(qn); return sha ? gqlRef(o.r, qn, sha) : null; },
    refs: (o, a) => {
      const prefix = String(a.refPrefix || 'refs/');
      const list = [...o.r.refs.entries()].filter(([rn]) => rn.startsWith(prefix)).sort((x, y) => x[0] < y[0] ? -1 : 1).map(([rn, sha]) => gqlRef(o.r, rn, sha));
      return gqlConnect('Ref', list, a);
    },
    object: (o, a) => {
      let expr = String(a.expression || a.oid || '');
      let pathPart = null;
      const ci = expr.indexOf(':');
      if (ci >= 0) { pathPart = expr.slice(ci + 1); expr = expr.slice(0, ci); }
      let sha = resolveRef(o.r, expr) || (isHex40(expr) ? expr : null);
      if (!sha) return null;
      let w = gqlGitObject(o.r, sha);
      if (!w) return null;
      if (w.__typename === 'Tag') { const tg = parseTag(w.o.data); if (tg.object) { const nw = gqlGitObject(o.r, tg.object); if (nw) w = nw; } }
      if (pathPart != null) {
        if (w.__typename !== 'Commit') return null;
        const tree = parseCommit(w.o.data).tree;
        if (!pathPart) return gqlGitObject(o.r, tree);
        let cur = tree;
        for (const part of pathPart.split('/').filter(Boolean)) {
          const to = o.r.objects.get(cur); if (!to || to.type !== 'tree') return null;
          const ent = parseTree(to.data).find(e => e.name === part); if (!ent) return null;
          cur = ent.sha;
        }
        return gqlGitObject(o.r, cur);
      }
      return w;
    },
    issues: (o, a) => gqlRepoIssuesConn(o.r, a),
    issue: (o, a) => { const i = o.r.issues.find(x => x.number === a.number) || o.r.pulls.find(x => x.number === a.number && !x.isPull); return i ? gqlIssue(o.r, i) : null; },
    issueOrPullRequest: (o, a) => {
      const i = o.r.issues.find(x => x.number === a.number); if (i) return gqlIssue(o.r, i);
      const p = o.r.pulls.find(x => x.number === a.number); if (p) return gqlPull(o.r, p);
      return null;
    },
    pullRequests: (o, a) => gqlRepoPullsConn(o.r, a),
    pullRequest: (o, a) => { const p = o.r.pulls.find(x => x.number === a.number); return p ? gqlPull(o.r, p) : null; },
    labels: (o, a) => {
      const names = new Set();
      for (const i of [...o.r.issues, ...o.r.pulls]) for (const l of i.labels || []) names.add(l);
      return gqlConnect('Label', [...names].sort().map(gqlLabel), a);
    },
    assignableUsers: () => gqlEmptyConn('User'),
    mentionableUsers: () => gqlEmptyConn('User'),
    releases: () => gqlEmptyConn('Release'),
    branchProtectionRules: () => gqlEmptyConn('BranchProtectionRule'),
  },
  Issue: null, // filled below (shared with PullRequest)
  PullRequest: null,
  IssueComment: {
    id: (o) => gqlNid('IC', o.i.id + '_' + o.c.id),
    databaseId: (o) => o.c.id,
    body: (o) => o.c.body || '',
    bodyText: (o) => o.c.body || '',
    author: (o) => gqlUser((o.c.user && o.c.user.login) || o.r.owner),
    createdAt: (o) => fakeISO(o.c.createdSeq),
    updatedAt: (o) => fakeISO(o.c.createdSeq),
    url: (o, a, ctx) => baseUrl(ctx.req) + '/' + o.r.owner + '/' + o.r.name + '/issues/' + o.i.number,
    issue: (o) => o.i.isPull ? gqlPull(o.r, o.i) : gqlIssue(o.r, o.i),
    repository: (o) => gqlRepo(o.r),
  },
  Label: {
    id: (o) => gqlNid('L', o.name),
    name: (o) => o.name,
    color: () => 'ededed',
    description: () => null,
    isDefault: () => false,
    url: (o, a, ctx) => baseUrl(ctx.req) + '/labels/' + encodeURIComponent(o.name),
  },
  Ref: {
    id: (o) => gqlNid('REF', o.refName),
    name: (o) => o.refName.replace(/^refs\/(heads|tags)\//, ''),
    prefix: (o) => o.refName.startsWith('refs/tags/') ? 'refs/tags/' : 'refs/heads/',
    qualifiedName: (o) => o.refName,
    target: (o) => gqlGitObject(o.r, o.sha),
    repository: (o) => gqlRepo(o.r),
    associatedPullRequests: () => gqlEmptyConn('PullRequest'),
  },
  Commit: {
    id: (o) => gqlNid('C', o.sha),
    oid: (o) => o.sha,
    abbreviatedOid: (o) => o.sha.slice(0, 7),
    message: (o) => parseCommit(o.o.data).message,
    messageHeadline: (o) => (parseCommit(o.o.data).message || '').split('\n')[0],
    messageBody: (o) => { const parts = (parseCommit(o.o.data).message || '').split('\n\n'); return parts.length > 1 ? parts.slice(1).join('\n\n') : ''; },
    tree: (o) => gqlGitObject(o.r, parseCommit(o.o.data).tree),
    treeOid: (o) => parseCommit(o.o.data).tree,
    parents: (o, a) => gqlConnect('Commit', parseCommit(o.o.data).parents.map(p => gqlGitObject(o.r, p)).filter(Boolean), a),
    history: (o, a) => gqlConnect('Commit', gqlAncestors(o.r, o.sha, 1000).map(x => gqlGitObject(o.r, x.sha)).filter(Boolean), a),
    author: (o) => { const id = gqlCommitIdents(o.r, o.sha); return { __typename: 'GitActor', name: id.author.name, email: id.author.email, date: id.author.date, user: null }; },
    committer: (o) => { const id = gqlCommitIdents(o.r, o.sha); return { __typename: 'GitActor', name: id.committer.name, email: id.committer.email, date: id.committer.date, user: null }; },
    authoredDate: (o) => gqlCommitIdents(o.r, o.sha).author.date,
    committedDate: (o) => gqlCommitIdents(o.r, o.sha).committer.date,
    url: (o, a, ctx) => baseUrl(ctx.req) + '/' + o.r.owner + '/' + o.r.name + '/commit/' + o.sha,
    resourcePath: (o) => '/' + o.r.owner + '/' + o.r.name + '/commit/' + o.sha,
    additions: () => 0,
    deletions: () => 0,
    changedFiles: () => null,
  },
  Tree: {
    id: (o) => gqlNid('T', o.sha),
    oid: (o) => o.sha,
    abbreviatedOid: (o) => o.sha.slice(0, 7),
    entries: (o) => parseTree(o.o.data).map(e => ({
      __typename: 'TreeEntry', name: e.name, path: e.name,
      type: (e.mode === '40000' || e.mode === '040000') ? 'tree' : 'blob',
      mode: parseInt(e.mode, 10),
      object: gqlGitObject(o.r, e.sha),
      extension: e.name.includes('.') ? e.name.slice(e.name.lastIndexOf('.')) : '',
    })),
    url: (o, a, ctx) => baseUrl(ctx.req) + '/' + o.r.owner + '/' + o.r.name + '/tree/' + o.sha,
  },
  Blob: {
    id: (o) => gqlNid('B', o.sha),
    oid: (o) => o.sha,
    abbreviatedOid: (o) => o.sha.slice(0, 7),
    text: (o) => o.o.data.includes(0) ? null : o.o.data.toString('utf8'),
    isBinary: (o) => o.o.data.includes(0),
    isTruncated: () => false,
    byteSize: (o) => o.o.data.length,
  },
  Tag: {
    id: (o) => gqlNid('TAG', o.sha),
    oid: (o) => o.sha,
    name: (o) => { for (const [rn, s] of o.r.refs) if (s === o.sha && rn.startsWith('refs/tags/')) return rn.slice(10); return ''; },
    message: (o) => { const t = o.o.data.toString('utf8'); const ix = t.indexOf('\n\n'); return ix >= 0 ? t.slice(ix + 2) : ''; },
    target: (o) => { const tg = parseTag(o.o.data); return tg.object ? gqlGitObject(o.r, tg.object) : null; },
    tagger: (o) => { const m = /^tagger (.*)$/m.exec(o.o.data.toString('utf8')); const a = gqlActorFromIdent(m ? m[1] : ''); return { __typename: 'GitActor', name: a.name, email: a.email, date: a.date, user: null }; },
  },
};
// Issue and PullRequest share most fields.
function gqlIssueFields(extra) {
  return Object.assign({
    id: (o) => gqlNid('I', o.i.id),
    databaseId: (o) => o.i.id,
    number: (o) => o.i.number,
    title: (o) => o.i.title,
    body: (o) => o.i.body || '',
    bodyText: (o) => o.i.body || '',
    state: (o) => o.i.merged ? 'MERGED' : String(o.i.state || 'open').toUpperCase(),
    stateReason: (o) => (o.i.state === 'closed' && !o.i.merged) ? (o.i.stateReason || 'COMPLETED') : null,
    locked: () => false,
    activeLockReason: () => null,
    author: (o) => gqlUser(o.i.user || o.r.owner),
    authorAssociation: () => 'OWNER',
    repository: (o) => gqlRepo(o.r),
    url: (o, a, ctx) => baseUrl(ctx.req) + '/' + o.r.owner + '/' + o.r.name + (o.i.isPull ? '/pull/' : '/issues/') + o.i.number,
    resourcePath: (o) => '/' + o.r.owner + '/' + o.r.name + (o.i.isPull ? '/pull/' : '/issues/') + o.i.number,
    createdAt: (o) => fakeISO(o.i.createdSeq),
    updatedAt: (o) => fakeISO(o.i.updatedSeq || o.i.createdSeq),
    closedAt: (o) => (o.i.state === 'closed' || o.i.merged) ? fakeISO(o.i.updatedSeq || o.i.createdSeq) : null,
    labels: (o, a) => gqlConnect('Label', (o.i.labels || []).map(gqlLabel), a),
    comments: (o, a) => gqlCommentsConn(o.r, o.i, a),
    assignees: () => gqlEmptyConn('User'),
    participants: () => gqlEmptyConn('User'),
    reactions: () => gqlEmptyConn('Reaction'),
    milestone: () => null,
    viewerCanUpdate: () => true,
    viewerCanClose: () => true,
    viewerCanReopen: () => true,
  }, extra || {});
}
GQL_SCHEMA.Issue = gqlIssueFields();
GQL_SCHEMA.PullRequest = gqlIssueFields({
  isDraft: (o) => !!o.i.draft,
  merged: (o) => !!o.i.merged,
  mergedAt: (o) => o.i.merged ? fakeISO(o.i.updatedSeq || o.i.createdSeq) : null,
  mergedBy: (o) => o.i.merged ? gqlUser(o.r.owner) : null,
  mergeable: () => 'MERGEABLE',
  headRefName: (o) => o.i.head || '',
  baseRefName: (o) => o.i.base || '',
  headRefOid: (o) => o.i.headSha || resolveRef(o.r, o.i.head) || '',
  baseRefOid: (o) => o.i.baseSha || resolveRef(o.r, o.i.base) || '',
  headRepository: (o) => gqlRepo(o.r),
  baseRepository: (o) => gqlRepo(o.r),
  headRef: (o) => { const sha = resolveRef(o.r, o.i.head); return sha ? gqlRef(o.r, 'refs/heads/' + o.i.head, sha) : null; },
  baseRef: (o) => { const sha = resolveRef(o.r, o.i.base); return sha ? gqlRef(o.r, 'refs/heads/' + o.i.base, sha) : null; },
  isCrossRepository: () => false,
  additions: () => 0,
  deletions: () => 0,
  changedFiles: (o) => gqlChangedFiles(o.r, o.i).length,
  files: (o, a) => gqlConnect('PullRequestChangedFile', gqlChangedFiles(o.r, o.i).map(f => ({ __typename: 'PullRequestChangedFile', path: f.path, additions: 0, deletions: 0, changeType: f.changeType })), a),
  commits: (o, a) => {
    const headSha = o.i.headSha || resolveRef(o.r, o.i.head);
    if (!headSha) return gqlEmptyConn('PullRequestCommit');
    const baseSha = o.i.baseSha || resolveRef(o.r, o.i.base);
    const baseSet = new Set(baseSha ? gqlAncestors(o.r, baseSha, 1000).map(x => x.sha) : []);
    const list = gqlAncestors(o.r, headSha, 1000).filter(x => !baseSet.has(x.sha)).map(x => ({ __typename: 'PullRequestCommit', commit: gqlGitObject(o.r, x.sha), oid: x.sha, url: '' }));
    return gqlConnect('PullRequestCommit', list, a);
  },
  reviews: () => gqlEmptyConn('PullRequestReview'),
  latestReviews: () => gqlEmptyConn('PullRequestReview'),
  reviewThreads: () => gqlEmptyConn('PullRequestReviewThread'),
  closingIssuesReferences: () => gqlEmptyConn('Issue'),
});

// ----- mutations -----
function gqlNewIssueItem(r, fields, isPull) {
  const item = {
    id: state.nextIssueId++, number: r.nextNumber++,
    title: String(fields.title || ''), body: fields.body ? String(fields.body) : '',
    state: 'open', user: fields.user || r.owner,
    labels: Array.isArray(fields.labels) ? fields.labels.map(l => String(l)) : [],
    comments: [], createdSeq: nextSeq(), updatedSeq: 0, isPull: !!isPull,
  };
  if (isPull) {
    item.head = fields.head ? String(fields.head) : ''; item.base = fields.base ? String(fields.base) : r.defaultBranch;
    item.headSha = resolveRef(r, item.head); item.baseSha = resolveRef(r, item.base);
    item.draft = !!fields.draft; item.merged = false;
    r.pulls.push(item);
  } else r.issues.push(item);
  scheduleSave();
  return item;
}
function gqlRepoFromInput(input) {
  if (!input) return null;
  if (input.repositoryId) return findRepoById(input.repositoryId);
  if (input.owner && (input.name || input.repositoryName)) return getRepo(input.owner, input.name || input.repositoryName);
  return null;
}
function gqlLabelNamesFromIds(labelIds) {
  if (!Array.isArray(labelIds)) return null;
  const names = [];
  for (const id of labelIds) { const d = gqlDecodeNid(id); if (d && d.prefix === 'L') names.push(d.val); }
  return names;
}
const GQL_MUTATIONS = {
  createIssue: (o, a) => {
    const input = a.input || a;
    const r = gqlRepoFromInput(input);
    if (!r) throw new Error('repository not found');
    if (!input.title) throw new Error('title is required');
    const labels = gqlLabelNamesFromIds(input.labelIds) || (input.labels || []);
    const item = gqlNewIssueItem(r, { title: input.title, body: input.body, labels }, false);
    return { __typename: 'CreateIssuePayload', clientMutationId: input.clientMutationId || null, issue: gqlIssue(r, item) };
  },
  updateIssue: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.id); if (!f) throw new Error('issue not found');
    if (input.title !== undefined) f.i.title = String(input.title);
    if (input.body !== undefined) f.i.body = String(input.body);
    if (input.state !== undefined) f.i.state = String(input.state).toLowerCase();
    const names = gqlLabelNamesFromIds(input.labelIds); if (names) f.i.labels = names;
    f.i.updatedSeq = nextSeq(); scheduleSave();
    return { __typename: 'UpdateIssuePayload', clientMutationId: input.clientMutationId || null, issue: f.i.isPull ? gqlPull(f.r, f.i) : gqlIssue(f.r, f.i) };
  },
  closeIssue: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.issueId); if (!f) throw new Error('issue not found');
    f.i.state = 'closed'; if (input.stateReason) f.i.stateReason = String(input.stateReason).toUpperCase();
    f.i.updatedSeq = nextSeq(); scheduleSave();
    return { __typename: 'CloseIssuePayload', clientMutationId: input.clientMutationId || null, issue: gqlIssue(f.r, f.i) };
  },
  reopenIssue: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.issueId); if (!f) throw new Error('issue not found');
    f.i.state = 'open'; f.i.updatedSeq = nextSeq(); scheduleSave();
    return { __typename: 'ReopenIssuePayload', clientMutationId: input.clientMutationId || null, issue: gqlIssue(f.r, f.i) };
  },
  deleteIssue: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.issueId); if (!f) throw new Error('issue not found');
    const coll = f.i.isPull ? f.r.pulls : f.r.issues;
    const ix = coll.indexOf(f.i); if (ix >= 0) coll.splice(ix, 1);
    scheduleSave();
    return { __typename: 'DeleteIssuePayload', clientMutationId: input.clientMutationId || null, repository: gqlRepo(f.r) };
  },
  addComment: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.subjectId); if (!f) throw new Error('subject not found');
    const c = { id: (f.i.comments.reduce((m, x) => Math.max(m, x.id || 0), 0) + 1), body: input.body ? String(input.body) : '', user: { login: f.r.owner }, createdSeq: nextSeq() };
    f.i.comments.push(c); scheduleSave();
    const node = gqlComment(f.r, f.i, c);
    return { __typename: 'AddCommentPayload', clientMutationId: input.clientMutationId || null, commentEdge: { __typename: 'IssueCommentEdge', cursor: gqlCursor(f.i.comments.length - 1), node }, subject: f.i.isPull ? gqlPull(f.r, f.i) : gqlIssue(f.r, f.i) };
  },
  createPullRequest: (o, a) => {
    const input = a.input || a;
    const r = gqlRepoFromInput(input) || (input.headRepositoryId ? findRepoById(input.headRepositoryId) : null);
    if (!r) throw new Error('repository not found');
    if (!input.title) throw new Error('title is required');
    const item = gqlNewIssueItem(r, { title: input.title, body: input.body, head: input.headRefName, base: input.baseRefName, draft: input.draft }, true);
    return { __typename: 'CreatePullRequestPayload', clientMutationId: input.clientMutationId || null, pullRequest: gqlPull(r, item) };
  },
  updatePullRequest: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.pullRequestId); if (!f) throw new Error('pull request not found');
    if (input.title !== undefined) f.i.title = String(input.title);
    if (input.body !== undefined) f.i.body = String(input.body);
    if (input.state !== undefined) f.i.state = String(input.state).toLowerCase();
    if (input.baseRefName !== undefined) { f.i.base = String(input.baseRefName); f.i.baseSha = resolveRef(f.r, f.i.base); }
    f.i.updatedSeq = nextSeq(); scheduleSave();
    return { __typename: 'UpdatePullRequestPayload', clientMutationId: input.clientMutationId || null, pullRequest: gqlPull(f.r, f.i) };
  },
  mergePullRequest: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.pullRequestId); if (!f) throw new Error('pull request not found');
    f.i.merged = true; f.i.state = 'closed'; f.i.updatedSeq = nextSeq(); scheduleSave();
    return { __typename: 'MergePullRequestPayload', clientMutationId: input.clientMutationId || null, pullRequest: gqlPull(f.r, f.i) };
  },
  closePullRequest: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.pullRequestId); if (!f) throw new Error('pull request not found');
    f.i.state = 'closed'; f.i.updatedSeq = nextSeq(); scheduleSave();
    return { __typename: 'ClosePullRequestPayload', clientMutationId: input.clientMutationId || null, pullRequest: gqlPull(f.r, f.i) };
  },
  reopenPullRequest: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.pullRequestId); if (!f) throw new Error('pull request not found');
    f.i.state = 'open'; f.i.merged = false; f.i.updatedSeq = nextSeq(); scheduleSave();
    return { __typename: 'ReopenPullRequestPayload', clientMutationId: input.clientMutationId || null, pullRequest: gqlPull(f.r, f.i) };
  },
  addLabelsToLabelable: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.labelableId); if (!f) throw new Error('labelable not found');
    const names = gqlLabelNamesFromIds(input.labelIds) || [];
    for (const n of names) if (!f.i.labels.includes(n)) f.i.labels.push(n);
    f.i.updatedSeq = nextSeq(); scheduleSave();
    return { __typename: 'AddLabelsToLabelablePayload', clientMutationId: input.clientMutationId || null, labelable: f.i.isPull ? gqlPull(f.r, f.i) : gqlIssue(f.r, f.i) };
  },
  removeLabelsFromLabelable: (o, a) => {
    const input = a.input || a;
    const f = findIssueByNid(input.labelableId); if (!f) throw new Error('labelable not found');
    const names = gqlLabelNamesFromIds(input.labelIds) || [];
    f.i.labels = (f.i.labels || []).filter(l => !names.includes(l));
    f.i.updatedSeq = nextSeq(); scheduleSave();
    return { __typename: 'RemoveLabelsFromLabelablePayload', clientMutationId: input.clientMutationId || null, labelable: f.i.isPull ? gqlPull(f.r, f.i) : gqlIssue(f.r, f.i) };
  },
  createRepository: (o, a) => {
    const input = a.input || a;
    if (!input.name) throw new Error('name is required');
    const owner = input.ownerLogin || 'forge';
    const r = createRepo(owner, String(input.name), { description: input.description || '', private: String(input.visibility || 'PUBLIC').toUpperCase() === 'PRIVATE' });
    return { __typename: 'CreateRepositoryPayload', clientMutationId: input.clientMutationId || null, repository: gqlRepo(r) };
  },
  updateRepository: (o, a) => {
    const input = a.input || a;
    const r = findRepoById(input.repositoryId); if (!r) throw new Error('repository not found');
    if (input.name !== undefined) r.name = String(input.name);
    if (input.description !== undefined) r.description = String(input.description);
    if (input.homepageUrl !== undefined) r.homepage = String(input.homepageUrl);
    scheduleSave();
    return { __typename: 'UpdateRepositoryPayload', clientMutationId: input.clientMutationId || null, repository: gqlRepo(r) };
  },
};
GQL_SCHEMA.Mutation = GQL_MUTATIONS;

// ----- executor -----
function gqlCollectFields(obj, selections, ctx, out) {
  out = out || new Map();
  for (const sel of selections || []) {
    if (!gqlDirsOk(sel.directives, ctx.vars)) continue;
    if (sel.kind === 'field') {
      const key = sel.alias || sel.name;
      if (!out.has(key)) out.set(key, { field: sel, selections: [] });
      const entry = out.get(key);
      if (sel.selections) entry.selections.push(...sel.selections);
    } else if (sel.kind === 'spread') {
      const frag = ctx.fragments[sel.name];
      if (frag && gqlTypeMatches(obj, frag.typeCondition)) gqlCollectFields(obj, frag.selections, ctx, out);
    } else if (sel.kind === 'inline') {
      if (gqlTypeMatches(obj, sel.typeCondition)) gqlCollectFields(obj, sel.selections, ctx, out);
    }
  }
  return out;
}
function gqlResolveField(obj, fieldName, args, ctx) {
  if (fieldName === '__typename') return obj && obj.__typename ? obj.__typename : null;
  const tn = obj && obj.__typename;
  const schema = tn && GQL_SCHEMA[tn];
  if (schema && typeof schema[fieldName] === 'function') return schema[fieldName](obj, args, ctx);
  if (obj && typeof obj === 'object' && fieldName in obj) {
    const v = obj[fieldName];
    return typeof v === 'function' ? v(args, ctx) : v;
  }
  return undefined;
}
function gqlComplete(value, entry, ctx, path) {
  if (value === null || value === undefined) return null;
  if (Array.isArray(value)) return value.map((v, ix) => gqlComplete(v, entry, ctx, [...path, ix]));
  if (typeof value === 'object') {
    if (!entry.selections || entry.selections.length === 0) return value.__typename ? { __typename: value.__typename } : value;
    return gqlExecObject(value, entry.selections, ctx, path);
  }
  return value;
}
function gqlExecObject(obj, selections, ctx, path) {
  const fields = gqlCollectFields(obj, selections, ctx);
  const out = {};
  for (const [key, entry] of fields) {
    const fname = entry.field.name;
    const fpath = [...path, key];
    try {
      const args = {};
      for (const an of Object.keys(entry.field.args || {})) args[an] = gqlValue(entry.field.args[an], ctx.vars);
      const raw = gqlResolveField(obj, fname, args, ctx);
      if (raw === undefined) {
        out[key] = null;
        ctx.errors.push({ message: 'Field \'' + fname + '\' doesn\'t exist on type \'' + (obj.__typename || 'Unknown') + '\'', path: fpath, extensions: { code: 'undefinedField' } });
        continue;
      }
      out[key] = gqlComplete(raw, entry, ctx, fpath);
    } catch (e) {
      out[key] = null;
      ctx.errors.push({ message: String((e && e.message) || e), path: fpath });
    }
  }
  return out;
}
function handleGraphQL(req, res, bodyObj) {
  const query = bodyObj && typeof bodyObj.query === 'string' ? bodyObj.query : '';
  const variables = (bodyObj && bodyObj.variables) || {};
  const operationName = bodyObj && bodyObj.operationName;
  if (!query) { res.writeHead(400, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ errors: [{ message: 'no query provided' }] })); return; }
  let doc;
  try { doc = gqlParse(query); }
  catch (e) {
    res.writeHead(400, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ errors: [{ message: 'Parse error: ' + e.message, locations: e.line ? [{ line: e.line, column: e.col }] : undefined }] }));
    return;
  }
  let op = doc.operations.find(x => !operationName || x.name === operationName) || doc.operations[0];
  if (!op) { res.writeHead(400, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ errors: [{ message: 'operation not found' }] })); return; }
  const vars = Object.assign({}, variables);
  for (const vd of op.varDefs || []) {
    if (vars[vd.name] === undefined && vd.default !== undefined) vars[vd.name] = gqlValue(vd.default, vars);
  }
  const ctx = { req, vars, fragments: doc.fragments, errors: [] };
  const rootType = op.op === 'mutation' ? 'Mutation' : 'Query';
  const root = { __typename: rootType };
  let data;
  try { data = gqlExecObject(root, op.selections, ctx, []); }
  catch (e) { res.writeHead(200, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ data: null, errors: [{ message: String((e && e.message) || e) }] })); return; }
  const payload = { data };
  if (ctx.errors.length) payload.errors = ctx.errors;
  sendJSON(res, 200, payload);
}

// ---------------- MCP (github-mcp-server shaped tools) ----------------
// JSON-RPC 2.0 over HTTP POST /mcp: initialize / ping / tools/list /
// tools/call, plus empty resources/prompts lists for probing clients.
// Tool names and argument shapes mirror github-mcp-server (owner + repo,
// issue_number, pullNumber); the previous build's names are kept as aliases.
function mcpRepoOf(args) {
  const r = getRepo(args.owner || 'forge', args.repo || args.name);
  if (!r) throw new Error('repository not found');
  return r;
}
function mcpIssueOf(r, args) {
  const num = args.issue_number != null ? args.issue_number : args.number;
  const item = r.issues.find(i => i.number === num) || r.pulls.find(i => i.number === num);
  if (!item) throw new Error('issue not found');
  return item;
}
function mcpPullOf(r, args) {
  const num = args.pullNumber != null ? args.pullNumber : (args.pull_number != null ? args.pull_number : args.number);
  const p = r.pulls.find(i => i.number === num);
  if (!p) throw new Error('pull request not found');
  return p;
}
function mcpLabels(args) {
  if (!Array.isArray(args.labels)) return [];
  return args.labels.map(l => typeof l === 'string' ? l : (l && l.name) || String(l));
}
const MCP_TOOL_DEFS = [
  ['get_me', 'Get the authenticated user', {}],
  ['create_repository', 'Create a new repository', { name: 'string*', description: 'string', private: 'boolean', autoInit: 'boolean', owner: 'string' }],
  ['search_repositories', 'Search repositories', { query: 'string*', page: 'number', perPage: 'number' }],
  ['list_repositories', 'List repositories', { owner: 'string' }],
  ['get_repository', 'Get a repository', { owner: 'string', repo: 'string', name: 'string' }],
  ['fork_repository', 'Fork a repository', { owner: 'string*', repo: 'string*', organization: 'string' }],
  ['create_branch', 'Create a branch', { owner: 'string*', repo: 'string*', branch: 'string*', from_branch: 'string' }],
  ['list_commits', 'List commits of a branch', { owner: 'string*', repo: 'string*', sha: 'string', page: 'number', perPage: 'number' }],
  ['get_file_contents', 'Get file or directory contents', { owner: 'string*', repo: 'string*', path: 'string*', branch: 'string', ref: 'string' }],
  ['create_or_update_file', 'Create or update a file in a repository', { owner: 'string*', repo: 'string*', path: 'string*', content: 'string*', message: 'string*', branch: 'string', sha: 'string' }],
  ['push_files', 'Push multiple files in one commit', { owner: 'string*', repo: 'string*', branch: 'string*', files: 'array*', message: 'string*' }],
  ['delete_file', 'Delete a file from a repository', { owner: 'string*', repo: 'string*', path: 'string*', message: 'string*', branch: 'string', sha: 'string' }],
  ['get_issue', 'Get an issue', { owner: 'string*', repo: 'string*', issue_number: 'number*' }],
  ['list_issues', 'List issues of a repository', { owner: 'string*', repo: 'string*', state: 'string', labels: 'array', page: 'number', perPage: 'number' }],
  ['create_issue', 'Create an issue', { owner: 'string*', repo: 'string*', title: 'string*', body: 'string', labels: 'array', assignees: 'array' }],
  ['update_issue', 'Update an issue', { owner: 'string*', repo: 'string*', issue_number: 'number*', title: 'string', body: 'string', state: 'string', labels: 'array' }],
  ['add_issue_comment', 'Add a comment to an issue', { owner: 'string*', repo: 'string*', issue_number: 'number*', body: 'string*' }],
  ['list_issue_comments', 'List comments of an issue', { owner: 'string*', repo: 'string*', issue_number: 'number*', page: 'number', perPage: 'number' }],
  ['get_issue_comments', 'List comments of an issue', { owner: 'string*', repo: 'string*', issue_number: 'number*', page: 'number', perPage: 'number' }],
  ['search_issues', 'Search issues and pull requests', { q: 'string*', query: 'string', page: 'number', perPage: 'number' }],
  ['search_pull_requests', 'Search pull requests', { q: 'string*', query: 'string', page: 'number', perPage: 'number' }],
  ['list_pull_requests', 'List pull requests of a repository', { owner: 'string*', repo: 'string*', state: 'string', page: 'number', perPage: 'number' }],
  ['get_pull_request', 'Get a pull request', { owner: 'string*', repo: 'string*', pullNumber: 'number*' }],
  ['create_pull_request', 'Create a pull request', { owner: 'string*', repo: 'string*', title: 'string*', body: 'string', head: 'string*', base: 'string', draft: 'boolean' }],
  ['update_pull_request', 'Update a pull request', { owner: 'string*', repo: 'string*', pullNumber: 'number*', title: 'string', body: 'string', state: 'string', base: 'string' }],
  ['merge_pull_request', 'Merge a pull request', { owner: 'string*', repo: 'string*', pullNumber: 'number*', merge_method: 'string', commit_title: 'string', commit_message: 'string' }],
  ['get_pull_request_files', 'List files changed in a pull request', { owner: 'string*', repo: 'string*', pullNumber: 'number*' }],
];
const MCP_TOOLS = MCP_TOOL_DEFS.map(([name, description, props]) => {
  const properties = {}; const required = [];
  for (const [k, v] of Object.entries(props)) {
    const req = v.endsWith('*');
    properties[k] = { type: v.replace('*', '') };
    if (req) required.push(k);
  }
  const schema = { type: 'object', properties };
  if (required.length) schema.required = required;
  return { name, description, inputSchema: schema };
});
function mcpPage(list, args) {
  const per = Math.min(100, Math.max(1, args.perPage || args.per_page || 30));
  const page = Math.max(1, args.page || 1);
  return list.slice((page - 1) * per, page * per);
}
function mcpCallTool(req, name, args) {
  args = args || {};
  switch (name) {
    case 'get_me': return { login: 'forge', id: 1, type: 'User', name: 'forge', html_url: baseUrl(req) + '/forge' };
    case 'list_repositories': {
      let list = [...state.repos.values()];
      if (args.owner) list = list.filter(r => r.owner.toLowerCase() === String(args.owner).toLowerCase());
      return list.map(r => repoJSON(req, r));
    }
    case 'search_repositories': {
      const q = String(args.query || '').toLowerCase();
      const list = [...state.repos.values()].filter(r => !q || r.key().includes(q) || (r.description || '').toLowerCase().includes(q));
      return { total_count: list.length, incomplete_results: false, items: mcpPage(list, args).map(r => repoJSON(req, r)) };
    }
    case 'get_repository': { const r = mcpRepoOf(args); return repoJSON(req, r); }
    case 'create_repository': {
      const owner = args.owner || 'forge';
      if (!args.name) throw new Error('name is required');
      if (getRepo(owner, args.name)) throw new Error('repository already exists');
      const r = createRepo(owner, args.name, args);
      if (args.autoInit) {
        const blob = r.storeObject('blob', Buffer.from('# ' + args.name + '\n', 'utf8'));
        const tree = buildTreeFromFiles(r, new Map([['README.md', { mode: '100644', sha: blob }]]));
        const commit = makeCommit(r, tree, [], 'Initial commit');
        r.refs.set('refs/heads/' + r.defaultBranch, commit);
        scheduleSave();
      }
      return repoJSON(req, r);
    }
    case 'fork_repository': {
      const src = mcpRepoOf(args);
      const owner = args.organization || 'forge';
      if (getRepo(owner, src.name)) throw new Error('fork already exists');
      const r = createRepo(owner, src.name, { description: src.description, private: src.isPrivate });
      for (const [sha, o] of src.objects) r.objects.set(sha, o);
      for (const [ref, sha] of src.refs) r.refs.set(ref, sha);
      r.issues = []; r.pulls = [];
      scheduleSave();
      return repoJSON(req, r);
    }
    case 'create_branch': {
      const r = mcpRepoOf(args);
      const fromSha = resolveRef(r, args.from_branch || r.defaultBranch);
      if (!fromSha) throw new Error('source branch not found');
      r.refs.set('refs/heads/' + args.branch, fromSha); scheduleSave();
      return { ref: 'refs/heads/' + args.branch, object: { sha: fromSha, type: 'commit' } };
    }
    case 'list_commits': {
      const r = mcpRepoOf(args);
      const tip = resolveRef(r, args.sha || r.defaultBranch);
      if (!tip) return [];
      return mcpPage(gqlAncestors(r, tip, 1000), args).map(x => ({ sha: x.sha, commit: { message: x.c.message, tree: { sha: x.c.tree }, author: gqlCommitIdents(r, x.sha).author }, parents: x.c.parents.map(p => ({ sha: p })) }));
    }
    case 'get_file_contents': {
      const r = mcpRepoOf(args);
      const ref = args.branch || args.ref || r.defaultBranch;
      const content = getContents(r, ref, args.path);
      if (!content) throw new Error('path not found');
      if (Array.isArray(content)) return content;
      const blob = r.objects.get(content.sha);
      return { type: 'file', name: content.name, path: content.path, sha: content.sha, size: content.size, content: blob ? blob.data.toString('utf8') : '', encoding: 'utf-8' };
    }
    case 'create_or_update_file': {
      const r = mcpRepoOf(args);
      const branch = args.branch || r.defaultBranch;
      const result = putContents(r, branch, args.path, Buffer.from(String(args.content), 'utf8'), args.message || ('Update ' + args.path), args.sha);
      if (result.error) throw new Error(result.error);
      return result.payload;
    }
    case 'push_files': {
      const r = mcpRepoOf(args);
      const branch = args.branch || r.defaultBranch;
      const ref = 'refs/heads/' + branch;
      const parentSha = r.refs.get(ref) || null;
      let files = new Map();
      if (parentSha) { const t = treeOfRef(r, ref); if (t) files = flattenTree(r, t.treeSha, '', new Map()); }
      for (const f of args.files || []) {
        const blobSha = r.storeObject('blob', Buffer.from(String(f.content), 'utf8'));
        files.set(f.path, { mode: '100644', sha: blobSha });
      }
      const treeSha = buildTreeFromFiles(r, files);
      const commitSha = makeCommit(r, treeSha, parentSha ? [parentSha] : [], args.message || 'Push files');
      r.refs.set(ref, commitSha); scheduleSave();
      return { ref, commit: { sha: commitSha, message: args.message || 'Push files' } };
    }
    case 'delete_file': {
      const r = mcpRepoOf(args);
      const result = deleteContents(r, args.branch || r.defaultBranch, args.path, args.message || ('Delete ' + args.path), args.sha);
      if (result.error) throw new Error(result.error);
      return result.payload;
    }
    case 'get_issue': { const r = mcpRepoOf(args); const i = mcpIssueOf(r, args); return i.isPull ? pullJSON(req, r, i) : issueJSON(req, r, i); }
    case 'list_issues': {
      const r = mcpRepoOf(args);
      let list = [...r.issues, ...r.pulls].sort((a, b) => b.number - a.number);
      if (args.state) list = list.filter(i => (i.state || 'open') === String(args.state).toLowerCase());
      if (Array.isArray(args.labels) && args.labels.length) { const want = mcpLabels(args); list = list.filter(i => want.every(l => (i.labels || []).includes(l))); }
      return mcpPage(list, args).map(i => i.isPull ? pullJSON(req, r, i) : issueJSON(req, r, i));
    }
    case 'create_issue': {
      const r = mcpRepoOf(args);
      if (!args.title) throw new Error('title is required');
      const item = { id: state.nextIssueId++, number: r.nextNumber++, title: String(args.title), body: args.body ? String(args.body) : '', state: 'open', user: args.owner || r.owner, labels: mcpLabels(args), comments: [], createdSeq: nextSeq(), updatedSeq: 0, isPull: false };
      r.issues.push(item); scheduleSave();
      return issueJSON(req, r, item);
    }
    case 'update_issue': {
      const r = mcpRepoOf(args); const item = mcpIssueOf(r, args);
      if (args.title !== undefined) item.title = String(args.title);
      if (args.body !== undefined) item.body = String(args.body);
      if (args.state !== undefined) item.state = String(args.state).toLowerCase();
      if (args.labels !== undefined) item.labels = mcpLabels(args);
      item.updatedSeq = nextSeq(); scheduleSave();
      return item.isPull ? pullJSON(req, r, item) : issueJSON(req, r, item);
    }
    case 'add_issue_comment': {
      const r = mcpRepoOf(args); const item = mcpIssueOf(r, args);
      const c = { id: (item.comments.reduce((m, x) => Math.max(m, x.id || 0), 0) + 1), body: String(args.body || ''), user: { login: r.owner }, createdSeq: nextSeq() };
      item.comments.push(c); scheduleSave();
      return { id: c.id, body: c.body, user: c.user, created_at: fakeISO(c.createdSeq), html_url: baseUrl(req) + '/' + r.owner + '/' + r.name + '/issues/' + item.number };
    }
    case 'list_issue_comments': case 'get_issue_comments': {
      const r = mcpRepoOf(args); const item = mcpIssueOf(r, args);
      return mcpPage([...(item.comments || [])], args).map(c => ({ id: c.id, body: c.body, user: c.user, created_at: fakeISO(c.createdSeq) }));
    }
    case 'search_issues': case 'search_pull_requests': {
      const q = String(args.q || args.query || '');
      const onlyPr = name === 'search_pull_requests' || /(^|\s)is:pr(\s|$)/.test(q);
      const onlyIssue = /(^|\s)is:issue(\s|$)/.test(q);
      const terms = q.split(/\s+/).filter(t => t && !t.includes(':')).map(t => t.toLowerCase());
      const items = [];
      for (const r of state.repos.values()) {
        const pool = onlyPr ? r.pulls : onlyIssue ? r.issues : [...r.issues, ...r.pulls];
        for (const i of pool) if (terms.every(t => (i.title + ' ' + (i.body || '')).toLowerCase().includes(t))) items.push(i.isPull ? pullJSON(req, r, i) : issueJSON(req, r, i));
      }
      return { total_count: items.length, incomplete_results: false, items: mcpPage(items, args) };
    }
    case 'list_pull_requests': {
      const r = mcpRepoOf(args);
      let list = [...r.pulls].sort((a, b) => b.number - a.number);
      if (args.state && String(args.state).toLowerCase() !== 'all') list = list.filter(p => (p.state || 'open') === String(args.state).toLowerCase());
      return mcpPage(list, args).map(p => pullJSON(req, r, p));
    }
    case 'get_pull_request': { const r = mcpRepoOf(args); return pullJSON(req, r, mcpPullOf(r, args)); }
    case 'create_pull_request': {
      const r = mcpRepoOf(args);
      if (!args.title) throw new Error('title is required');
      const item = { id: state.nextIssueId++, number: r.nextNumber++, title: String(args.title), body: args.body ? String(args.body) : '', state: 'open', user: args.owner || r.owner, labels: [], comments: [], createdSeq: nextSeq(), updatedSeq: 0, isPull: true, head: String(args.head || ''), base: args.base ? String(args.base) : r.defaultBranch, draft: !!args.draft, merged: false };
      item.headSha = resolveRef(r, item.head); item.baseSha = resolveRef(r, item.base);
      r.pulls.push(item); scheduleSave();
      return pullJSON(req, r, item);
    }
    case 'update_pull_request': {
      const r = mcpRepoOf(args); const p = mcpPullOf(r, args);
      if (args.title !== undefined) p.title = String(args.title);
      if (args.body !== undefined) p.body = String(args.body);
      if (args.state !== undefined) p.state = String(args.state).toLowerCase();
      if (args.base !== undefined) { p.base = String(args.base); p.baseSha = resolveRef(r, p.base); }
      p.updatedSeq = nextSeq(); scheduleSave();
      return pullJSON(req, r, p);
    }
    case 'merge_pull_request': {
      const r = mcpRepoOf(args); const p = mcpPullOf(r, args);
      p.merged = true; p.state = 'closed'; p.updatedSeq = nextSeq(); scheduleSave();
      return { sha: p.headSha || '', merged: true, message: 'Pull Request successfully merged' };
    }
    case 'get_pull_request_files': {
      const r = mcpRepoOf(args); const p = mcpPullOf(r, args);
      return gqlChangedFiles(r, p).map(f => ({ filename: f.path, status: f.changeType === 'ADDED' ? 'added' : f.changeType === 'DELETED' ? 'removed' : 'modified', additions: 0, deletions: 0 }));
    }
  }
  throw new Error('unknown tool: ' + name);
}
function mcpHandleOne(req, msg) {
  const id = msg && msg.id !== undefined ? msg.id : null;
  const isNotification = !msg || msg.id === undefined;
  if (!msg || typeof msg.method !== 'string') return { jsonrpc: '2.0', id, error: { code: -32600, message: 'invalid request' } };
  if (msg.method.startsWith('notifications/')) return null;
  switch (msg.method) {
    case 'initialize': {
      const want = msg.params && msg.params.protocolVersion;
      const known = ['2024-11-05', '2025-03-26', '2025-06-18'];
      return { jsonrpc: '2.0', id, result: { protocolVersion: known.includes(want) ? want : '2024-11-05', capabilities: { tools: { listChanged: false } }, serverInfo: { name: 'forge-mcp', version: '1.1.0' } } };
    }
    case 'ping': return { jsonrpc: '2.0', id, result: {} };
    case 'tools/list': return { jsonrpc: '2.0', id, result: { tools: MCP_TOOLS } };
    case 'tools/call': {
      try {
        const result = mcpCallTool(req, msg.params && msg.params.name, msg.params && msg.params.arguments);
        return { jsonrpc: '2.0', id, result: { content: [{ type: 'text', text: JSON.stringify(result) }], isError: false } };
      } catch (e) {
        return { jsonrpc: '2.0', id, result: { content: [{ type: 'text', text: String((e && e.message) || e) }], isError: true } };
      }
    }
    case 'resources/list': return { jsonrpc: '2.0', id, result: { resources: [] } };
    case 'resources/templates/list': return { jsonrpc: '2.0', id, result: { resourceTemplates: [] } };
    case 'prompts/list': return { jsonrpc: '2.0', id, result: { prompts: [] } };
    default:
      if (isNotification) return null;
      return { jsonrpc: '2.0', id, error: { code: -32601, message: 'method not found: ' + msg.method } };
  }
}
function handleMCP(req, res, bodyObj) {
  if (req.method === 'GET') { sendJSON(res, 200, { name: 'forge-mcp', version: '1.1.0', protocolVersion: '2024-11-05', tools: MCP_TOOLS.map(t => t.name) }); return; }
  if (Array.isArray(bodyObj)) {
    const replies = bodyObj.map(m => mcpHandleOne(req, m)).filter(x => x !== null);
    if (!replies.length) { res.writeHead(202); res.end(); return; }
    sendJSON(res, 200, replies); return;
  }
  const reply = mcpHandleOne(req, bodyObj || {});
  if (reply === null) { res.writeHead(202); res.end(); return; }
  if (bodyObj && bodyObj.method === 'initialize') res.setHeader('Mcp-Session-Id', 'forge-session');
  sendJSON(res, 200, reply);
}

// ---------------- HTTP server ----------------
function readBody(req) {
  return new Promise((resolve, reject) => {
    const chunks = []; let total = 0;
    req.on('data', c => { total += c.length; if (total > 512 * 1024 * 1024) { reject(new Error('body too large')); req.destroy(); return; } chunks.push(c); });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
async function handleRequest(req, res) {
  try {
    const u = new URL(req.url, 'http://localhost');
    const pathname = u.pathname;
    const query = u.searchParams;
    // health / export / meta
    if (pathname === '/healthz' || pathname === '/health') { sendJSON(res, 200, { status: 'ok', repos: state.repos.size }); return; }
    if (pathname === '/__export' || pathname === '/__state' || pathname === '/export') {
      const body = canonicalJSON(exportState());
      res.writeHead(200, { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(body) });
      res.end(body); return;
    }
    if (pathname === '/' && req.method === 'GET') { sendJSON(res, 200, { name: 'forge', version: '1.0.0', message: 'forge git server', documentation_url: baseUrl(req) + '/api/v3' }); return; }
    // git smart HTTP: /{owner}/{repo}.git/...
    const gitMatch = pathname.match(/^\/([^/]+)\/([^/]+?)(\.git)?\/(info\/refs|git-upload-pack|git-receive-pack)$/);
    if (gitMatch) {
      const owner = decodeURIComponent(gitMatch[1]); const name = decodeURIComponent(gitMatch[2]);
      const action = gitMatch[4];
      if (action === 'info/refs') {
        const service = query.get('service');
        if (service !== 'git-upload-pack' && service !== 'git-receive-pack') { res.writeHead(400); res.end('service required'); return; }
        let repo = getRepo(owner, name);
        if (!repo) {
          if (service === 'git-receive-pack') repo = createRepo(owner, name, {});
          else { res.writeHead(404, { 'Content-Type': 'text/plain' }); res.end('repository not found'); return; }
        }
        const body = advertiseRefs(repo, service);
        res.writeHead(200, { 'Content-Type': 'application/x-' + service + '-advertisement', 'Cache-Control': 'no-cache', 'Expires': 'Fri, 01 Jan 1980 00:00:00 GMT', 'Pragma': 'no-cache' });
        res.end(body); return;
      }
      const body = await readBody(req);
      let repo = getRepo(owner, name);
      if (!repo) {
        if (action === 'git-receive-pack') repo = createRepo(owner, name, {});
        else { res.writeHead(404); res.end('repository not found'); return; }
      }
      if (action === 'git-upload-pack') handleUploadPack(req, res, repo, body);
      else handleReceivePack(req, res, repo, body);
      return;
    }
    // GraphQL
    if (pathname === '/graphql' || pathname === '/api/graphql' || pathname === '/api/v3/graphql') {
      if (req.method === 'GET') {
        const q = query.get('query') || '';
        let gvars = {};
        try { gvars = JSON.parse(query.get('variables') || '{}'); } catch (e) { /* ignore */ }
        handleGraphQL(req, res, { query: q, variables: gvars, operationName: query.get('operationName') || undefined }); return;
      }
      const body = await readBody(req);
      let obj = {}; try { obj = JSON.parse(body.toString('utf8') || '{}'); } catch (e) { /* ignore */ }
      handleGraphQL(req, res, obj); return;
    }
    // MCP
    if (pathname === '/mcp' || pathname === '/api/mcp') {
      if (req.method === 'GET') { handleMCP(req, res, null); return; }
      const body = await readBody(req);
      let obj = {}; try { obj = JSON.parse(body.toString('utf8') || '{}'); } catch (e) { sendJSON(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'parse error' } }); return; }
      handleMCP(req, res, obj); return;
    }
    // REST: strip optional /api/v3 or /api prefix
    let restPath = pathname;
    if (restPath.startsWith('/api/v3/')) restPath = restPath.slice(7);
    else if (restPath === '/api/v3') restPath = '/';
    else if (restPath.startsWith('/api/')) restPath = restPath.slice(4);
    const seg = restPath.split('/').filter(s => s.length > 0);
    let bodyObj = null;
    if (['POST', 'PUT', 'PATCH', 'DELETE'].includes(req.method)) {
      const body = await readBody(req);
      if (body.length) { try { bodyObj = JSON.parse(body.toString('utf8')); } catch (e) { bodyObj = null; } }
    }
    if (seg.length === 0 && req.method === 'GET') { sendJSON(res, 200, { current_user_url: baseUrl(req) + '/user' }); return; }
    const handled = handleREST(req, res, seg, query, bodyObj);
    if (!handled) notFound(res);
  } catch (e) {
    try { sendJSON(res, 500, { message: 'Internal error: ' + (e && e.message) }); } catch (_) { /* socket gone */ }
  }
}

// ---------------- make.fun trial env ----------------
// When the trial environment is present (MAKEFUN_ENV_URL set), the suite
// waits beside this program: the program POSTs {"port": <port>} to
// $MAKEFUN_ENV_URL/register, the suite drives the forge, and meanwhile the
// program long-polls GET $MAKEFUN_ENV_URL/done; on {"done": true} it exits 0.
// Without the variable (local runs) the forge just serves, as before.
function envRequest(method, envUrl, suffix, body) {
  return new Promise((resolve) => {
    let u;
    try { u = new URL(envUrl + suffix); } catch (e) { resolve(null); return; }
    const lib = u.protocol === 'https:' ? require('node:https') : http;
    const payload = body ? JSON.stringify(body) : null;
    const headers = {};
    if (payload) { headers['Content-Type'] = 'application/json'; headers['Content-Length'] = Buffer.byteLength(payload); }
    const req = lib.request({ method, hostname: u.hostname, port: u.port, path: u.pathname, headers, timeout: 30000 }, (res) => {
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => {
        let parsed = null;
        try { parsed = JSON.parse(Buffer.concat(chunks).toString('utf8')); } catch (e) { /* not json */ }
        resolve(parsed);
      });
    });
    req.on('timeout', () => { req.destroy(); resolve(null); });
    req.on('error', () => resolve(null));
    if (payload) req.write(payload);
    req.end();
  });
}

async function announceToEnv(port) {
  const envUrl = process.env.MAKEFUN_ENV_URL;
  if (!envUrl) return;
  for (let attempt = 0; attempt < 120; attempt++) {
    const r = await envRequest('POST', envUrl, '/register', { port });
    if (r !== null) break;
    await new Promise((r2) => setTimeout(r2, 500));
  }
  for (;;) {
    const r = await envRequest('GET', envUrl, '/done', null);
    if (r && r.done === true) {
      try { saveState(); } catch (e) { /* ignore */ }
      process.exit(0);
    }
    await new Promise((r2) => setTimeout(r2, 250));
  }
}

function main() {
  loadState();
  const server = http.createServer((req, res) => { handleRequest(req, res); });
  server.on('error', (e) => { console.error('server error', e); });
  const requested = process.env.FORGE_PORT ? parseInt(process.env.FORGE_PORT, 10) : 0;
  const listenPort = requested && requested !== 8080 ? requested : 0;
  server.listen(listenPort, '0.0.0.0', () => {
    const port = server.address().port;
    console.log('forge listening on port ' + port);
    console.log('PORT=' + port);
    console.log('http://127.0.0.1:' + port);
    try { fs.writeFileSync(process.env.FORGE_PORT_FILE || path.join(process.cwd(), 'port.txt'), String(port) + '\n'); } catch (e) { /* ignore */ }
    try { fs.writeFileSync(path.join(process.cwd(), '.forge-port'), String(port) + '\n'); } catch (e) { /* ignore */ }
    announceToEnv(port);
  });
}
main();
