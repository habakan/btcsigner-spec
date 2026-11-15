// bitwasm-signer's plan_t and the model's transaction, the mutations made on plans, and the parser that
// turns a PSBT into a plan, for adapters/bitwasm.mjs and other builds compared on the same cases
import { readFileSync } from "node:fs";
import * as btc from "./bitcoin.mjs";
import { w, ZOO, LEGAL, LETTER, ACCOUNT, wsAt, orDAt, ourScript, bitwasm } from "./model.mjs";

const MAX_MONEY = 2100000000000000n;
// plan_t version 3 (bitwasm-signer #23): a witness script holds an or_d of two three-key multis
export const VERSION = 3, NI = 16, NO = 16, SPK = 83, DEPTH = 8, WS = 219;
export const IN = 24, IN_SIZE = 176, OUT = IN + NI * IN_SIZE, OUT_SIZE = 136, WSO = OUT + NO * OUT_SIZE, WS_SIZE = WS + 1;
export const PLAN_SIZE = WSO + NI * WS_SIZE;

// --- plan_t <-> the model's transaction. Byte-level faults (padding, magic) are below the model: the
// adapter reports them as malformed and the signer must answer FORMAT
function decodeKey(v, o) {
  const depth = v.getUint8(o), fp = v.getUint32(o + 4, true);
  const path = [...Array(DEPTH)].map((_, i) => v.getUint32(o + 8 + 4 * i, true));
  if (depth > DEPTH || path.slice(depth).some((x) => x) || (depth === 0 && fp)) throw new Error("keypath");
  return depth ? { fp, path: path.slice(0, depth) } : null;
}
function decodeScript(b, o, cap) {
  const len = b[o];
  if (len > cap || b.subarray(o + 1 + len, o + 1 + cap).some((x) => x)) throw new Error("script");
  return Buffer.from(b.subarray(o + 1, o + 1 + len));
}

export function decodePlan(b) {
  const v = new DataView(b.buffer, b.byteOffset, b.byteLength);
  if (v.getUint32(0, true) !== 0x4e4c5042 || v.getUint32(4, true) !== VERSION) throw new Error("magic");
  const nIn = b[16], nOut = b[17];
  if (nIn > NI || nOut > NO) throw new Error("count");
  const plan = { head: Buffer.from(b.subarray(8, 16)), inputs: [], outputs: [] };
  for (let i = 0; i < NI; i++) {
    const o = IN + i * IN_SIZE, ws = WSO + i * WS_SIZE;
    if (i >= nIn) {
      if (b.subarray(o, o + IN_SIZE).some((x) => x) || b.subarray(ws, ws + WS_SIZE).some((x) => x)) throw new Error("unused");
      continue;
    }
    const wscript = decodeScript(b, ws, WS);
    plan.inputs.push({
      txid: Buffer.from(b.subarray(o, o + 32)), vout: v.getUint32(o + 32, true), sequence: v.getUint32(o + 36, true),
      amount: v.getBigUint64(o + 40, true), spk: decodeScript(b, o + 48, SPK), key: decodeKey(v, o + 132),
      sighash: b[o + 172], ws: wscript.length ? wscript : null,
    });
  }
  for (let i = 0; i < NO; i++) {
    const o = OUT + i * OUT_SIZE;
    if (i >= nOut) {
      if (b.subarray(o, o + OUT_SIZE).some((x) => x)) throw new Error("unused");
      continue;
    }
    plan.outputs.push({ amount: v.getBigUint64(o, true), spk: decodeScript(b, o + 8, SPK), key: decodeKey(v, o + 92) });
  }
  return plan;
}

export function encodePlan(p) {
  const b = new Uint8Array(PLAN_SIZE), v = new DataView(b.buffer);
  v.setUint32(0, 0x4e4c5042, true);
  v.setUint32(4, VERSION, true);
  b.set(p.head, 8);
  b[16] = p.inputs.length;
  b[17] = p.outputs.length;
  const key = (o, k) => {
    if (!k) return;
    b[o] = k.path.length;
    v.setUint32(o + 4, k.fp, true);
    k.path.forEach((x, i) => v.setUint32(o + 8 + 4 * i, x, true));
  };
  p.inputs.forEach((x, i) => {
    const o = IN + i * IN_SIZE;
    b.set(x.txid, o);
    v.setUint32(o + 32, x.vout, true);
    v.setUint32(o + 36, x.sequence, true);
    v.setBigUint64(o + 40, x.amount, true);
    b[o + 48] = x.spk.length;
    b.set(x.spk, o + 49);
    key(o + 132, x.key);
    b[o + 172] = x.sighash;
    if (x.ws) { b[WSO + i * WS_SIZE] = x.ws.length; b.set(x.ws, WSO + i * WS_SIZE + 1); }
  });
  p.outputs.forEach((x, i) => {
    const o = OUT + i * OUT_SIZE;
    v.setBigUint64(o, x.amount, true);
    b[o + 8] = x.spk.length;
    b.set(x.spk, o + 9);
    key(o + 92, x.key);
  });
  return b;
}


/** What the plan shows the model: each input's previous transaction already checked */
export function viewOf(p, prevTxs) {
  return {
    inputs: p.inputs.map((x, i) => {
      const prevInfo = btc.prevInfo(prevTxs[i], x.vout);
      return { ...x, prevInfo, prev: btc.prevStatus(prevInfo, x.txid, x.amount, x.spk) };
    }),
    outputs: p.outputs,
  };
}

// --- mutations: each picks a field the review decides on and moves it somewhere interesting
/** The same plan on coin 1': every single-sig key of ours moves there with its script. A moved input loses
 * its previous transaction, which no longer matches */
export function toTestnet(p, prev) {
  const move = (x) => {
    if (!x.key || x.key.fp !== w.fingerprint || x.key.path.length !== 5 || x.key.path[1] !== btc.H) return false;
    x.key = { ...x.key, path: x.key.path.map((v, j) => (j === 1 ? 1 + btc.H : v)) };
    x.spk = ourScript(x.key.path);
    return true;
  };
  p.inputs.forEach((x, i) => { if (move(x)) prev[i] = null; });
  p.outputs.forEach(move);
}

export function mutators(R) {
  const pick = (a) => a[Math.floor(R() * a.length)];
  const amounts = [0n, 1n, 546n, 100000n, MAX_MONEY - 1n, MAX_MONEY, MAX_MONEY + 1n, (1n << 63n), (1n << 64n) - 1n];
  return [
    ["output amount", (p) => { pick(p.outputs).amount = pick(amounts); }],
    ["output script replaced", (p) => {
      const h = (n) => Buffer.from(Array.from({ length: n }, () => Math.floor(R() * 256)));
      const o = pick(p.outputs);
      o.key = null;
      o.spk = pick([
        () => Buffer.concat([Buffer.from([0x76, 0xa9, 0x14]), h(20), Buffer.from([0x88, 0xac])]),
        () => Buffer.concat([Buffer.from([0xa9, 0x14]), h(20), Buffer.from([0x87])]),
        () => Buffer.concat([Buffer.from([0x00, 0x14]), h(20)]),
        () => Buffer.concat([Buffer.from([0x00, 0x20]), h(32)]),
        () => Buffer.concat([Buffer.from([0x51, 0x20]), h(32)]),
        () => Buffer.concat([Buffer.from([0x52, 0x10]), h(16)]),
        () => Buffer.concat([Buffer.from([0x6a, 0x4c, 80]), h(80)]),
        () => Buffer.from([0x6a]),
        () => h(1 + Math.floor(R() * SPK)),
      ])();
    }],
    ["input amount", (p) => { pick(p.inputs).amount = pick(amounts); }],
    ["sighash", (p) => { pick(p.inputs).sighash = pick([0, 1, 2, 3, 0x81, 0x83]); }],
    ["input key dropped", (p) => { const i = pick(p.inputs); i.key = null; i.sighash = 0; i.ws = null; }],
    ["input fingerprint", (p) => { const i = pick(p.inputs); if (i.key) i.key = { ...i.key, fp: i.key.fp ^ 1 }; }],
    ["input path", (p) => { const i = pick(p.inputs); if (i.key) i.key = { ...i.key, path: i.key.path.map((x, j) => j === 4 ? x + 1 : x) }; }],
    ["input script", (p) => { pick(p.inputs).spk = Buffer.from(pick([p.outputs[0].spk, Buffer.from("6a0401020304", "hex"), Buffer.alloc(0)])); }],
    ["witness script", (p) => {
      const i = pick(p.inputs);
      if (i.ws) i.ws = pick([null, i.ws.subarray(0, i.ws.length - 1), Buffer.concat([Buffer.from([0x54]), i.ws.subarray(1)])]);
    }],
    ["output key from an input", (p) => {
      const src = pick(p.inputs).key;
      if (src) pick(p.outputs).key = { fp: src.fp, path: src.path.map((x, j) => j === 3 ? pick([0, 1, 2]) : j === 4 ? pick([0, 7, 99999, 100000]) : x) };
    }],
    ["output made ours", (p) => {
      const src = pick(p.inputs).key;
      if (!src || src.path.length !== 5) return;
      const path = [src.path[0], pick([src.path[1], 1 + btc.H]), pick([src.path[2], src.path[2] + 1, 5]), pick([0, 1, 2]), pick([0, 3, 99999, 100000])];
      Object.assign(pick(p.outputs), { key: { fp: w.fingerprint, path }, spk: ourScript(path) });
    }],
    ["input made ours", (p, prev) => {
      const i = Math.floor(R() * p.inputs.length);
      const path = [pick([84, 49, 86]) + btc.H, pick([btc.H, 1 + btc.H]), btc.H, pick([0, 1]), pick([0, 2])];
      Object.assign(p.inputs[i], { key: { fp: w.fingerprint, path }, spk: ourScript(path), ws: null, sighash: 1 });
      if (R() < 0.7) prev[i] = null;
    }],
    ["output in a wallet", (p) => {
      const path = [...ACCOUNT, pick([0, 1, 2]), pick([0, 5, 99999, 100000])];
      const ws = pick([(p) => wsAt([w, ZOO, LEGAL], p), (p) => wsAt([w, ZOO, LETTER], p), orDAt])(path);
      Object.assign(pick(p.outputs), { key: { fp: pick([w.fingerprint, w.fingerprint, ZOO.fingerprint]), path }, spk: btc.p2wsh(ws) });
    }],
    ["input in a wallet", (p, prev) => {
      const i = Math.floor(R() * p.inputs.length), x = p.inputs[i];
      const path = [...ACCOUNT, pick([0, 1, 2]), pick([0, 1, 100000])];
      x.ws = pick([(p) => wsAt([w, ZOO, LEGAL], p), (p) => wsAt([w, ZOO, LETTER], p), (p) => wsAt([ZOO, LEGAL, LETTER], p), orDAt])(path);
      Object.assign(x, { spk: btc.p2wsh(x.ws), key: { fp: w.fingerprint, path }, sighash: 1 });
      if (R() < 0.5) prev[i] = null;
    }],
    ["output path element", (p) => {
      const o = pick(p.outputs);
      if (o.key) o.key = { ...o.key, path: o.key.path.map((x, j) => j === Math.floor(R() * o.key.path.length) ? pick([0, 1, 2, x ^ btc.H, 1 + btc.H]) : x) };
    }],
    ["output key dropped", (p) => { pick(p.outputs).key = null; }],
    ["output script swapped", (p) => { const a = pick(p.outputs), b = pick(p.outputs); [a.spk, b.spk] = [b.spk, a.spk]; }],
    ["output removed", (p) => { if (p.outputs.length > 1) p.outputs.pop(); else p.outputs = []; }],
    ["input removed", (p, prev) => { if (p.inputs.length > 1) { p.inputs.pop(); prev.pop(); } }],
    ["prevtx", (p, prev) => {
      const i = Math.floor(R() * p.inputs.length);
      if (!prev[i]) return;
      const raw = Uint8Array.from(prev[i]);
      if (R() < 0.3) prev[i] = null; else { raw[Math.floor(R() * raw.length)] ^= 1; prev[i] = raw; }
    }],
  ];
}

/** parser.wasm as a function from a PSBT to its plan and previous transactions, or null if refused */
export async function loadParser() {
  const P = (await WebAssembly.instantiate(readFileSync(`${bitwasm}build/parser.wasm`), {})).instance.exports;
  return function parse(psbt) {
    new Uint8Array(P.memory.buffer).set(psbt, P.parser_input());
    if (P.parser_parse(psbt.length, w.fingerprint) !== 0) return null;
    const mem = new Uint8Array(P.memory.buffer);
    const plan = mem.slice(P.parser_plan(), P.parser_plan() + PLAN_SIZE);
    const prev = [];
    for (let i = 0; i < plan[16]; i++) {
      const len = P.parser_prevtx_len(i), off = P.parser_input() + P.parser_prevtx_off(i);
      prev.push(len ? mem.slice(off, off + len) : null);
    }
    return { plan, prev };
  };
}
