// PSBT v0 read and written back as key-value maps, and what one says to a signer in the model's terms.
// Independent of every signer under test, so a PSBT can be mutated and handed to any of them.
import * as btc from "./bitcoin.mjs";

function reader(b) {
  let o = 0;
  const r = {
    bytes(n) { if (o + n > b.length) throw new RangeError("short"); const s = b.subarray(o, o + n); o += n; return s; },
    varint() {
      const x = r.bytes(1)[0];
      if (x < 0xfd) return x;
      const n = x === 0xfd ? 2 : x === 0xfe ? 4 : 8, v = r.bytes(n);
      return Number(n === 8 ? v.readBigUInt64LE(0) : v.readUIntLE(0, n));
    },
    get done() { return o === b.length; },
  };
  return r;
}
export function varint(n) {
  if (n < 0xfd) return Buffer.from([n]);
  const b = Buffer.alloc(n <= 0xffff ? 3 : 5);
  b[0] = n <= 0xffff ? 0xfd : 0xfe;
  n <= 0xffff ? b.writeUInt16LE(n, 1) : b.writeUInt32LE(n, 1);
  return b;
}
const withLen = (b) => Buffer.concat([varint(b.length), b]);

function readMap(r) {
  const m = [];
  for (let n = r.varint(); n; n = r.varint()) {
    const k = Buffer.from(r.bytes(n));
    m.push([k, Buffer.from(r.bytes(r.varint()))]);
  }
  return m;
}
const writeMap = (m) => Buffer.concat([...m.map(([k, v]) => Buffer.concat([withLen(k), withLen(v)])), Buffer.from([0])]);

/** A transaction; a previous one may carry witnesses, which are skipped */
function readTx(b) {
  const r = reader(b), u32 = () => r.bytes(4).readUInt32LE(0);
  const tx = { version: u32(), inputs: [], outputs: [] };
  const segwit = b[4] === 0 && b[5] === 1;
  if (segwit) r.bytes(2);
  for (let n = r.varint(); n; n--) tx.inputs.push({ txid: Buffer.from(r.bytes(32)), vout: u32(), scriptSig: Buffer.from(r.bytes(r.varint())), sequence: u32() });
  for (let n = r.varint(); n; n--) tx.outputs.push({ amount: r.bytes(8).readBigUInt64LE(0), spk: Buffer.from(r.bytes(r.varint())) });
  if (segwit) tx.inputs.forEach(() => { for (let n = r.varint(); n; n--) r.bytes(r.varint()); });
  tx.locktime = u32();
  return tx;
}
export function writeTx(tx) {
  const u32 = (x) => { const b = Buffer.alloc(4); b.writeUInt32LE(x); return b; };
  const u64 = (x) => { const b = Buffer.alloc(8); b.writeBigUInt64LE(x); return b; };
  return Buffer.concat([
    u32(tx.version), varint(tx.inputs.length),
    ...tx.inputs.map((x) => Buffer.concat([x.txid, u32(x.vout), withLen(x.scriptSig), u32(x.sequence)])),
    varint(tx.outputs.length), ...tx.outputs.map((x) => Buffer.concat([u64(x.amount), withLen(x.spk)])), u32(tx.locktime),
  ]);
}

export function parse(raw) {
  const r = reader(raw);
  if (!Buffer.from(r.bytes(5)).equals(Buffer.from("psbt\xff", "latin1"))) throw new Error("not a PSBT");
  const global = readMap(r);
  const unsigned = global.find(([k]) => k.length === 1 && k[0] === 0x00);
  if (!unsigned) throw new Error("no unsigned transaction");
  const tx = readTx(unsigned[1]);
  const p = { global, tx, inputs: tx.inputs.map(() => readMap(r)), outputs: tx.outputs.map(() => readMap(r)) };
  if (!r.done) throw new Error("trailing bytes");
  return p;
}

export function serialize(p) {
  const global = p.global.map(([k, v]) => [k, k.length === 1 && k[0] === 0x00 ? writeTx(p.tx) : v]);
  return Buffer.concat([Buffer.from("psbt\xff", "latin1"), writeMap(global), ...p.inputs.map(writeMap), ...p.outputs.map(writeMap)]);
}

export const clone = (p) => parse(serialize(p));
const keyed = (m) => m.map(([k]) => k.toString("hex"));
/** A key twice in a map, which BIP174 makes the PSBT invalid (Psbt.lean: readers then disagree) */
export const duplicated = (p) => [p.global, ...p.inputs, ...p.outputs].some((m) => new Set(keyed(m)).size !== m.length);
/** What a reader that keeps the last value of a repeated key sees; `parse` keeps the first */
export function lastWins(p) {
  const q = clone(p), last = (m) => m.filter((_, i) => keyed(m).lastIndexOf(keyed(m)[i]) === i);
  return { ...q, inputs: q.inputs.map(last), outputs: q.outputs.map(last) };
}
export const get = (m, type) => m.find(([k]) => k[0] === type)?.[1];
export const drop = (m, type) => m.filter(([k]) => k[0] !== type);

/** The first derivation naming this fingerprint, with its key: BIP32 entries of compressed keys, taproot
 * entries without leaf hashes. Depth 0 or over 8 names nobody */
function candidate(m, type, tap, fingerprint) {
  for (const [k, v] of m) {
    if (k[0] !== type) continue;
    let body = v;
    if (tap) {
      const n = reader(v).varint();
      if (n) continue;
      body = v.subarray(1);
    } else if (k.length !== 34) continue;
    if (body.length < 4 || body.length % 4 || body.readUInt32BE(0) !== fingerprint) continue;
    const path = [];
    for (let i = 4; i < body.length; i += 4) path.push(body.readUInt32LE(i));
    if (path.length > 8) continue;
    return { pub: k.subarray(1), key: path.length ? { fp: fingerprint, path } : null };
  }
  return null;
}

/** Every (fingerprint, path) a map's BIP32 or taproot derivations give, whatever their key or leaves */
export function derivations(m, bip32Type, tapType) {
  const out = [];
  for (const [k, v] of m) {
    if (k[0] !== bip32Type && k[0] !== tapType) continue;
    let body = v;
    if (k[0] === tapType) { const n = reader(v).varint(); body = v.subarray(varint(n).length + 32 * n); }
    if (body.length < 4 || body.length % 4) continue;
    const path = [];
    for (let i = 4; i < body.length; i += 4) path.push(body.readUInt32LE(i));
    out.push({ fp: body.readUInt32BE(0), path });
  }
  return out;
}

/** An input's BIP32 derivation entry (0x06) */
export const inputDerivation = (pub, fp, path) => [Buffer.from([0x06, ...pub]), outputDerivation(false, pub, fp, path)[1]];
/** A witness_utxo entry: the amount and script of the output an input spends */
export const witnessUtxo = (amount, spk) => {
  const v = Buffer.alloc(8); v.writeBigUInt64LE(amount);
  return [Buffer.from([0x01]), Buffer.concat([v, withLen(spk)])];
};

/** An output's BIP32 (0x02) or taproot (0x07, no leaf hashes) derivation entry */
export function outputDerivation(tap, pub, fp, path) {
  const v = Buffer.alloc(4 + 4 * path.length);
  v.writeUInt32BE(fp, 0);
  path.forEach((x, i) => v.writeUInt32LE(x, 4 + 4 * i));
  return tap ? [Buffer.concat([Buffer.from([0x07]), pub]), Buffer.concat([Buffer.from([0]), v])] : [Buffer.concat([Buffer.from([0x02]), pub]), v];
}

const isP2tr = (spk) => spk.length === 34 && spk[0] === 0x51 && spk[1] === 32;
const isP2wsh = (spk) => spk.length === 34 && spk[0] === 0x00 && spk[1] === 32;

const isP2pkh = (spk) => spk.length === 25 && spk[0] === 0x76 && spk[1] === 0xa9 && spk[2] === 20 && spk[23] === 0x88 && spk[24] === 0xac;
/** P2SH-P2WSH: a P2SH script whose redeem script is the P2WSH of this witness script */
const nestedWsh = (spk, redeem, ws) => spk.length === 23 && spk[0] === 0xa9 && redeem && ws && ws.length <= 105 &&
  redeem.length === 34 && redeem[0] === 0 && redeem[1] === 32 && btc.p2wsh(ws).equals(redeem);
const isWpkh = (spk) => (spk.length === 22 && spk[0] === 0x00 && spk[1] === 20) ||
  (spk.length === 23 && spk[0] === 0xa9 && spk[1] === 20 && spk[22] === 0x87);

/** The model's view of a PSBT for the signer with this fingerprint. An input may be its own when it is
 * P2PKH, P2WPKH (bare, or nested with a P2WPKH redeem script), P2WSH with a witness script (bare or nested), or P2TR with a
 * key-path derivation and no merkle root; and not finalized or already signed by it. An output may be its
 * own when it is P2WPKH or P2WSH with a derivation, or P2TR with one and no script tree */
export function view(p, fingerprint) {
  const inputs = p.inputs.map((m, i) => {
    const wu = get(m, 0x01), nwu = get(m, 0x00), txin = p.tx.inputs[i];
    let amount = 0n, spk = Buffer.alloc(0);
    if (wu) { const r = reader(wu); amount = r.bytes(8).readBigUInt64LE(0); spk = Buffer.from(r.bytes(r.varint())); }
    else if (nwu) ({ amount, spk } = readTx(nwu).outputs[txin.vout] ?? { amount, spk });
    const has = (type) => m.some(([k]) => k[0] === type);
    const bip = candidate(m, 0x06, false, fingerprint), tap = candidate(m, 0x16, true, fingerprint);
    const signedByUs = bip && m.some(([k]) => k[0] === 0x02 && k.length === 34 && k.subarray(1).equals(bip.pub));
    const redeem = get(m, 0x04), ws = get(m, 0x05);
    const wpkhRedeem = redeem && redeem.length === 22 && redeem[0] === 0 && redeem[1] === 20;
    let c = null;
    if (isWpkh(spk) && (spk.length === 22 || wpkhRedeem) && bip && !signedByUs) c = bip;
    else if (isP2wsh(spk) && ws && ws.length <= 105 && bip && !signedByUs) c = bip;
    else if (nestedWsh(spk, redeem, ws) && bip && !signedByUs) c = bip;
    else if (isP2tr(spk) && tap && !has(0x18) && !has(0x13)) c = tap;
    else if (isP2pkh(spk) && bip && !signedByUs) c = bip;
    const key = c && !has(0x07) && !has(0x08) ? c.key : null;
    const sh = get(m, 0x03), prevInfo = btc.prevInfo(nwu ?? null, txin.vout);
    return {
      amount, spk, key,
      sighash: !key ? 0 : sh ? sh.readUInt32LE(0) : isP2tr(spk) ? 0 : 1,
      ws: key && ws && (isP2wsh(spk) || nestedWsh(spk, redeem, ws)) ? ws : null,
      txid: txin.txid, prevInfo, prev: btc.prevStatus(prevInfo, txin.txid, amount, spk),
    };
  });
  const outputs = p.outputs.map((m, i) => {
    const spk = p.tx.outputs[i].spk;
    const bip = candidate(m, 0x02, false, fingerprint), tap = candidate(m, 0x07, true, fingerprint);
    const c = (isWpkh(spk) || isP2wsh(spk) || isP2pkh(spk)) && bip ? bip : isP2tr(spk) && tap && !m.some(([k]) => k[0] === 0x06) ? tap : null;
    return { amount: p.tx.outputs[i].amount, spk, key: c?.key ?? null };
  });
  return { inputs, outputs };
}
