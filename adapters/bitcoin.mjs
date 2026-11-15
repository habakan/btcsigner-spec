// What the model takes as given, computed with node:crypto alone so that it shares no code with any
// signer under test: BIP32 derivation, the scripts a key makes, and checking a previous transaction.
import { ECDH, createECDH, createHash, createHmac, createPublicKey, pbkdf2Sync, verify as cryptoVerify } from "node:crypto";

export const H = 0x80000000;
const N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n;

const sha256 = (b) => createHash("sha256").update(b).digest();
const hash160 = (b) => createHash("ripemd160").update(sha256(b)).digest();
const big = (b) => BigInt("0x" + Buffer.from(b).toString("hex"));
const b32 = (n) => Buffer.from(n.toString(16).padStart(64, "0"), "hex");
const u32be = (i) => { const b = Buffer.alloc(4); b.writeUInt32BE(i); return b; };
const taggedHash = (tag, b) => sha256(Buffer.concat([sha256(tag), sha256(tag), b]));

function pubkey(k) {
  const e = createECDH("secp256k1");
  e.setPrivateKey(k);
  return e.getPublicKey(null, "compressed");
}

export function wallet(mnemonic, passphrase = "") {
  const seed = pbkdf2Sync(mnemonic, "mnemonic" + passphrase, 2048, 64, "sha512");
  const I = createHmac("sha512", "Bitcoin seed").update(seed).digest();
  const master = { k: I.subarray(0, 32), c: I.subarray(32) };
  return { master, fingerprint: hash160(pubkey(master.k)).readUInt32BE(0) };
}

const derived = new Map();
export function derive(master, path) {
  const id = master.c.toString("hex") + path.join("/");
  if (!derived.has(id)) derived.set(id, deriveUncached(master, path));
  return derived.get(id);
}
function walk(master, path) {
  let { k, c } = master, parent = null;
  for (const i of path) {
    const data = i >= H ? Buffer.concat([Buffer.alloc(1), k, u32be(i)]) : Buffer.concat([pubkey(k), u32be(i)]);
    const I = createHmac("sha512", c).update(data).digest();
    parent = k;
    k = b32((big(I.subarray(0, 32)) + big(k)) % N);
    c = I.subarray(32);
  }
  return { k, c, parent };
}
const deriveUncached = (master, path) => walk(master, path).k;

const B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
function base58check(payload) {
  const b = Buffer.concat([payload, sha256(sha256(payload)).subarray(0, 4)]);
  let n = big(b), s = "";
  for (; n > 0n; n /= 58n) s = B58[Number(n % 58n)] + s;
  for (const x of b) { if (x) break; s = "1" + s; }
  return s;
}
/** The mainnet xpub at this path, as a descriptor names a cosigner */
export function xpub(master, path) {
  const { k, c, parent } = walk(master, path);
  return base58check(Buffer.concat([Buffer.from("0488b21e", "hex"), Buffer.from([path.length]),
    parent ? hash160(pubkey(parent)).subarray(0, 4) : Buffer.alloc(4), u32be(path.at(-1) ?? 0), c, pubkey(k)]));
}

export function p2wpkh(pub) { return Buffer.concat([Buffer.from([0x00, 0x14]), hash160(pub)]); }
export function p2shP2wpkh(pub) {
  return Buffer.concat([Buffer.from([0xa9, 0x14]), hash160(p2wpkh(pub)), Buffer.from([0x87])]);
}
/** BIP86: the key-path-only taproot output key, tweaking the secret so no point addition is needed */
export function p2tr(k) {
  const p = pubkey(k);
  const d = p[0] === 3 ? N - big(k) : big(k);
  const q = pubkey(b32((d + big(taggedHash("TapTweak", p.subarray(1)))) % N));
  return Buffer.concat([Buffer.from([0x51, 0x20]), q.subarray(1)]);
}

export function p2wsh(ws) { return Buffer.concat([Buffer.from([0x00, 0x20]), sha256(ws)]); }
export function p2sh(redeem) { return Buffer.concat([Buffer.from([0xa9, 0x14]), hash160(redeem), Buffer.from([0x87])]); }
/** BIP67 sortedmulti: OP_m, the keys in byte order, OP_n, OP_CHECKMULTISIG */
export function sortedmulti(m, pubs) {
  const keys = [...pubs].sort(Buffer.compare).map((k) => Buffer.concat([Buffer.from([33]), k]));
  return Buffer.concat([Buffer.from([0x50 + m]), ...keys, Buffer.from([0x50 + pubs.length, 0xae])]);
}

/** The keys of OP_m <n distinct compressed keys> OP_n OP_CHECKMULTISIG, or [] for any other script */
export function multisigKeys(w) {
  const n = w.length >= 3 ? Math.floor((w.length - 3) / 34) : 0, m = w[0] - 0x50;
  if (n === 0 || w.length !== 3 + 34 * n || m < 1 || m > n || w[w.length - 2] !== 0x50 + n || w[w.length - 1] !== 0xae)
    return [];
  const keys = [];
  for (let i = 0; i < n; i++) {
    if (w[1 + 34 * i] !== 33 || (w[2 + 34 * i] !== 2 && w[2 + 34 * i] !== 3)) return [];
    const key = w.subarray(2 + 34 * i, 2 + 34 * i + 33);
    if (keys.some((x) => x.equals(key))) return [];
    keys.push(key);
  }
  return keys;
}

const scriptNum = (n) => {
  if (n <= 16) return Buffer.from([0x50 + n]);
  const b = [];
  for (let v = n; v; v = Math.floor(v / 256)) b.push(v % 256);
  if (b.at(-1) & 0x80) b.push(0);
  return Buffer.from([b.length, ...b]);
};
const check = (c, verify) => c.hash
  ? Buffer.concat([Buffer.from([0x76, 0xa9, 0x14]), c.hash, Buffer.from([0x88, 0xac + verify])])
  : c.keys.length === 1 ? Buffer.concat([Buffer.from([33]), c.keys[0], Buffer.from([0xac + verify])])
  : Buffer.concat([Buffer.from([0x50 + c.m]), ...c.keys.map((k) => Buffer.concat([Buffer.from([33]), k])),
    Buffer.from([0x50 + c.keys.length, 0xae + verify])]);
const okKey = (k) => k.length === 33 && (k[0] === 2 || k[0] === 3);
/** The or_d script of paths x and y ({m, keys} or {hash}), after(lock) or older(lock) */
export const orDScript = (x, y, after, lock) => Buffer.concat([check(x, 0), Buffer.from([0x73, 0x64]), check(y, 1),
  scriptNum(lock), Buffer.from([after ? 0xb1 : 0xb2, 0x68])]);

/** or_d(X,and_v(v:Y,older(n))) or after(n), X pk() or multi() of 2 or 3 keys and Y those or pkh(): its keys and
 * pkh()'s HASH160, or null. Read loosely, then accepted only if writing it back gives the same bytes */
export function orD(w) {
  const read = (o, verify) => {
    if (w[o] === 0x76) return verify ? { keys: [], hash: w.subarray(o + 3, o + 23) } : null;
    if (w[o] === 33) return { keys: [w.subarray(o + 1, o + 34)] };
    const keys = [];
    for (let p = o + 1; keys.length < 3 && w[p] === 33; p += 34) keys.push(w.subarray(p + 1, p + 34));
    return keys.length >= 2 && w[o] - 0x50 >= 1 && w[o] - 0x50 <= keys.length ? { m: w[o] - 0x50, keys } : null;
  };
  const x = read(0, 0);
  if (!x) return null;
  const y = read(check(x, 0).length + 2, 1);
  if (!y) return null;
  const at = check(x, 0).length + 2 + check(y, 1).length, push = w.subarray(at, w.length - 2);
  const lock = push.length === 1 ? push[0] - 0x50 : push.subarray(1).reduceRight((v, b) => v * 256 + b, 0);
  const keys = [...x.keys, ...y.keys];
  if (!(lock >= 1 && lock < 2 ** 31) || !keys.every(okKey) || new Set(keys.map((k) => k.toString("hex"))).size !== keys.length ||
      (y.hash && y.hash.length !== 20)) return null;
  return orDScript(x, y, w[w.length - 2] === 0xb1, lock).equals(w) ? { keys, hash: y.hash ?? null } : null;
}

/** Does the key at this path produce this script? The question the model calls `Env.owns`. */
export function owns(w, key, spk, ws) {
  if (key.fp !== w.fingerprint) return false;
  const k = derive(w.master, key.path);
  if (spk.length === 22 && spk[0] === 0x00 && spk[1] === 20) return p2wpkh(pubkey(k)).equals(spk);
  if (spk.length === 23 && spk[0] === 0xa9 && spk[1] === 20 && spk[22] === 0x87) {
    if (!ws) return p2shP2wpkh(pubkey(k)).equals(spk);
    const pub = pubkey(k);
    return p2sh(p2wsh(ws)).equals(spk) && multisigKeys(ws).some((x) => x.equals(pub));
  }
  if (spk.length === 34 && spk[0] === 0x51 && spk[1] === 32) return p2tr(k).equals(spk);
  if (spk.length === 25 && spk[0] === 0x76) return p2pkhCode(pubkey(k)).equals(spk);
  if (spk.length === 34 && spk[0] === 0x00 && spk[1] === 32 && ws) {
    const pub = pubkey(k);
    const d = orD(ws);
    return sha256(ws).equals(spk.subarray(2)) && (multisigKeys(ws).some((x) => x.equals(pub)) ||
      !!d && (d.keys.some((x) => x.equals(pub)) || !!d.hash?.equals(hash160(pub))));
  }
  return false;
}

export { pubkey };

function reader(b) {
  let o = 0;
  const need = (n) => { if (o + n > b.length) throw new RangeError("short"); };
  const r = {
    bytes(n) { need(n); const s = b.subarray(o, o + n); o += n; return s; },
    u8() { return r.bytes(1)[0]; },
    u32() { return r.bytes(4).readUInt32LE(0); },
    u64() { return r.bytes(8).readBigUInt64LE(0); },
    varint() {
      const x = r.u8();
      return x < 0xfd ? x : x === 0xfd ? r.bytes(2).readUInt16LE(0) : x === 0xfe ? r.u32() : Number(r.u64());
    },
    get off() { return o; },
  };
  return r;
}

/** What a previous transaction says, as Model.lean's `PrevInfo`: null when absent, else its txid and its
 * output `vout` ({amount, spk} or null). One that does not parse gets an empty txid, which matches none */
export function prevInfo(raw, vout) {
  if (!raw) return null;
  try {
    const r = reader(Buffer.from(raw));
    const version = r.bytes(4);
    let segwit = false;
    if (raw[4] === 0 && raw[5] === 1) { r.bytes(2); segwit = true; }
    const startIn = r.off;
    const nIn = r.varint();
    for (let i = 0; i < nIn; i++) { r.bytes(36); r.bytes(r.varint()); r.bytes(4); }
    const nOut = r.varint();
    let out = null;
    for (let i = 0; i < nOut; i++) {
      const amount = r.u64(), spk = Buffer.from(r.bytes(r.varint()));
      if (i === vout) out = { amount, spk };
    }
    const endOut = r.off;
    if (segwit) for (let i = 0; i < nIn; i++) { const n = r.varint(); for (let j = 0; j < n; j++) r.bytes(r.varint()); }
    const locktime = r.bytes(4);
    if (r.off !== raw.length) throw new RangeError("trailing bytes");
    return { txid: sha256(sha256(Buffer.concat([version, Buffer.from(raw).subarray(startIn, endOut), locktime]))), out };
  } catch {
    return { txid: Buffer.alloc(0), out: null };
  }
}

/** `PrevTx.of` in Model.lean: the txid alone does not bind the amount, so the output is compared too */
export function prevStatus(info, txid, amount, spk) {
  if (!info) return "absent";
  return info.txid.equals(Buffer.from(txid)) && info.out?.amount === amount && info.out.spk.equals(spk) ? "matches" : "mismatch";
}

// --- what a signature commits to: BIP143 and BIP341 key path, SIGHASH_ALL (or DEFAULT) only, as the model allows
const u32le = (i) => { const b = Buffer.alloc(4); b.writeUInt32LE(i >>> 0); return b; };
const u64le = (n) => { const b = Buffer.alloc(8); b.writeBigUInt64LE(n); return b; };
const varstr = (s) => {
  if (s.length >= 0xfd) throw new RangeError("script too long for this helper");
  return Buffer.concat([Buffer.from([s.length]), s]);
};
const outpoint = (x) => Buffer.concat([Buffer.from(x.txid), u32le(x.vout)]);
const serOut = (o) => Buffer.concat([u64le(o.amount), varstr(o.spk)]);

/** SHA-256 of the BIP143 preimage: its second SHA-256 is what the ECDSA signature signs */
export function sighashV0(tx, i, scriptCode) {
  const d = (l) => sha256(sha256(Buffer.concat(l)));
  const x = tx.inputs[i];
  return sha256(Buffer.concat([
    u32le(tx.version), d(tx.inputs.map(outpoint)), d(tx.inputs.map((y) => u32le(y.sequence))),
    outpoint(x), varstr(scriptCode), u64le(x.amount), u32le(x.sequence), d(tx.outputs.map(serOut)),
    u32le(tx.locktime), u32le(1),
  ]));
}

export function sighashTaproot(tx, i, hashType) {
  const s = (l) => sha256(Buffer.concat(l));
  return taggedHash("TapSighash", Buffer.concat([
    Buffer.from([0, hashType]), u32le(tx.version), u32le(tx.locktime),
    s(tx.inputs.map(outpoint)), s(tx.inputs.map((y) => u64le(y.amount))), s(tx.inputs.map((y) => varstr(y.spk))),
    s(tx.inputs.map((y) => u32le(y.sequence))), s(tx.outputs.map(serOut)), Buffer.from([0]), u32le(i),
  ]));
}

export function p2pkhCode(pub) { return Buffer.concat([Buffer.from([0x76, 0xa9, 0x14]), hash160(pub), Buffer.from([0x88, 0xac])]); }

/** ECDSA over sha256(h), DER as in a witness without its sighash byte */
export function verifyEcdsa(pub, h, der) {
  const raw = ECDH.convertKey(pub, "secp256k1", null, null, "uncompressed");
  const key = createPublicKey({ key: { kty: "EC", crv: "secp256k1",
    x: raw.subarray(1, 33).toString("base64url"), y: raw.subarray(33).toString("base64url") }, format: "jwk" });
  return cryptoVerify("sha256", h, { key, dsaEncoding: "der" }, der);
}

// BIP340 verification, in Jacobian coordinates so no inverse is taken until the end
const P = 2n ** 256n - 2n ** 32n - 977n;
const G = [0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n,
  0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8n, 1n];
const mod = (a, m = P) => ((a % m) + m) % m;
const pow = (b, e) => { let r = 1n; for (b = mod(b); e; e >>= 1n, b = b * b % P) if (e & 1n) r = r * b % P; return r; };
function dbl([x, y, z]) {
  if (!y) return [0n, 1n, 0n];
  const s = 4n * x * y * y % P, m = 3n * x * x % P, x3 = mod(m * m - 2n * s);
  return [x3, mod(m * (s - x3) - 8n * y ** 4n), 2n * y * z % P];
}
function add(a, b) {
  if (!a[2]) return b;
  if (!b[2]) return a;
  const z1 = a[2] * a[2] % P, z2 = b[2] * b[2] % P;
  const u1 = a[0] * z2 % P, u2 = b[0] * z1 % P, s1 = a[1] * z2 * b[2] % P, s2 = b[1] * z1 * a[2] % P;
  if (u1 === u2) return s1 === s2 ? dbl(a) : [0n, 1n, 0n];
  const h = mod(u2 - u1), r = mod(s2 - s1), h2 = h * h % P, h3 = h2 * h % P;
  const x3 = mod(r * r - h3 - 2n * u1 * h2);
  return [x3, mod(r * (u1 * h2 - x3) - s1 * h3), h * a[2] * b[2] % P];
}
const mul = (pt, k) => { let r = [0n, 1n, 0n]; for (; k; k >>= 1n, pt = dbl(pt)) if (k & 1n) r = add(r, pt); return r; };

export function verifySchnorr(xonly, m, sig) {
  const px = big(xonly), r = big(sig.subarray(0, 32)), s = big(sig.subarray(32, 64));
  if (px >= P || r >= P || s >= N) return false;
  const c = mod(px ** 3n + 7n);
  let y = pow(c, (P + 1n) / 4n);
  if (y * y % P !== c) return false;
  if (y & 1n) y = P - y;
  const e = big(taggedHash("BIP0340/challenge", Buffer.concat([sig.subarray(0, 32), xonly, m]))) % N;
  const [X, Y, Z] = add(mul(G, s), mul([px, P - y, 1n], e));
  if (!Z) return false;
  const zi = pow(Z, P - 2n), zi2 = zi * zi % P;
  return X * zi2 % P === r && (Y * zi2 * zi % P & 1n) === 0n;
}

/** BIP86's output key for a secret, x-only */
export function p2trKey(k) { return p2tr(k).subarray(2); }
