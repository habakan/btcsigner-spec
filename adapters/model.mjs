// What every adapter shares: the test wallet and its cosigners, turning a signer's view of a transaction
// into the case Main.lean reads, and the Lean process itself.
import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
import * as btc from "./bitcoin.mjs";

export const root = new URL("../", import.meta.url).pathname;
/** bitwasm-signer's checkout: one of the signers, and its build generates the PSBT vectors */
export const bitwasm = process.env.BITWASM ?? `${root}third_party/bitwasm-signer/`;
/** The PSBTs every comparison starts from: Bitcoin Core's rpc_psbt.json and the wallet vectors */
export const vectorDir = process.env.VECTORS ?? `${bitwasm}parser/build/vectors/`;

export const w = btc.wallet("abandon ".repeat(11) + "about");

// BIP48 P2WSH 2-of-3 test wallets: our seed with these cosigners. The witness scripts come from the
// cosigners' seeds; a signer under test reads the xpubs
export const ZOO = btc.wallet("zoo ".repeat(11) + "wrong");
export const LEGAL = btc.wallet("legal winner thank year wave sausage worth useful legal winner thank yellow");
export const LETTER = btc.wallet("letter advice cage absurd amount doctor acoustic avoid letter advice cage above");
export const ACCOUNT = [48 + btc.H, btc.H, btc.H, 2 + btc.H];
/** BIP48's account for P2SH-P2WSH, which the model does not describe */
export const NESTED_ACCOUNT = [48 + btc.H, btc.H, btc.H, 1 + btc.H];
export const XPUB = {
  "73c5da0a": "xpub6DkFAXWQ2dHxq2vatrt9qyA3bXYU4ToWQwCHbf5XB2mSTexcHZCeKS1VZYcPoBd5X8yVcbXFHJR9R8UCVpt82VX1VhR28mCyxUFL4r6KFrf",
  "3f635a63": "xpub6FHZCoNb3tg3o1GAJQxSwgFNF8mLRtTk2GgkF7n5rwzoxBhUEdFWa8cyZRHqytAzKZWsKz8627cQEMCCfR5GDSv6yXegqirpgDUX41Pxybr",
  "b8688df1": "xpub6FQya7zGhR92kacYsNnjreouvnHJMpXYsUXnW6NJJAJRCKsa26TzDy4LdnGhEurr3d6y1J8PJ7EEMKQp74XTqYvmGJNogYXSKDszYHtF8mX",
  "28645006": "xpub6DnEBNkSJKBYQmsbhS1sP9cNdtU5c9PLFGCjTJmxicxc13WB8zNNGQazabQpyFAGW5bV9tMko4uBxDxjUKL6dSAcx1tEbgEHtgSqyRsekh6",
};
export const fpHex = (m) => m.fingerprint.toString(16).padStart(8, "0");
const keyAt = (m, path) => btc.pubkey(btc.derive(m.master, path));
export const wsAt = (members, path) => btc.sortedmulti(2, members.map((m) => keyAt(m, path)));
const xkey = (m, account, steps = "0;1") =>
  `[${fpHex(m)}/${account.map((x) => `${x - btc.H}h`).join("/")}]${btc.xpub(m.master, account)}/<${steps}>/*`;

/** A registered wallet whose witness script at our key path m/48'/0'/0'/2'/chain/index is script(path).
 * second(k) is its other key of ours there, if it holds us twice on chains 2 and 3 as well */
function registered(descriptor, script, { nested = false, second = () => null, chains = 2 } = {}) {
  const account = nested ? NESTED_ACCOUNT : ACCOUNT;
  return {
    descriptor, second,
    /** The wallet's witness script at this key path of ours, or null when the path is not one of its own */
    at(k) {
      const ok = k.fp === w.fingerprint && k.path.length === 6 && account.every((x, i) => k.path[i] === x) &&
        k.path[4] < chains && k.path[5] < 100000;
      return ok ? script([...account, k.path[4] % 2, k.path[5]]) : null;
    },
    /** The script its keys at this path make, whatever the path: a cosigner may sign for any */
    spkAt(path) {
      if (path.length !== 6) return null;
      const s = btc.p2wsh(script(path));
      return nested ? btc.p2sh(s) : s;
    },
  };
}

export function multisig(members, nested = false) {
  const keys = members.map((m) => xkey(m, nested ? NESTED_ACCOUNT : ACCOUNT)).join(",");
  return { members, ...registered(nested ? `sh(wsh(sortedmulti(2,${keys})))` : `wsh(sortedmulti(2,${keys}))`,
    (path) => wsAt(members, path), { nested }) };
}

/** The cosigners' second account, for the or_d wallet's recovery path */
const RECOVERY_ACCOUNT = [48 + btc.H, btc.H, 1 + btc.H, 2 + btc.H];
const ourRecovery = (path) => [...ACCOUNT, path[4] + 2, path[5]];
const ourOther = (path) => [...ACCOUNT, path[4] < 2 ? path[4] + 2 : path[4] - 2, path[5]];
/** bitwasm-signer's own_or_d_two_keys_1in wallet: 2-of-3 of us, ZOO and LEGAL, or after 4320 blocks a 2-of-3
 * that reuses our seed on <2;3> */
export const orDAt = (path) => btc.orDScript({ m: 2, keys: [w, ZOO, LEGAL].map((m) => keyAt(m, path)) },
  { m: 2, keys: [keyAt(w, ourRecovery(path)), ...[ZOO, LEGAL].map((m) => keyAt(m, [...RECOVERY_ACCOUNT, ...path.slice(4)]))] },
  false, 4320);
const orDWallet = registered(`wsh(or_d(multi(2,${[w, ZOO, LEGAL].map((m) => xkey(m, ACCOUNT))}),and_v(v:multi(2,${
  [xkey(w, ACCOUNT, "2;3"), xkey(ZOO, RECOVERY_ACCOUNT), xkey(LEGAL, RECOVERY_ACCOUNT)]}),older(4320))))`, orDAt,
{ second: (k) => ({ fp: k.fp, path: ourOther(k.path) }), chains: 4 });

export const WALLETS = {
  ours: multisig([w, ZOO, LEGAL]), other: multisig([w, ZOO, LETTER]), nested: multisig([w, ZOO, LEGAL], true), orD: orDWallet,
};

/** The single-sig script of ours at m/purpose'/coin'/account'/chain/index */
export function ourScript(path) {
  const k = btc.derive(w.master, path), pub = btc.pubkey(k);
  return path[0] === 84 + btc.H ? btc.p2wpkh(pub) : path[0] === 49 + btc.H ? btc.p2shP2wpkh(pub) : btc.p2tr(k);
}

const hex = (b) => Buffer.from(b).toString("hex");

/** The JSON case Main.lean reads, from a signer's view: inputs {amount, spk, key, sighash, ws, txid, prev} and
 * outputs {amount, spk, key}, keys being the PSBT's claims. `owns` and the wallet list only what holds.
 * `policy` is what the signer the model stands for signs besides: {legacy, nested, orD} */
export function caseFor(view, network, ms, policy = {}) {
  const owns = [];
  const ask = (key, spk, ws) => {
    if (key && btc.owns(w, key, spk, ws)) owns.push({ fp: key.fp, path: key.path, spk: hex(spk), ws: ws ? hex(ws) : null });
  };
  const walletIns = ms ? view.inputs.filter((x) => x.key && x.ws && ms.at(x.key)?.equals(x.ws)) : [];
  view.inputs.forEach((x) => ask(x.key, x.spk, x.ws));
  walletIns.forEach((x) => ms.second(x.key) && ask(ms.second(x.key), x.spk, x.ws));
  view.outputs.forEach((x) => ask(x.key, x.spk, null));
  return {
    network, fingerprint: w.fingerprint, owns, legacy: !!policy.legacy, nested: !!policy.nested, orD: !!policy.orD,
    inputs: view.inputs.map((x) => ({
      amount: String(x.amount), spk: hex(x.spk), key: x.key, sighash: x.sighash, ws: x.ws ? hex(x.ws) : null, txid: hex(x.txid),
      prev: x.prevInfo && { txid: hex(x.prevInfo.txid), out: x.prevInfo.out && { amount: String(x.prevInfo.out.amount), spk: hex(x.prevInfo.out.spk) } },
    })),
    outputs: view.outputs.map((x) => ({ amount: String(x.amount), spk: hex(x.spk), key: x.key })),
    wallet: ms ? {
      inputs: walletIns.map((x) => ({ fp: x.key.fp, path: x.key.path, ws: hex(x.ws), second: ms.second(x.key) })),
      outputs: view.outputs.filter((x) => x.key && ms.at(x.key) && ms.spkAt(x.key.path).equals(x.spk))
        .map((x) => ({ fp: x.key.fp, path: x.key.path, spk: hex(x.spk), chain: x.key.path[4] % 2 })),
    } : null,
  };
}

/** The Lean model as a process: one case in, one verdict out */
export function startModel() {
  const lean = spawn(`${root}.lake/build/bin/signer-spec`, [], { stdio: ["pipe", "pipe", "inherit"] });
  const lines = createInterface({ input: lean.stdout })[Symbol.asyncIterator]();
  return {
    async review(c) {
      lean.stdin.write(JSON.stringify(c) + "\n");
      const v = JSON.parse((await lines.next()).value);
      if (v.fatal) throw new Error(`the model could not read a case: ${v.fatal}`);
      return v;
    },
    /** What Notation.lean writes for this script on `network` ("main", "test" or "regtest") */
    async render(network, spk) {
      lean.stdin.write(JSON.stringify({ render: { network, spk: Buffer.from(spk).toString("hex") } }) + "\n");
      const v = JSON.parse((await lines.next()).value);
      if (v.fatal) throw new Error(`the model could not render a script: ${v.fatal}`);
      return v.address;
    },
    /** What Message.lean shows for these bytes: { kind: "text" | "hex", text } */
    async message(bytes) {
      lean.stdin.write(JSON.stringify({ message: Buffer.from(bytes).toString("hex") }) + "\n");
      const v = JSON.parse((await lines.next()).value);
      if (v.fatal) throw new Error(`the model could not show a message: ${v.fatal}`);
      return v;
    },
    stop() { lean.stdin.end(); },
  };
}

export function rng(seed) {
  let s = seed >>> 0 || 1;
  return () => ((s ^= s << 13, s ^= s >>> 17, s ^= s << 5) >>> 0) / 4294967296;
}
