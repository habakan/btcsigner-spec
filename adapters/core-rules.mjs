// One PSBT per row of the manual's review table and BIP 174 chapter, through the model and Bitcoin Core's
// wallet, so the manual's Bitcoin Core column is what Core does. Fails when either side changes.
// Usage: node adapters/core-rules.mjs
import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
import * as btc from "./bitcoin.mjs";
import * as P from "./psbt.mjs";
import { w, ZOO, LETTER, ACCOUNT, WALLETS, wsAt, caseFor, startModel, root } from "./model.mjs";

const MAX_MONEY = 2100000000000000n;
const u32 = (x) => { const b = Buffer.alloc(4); b.writeUInt32LE(x); return b; };
const at = (purpose, index, chain = 0) => [purpose + btc.H, btc.H, btc.H, chain, index];
const PAY = btc.p2wpkh(btc.pubkey(btc.derive(ZOO.master, at(84, 0))));

/** An input of `who` at `path`: its script, a previous transaction paying `prevAmount` to it, and the PSBT fields asked for */
function input(n, { type = "wpkh", path = at(84, n), keyPath = path, who = w, amount = 100000n, prevAmount = amount,
  wu = type !== "pkh", prev = type !== "tr", sighash = null, ws = null }) {
  const k = btc.derive(who.master, path), pub = btc.pubkey(k);
  const spk = ws ? btc.p2wsh(ws) : type === "pkh" ? btc.p2pkhCode(pub) : type === "tr" ? btc.p2tr(k) : btc.p2wpkh(pub);
  const raw = P.writeTx({ version: 2, locktime: 0, outputs: [{ amount: prevAmount, spk }],
    inputs: [{ txid: Buffer.alloc(32, n + 1), vout: 0, scriptSig: Buffer.alloc(0), sequence: 0xffffffff }] });
  const kp = btc.pubkey(btc.derive(who.master, keyPath));
  const m = [];
  if (prev) m.push([Buffer.from([0x00]), raw]);
  if (wu) m.push(P.witnessUtxo(amount, spk));
  if (sighash !== null) m.push([Buffer.from([0x03]), u32(sighash)]);
  if (ws) m.push([Buffer.from([0x05]), ws]);
  if (type === "tr") m.push([Buffer.concat([Buffer.from([0x16]), kp.subarray(1)]), P.outputDerivation(true, kp, who.fingerprint, keyPath)[1]]);
  else m.push(P.inputDerivation(kp, who.fingerprint, keyPath));
  return { txin: { txid: btc.prevInfo(raw, 0).txid, vout: 0, scriptSig: Buffer.alloc(0), sequence: 0xfffffffd }, m };
}

function psbt(inputs, outputs = [90000n]) {
  const ins = inputs.map((x, n) => input(n, x));
  const tx = { version: 2, locktime: 0, inputs: ins.map((x) => x.txin), outputs: outputs.map((amount) => ({ amount, spk: PAY })) };
  return { global: [[Buffer.from([0x00]), P.writeTx(tx)]], tx, inputs: ins.map((x) => x.m), outputs: outputs.map(() => []) };
}

const msPath = [...ACCOUNT, 0, 0];
const ROWS = [
  ["accepted", psbt([{}]), {}, "ok", "signs"],
  ["format: more than 16 outputs", psbt([{ amount: 2000000n }], Array(17).fill(1000n)), {}, "FORMAT", "signs"],
  ["format: inputs over 21M BTC", psbt([{ amount: MAX_MONEY }, { amount: MAX_MONEY }]), {}, "FORMAT", "signs"],
  ["script: a witness script it does not know", psbt([{ ws: Buffer.concat([Buffer.from([0x21]), btc.pubkey(btc.derive(w.master, msPath)), Buffer.from([0xac])]), path: msPath }]), { wallet: "ours" }, "SCRIPT", "signs"],
  ["sighash: NONE", psbt([{ sighash: 2 }]), {}, "SIGHASH", "refuses"],
  ["notOurs: the path does not make the script", psbt([{ keyPath: at(84, 5) }]), {}, "NOT_OURS", "signs"],
  ["wallet: a multisig not registered", psbt([{ ws: wsAt([w, ZOO, LETTER], msPath), path: msPath }]), { wallet: "ours" }, "WALLET", "signs"],
  ["nothingToSign: no input of ours", psbt([{ who: ZOO }]), {}, "NOTHING_TO_SIGN", "does not sign"],
  ["prevtxMismatch: the amounts disagree", psbt([{ prevAmount: 90001n }]), {}, "PREVTX_MISMATCH", "signs"],
  ["prevtxMissing: two SegWit v0 inputs, no previous transactions", psbt([{ prev: false }, { prev: false }], [190000n]), {}, "PREVTX_MISSING", "signs"],
  ["taproot: two inputs, no previous transactions", psbt([{ type: "tr", path: at(86, 0) }, { type: "tr", path: at(86, 1) }], [190000n]), {}, "ok", "signs"],
  ["legacy: only a witness UTXO", psbt([{ type: "pkh", path: at(44, 0), wu: true, prev: false }]), { wallet: "legacy", legacy: true }, "PREVTX_MISSING", "does not sign"],
  ["legacy: both UTXOs, agreeing", psbt([{ type: "pkh", path: at(44, 0), wu: true }]), { wallet: "legacy", legacy: true }, "ok", "signs"],
  ["format: outputs over 21M BTC", psbt([{}], [MAX_MONEY, MAX_MONEY]), {}, "FORMAT", "signs"],
  ["fee: outputs over inputs", psbt([{}], [100001n]), {}, "FEE", "signs"],
];

const core = spawn(process.execPath, [`${root}adapters/core-worker.mjs`, process.env.BITCOIND ?? "bitcoind"], { stdio: ["pipe", "pipe", "inherit"] });
const lines = createInterface({ input: core.stdout })[Symbol.asyncIterator]();
const model = startModel();
/** Core's wallet signs when `walletprocesspsbt` adds a signature; "fee" is a signature with no fee reported */
const coreVerdict = (c) => c.ok || c.error === "fee" ? "signs" : c.detail === "nothing signed" ? "does not sign" : "refuses";
let failed = 0;
for (const [name, p, cfg, wantModel, wantCore] of ROWS) {
  const ms = cfg.wallet === "ours" ? WALLETS.ours : null;
  const m = await model.review(caseFor(P.view(p, w.fingerprint), 0, ms, { legacy: !!cfg.legacy, nested: true }));
  core.stdin.write(JSON.stringify({ psbt: P.serialize(p).toString("base64"), config: { wallet: cfg.wallet ?? "single" } }) + "\n");
  const c = JSON.parse((await lines.next()).value);
  const got = [m.error ?? "ok", coreVerdict(c)], bad = got[0] !== wantModel || got[1] !== wantCore;
  failed += bad;
  console.log(`${bad ? "FAIL" : "ok  "} ${name}: model ${got[0]}, Core ${got[1]}${c.ok ? ` (fee ${c.ok.fee})` : c.detail ? ` (${c.detail})` : ""}`);
}
model.stop(); core.stdin.end();
process.exit(failed ? 1 : 0);
