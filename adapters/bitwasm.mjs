// Differential test: bitwasm-signer's signer.wasm against the Lean model, on the parser's vectors and on
// plans mutated from them. Usage: node adapters/bitwasm.mjs [cases per vector] [seed]
import { readFileSync, readdirSync } from "node:fs";
import { createHash } from "node:crypto";
import * as btc from "./bitcoin.mjs";
import * as PS from "./psbt.mjs";
import { w, WALLETS, caseFor, startModel, rng, bitwasm } from "./model.mjs";
import { OUT, decodePlan, encodePlan, viewOf, toTestnet, mutators, loadParser } from "./plan.mjs";

const { Signer, ERRORS } = await import(`${bitwasm}signer/hosts/js/signer.mjs`);

// --- driving both sides
const parse = await loadParser();
const signerWasm = readFileSync(`${bitwasm}build/signer.wasm`);
const S = await Signer.load(signerWasm, { sha256: createHash("sha256").update(signerWasm).digest("hex") });
// A second instance whose raw exports reach signer_sign past the JS wrapper's own check
const raw = (await WebAssembly.instantiate(signerWasm, {})).instance, R2 = new Signer(raw), E = raw.exports;
S.init();
S.seedFromMnemonic(new TextEncoder().encode("abandon ".repeat(11) + "about"));
R2.init().seedFromMnemonic(new TextEncoder().encode("abandon ".repeat(11) + "about"));
const NOT_REVIEWED = -Number(Object.keys(ERRORS).find((k) => ERRORS[k] === "NOT_REVIEWED"));

function signerVerdict(plan, prev) {
  S.setPlan(plan).setPrevTxs(prev);
  try {
    const r = S.review();
    return { ok: {
      totalIn: String(r.totalIn), totalOut: String(r.totalOut), fee: String(r.fee),
      willSign: r.willSign.slice(0, plan[16]).map((x) => x === 1), owners: r.owner.slice(0, plan[17]),
    }, display: S.display() };
  } catch (e) {
    if (e.code === undefined) throw e;
    return { error: ERRORS[e.code] };
  }
}

// Key order differs between the two sides, so compare a canonical form
const canon = (v) => JSON.stringify(v, Object.keys({ ok: 1, error: 1, totalIn: 1, totalOut: 1, fee: 1, willSign: 1, owners: 1 }));

const model = startModel();
const perVector = Number(process.argv[2] ?? 200);
const R = rng(Number(process.argv[3] ?? 1));
const muts = mutators(R);
const dir = `${bitwasm}parser/build/vectors/`;
const tally = {};
let cases = 0, diffs = 0, malformed = 0;

async function compare(name, plan, prev, cfg) {
  cases++;
  const got = signerVerdict(plan, prev);
  let decoded = null, want = { error: "FORMAT" };
  try {
    decoded = decodePlan(plan);
  } catch {
    malformed++;
  }
  if (decoded) want = await model.review(caseFor(viewOf(decoded, prev), cfg.network, cfg.wallet, { orD: true }));
  const owned = (got.ok?.owners ?? []).flatMap((x, i) =>
    x ? [`${x === 1 ? "change" : "self"}${decoded?.outputs[i].spk.length === 34 && decoded.outputs[i].spk[0] === 0 ? " (P2WSH)" : ""}`] : []);
  for (const k of [got.error ?? "OK", ...owned])
    tally[k] = (tally[k] ?? 0) + 1;
  if (canon(got) !== canon(want)) {
    diffs++;
    if (diffs <= 20) console.log(`DIFF ${name}\n  signer ${canon(got)}\n  model  ${canon(want)}`);
  }
  if (got.display && decoded) {
    const bad = await displayDiff(got, decoded, cfg.network ? "test" : "main");
    if (bad) { diffs++; if (diffs <= 20) console.log(`DIFF ${name} (display)\n  ${bad}`); }
  }
  const bad = signDiff(plan, prev, got, want, decoded);
  if (bad) { diffs++; if (diffs <= 20) console.log(`DIFF ${name} (sign)\n  ${bad}`); }
}

/** Guarantee 4 against the module: with no passing review signer_sign refuses; after one it refuses any
 * other plan, and signs exactly the inputs and keys the model's sign names, each over the reviewed transaction */
function signDiff(plan, prev, got, want, decoded) {
  const mem = () => new Uint8Array(E.memory.buffer);
  const reviewed = () => { R2.setPlan(plan).setPrevTxs(prev); try { R2.review(); return true; } catch { return false; } };
  if (reviewed() !== !!got.ok) return "the second instance reviewed differently";
  if (!got.ok) return E.signer_sign() === NOT_REVIEWED ? null : "signed with no passing review";
  if (!want.ok) return null; // already counted as a verdict difference
  const other = Uint8Array.from(plan);
  other[OUT] ^= 1;
  mem().set(other, E.signer_plan());
  if (E.signer_sign() !== NOT_REVIEWED) return "signed a plan other than the one reviewed";
  reviewed();
  const sigs = R2.sign();
  if (E.signer_sign() !== NOT_REVIEWED) return "signed twice on one review";
  // The model names each signature's input and key; the module reports the key's public form
  const pubOf = (j, path) => decoded.inputs[j].spk[0] === 0x51
    ? Buffer.concat([Buffer.alloc(1), btc.p2trKey(btc.derive(w.master, path))]) : btc.pubkey(btc.derive(w.master, path));
  const expect = new Map(want.sigs.map((s) => [`${s.input}:${pubOf(s.input, s.path).toString("hex")}`, s.path]));
  const named = sigs.map((s) => `${s.input}:${Buffer.from(s.pubkey).toString("hex")}`);
  if (named.length !== expect.size || named.some((x) => !expect.has(x)))
    return `signed [${sigs.map((x) => x.input)}], model [${want.sigs.map((x) => x.input)}]`;
  const v = new DataView(plan.buffer, plan.byteOffset);
  const tx = { version: v.getInt32(8, true), locktime: v.getUint32(12, true), ...decoded };
  for (const [n, s] of sigs.entries()) {
    const x = decoded.inputs[s.input], k = btc.derive(w.master, expect.get(named[n])), sig = Buffer.from(s.sig);
    if (x.spk[0] === 0x51) {
      const ht = x.sighash, xonly = btc.p2trKey(k);
      if (!Buffer.from(s.pubkey).equals(Buffer.concat([Buffer.alloc(1), xonly])) || sig.length !== (ht ? 65 : 64) ||
          (ht && sig[64] !== ht) || !btc.verifySchnorr(xonly, btc.sighashTaproot(tx, s.input, ht), sig.subarray(0, 64)))
        return `input ${s.input}: not a BIP341 signature by its key over the reviewed transaction`;
      tally["signed (BIP341)"] = (tally["signed (BIP341)"] ?? 0) + 1;
    } else {
      const pub = btc.pubkey(k), code = x.ws ?? btc.p2pkhCode(pub);
      if (!Buffer.from(s.pubkey).equals(pub) || sig[sig.length - 1] !== 1 ||
          !btc.verifyEcdsa(pub, btc.sighashV0(tx, s.input, code), sig.subarray(0, -1)))
        return `input ${s.input}: not a BIP143 signature by its key over the reviewed transaction`;
      const t = expect.get(named[n]).join() === x.key.path.join() ? "signed (BIP143)" : "signed (BIP143, second key)";
      tally[t] = (tally[t] ?? 0) + 1;
    }
  }
  return null;
}

/** What display() writes against the review and Notation.lean: each address as the model renders its
 * script, OP_RETURN data and other scripts as hex, and the fee and spend review settled */
async function displayDiff(got, decoded, network) {
  const d = got.display, hex = (b) => Buffer.from(b).toString("hex");
  if (String(d.fee) !== got.ok.fee) return `fee ${d.fee}, review ${got.ok.fee}`;
  const spend = d.outputs.reduce((a, o) => (o.owner === 0 ? a + o.amount : a), 0n);
  if (d.spend !== spend) return `spend ${d.spend}, external outputs ${spend}`;
  for (const [i, o] of d.outputs.entries()) {
    const spk = decoded.outputs[i].spk, ref = await model.render(network, spk);
    const want = ref.startsWith("script:") ? (spk[0] === 0x6a ? [1, hex(spk.subarray(1))] : [2, hex(spk)]) : [0, ref];
    if (o.amount !== decoded.outputs[i].amount) return `output ${i} amount ${o.amount}, plan ${decoded.outputs[i].amount}`;
    if (o.textKind !== want[0] || o.text !== want[1]) return `output ${i} shown as ${o.textKind}:${o.text}, model ${want[0]}:${want[1]}`;
  }
  return null;
}

const CONFIGS = [
  { name: "mainnet", network: 0, wallet: null },
  { name: "mainnet, wallet registered", network: 0, wallet: WALLETS.ours },
  { name: "mainnet, another wallet registered", network: 0, wallet: WALLETS.other },
  { name: "mainnet, or_d wallet registered", network: 0, wallet: WALLETS.orD },
  { name: "testnet", network: 1, wallet: null, move: toTestnet },
];
const vectors = readdirSync(dir).filter((f) => f.endsWith(".psbt")).sort()
  .map((f) => [f, parse(readFileSync(dir + f))]).filter(([, v]) => v);

for (const cfg of CONFIGS) {
  for (const x of [S, R2]) {
    x.init({ testnet: cfg.network === 1 });
    if (cfg.wallet) x.multisigLoad(cfg.wallet.descriptor);
  }
  for (const k of Object.keys(tally)) delete tally[k];
  const before = { cases, diffs };
  for (const [f, v] of vectors) {
    const base = { plan: v.plan, prev: [...v.prev] };
    if (cfg.move) {
      const p = decodePlan(base.plan);
      cfg.move(p, base.prev);
      base.plan = encodePlan(p);
    }
    await compare(f, base.plan, base.prev, cfg);
    for (let n = 0; n < perVector; n++) {
      const p = decodePlan(base.plan), prev = [...base.prev];
      const applied = [];
      for (let k = 1 + Math.floor(R() * 3); k > 0 && p.outputs.length; k--) {
        const [what, fn] = muts[Math.floor(R() * muts.length)];
        fn(p, prev);
        applied.push(what);
      }
      await compare(`${cfg.name}: ${f} [${applied.join(", ")}]`, encodePlan(p), prev, cfg);
    }
  }
  console.log(`${cfg.name}: ${cases - before.cases} cases, ${diffs - before.diffs} differences`);
  console.log("  " + Object.entries(tally).sort().map(([k, v]) => `${k} ${v}`).join(", "));
}
// Message review: what it shows for bytes built mostly of spaces, letters and the edges of printable ASCII
S.init();
const MSG_BYTES = [0x20, 0x20, 0x20, 0x61, 0x62, 0x7e, 0x21, 0x1f, 0x7f, 0x00, 0x0a, 0xff];
const msgTally = {};
for (let n = 0; n < perVector * 20; n++) {
  const m = Uint8Array.from({ length: Math.floor(R() * 12) }, () => MSG_BYTES[Math.floor(R() * MSG_BYTES.length)]);
  const got = S.messageReview(m), want = await model.message(m);
  const kind = got.textKind === "message" ? "text" : "hex";
  cases++;
  msgTally[`${kind}/${want.kind}`] = (msgTally[`${kind}/${want.kind}`] ?? 0) + 1;
  if (kind !== want.kind || got.text !== want.text) {
    diffs++;
    if (diffs <= 20) console.log(`DIFF message ${Buffer.from(m).toString("hex")}\n  signer ${kind} ${JSON.stringify(got.text)}\n  model  ${want.kind} ${JSON.stringify(want.text)}`);
  }
}
console.log("messages (signer/model): " + Object.entries(msgTally).sort().map(([k, v]) => `${k} ${v}`).join(", "));
// A key twice in an input or output map, with the same value or another first or last: the model refuses all
let dupCases = 0;
for (const f of readdirSync(dir).filter((f) => f.endsWith(".psbt")).sort()) {
  let base;
  try { base = PS.parse(readFileSync(dir + f)); } catch { continue; }
  for (const [side, i] of [...base.inputs.map((_, i) => ["inputs", i]), ...base.outputs.map((_, i) => ["outputs", i])])
    for (const [j, [k, v]] of base[side][i].entries()) for (const [first, same] of [[true, false], [false, false], [false, true]]) {
      const p = PS.clone(base), again = [k, same ? v : Buffer.from(v.length ? v.map((b, n) => (n === v.length - 1 ? b ^ 1 : b)) : [0])];
      p[side][i].splice(first ? j : p[side][i].length, 0, again);
      cases++, dupCases++;
      if (parse(PS.serialize(p))) {
        diffs++;
        if (diffs <= 20) console.log(`DIFF ${f}: ${side} ${i} key ${k.toString("hex")} twice is accepted`);
      }
    }
}
console.log(`repeated keys: ${dupCases} cases`);
model.stop();
console.log(`${cases} cases, ${diffs} differences, ${malformed} malformed below the model`);
process.exit(diffs ? 1 : 0);
