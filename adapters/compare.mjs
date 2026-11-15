// A signer against the Lean model, on the parser's vectors and PSBTs mutated from them. Its policy is
// its own, so two things are reported apart: invariants any signer must keep, which fail the run, and where
// its policy differs from the model's, which is counted and explained.
//
// A signer is a worker process: one JSON request {psbt (base64), config} per line in, one verdict per line
// out, either {error, detail} or {ok: {input, spend, change, fee, outputs, warnings}}. `outputs` lists those
// it shows as ours, {index, verified}: true, false (it stops), "unverified" (the user may skip checking) or
// "unsupported" (it stops); `change` is their total and `spend` the rest. A warning the user has to get past
// goes in `warnings`; "unverified input amounts" is the one the invariants know. A worker may add
// `addresses`, [{index, address}], the text its screen shows for those outputs.
import { readFileSync, readdirSync } from "node:fs";
import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
import * as btc from "./bitcoin.mjs";
import * as P from "./psbt.mjs";
import { w, ZOO, LEGAL, LETTER, ACCOUNT, NESTED_ACCOUNT, wsAt, caseFor, startModel, rng, root, vectorDir } from "./model.mjs";
export { root };

const MAX_MONEY = 2100000000000000n;

function startWorker(command, args) {
  const proc = spawn(command, args, { stdio: ["pipe", "pipe", "inherit"] });
  const lines = createInterface({ input: proc.stdout })[Symbol.asyncIterator]();
  return {
    async review(psbt, config) {
      proc.stdin.write(JSON.stringify({ psbt: psbt.toString("base64"), config }) + "\n");
      const line = (await lines.next()).value;
      if (line === undefined) throw new Error(`${command} exited`);
      return JSON.parse(line);
    },
    stop() { proc.stdin.end(); },
  };
}

// --- mutations on the PSBT itself
function setOutput(p, i, spk, entries) {
  p.tx.outputs[i].spk = spk;
  p.outputs[i] = [...p.outputs[i].filter(([k]) => ![0x00, 0x01, 0x02, 0x06, 0x07].includes(k[0])), ...entries];
}

export function mutators(R) {
  const pick = (a) => a[Math.floor(R() * a.length)];
  const at = (a) => Math.floor(R() * a.length);
  const amounts = [0n, 1n, 546n, 100000n, MAX_MONEY, MAX_MONEY + 1n, (1n << 63n), (1n << 64n) - 1n];
  const purposes = { wpkh: 84, sh: 49, tr: 86 };
  return [
    ["output made ours", (p) => {
      const type = pick(["wpkh", "sh", "tr"]);
      const purpose = R() < 0.8 ? purposes[type] : pick([84, 49, 86, 44]);
      const path = [purpose + btc.H, pick([btc.H, btc.H, 1 + btc.H]), pick([btc.H, btc.H, 1 + btc.H, 5 + btc.H]),
        pick([0, 1, 1, 2]), pick([0, 3, 99999, 100000, 0x7fffffff])];
      const k = btc.derive(w.master, path), pub = btc.pubkey(k);
      const spk = type === "wpkh" ? btc.p2wpkh(pub) : type === "sh" ? btc.p2shP2wpkh(pub) : btc.p2tr(k);
      const entries = [P.outputDerivation(type === "tr", type === "tr" ? pub.subarray(1) : pub, w.fingerprint, path)];
      if (type === "sh") entries.push([Buffer.from([0x00]), btc.p2wpkh(pub)]);
      setOutput(p, at(p.outputs), spk, entries);
    }],
    ["output fingerprint zeroed", (p) => {
      const m = p.outputs[at(p.outputs)];
      for (const e of m) if ((e[0][0] === 0x02 || e[0][0] === 0x07) && e[1].length >= 4) {
        const o = e[0][0] === 0x07 ? 1 : 0;
        if (e[1].readUInt32BE(o) === w.fingerprint) { e[1] = Buffer.from(e[1]); e[1].writeUInt32BE(0, o); }
      }
    }],
    ["output derivation removed", (p) => { const i = at(p.outputs); p.outputs[i] = P.drop(P.drop(p.outputs[i], 0x02), 0x07); }],
    ["output amount", (p) => { p.tx.outputs[at(p.tx.outputs)].amount = pick(amounts); }],
    ["input amount", (p) => {
      const m = p.inputs[at(p.inputs)], e = m.find(([k]) => k[0] === 0x01);
      if (e) { e[1] = Buffer.from(e[1]); e[1].writeBigUInt64LE(pick(amounts), 0); }
    }],
    ["input script changed", (p) => {
      const e = p.inputs[at(p.inputs)].find(([k]) => k[0] === 0x01);
      if (e) { e[1] = Buffer.from(e[1]); e[1][e[1].length - 1] ^= 1; }
    }],
    ["input previous transactions swapped", (p) => {
      if (p.inputs.length < 2) return;
      const i = at(p.inputs), j = (i + 1) % p.inputs.length, a = P.get(p.inputs[i], 0x00), b = P.get(p.inputs[j], 0x00);
      if (!a || !b) return;
      p.inputs[i] = [...P.drop(p.inputs[i], 0x00), [Buffer.from([0x00]), b]];
      p.inputs[j] = [...P.drop(p.inputs[j], 0x00), [Buffer.from([0x00]), a]];
    }],
    ["input prev_vout changed", (p) => { const t = p.tx.inputs[at(p.tx.inputs)]; t.vout = pick([(t.vout + 1) >>> 0, 0xffffffff]); }],
    ["input previous transaction removed", (p) => {
      const i = at(p.inputs);
      if (P.get(p.inputs[i], 0x01)) p.inputs[i] = P.drop(p.inputs[i], 0x00);
    }],
    ["sighash", (p) => {
      const i = at(p.inputs), v = Buffer.alloc(4);
      v.writeUInt32LE(pick([1, 2, 3, 0x81, 0x83]));
      p.inputs[i] = [...P.drop(p.inputs[i], 0x03), [Buffer.from([0x03]), v]];
    }],
    ["output in a wallet", (p) => {
      const members = pick([[w, ZOO, LEGAL], [w, ZOO, LETTER], [ZOO, LEGAL, LETTER]]);
      const path = [...ACCOUNT, pick([0, 1, 1, 2]), pick([0, 5, 99999, 100000])];
      const ws = wsAt(members, path);
      setOutput(p, at(p.outputs), btc.p2wsh(ws), [[Buffer.from([0x01]), ws],
        ...members.map((m) => P.outputDerivation(false, btc.pubkey(btc.derive(m.master, path)), m.fingerprint, path))]);
    }],
    ["output script replaced", (p) => {
      const h = (n) => Buffer.from(Array.from({ length: n }, () => Math.floor(R() * 256)));
      const spk = pick([
        () => Buffer.concat([Buffer.from([0x76, 0xa9, 0x14]), h(20), Buffer.from([0x88, 0xac])]),
        () => Buffer.concat([Buffer.from([0xa9, 0x14]), h(20), Buffer.from([0x87])]),
        () => Buffer.concat([Buffer.from([0x00, 0x14]), h(20)]),
        () => Buffer.concat([Buffer.from([0x00, 0x20]), h(32)]),
        () => Buffer.concat([Buffer.from([0x51, 0x20]), h(32)]),
        () => Buffer.concat([Buffer.from([0x52, 0x10]), h(16)]),
        () => Buffer.concat([Buffer.from([0x6a, 0x05]), h(5)]),
        () => h(1 + Math.floor(R() * 40)),
      ])();
      setOutput(p, at(p.outputs), spk, []);
    }],
    ["output removed", (p) => { if (p.outputs.length > 1) { p.outputs.pop(); p.tx.outputs.pop(); } }],
    ["output in a nested wallet", (p) => {
      const members = pick([[w, ZOO, LEGAL], [w, ZOO, LETTER]]);
      const path = [...NESTED_ACCOUNT, pick([0, 1, 1, 2]), pick([0, 5, 99999, 100000])];
      const ws = wsAt(members, path);
      setOutput(p, at(p.outputs), btc.p2sh(btc.p2wsh(ws)), [[Buffer.from([0x00]), btc.p2wsh(ws)], [Buffer.from([0x01]), ws],
        ...members.map((m) => P.outputDerivation(false, btc.pubkey(btc.derive(m.master, path)), m.fingerprint, path))]);
    }],
    ["output made a legacy one of ours", (p) => {
      const path = [44 + btc.H, pick([btc.H, btc.H, 1 + btc.H]), btc.H, pick([0, 1, 1]), pick([0, 3, 100000])];
      const pub = btc.pubkey(btc.derive(w.master, path));
      setOutput(p, at(p.outputs), btc.p2pkhCode(pub), [P.outputDerivation(false, pub, w.fingerprint, path)]);
    }],
    ["input from a nested wallet", (p) => {
      const i = at(p.inputs), path = [...NESTED_ACCOUNT, pick([0, 1]), pick([0, 7])];
      const ws = wsAt(pick([[w, ZOO, LEGAL], [w, ZOO, LETTER]]), path), wu = P.get(p.inputs[i], 0x01);
      const amount = wu ? wu.readBigUInt64LE(0) : 100000n;
      p.inputs[i] = [...p.inputs[i].filter(([k]) => k[0] === 0x03), P.witnessUtxo(amount, btc.p2sh(btc.p2wsh(ws))),
        [Buffer.from([0x04]), btc.p2wsh(ws)], [Buffer.from([0x05]), ws],
        ...[w, ZOO, LEGAL, LETTER].filter((m) => btc.multisigKeys(ws).some((k) => k.equals(btc.pubkey(btc.derive(m.master, path)))))
          .map((m) => P.inputDerivation(btc.pubkey(btc.derive(m.master, path)), m.fingerprint, path))];
    }],
    ["input made a legacy one of ours", (p) => {
      const i = at(p.inputs), path = [44 + btc.H, btc.H, btc.H, pick([0, 1]), pick([0, 2])];
      const pub = btc.pubkey(btc.derive(w.master, path)), wu = P.get(p.inputs[i], 0x01);
      const amount = wu ? wu.readBigUInt64LE(0) : 100000n;
      const prev = P.writeTx({ version: 2, locktime: 0, outputs: [{ amount, spk: btc.p2pkhCode(pub) }],
        inputs: [{ txid: Buffer.from(Array.from({ length: 32 }, () => Math.floor(R() * 256))), vout: 0, scriptSig: Buffer.alloc(0), sequence: 0xffffffff }] });
      Object.assign(p.tx.inputs[i], { txid: btc.prevInfo(prev, 0).txid, vout: 0 });
      p.inputs[i] = [...p.inputs[i].filter(([k]) => k[0] === 0x03), [Buffer.from([0x00]), prev], P.inputDerivation(pub, w.fingerprint, path)];
    }],
    ["key repeated", (p) => {
      // A witness_utxo again with another amount where there is one, else any pair with its last byte flipped
      const m = p.inputs[at(p.inputs)], e = m.find(([k]) => k[0] === 0x01) ?? (m.length ? m[at(m)] : null);
      if (!e) return;
      const v = Buffer.from(e[1]);
      if (e[0][0] === 0x01 && e[0].length === 1) v.writeBigUInt64LE(pick(amounts), 0);
      else v[v.length - 1] ^= 1;
      R() < 0.5 ? m.push([e[0], v]) : m.unshift([e[0], v]);
    }],
  ];
}

// --- what each side decided
const sum = (xs) => xs.reduce((a, b) => a + b, 0n);
const isP2wsh = (spk) => spk.length === 34 && spk[0] === 0 && spk[1] === 32;

/** Why the model calls this output external although the signer calls it change */
function whyExternal(view, i, cfg) {
  const o = view.outputs[i], k = o.key;
  if (!k) return "no derivation of ours the model reads (fingerprint, or a script type it does not sign for)";
  const nested = o.spk.length === 23 && cfg.wallet?.spkAt(k.path)?.equals(o.spk);
  if (isP2wsh(o.spk) || nested) {
    const kind = nested ? "P2SH-P2WSH" : "P2WSH";
    if (!cfg.wallet) return `${kind} change without a registered wallet`;
    if (!cfg.wallet.at(k) || !cfg.wallet.spkAt(k.path).equals(o.spk)) return `${kind} not of the registered wallet (or chain > 1, index >= 100000)`;
    return `${kind} change with no multisig input being signed`;
  }
  const p = k.path;
  if (p.length !== 5) return `path of depth ${p.length}, not m/purpose'/coin'/account'/chain/index`;
  const type = o.spk.length === 25 ? 44 : o.spk.length === 22 ? 84 : o.spk.length === 23 ? 49 : 86;
  if (p[0] !== type + btc.H) return "purpose does not match the script type";
  if (p[1] !== btc.H) return "coin type of another network";
  if (p[3] > 1) return "chain other than 0 (receive) or 1 (change)";
  if (p[4] >= 100000) return "address index >= 100000";
  if (!btc.owns(w, k, o.spk, null)) return "the key at that path does not make this script";
  return "no input being signed on the same account";
}

const backedBy = (x) => x.prevInfo?.out && x.prevInfo.txid.equals(x.txid) ? x.prevInfo.out.amount : null;
/** bech32 (hrp, '1', data) or base58 text: what a user would take for an address */
const looksLikeAddress = (t) => /^[a-z]{2,4}1[qpzry9x8gf2tvdw0s3jn54khce6mua7l]{6,}$/.test(t) ||
  /^[1-9A-HJ-NP-Za-km-z]{25,35}$/.test(t);

const sumBacked = (view) => sum(view.inputs.map((x) => backedBy(x) ?? x.amount));
/** A mismatch in the script alone leaves the amount, and so the fee, as the previous transaction says */
const contradicted = (x) => x.prev === "mismatch" && backedBy(x) !== x.amount;

/** What any signer that lets the user approve this PSBT has to show, whatever its policy. A fee below zero
 * is not part of it, nor the fee of an output of 2^63 or more, which consensus reads as negative: neither can
 * be mined, so they are counted with the policy differences instead */
export function expectations(p, view, cfg) {
  const sumIn = sum(view.inputs.map((x) => x.amount)), backed = sumBacked(view);
  // Whatever fingerprint the PSBT gives: only whether our seed, or the registered wallet, makes the script at that path counts
  const owned = (i) => P.derivations(p.outputs[i], 0x02, 0x07).some(({ path }) => cfg.wallet?.spkAt(path)?.equals(view.outputs[i].spk) ||
    btc.owns(w, { fp: w.fingerprint, path }, view.outputs[i].spk, null));
  return {
    // A signer may take each amount from the previous transaction its txid binds, over the witness_utxo
    inputTotals: backed === sumIn ? [sumIn] : [sumIn, backed],
    outputTotal: sum(view.outputs.map((x) => x.amount)),
    feeChecked: !view.outputs.some((x) => x.amount >= 1n << 63n),
    // BIP143 signs only the input's own amount: one the PSBT's own previous transaction contradicts lets a
    // coordinator understate the fee over two signing sessions, so it may not pass without a word
    warnUnlessPrevious: view.inputs.some(contradicted),
    notChange: view.outputs.map((_, i) => i).filter((i) => !owned(i)),
  };
}

/** The invariants any signer has to keep for what it lets the user approve */
function invariants(p, view, s, cfg) {
  const bad = [], e = expectations(p, view, cfg);
  const [input, spend, change, fee] = ["input", "spend", "change", "fee"].map((k) => BigInt(s[k]));
  const fromPrev = e.inputTotals.length === 2 && input === e.inputTotals[1];
  const total = fromPrev ? input : e.inputTotals[0];
  if (input !== spend + change + fee) bad.push("the screen does not add up: spend + change + fee != input");
  if (input !== total) bad.push("input total differs from the PSBT's input amounts");
  if (e.feeChecked && fee !== total - e.outputTotal) bad.push("fee is not inputs minus outputs");
  if (!fromPrev && e.warnUnlessPrevious && !s.warnings?.includes("unverified input amounts"))
    bad.push("an input amount its previous transaction contradicts is shown without a warning");
  for (const c of s.outputs)
    if (c.verified === true && e.notChange.includes(c.index))
      bad.push(`output ${c.index} is shown as verified change but no key of ours at its path makes it`);
  return bad;
}

/** The parser's vectors, each followed by `perVector` copies with one to three mutations drawn from `R` */
export function loadVectors() {
  return readdirSync(vectorDir).filter((f) => f.endsWith(".psbt")).sort().flatMap((f) => {
    try { return [[f, P.parse(readFileSync(vectorDir + f))]]; } catch { return []; }
  });
}

export function* cases(vectors, muts, R, perVector) {
  for (const [f, base] of vectors) {
    for (let n = 0; n <= (base.inputs.length && base.outputs.length ? perVector : 0); n++) {
      const p = P.clone(base), applied = [];
      for (let k = n ? 1 + Math.floor(R() * 3) : 0; k > 0; k--) {
        const [what, fn] = muts[Math.floor(R() * muts.length)];
        fn(p, R);
        applied.push(what);
      }
      yield { name: `${f}${applied.length ? ` [${applied.join(", ")}]` : ""}`, p };
    }
  }
}

/** Runs the comparison for a signer: {name, command, args, configs: [{name, wallet, request}]}. `wallet` is
 * the registered wallet the model is given; `request` is passed to the worker as is */
export async function compare(signer) {
  const perVector = Number(process.argv[2] ?? 100);
  const R = rng(Number(process.argv[3] ?? 1));
  // MUTATIONS="a,b" keeps only those, to see what one of them does on its own
  const only = process.env.MUTATIONS?.split(",");
  const muts = mutators(R).filter(([what]) => !only || only.includes(what));
  const model = startModel(), worker = startWorker(signer.command, signer.args);
  const vectors = loadVectors();
  const S = signer.name;

  let violations = 0;
  for (const cfg of signer.configs) {
    const outcomes = {}, reasons = {}, examples = {}, broken = {};
    const note = (table, k, ex) => { table[k] = (table[k] ?? 0) + 1; if (ex && !examples[k]) examples[k] = ex; };
    let count = 0;
    for (const { name, p } of cases(vectors, muts, R, perVector)) {
      let view = P.view(p, w.fingerprint), pp = p;
      const dup = P.duplicated(p);
      const m = dup ? { error: "DUPLICATE_KEY" } : await model.review(caseFor(view, 0, cfg.wallet, signer.policy ?? { legacy: true, nested: true }));
      const s = await worker.review(P.serialize(p), cfg.request);
      count++;

      const refusedAt = s.ok?.outputs.find((c) => c.verified === false || c.verified === "unsupported");
      const warns = s.ok?.warnings?.length ? ` after warning (${s.ok.warnings.join(", ")})` : "";
      const sClass = s.error ? `refuses (${s.error}${s.detail ? `: ${s.detail.split(":")[0]}` : ""})`
        : refusedAt ? `stops at change (${refusedAt.verified === false ? "verification failed" : "no derivation of ours"})`
        : `lets the user approve${warns}`;
      note(outcomes, `${S} ${sClass} / model ${m.error ?? "OK"}`, name);
      if (s.error || refusedAt) continue;
      let either = null;
      if (dup) {
        // Which of the two values its screen took, where the totals tell: the invariants are checked against that.
        // Where they do not, either reading is the signer's, so only what breaks under both counts
        const last = P.lastWins(p), lv = P.view(last, w.fingerprint), total = (v) => sum(v.inputs.map((x) => x.amount));
        const took = total(lv) === total(view) ? "" : BigInt(s.ok.input) === total(view) ? ", showing the first value"
          : BigInt(s.ok.input) === total(lv) ? ", showing the last value" : "";
        note(reasons, `accepts a key twice in a map (BIP174: invalid)${took}`, name);
        if (took.includes("last")) { pp = last; view = lv; } else if (!took) either = invariants(last, lv, s.ok, cfg);
      }

      for (const v of invariants(pp, view, s.ok, cfg).filter((v) => !either || either.includes(v))) { note(broken, v, name); violations++; }
      for (const { index, address } of s.ok.addresses ?? []) {
        const ref = await model.render(signer.network ?? "main", view.outputs[index].spk);
        if (ref.startsWith("script:")) note(reasons, "shows a script with no address in its own way", name);
        else if (!looksLikeAddress(address)) note(reasons, "shows text other than its address for a script that has one", `${name} (${address} for ${ref})`);
        else if (address !== ref) { note(broken, `output ${index} is shown as an address its script does not have`, `${name} (${address} for ${ref})`); violations++; }
      }
      if (sumBacked(view) !== sum(view.inputs.map((x) => x.amount)) && BigInt(s.ok.input) === sumBacked(view))
        note(reasons, "takes input amounts from the previous transactions where the witness_utxo contradicts them (the model refuses)", name);
      if (BigInt(s.ok.fee) < 0n) note(reasons, "approves outputs worth more than the inputs, with a negative fee (cannot be mined)", name);
      if (view.outputs.some((x) => x.amount >= 1n << 63n)) note(reasons, "approves an output of 2^63 or more, negative to consensus (cannot be mined)", name);
      if (!m.ok) continue;
      const ours = new Set(s.ok.outputs.map((c) => c.index));
      const unverified = new Set(s.ok.outputs.filter((c) => c.verified === "unverified").map((c) => c.index));
      view.outputs.forEach((_, i) => {
        const sOurs = ours.has(i), mOurs = m.ok.owners[i] !== 0;
        if (sOurs && unverified.has(i)) note(reasons, `change shown unverified (multisig, no descriptor): model says ${mOurs ? "ours" : "external"}`, name);
        else if (sOurs && !mOurs) note(reasons, `${S} ours, model external: ${whyExternal(view, i, cfg)}`, name);
        else if (!sOurs && mOurs) note(reasons, `${S} external, model ours`, name);
      });
      if (BigInt(s.ok.fee) !== BigInt(m.ok.fee)) note(reasons, "fee differs from the model's", name);
    }
    console.log(`\n== ${S}, ${cfg.name}: ${count} cases`);
    const show = (title, table) => {
      console.log(title);
      for (const [k, v] of Object.entries(table).sort((a, b) => b[1] - a[1])) console.log(`  ${String(v).padStart(6)}  ${k}\n          e.g. ${examples[k]}`);
    };
    show("outcomes", outcomes);
    show("where the policies differ", reasons);
    show("invariant violations", broken);
  }
  model.stop();
  worker.stop();
  console.log(`\n${violations} invariant violations`);
  process.exit(violations ? 1 : 0);
}
