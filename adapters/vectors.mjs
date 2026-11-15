// The comparison's cases as one JSON file, for a signer to test against without Lean or Node.
// Usage: node adapters/vectors.mjs [cases per vector] [seed] > vectors.json
import * as P from "./psbt.mjs";
import { mutators, expectations, loadVectors, cases } from "./compare.mjs";
import { w, WALLETS, caseFor, startModel, rng } from "./model.mjs";

const perVector = Number(process.argv[2] ?? 5);
const R = rng(Number(process.argv[3] ?? 1));
const single = (script) => ({ name: `single-sig ${script}`, wallet: null, holds: { script } });
const multisig = (name, wallet) => ({ name, wallet, holds: { descriptor: wallet.descriptor } });
const configs = [single("p2wpkh"), single("p2sh-p2wpkh"), single("p2tr"), single("p2pkh"),
  multisig("multisig, wallet registered", WALLETS.ours), multisig("multisig, another wallet registered", WALLETS.other),
  multisig("nested multisig, wallet registered", WALLETS.nested)];

const model = startModel(), muts = mutators(R), vectors = loadVectors();
const out = [];
for (const cfg of configs) {
  for (const { name, p } of cases(vectors, muts, R, perVector)) {
    const view = P.view(p, w.fingerprint), dup = P.duplicated(p);
    const e = expectations(p, view, cfg);
    out.push({
      wallet: cfg.name, name, psbt: P.serialize(p).toString("base64"),
      invalid: dup ? "a key twice in one map (BIP 174)" : null,
      model: dup ? { error: "DUPLICATE_KEY" } : await model.review(caseFor(view, 0, cfg.wallet, { legacy: true, nested: true })),
      ifApproved: {
        inputTotal: e.inputTotals.map(String),
        fee: e.feeChecked ? e.inputTotals.map((t) => String(t - e.outputTotal)) : null,
        warnUnlessPreviousAmounts: e.warnUnlessPrevious,
        notChange: e.notChange,
      },
    });
  }
}
model.stop();
console.log(JSON.stringify({
  format: "btcsigner-spec vectors 1",
  mnemonic: "abandon ".repeat(11) + "about",
  network: "main",
  wallets: configs.map((c) => ({ name: c.name, ...c.holds })),
  cases: out,
}, null, 1));
