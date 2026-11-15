// Specter DIY against the Lean model. Usage: node adapters/specter.mjs [cases per vector] [seed]
import { compare, root } from "./compare.mjs";
import { WALLETS } from "./model.mjs";

const single = (script) => ({ name: `single-sig ${script}`, wallet: null, request: { script, descriptor: null } });
await compare({
  name: "Specter DIY",
  formats: true,
  command: process.env.SPEC_SPECTER_PYTHON ?? `${root}build/venv-specter/bin/python`,
  args: [`${root}adapters/specter.py`, process.env.SPECTER_SRC ?? `${root}third_party/specter-diy`],
  configs: [
    single("p2wpkh"), single("p2sh-p2wpkh"), single("p2tr"), single("p2pkh"),
    { name: "multisig, wallet descriptor loaded", wallet: WALLETS.ours, request: { descriptor: WALLETS.ours.descriptor } },
    { name: "multisig, another wallet's descriptor loaded", wallet: WALLETS.other, request: { descriptor: WALLETS.other.descriptor } },
    { name: "nested multisig, wallet descriptor loaded", wallet: WALLETS.nested, request: { descriptor: WALLETS.nested.descriptor } },
  ],
});
