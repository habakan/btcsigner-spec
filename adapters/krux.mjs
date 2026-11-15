// Krux against the Lean model. Usage: node adapters/krux.mjs [cases per vector] [seed]
import { compare, root } from "./compare.mjs";
import { WALLETS } from "./model.mjs";

const single = (script) => ({ name: `single-sig ${script}`, wallet: null, request: { script, descriptor: null } });
await compare({
  name: "Krux",
  formats: true,
  command: process.env.SPEC_KRUX_PYTHON ?? `${root}build/venv-krux/bin/python`,
  args: [`${root}adapters/krux.py`, process.env.KRUX_SRC ?? `${root}third_party/krux`],
  configs: [
    single("p2wpkh"), single("p2sh-p2wpkh"), single("p2tr"), single("p2pkh"),
    { name: "multisig, wallet descriptor loaded", wallet: WALLETS.ours, request: { descriptor: WALLETS.ours.descriptor } },
    { name: "multisig, another wallet's descriptor loaded", wallet: WALLETS.other, request: { descriptor: WALLETS.other.descriptor } },
    { name: "nested multisig, wallet descriptor loaded", wallet: WALLETS.nested, request: { descriptor: WALLETS.nested.descriptor } },
  ],
});
