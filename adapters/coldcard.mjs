// Coldcard against the Lean model. Usage: node adapters/coldcard.mjs [cases per vector] [seed]
// A Coldcard signs for every single-sig script type of its seed at once, so there is one single-sig config
import { compare, root } from "./compare.mjs";
import { WALLETS } from "./model.mjs";

const multisig = (name, wallet) => ({ name, wallet, request: { descriptor: wallet.descriptor } });
await compare({
  name: "Coldcard",
  formats: true,
  command: process.env.SPEC_COLDCARD_PYTHON ?? `${root}build/venv-coldcard/bin/python`,
  args: [`${root}adapters/coldcard.py`, process.env.COLDCARD_SRC ?? `${root}third_party/coldcard`],
  configs: [
    { name: "single-sig", wallet: null, request: { descriptor: null } },
    multisig("multisig, wallet registered", WALLETS.ours),
    multisig("multisig, another wallet registered", WALLETS.other),
    multisig("nested multisig, wallet registered", WALLETS.nested),
  ],
});
