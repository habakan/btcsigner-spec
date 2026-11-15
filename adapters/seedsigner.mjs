// SeedSigner against the Lean model. Usage: node adapters/seedsigner.mjs [cases per vector] [seed]
import { compare, root } from "./compare.mjs";
import { WALLETS } from "./model.mjs";

await compare({
  name: "SeedSigner",
  formats: true,
  command: process.env.SPEC_PYTHON ?? `${root}build/venv-seedsigner/bin/python`,
  args: [`${root}adapters/seedsigner.py`, process.env.SEEDSIGNER_SRC ?? `${root}third_party/seedsigner/src`],
  configs: [
    { name: "no wallet loaded", wallet: null, request: { descriptor: null } },
    { name: "wallet descriptor loaded", wallet: WALLETS.ours, request: { descriptor: WALLETS.ours.descriptor } },
    { name: "another wallet's descriptor loaded", wallet: WALLETS.other, request: { descriptor: WALLETS.other.descriptor } },
    { name: "nested multisig descriptor loaded", wallet: WALLETS.nested, request: { descriptor: WALLETS.nested.descriptor } },
  ],
});
