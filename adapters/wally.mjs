// libwally-core against the Lean model. Usage: node adapters/wally.mjs [cases per vector] [seed]
import { compare, root } from "./compare.mjs";

await compare({
  name: "libwally-core",
  command: process.env.SPEC_PYTHON ?? `${root}build/venv-wally/bin/python`,
  args: ["-I", `${root}adapters/wally.py`],
  configs: [{ name: "BIP32 signer of the test seed", wallet: null, request: {} }],
});
