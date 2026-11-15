// rust-bitcoin against the Lean model. Usage: node adapters/rust-bitcoin.mjs [cases per vector] [seed]
import { compare, root } from "./compare.mjs";

await compare({
  name: "rust-bitcoin",
  command: `${root}build/rust-bitcoin-review`,
  args: [],
  configs: [{ name: "Psbt::sign with the test seed's master key", wallet: null, request: {} }],
});
