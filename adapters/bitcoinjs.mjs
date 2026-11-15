// bitcoinjs-lib against the Lean model. Usage: node adapters/bitcoinjs.mjs [cases per vector] [seed]
import { compare, root } from "./compare.mjs";

await compare({
  name: "bitcoinjs-lib",
  command: process.execPath,
  args: [`${root}adapters/bitcoinjs-worker.mjs`, process.env.BITCOINJS_SRC ?? `${root}third_party/bitcoinjs-lib`],
  configs: [{ name: "HD signer of the test seed", wallet: null, request: {} }],
});
