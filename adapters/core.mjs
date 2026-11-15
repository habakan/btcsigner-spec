// Bitcoin Core's wallet against the Lean model. Usage: node adapters/core.mjs [cases per vector] [seed]
import { compare, root } from "./compare.mjs";
import { WALLETS } from "./model.mjs";

await compare({
  name: "Bitcoin Core",
  network: "regtest",
  command: process.execPath,
  args: [`${root}adapters/core-worker.mjs`, process.env.BITCOIND ?? "bitcoind"],
  configs: [
    { name: "single-sig descriptors of the test seed", wallet: null, request: { wallet: "single" } },
    { name: "with our 2-of-3 multisig imported", wallet: WALLETS.ours, request: { wallet: "ours" } },
  ],
});
