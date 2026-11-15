// Coconut Vault against the Lean model. Usage: node adapters/coconut.mjs [cases per vector] [seed]
import { compare, root } from "./compare.mjs";
import { WALLETS, XPUB, fpHex, w } from "./model.mjs";

const members = (ms) => ms.members.map((m) => ({ fp: fpHex(m), xpub: XPUB[fpHex(m)], ours: m === w }));
await compare({
  name: "Coconut Vault",
  command: process.env.SPEC_COCONUT ?? `${root}build/coconut-review`,
  args: [],
  configs: [
    { name: "single-sig vault", wallet: null, request: { members: null } },
    { name: "multisig vault", wallet: WALLETS.ours, request: { members: members(WALLETS.ours) } },
    { name: "another multisig vault", wallet: WALLETS.other, request: { members: members(WALLETS.other) } },
  ],
});
