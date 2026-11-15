// Bitcoin Core's wallet handling a PSBT, one JSON request per line on stdin and one verdict per line on stdout.
// A regtest bitcoind holds the test seed as descriptor wallets; what its user would approve is the fee
// `decodepsbt` reports for the PSBT once `walletprocesspsbt` has signed what it can. It names no output change.
// Usage: node core-worker.mjs <bitcoind>
import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createInterface } from "node:readline";
import { w, ZOO, LEGAL, XPUB } from "./model.mjs";

const B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
const sha256d = (b) => createHash("sha256").update(createHash("sha256").update(b).digest()).digest();
function b58check(payload) {
  const b = Buffer.concat([payload, sha256d(payload).subarray(0, 4)]);
  let n = BigInt("0x" + b.toString("hex")), s = "";
  for (; n > 0n; n /= 58n) s = B58[Number(n % 58n)] + s;
  for (const x of b) { if (x) break; s = "1" + s; }
  return s;
}
function unb58check(s) {
  let n = 0n;
  for (const c of s) n = n * 58n + BigInt(B58.indexOf(c));
  return Buffer.from(n.toString(16).padStart(164, "0"), "hex").subarray(0, 78);
}
// Regtest takes only testnet version bytes; the keys are the same
const tprv = b58check(Buffer.concat([Buffer.from("04358394", "hex"), Buffer.alloc(9), w.master.c, Buffer.from([0]), w.master.k]));
const tpub = (xpub) => b58check(Buffer.concat([Buffer.from("043587cf", "hex"), unb58check(xpub).subarray(4)]));
const fp = (m) => m.fingerprint.toString(16).padStart(8, "0");

const dir = mkdtempSync(join(tmpdir(), "btcsigner-core-"));
const port = 20000 + Math.floor(Math.random() * 20000);
const bitcoind = spawn(process.argv[2], ["-regtest", `-datadir=${dir}`, `-rpcport=${port}`, "-listen=0",
  "-rpcuser=spec", "-rpcpassword=spec", "-server", "-disablewallet=0"], { stdio: "ignore" });
process.on("exit", () => { bitcoind.kill(); rmSync(dir, { recursive: true, force: true }); });

async function rpc(method, params = [], wallet) {
  const res = await fetch(`http://127.0.0.1:${port}/${wallet ? `wallet/${wallet}` : ""}`, {
    method: "POST", headers: { authorization: "Basic " + Buffer.from("spec:spec").toString("base64") },
    body: JSON.stringify({ jsonrpc: "2.0", id: 0, method, params }),
  });
  const { result, error } = await res.json();
  if (error) throw new Error(error.message);
  return result;
}
for (;;) {
  try { await rpc("getblockchaininfo"); break; } catch { await new Promise((r) => setTimeout(r, 200)); }
}

async function makeWallet(name, descs) {
  await rpc("createwallet", [name, false, true]);
  const req = await Promise.all(descs.map(async (d) => ({
    desc: `${d}#${(await rpc("getdescriptorinfo", [d])).checksum}`, timestamp: "now", range: [0, 1000], active: false,
  })));
  for (const r of await rpc("importdescriptors", [req], name)) if (!r.success) throw new Error(JSON.stringify(r.error));
}
const single = ["wpkh", "sh(wpkh", "tr"].flatMap((f, i) => [0, 1].map((chain) =>
  `${f}(${tprv}/${[84, 49, 86][i]}h/0h/0h/${chain}/*)${f.includes("(") ? ")" : ""}`));
const ms = (others) => [0, 1].map((chain) => `wsh(sortedmulti(2,${tprv}/48h/0h/0h/2h/${chain}/*,${others
  .map((m) => `[${fp(m)}/48h/0h/0h/2h]${tpub(XPUB[fp(m)])}/${chain}/*`).join(",")}))`);
await makeWallet("single", single);
await makeWallet("ours", [...single, ...ms([ZOO, LEGAL])]);
// Only adapters/core-rules.mjs uses it, for the legacy rows
await makeWallet("legacy", [...single, ...[0, 1].map((chain) => `pkh(${tprv}/44h/0h/0h/${chain}/*)`)]);

const sigs = (d) => d.inputs.reduce((a, x) => a + Object.keys(x.partial_signatures ?? {}).length + (x.taproot_key_path_sig ? 1 : 0), 0);
const sats = (btc) => BigInt(Math.round(btc * 1e8));

async function review(b64, wallet) {
  let before, out, d;
  try { before = await rpc("decodepsbt", [b64]); } catch (e) { return { error: "parse", detail: e.message }; }
  try { out = await rpc("walletprocesspsbt", [b64, true, "DEFAULT", true, false], wallet); } catch (e) { return { error: "sign", detail: e.message }; }
  d = await rpc("decodepsbt", [out.psbt]);
  if (sigs(d) <= sigs(before)) return { error: "sign", detail: "nothing signed" };
  if (d.fee === undefined) return { error: "fee", detail: "no fee reported" };
  const fee = sats(d.fee), spend = d.tx.vout.reduce((a, o) => a + sats(o.value), 0n);
  const addresses = d.tx.vout.flatMap((o, index) => o.scriptPubKey.address ? [{ index, address: o.scriptPubKey.address }] : []);
  return { ok: { input: String(fee + spend), spend: String(spend), change: "0", fee: String(fee), outputs: [], warnings: [], addresses } };
}

for await (const line of createInterface({ input: process.stdin })) {
  const { psbt, config } = JSON.parse(line);
  process.stdout.write(JSON.stringify(await review(psbt, config.wallet)) + "\n");
}
process.exit(0);
