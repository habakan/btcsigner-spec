// bitcoinjs-lib's handling of a PSBT, one JSON request per line on stdin and one verdict per line on stdout.
// It is a library with no review screen: what a wallet built on it shows is what getFee() returns once
// its own signAllInputsHD() and finalizeAllInputs() have run with the test seed. It names no output change.
// Usage: node bitcoinjs-worker.mjs <bitcoinjs-lib checkout, with its npm dependencies installed>
import { createRequire } from "node:module";
import { createInterface } from "node:readline";
import { pathToFileURL } from "node:url";
import { w } from "./model.mjs";

const src = process.argv[2];
const load = (name) => import(pathToFileURL(createRequire(`${src}/package.json`).resolve(name)).href);
const { Psbt, initEccLib, address, networks } = await import(pathToFileURL(`${src}/src/esm/index.js`).href);
const ecc = await load("tiny-secp256k1");
const { BIP32Factory } = await load("bip32");
initEccLib(ecc);
const hd = BIP32Factory(ecc).fromPrivateKey(w.master.k, w.master.c);

function review(b64) {
  let psbt;
  try { psbt = Psbt.fromBase64(b64); } catch (e) { return { error: "parse", detail: e.message }; }
  try { psbt.signAllInputsHD(hd); } catch (e) { return { error: "sign", detail: e.message }; }
  try { psbt.finalizeAllInputs(); } catch (e) { return { error: "finalize", detail: e.message }; }
  let fee;
  try { fee = psbt.getFee(); } catch (e) { return { error: "fee", detail: e.message }; }
  const spend = psbt.txOutputs.reduce((a, o) => a + o.value, 0n);
  const addresses = psbt.txOutputs.flatMap((o, index) => {
    try { return [{ index, address: address.fromOutputScript(o.script, networks.bitcoin) }]; } catch { return []; }
  });
  return { ok: { input: String(fee + spend), spend: String(spend), change: "0", fee: String(fee), outputs: [], warnings: [], addresses } };
}

for await (const line of createInterface({ input: process.stdin })) {
  process.stdout.write(JSON.stringify(review(JSON.parse(line).psbt)) + "\n");
}
