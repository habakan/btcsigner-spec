import VersoManual

open Verso.Genre Manual

#doc (Manual) "Comparing a signer" =>
%%%
tag := "comparing"
%%%

The model never links against a signer. Each signer runs its own code, the model runs as a separate process,
and Node scripts in `adapters/` hand both the same transaction and compare what comes back.

Every comparison starts from the same PSBTs: Bitcoin Core's `rpc_psbt.json` vectors and a set of wallet vectors,
plus mutations of them.

Adapters exist for bitwasm-signer, SeedSigner, Krux, Specter DIY, Coldcard, Coconut Vault, Bitcoin Core's wallet, libwally-core,
rust-bitcoin and bitcoinjs-lib. Each runs that project's code at the commit or version the repository pins.

What a run finds in a released version of a project goes to that project privately before it is written down
anywhere public.

# Invariants and policy

A signer's policy need not be the model's. A difference in what it decides is counted and explained, not failed.
A run fails only on an invariant any signer has to keep for what it lets the user approve:

 * the screen adds up: spend + change + fee = input
 * the input total is the PSBT's
 * the fee is inputs minus outputs, unless an output is 2^63 or more, which consensus reads as negative
 * change shown as verified is made by our seed at the path the PSBT gives
 * an input amount the PSBT's own previous transaction contradicts is not shown without a warning
 * an address shown for an output is the one the notation writes for its script on that network

A worker whose output breaks any of the first four on purpose, such as a fee a satoshi off, has to fail the run.

A signer whose review reports its decisions as data can be held to more. In _exact agreement_, its error, or its
totals, inputs signed and every output's owner, must equal the model's on every case. bitwasm-signer is compared
this way.

# Cases as a file

`make vectors` writes every case to `build/vectors.json`, so a signer can test against them in its own suite,
without Lean or Node. The file names the mnemonic, the network and the wallets. Each case has:

 * `wallet`: which wallet the signer holds, a script type or a descriptor
 * `psbt`: the PSBT, in base64
 * `invalid`: why BIP 174 makes the PSBT invalid, or `null`
 * `model`: the model's verdict. This is the model's policy, and a signer need not share it.
 * `ifApproved`: what the screen has to show if the signer lets the user approve. `inputTotal` is the PSBT's input amounts or, where they differ, those of the previous transactions. `fee` gives the fee for each of those totals, or `null` when an output reads as negative to consensus. `warnUnlessPreviousAmounts` says whether showing the PSBT's own amounts needs a warning, and `notChange` lists the outputs it may not call verified change.

# The worker protocol

A worker is a long-running process that speaks one JSON line per request, in whatever language runs the signer's
code.

Each request carries a PSBT, and `config` says which wallet to hold, such as a descriptor or a script type:

```
{"psbt": base64, "config": {…}}
```

Each verdict is a refusal or the figures the signer's screens would show. `addresses` is optional:

```
{"error": …, "detail": …}
{"ok": {"input", "spend", "change", "fee",
        "outputs": [{"index", "verified"}],
        "warnings": […],
        "addresses": [{"index", "address"}]}}
```

# The model's side

The executable reads one JSON case per line and prints one verdict per line. It calls the same `review` the
theorems are about, so a verdict is the proved model's answer and not a re-implementation of it.

```
{
  "network": 0, "fingerprint": 1942346250,
  "inputs":  [{"amount": "100000", "spk": "0014…",
               "key": {"fp": 1942346250, "path": [2147483732, …]},
               "sighash": 1, "ws": null, "txid": "3b…",
               "prev": {"txid": "3b…", "out": {"amount": "100000", "spk": "0014…"}}}],
  "outputs": [{"amount": "60000", "spk": "0014…", "key": null}],
  "owns":    [{"fp": 1942346250, "path": [2147483732, …], "spk": "0014…", "ws": null}],
  "wallet":  null
}
```

 * `key` is the PSBT's claim that an input or output is ours. The model does not trust it.
 * `owns` lists the claims that hold. `adapters/bitcoin.mjs` computes them from the seed, never the signer under test.
 * `prev` is the `non_witness_utxo` as parsed: `null` when absent, else the txid it hashes to and its output at `prev_vout`.
 * `wallet`, when a multisig is registered, lists which scripts belong to it and on which chain.
 * `legacy` and `nested`, when true, make the model a signer that signs P2PKH and P2SH-P2WSH multisig inputs. Both are true for every signer here but bitwasm-signer, which signs neither.

The verdict is `{"ok": …}` with the totals, fee, inputs signed and owners, `{"error": …}` naming the model's error,
or `{"fatal": …}` when a case cannot be read.

# Adding a signer

 1. Pin it in the `Makefile`'s `deps` target and fetch it into `third_party/`.
 2. Write a worker that calls the signer's own review and signing and prints a verdict in the shape above. Mirror what its UI checks around that code, and do not re-implement its policy.
 3. Write `adapters/<name>.mjs`, calling `compare()` with a `command` that starts the worker and one config per kind of wallet it holds.
 4. Add `check-<name>` to the `Makefile`. Before trusting a clean run, plant a bug in the worker's output and check that an invariant catches it.
 5. If the signer can report its decisions as data, add an exact comparison too.
