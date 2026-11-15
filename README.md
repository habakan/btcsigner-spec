# btcsigner-spec

A model of what a Bitcoin signer decides about a transaction before signing it, in Lean 4 with no
dependencies, proofs of what that guarantees, and a way to test any signer against it. Signers tested so
far: bitwasm-signer, SeedSigner, Krux, Specter DIY, Coldcard and Coconut Vault, each running its own code at a pinned commit.
Bitcoin Core's wallet and the PSBT libraries libwally-core, bitcoinjs-lib and rust-bitcoin, which other wallets are
built on, are compared the same way.

```sh
make check      # build the model and check every proof
make deps       # fetch the signers at pinned commits and set them up (needs uv, and each signer's build tools)
make check-bitwasm check-seedsigner check-krux check-specter check-coconut check-bitcoinjs   # check-coconut also needs dart
make check-core check-wally     # check-core needs bitcoind (run on regtest in a temporary datadir)
make check-rust-bitcoin         # needs cargo
make check-coldcard             # runs Coldcard's desktop simulator headless; needs SDL2 (brew install sdl2)
```

How each signer's code is run and handed to the model, step by step: [docs/architecture.md](docs/architecture.md).
The model and its guarantees, with each theorem read from the compiled source: [habakan.github.io/btcsigner-spec](https://habakan.github.io/btcsigner-spec/), or `make docs` and open `manual/_out/html-multi/index.html`.

| | |
|---|---|
| `SignerSpec/Model.lean` | the transaction, the review (which inputs are signed, what is change, the fee), the screen, signing |
| `SignerSpec/Theorems.lean` | the guarantees, all proved |
| `SignerSpec/Sessions.lean` | what a signature commits to, and what any transaction assembled from one pays |
| `SignerSpec/Notation.lean` | how the screen writes amounts and scripts, and that it is one to one |
| `SignerSpec/Checksums.lean` | the real address checksums (bech32 polymod, SHA-256), for the executable |
| `SignerSpec/Sighash.lean` | the BIP143 and BIP341 digests, what each binds, and `SigValid` derived from them |
| `tests/Notation.lean` | that notation against SHA-256, BIP173, BIP350 and base58check vectors (`make check`) |
| `SignerSpec/Message.lean` | how a message to sign is shown, and that a reader can tell any two apart |
| `SignerSpec/Txid.lean` | the serialization a txid hashes, and `Bound` derived from it |
| `tests/Txid.lean` | that serialization and txid against raw mainnet transactions (`make check`) |
| `tests/Sighash.lean` | those digests against the BIP143 and BIP341 vectors (`make check`) |
| `tests/Message.lean` | the message display on the cases that decide it (`make check`) |
| `SignerSpec/Address.lean` | an address read back to its script, accepting only the string the screen writes |
| `tests/Address.lean` | that reading against BIP350's valid and invalid addresses and base58check (`make check`) |
| `SignerSpec/Wordlist.lean`, `SignerSpec/Mnemonic.lean` | the BIP39 wordlist, a mnemonic and its entropy, the last word, SeedQR |
| `tests/Mnemonic.lean` | those against the wordlist's hash, the BIP39 vectors and SeedSigner's SeedQR vectors (`make check`) |
| `SignerSpec/Psbt.lean` | a PSBT's maps as bytes, and that faithful readers agree |
| `tests/Psbt.lean` | that against PSBT vectors, with a repeated key and trailing bytes refused (`make check`) |
| `SignerSpec/Multisig.lean` | a sortedmulti witness script, and what it and its P2WSH output bind |
| `tests/Multisig.lean` | that script against the BIP67 vectors (`make check`) |
| `SignerSpec/OrD.lean` | an or_d wallet's witness script (Liana's shape), and what it and its P2WSH output bind |
| `tests/OrD.lean` | that reading against bitwasm-signer's or_d vectors and broken copies of them (`make check`) |
| `Main.lean` | the model as an executable: one JSON case per line in, one verdict per line out |
| `adapters/bitcoin.mjs` | what the model takes as given (BIP32, the scripts a key makes, a previous transaction), from `node:crypto` alone |
| `adapters/model.mjs` | the test wallet and its cosigners, a transaction as the model's case, the Lean process |
| `adapters/psbt.mjs` | PSBT v0 read and written back, and what it says in the model's terms |
| `adapters/compare.mjs` | the invariant comparison: mutations, invariants, the report |
| `adapters/<signer>.*`, `adapters/coconut/` | one adapter per signer, each driving that project's own code |

## What the model guarantees

1. **The fee** is total in minus total out, and every total stays within 21M BTC, so none wraps a uint64
   and every amount reads the same as a signed or an unsigned 64-bit integer.
2. **Nothing on the PSBT's word alone.** An input is signed, and an output is called ours, only when the
   key re-derived from the seed produces its script. An output must also share an account with an
   input being signed (or, for P2WSH and P2SH-P2WSH, a registered wallet).
3. **The screen** shows every output's amount and script as they are, and external outputs + fee +
   our outputs = total in. As written, two different amounts never read the same (BTC with eight
   decimals), nor two different scripts on one network (bech32/bech32m for witness versions 0 to 16,
   base58check, or `script:` and hex for a script with no address). Read back, that string gives its
   script, and a string gives a script only if it is exactly the one written for it, checksum included
   (`decode_render`, `render_decode`). An output paying more than zero to a script nobody can spend
   (OP_RETURN, or longer than 10,000 bytes) is flagged burned, is never ours, and so counts in what
   leaves the wallet.
4. **Signing** produces signatures only for the transaction reviewed and only for the inputs review
   accepted, each by a key whose script the input's is: the key the PSBT names, and for a registered
   wallet that holds us twice (an or_d that reuses a signer), our other key in it. It also consumes the
   approval.
5. **Input amounts.** None is one its previous transaction contradicts, and once two or more inputs
   include one signed under BIP143, or any input is signed as legacy P2PKH, every amount is backed by its
   previous transaction, so a fee cannot be understated across two signing sessions. A previous transaction matches only when its txid is the one
   spent and its output there has the input's amount and script; the txid alone is not enough.
6. **Signatures across reviews.** Whatever transaction a coordinator assembles in which a signature
   from review verifies, from however many reviews, pays the fee that review showed to the outputs it
   showed. This follows from what BIP143 and BIP341 signatures commit to, which `SigValid` states, and
   from 4 and 5; it is why review may skip previous transactions when every input it signs is taproot.
   `Sighash.lean` derives `SigValid` from the two digests, and shows a BIP143 digest that stays the same
   while another input's amount, and so the fee, changes. `Txid.lean` derives `Bound`, that a previous
   transaction review matched pays what the chain holds at that outpoint, from the txid.
7. **Messages.** A message to sign is shown as text only when it is printable ASCII with no space at
   either end and never two in a row, and as hex otherwise. To a reader who cannot count spaces, two
   different messages never look the same; printable alone is not enough ("a" and "a ").
8. **Mnemonics.** Four typed letters name one BIP39 word; three do not ("act", "action"). A mnemonic and
   its entropy determine each other, so a CompactSeedQR loses nothing, and a Standard SeedQR reads back
   to its words while no other digits read as them. The last words that pass the checksum are exactly
   `finalWords`: 128 of 2048 with 12 words, so the checksum misses one wrong last word in 16.
9. **Reading a PSBT.** Two readers that accept only bytes their reading writes back, with no key twice in
   a map, never read one PSBT two ways (`readers_agree`). With a key twice the first value and the last
   can differ (`first_last_differ`), so one reader may show what another signs.
10. **Multisig wallets.** A sortedmulti witness script is the same whatever order its keys are given in,
    and binds the threshold and the keys up to order; so does its P2WSH output, taking SHA-256 to be one
    to one (`p2wsh_binds`). Change that pays a registered wallet's P2WSH script pays no other quorum; for
    P2SH-P2WSH that also takes HASH160 to be one to one, which is not proved here. An or_d wallet's script
    (`or_d(X,and_v(v:Y,older(n)))` or `after(n)`, as Liana writes it) is read back as exactly that wallet
    (`orDOf_script`), so it binds both paths' keys and threshold and the timelock's kind and value, and so
    does its P2WSH output (`p2wsh_orD_binds`). The model signs such inputs only for a signer whose policy
    says it signs or_d wallets.

## How a signer is compared

Every comparison starts from the same PSBTs: Bitcoin Core's `rpc_psbt.json` vectors and a set of wallet
vectors, generated by bitwasm-signer's build, plus mutations of them. `Env.owns`, the registered wallet's
witness scripts and the parsed previous transactions are computed by `adapters/bitcoin.mjs` from the test
seeds, sharing no code with any signer.

**Invariants**, for every signer. A signer's policy need not be the model's, so a difference in what it
decides is counted and explained, not failed. A run fails only on an invariant any signer has to keep for
what it lets the user approve:

- the screen adds up (spend + change + fee = input)
- the input total is the PSBT's
- the fee is inputs minus outputs, unless an output is 2^63 or more: consensus reads it as negative, so
  the transaction cannot be mined and the fee is counted as a policy difference
- change shown as verified is made by our seed at the path the PSBT gives
- an input amount the PSBT's own previous transaction contradicts is not shown without a warning (a signer
  that shows the previous transaction's amounts instead keeps this and the totals above with those)
- an address shown for an output is the one `Notation.lean` writes for its script on that network (a
  script with no address may be shown in the signer's own way)
- an amount the screen shows, read back in the unit and decimal point the screen writes, is the amount it
  stands for, and no two amounts up to 21M BTC are written the same (one written with no unit is counted as
  a policy difference). Krux, Coldcard, SeedSigner and Specter
  DIY write them with their own code, on every case and on edge values (every unit Coldcard offers, a
  decimal comma for Krux). Specter writes them under MicroPython on the device, and this runs its
  expression under CPython, whose float printing differs

A PSBT with a key twice in a map is invalid (BIP174) and the model refuses it; one mutation repeats a key
with another value, first or last, and a signer that accepts it is counted with which value its screen took.
Every signer compared here refuses it.

A worker whose output breaks any of the first four on purpose (verification skipped, the fee a satoshi
off, change left out of the total) fails it. `make check-seedsigner`, `check-krux`, `check-specter`, `check-coldcard` and `check-coconut`
run this, with each kind of wallet the signer holds. `make check-bitcoinjs` runs it on a library (below).

**Exact agreement**, for a signer whose review reports the same decisions as the model: the error, or
the totals, the inputs signed and every output's owner. Each verdict must then be identical. This is
stronger and needs the signer's decisions as data, which bitwasm-signer's review gives (`make
check-bitwasm`, mutating its fixed-layout plan). It runs on mainnet, with a multisig registered, with
another multisig registered, and on testnet, and its parser has to refuse every input and output map
of the vectors with a key repeated. A model with a planted bug has to fail it, and each of these
did, in the configuration it concerns: ignoring the account check on change, counting chain 1 as receive,
skipping the sighash check, an index bound off by one, P2WSH change without a P2WSH input being signed,
no wallet check, and change that ignores the network.

`make vectors` writes the same cases to `build/vectors.json`, for a signer to test against in its own suite
without Lean or Node. CI publishes the file for each commit on main at
[habakan.github.io/btcsigner-spec/vectors.json](https://habakan.github.io/btcsigner-spec/vectors.json), with its SHA-256 beside it. Each case has the PSBT, the wallet the signer holds, the model's verdict, and what any
signer that lets the user approve it has to show: the input total (the PSBT's amounts, or the previous
transactions' where they differ), the fee for each, whether it has to warn about unverified input amounts,
and which outputs it may not call verified change. The model's verdict is its policy, not a requirement.

What a run finds in a released version of a project goes to that project privately before it is written
down anywhere public.

## Where each signer's policy differs from the model

- **bitwasm-signer** decides as the model does on everything the model describes, which the exact
  comparison checks.
- **SeedSigner** calls change any output our seed makes at the path the PSBT gives, showing that path
  rather than refusing an unusual one; fills in a missing fingerprint; refuses inputs of mixed script
  types; shows a negative fee for a transaction that cannot be mined; past 1M sats writes the totals in
  btc and the fee in sats with no unit beside them;
  and its review passes a sighash other than ALL, which embit's `sign_with` then declines to sign.
- **Krux** holds one script type per wallet and refuses a PSBT of another; warns rather than refuses on
  a path mismatch, an unset fingerprint and high fees; and
  refuses outputs worth more than the inputs, a sighash other than ALL, and a PSBT it signs nothing in.
- **Specter DIY** (1.10.5) holds its default P2WPKH wallet and the one a config adds. It warns rather than
  refuses on inputs of an unknown wallet, inputs of several wallets, and a sighash other than ALL; takes
  input amounts from the previous transactions where the witness_utxo contradicts them; approves outputs
  worth more than the inputs; and refuses a PSBT it signs nothing in.
- **Coldcard** refuses a PSBT with no key paths, multisig inputs of a wallet it has not registered, a fee
  over 10% of the amount sent, and outputs worth more than the inputs. It takes input amounts from the
  previous transactions where the witness_utxo contradicts them, and calls change an output of its seed at
  paths the model treats as external: another coin type or purpose, a chain above 1, an index of 100000 or
  more, or an account no input being signed is on. Its non-EDGE firmware signs no taproot input and shows a
  taproot output of its seed as a payment.
- **Bitcoin Core** (31.1) signs with descriptor wallets of the test seed and shows what `decodepsbt` reports
  after `walletprocesspsbt`. It takes each input amount from the previous transaction when the PSBT has one,
  so a witness_utxo that contradicts it changes nothing; it refuses a sighash other than the one it is asked
  for, and many malformed PSBTs at parsing. It names no output change here.
- **libwally-core** (1.5.6) has no fee function. A wallet built on it adds up `psbt_get_input_best_utxo`,
  which documents taking witness_utxo first, after `psbt_sign_bip32`; that sum shows a contradicted amount
  without a word, so a wallet on libwally has to compare the two itself. It signs whatever sighash the PSBT
  names.
- **rust-bitcoin** (0.32.102) is taken to show `Psbt::fee()` after `Psbt::sign()` with the test seed's
  master key, and `Address::from_script` for each output. Like libwally it takes witness_utxo first and
  compares nothing; it also signs a non_witness_utxo whose txid is not the one spent. Its `Psbt` leaves
  that consistency to the caller ([#1366](https://github.com/rust-bitcoin/rust-bitcoin/issues/1366)).
- **bitcoinjs-lib** is a library with no review screen. What a wallet built on it would show is taken to be
  what `getFee()` returns after its own `signAllInputsHD()` and `finalizeAllInputs()` with the test seed. It
  names no output change and gives no warnings, so it is compared on the totals, the fee and input amounts
  only; it refuses a PSBT it cannot sign and finalize in full, such as a multisig or taproot script path.
  It reads an output of 2^63 or more as negative, as consensus does, and `getFee()` counts it that way.
- **Coconut Vault** holds P2WPKH single-sig and P2WSH multisig vaults, and signs ECDSA with SIGHASH_ALL whatever the PSBT asks for.

## What this does not prove

The theorems are about the model. That a signer behaves like it is tested, not proved. Key derivation,
script hashing and SHA-256 are assumptions (`Env.owns`, equality of `Tx` standing in for equal hashes),
not things proved here. What a signature commits to, and that a txid binds its transaction (`Bound`), are
derived from the digests and the serialization, taking SHA-256 to be one to one; that a signature
verifies only over its digest (ECDSA, Schnorr) is assumed. Address checksums are parameters of the notation; its proofs hold whatever they are, and the vectors check the
rest. Signers' addresses are compared with it, and their amounts are read back to the value they stand for.

## License

MIT. See [LICENSE](LICENSE).
