import VersoManual
import SignerSpec
import SpecManual.Beside

open Verso.Genre Manual
open SpecManual

set_option verso.docstring.allowMissing false

#doc (Manual) "What this does not prove" =>
%%%
tag := "limits"
%%%

The theorems are about the model. That a signer behaves like the model is tested, not proved.

# What the model covers

The model describes a narrower signer than BIP 174 allows. Outside what it describes, it refuses or leaves an
input unsigned, so it never signs something it does not describe. A signer that supports more is compared on
what both cover. The rest of what it does shows up only as a policy difference, and is not checked.

 * *Inputs it signs:* P2WPKH, P2SH-P2WPKH, P2WSH multisig with compressed keys and `OP_CHECKMULTISIG`, and P2TR by key path. P2PKH too, for a signer whose `legacy` is set, and then every input's previous transaction is required. P2SH-P2WSH multisig too, for a signer whose `nested` is set. Otherwise a legacy input the PSBT claims as ours is refused, and a P2SH-P2WSH one cannot be read.
 * *Taproot script paths:* not modelled. The adapters give no key for an input with leaf scripts, so it is not signed.
 * *Outputs:* any script can be paid, and is shown. Change is recognised only at `m / purpose' / coin' / account' / chain / index` with purpose 84', 49', 86', or 44' when `legacy` is set, and an index below 100,000, or in a registered P2WSH wallet, or P2SH-P2WSH one when `nested` is set.
 * *Sighash:* ALL, and DEFAULT on taproot. NONE, SINGLE, ANYONECANPAY and annexes are refused.
 * *Size:* at most 16 inputs and 16 outputs, and key paths of at most 8 steps.
 * *PSBT:* version 0, from BIP 174. Version 2, from BIP 370, is not modelled.
 * *Mnemonics:* the BIP 39 English wordlist, words and entropy, and SeedQR. The seed a mnemonic derives, and passphrases, are not modelled.
 * *Messages:* how a message is shown, not how it is signed.

Nothing after review and approval is modelled beyond which inputs get a signature: how signatures are made
(nonces, RFC 6979, anti-exfil), how keys are generated and stored, BIP 85 children, and exporting xpubs. The
screen is what review decides to show. How a device draws it is not modelled.

# What the proofs assume

 * Key derivation, script hashing and SHA-256 are assumptions: `Env.owns`, and equality of `Tx` standing in for equal hashes.
 * What a signature commits to, and that a txid binds its transaction, are derived from the digests and the serialization, taking SHA-256 to be one to one.
 * That a signature verifies only over its digest, for ECDSA and Schnorr, is assumed.
 * For P2SH-P2WSH change, that its script binds the quorum also takes HASH160 to be one to one, which is not proved.
 * A legacy signature's digest is not modelled. `SigValid` takes it to commit to the outputs under ALL and to no amount.
 * Address checksums are parameters of the notation. Its proofs hold whatever they are, and published vectors check the rest.

The assumption about hashing is stated once, and the theorems that need it take it as a hypothesis:

:::beside
{docstring SignerSpec.HashOk}

*Beyond the BIPs:* BIPs take SHA-256 as given. This is that assumption, stated once.
:::

:::beside
{docstring SignerSpec.Checksums}

_Defined_ in [BIP 173, Bech32][b173-bech32]. The Bech32 checksum.

_Defined_ in [BIP 350, Bech32m][b350-bech32m]. Bech32m changes its final constant.

*The model:* Proofs take the checksums as parameters. `Checksums.lean` has the real ones, for the executable.
:::

# What the comparisons rest on

The theorems hold for `review`, `display` and `sign`, and so for every verdict the executable prints. They do
not reach the adapters or the signers, and the inputs the model is given rest on code that is not proved:

 * `adapters/bitcoin.mjs`: key derivation, scripts, previous transactions, sighash digests, signature verification
 * `adapters/psbt.mjs`: what a PSBT says
 * `adapters/plan.mjs`: decoding a plan

`bitcoin.mjs` is shared by every comparison and shares no code with any signer. `psbt.mjs` and `plan.mjs` are
two independent routes from the same vector to the model, and on every unmutated vector they give the same
verdict.

Signers' addresses are compared with the notation. Their amounts are read back to the value they stand for; that they are written one to one is tested, not proved.

[b173-bech32]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0173.mediawiki#bech32
[b350-bech32m]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0350.mediawiki#bech32m
