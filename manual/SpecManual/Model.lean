import VersoManual
import SignerSpec
import SpecManual.Beside

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open SpecManual

set_option verso.docstring.allowMissing false

#doc (Manual) "The model" =>
%%%
tag := "model"
%%%

The model describes a transaction as a signer sees it, with the cryptography already answered. It decides
whether to sign, what to call each output, and what to put on the screen.

Beside each definition is what the BIPs say about it, in our words, with a link to the text itself. The BIP text is authoritative.

# A transaction

A transaction is its inputs and outputs. The key path on either is the PSBT's claim that it is ours, and
the model does not trust that claim.

:::beside
{docstring SignerSpec.Tx}

_Defined_ in [BIP 174, Specification][b174-specification]. A PSBT is a global map, then one map per input and one per output. `PSBT_GLOBAL_UNSIGNED_TX` holds the unsigned transaction, with empty scriptSigs and witnesses.

*The model:* Only what review needs is kept: the inputs and outputs in order. Bytes are handled separately, in {ref "guarantees"}[Reading a PSBT].
:::

:::beside
{docstring SignerSpec.Input}

_Defined_ in [BIP 174, Specification][b174-specification]. Each input map holds fields keyed by type. The model reads:

 * `amount`, `spk`: `PSBT_IN_WITNESS_UTXO`, otherwise the spent output of `PSBT_IN_NON_WITNESS_UTXO`
 * `key`: `PSBT_IN_BIP32_DERIVATION`, a fingerprint and a path
 * `sighash`: `PSBT_IN_SIGHASH_TYPE`
 * `wscript`: `PSBT_IN_WITNESS_SCRIPT`
 * `prev`: `PSBT_IN_NON_WITNESS_UTXO`

_Defined_ in [BIP 371, Specification][b371-specification]. Taproot inputs give their derivation in `PSBT_IN_TAP_BIP32_DERIVATION` instead, keyed by an x-only public key.
:::

:::beside
{docstring SignerSpec.Output}

_Defined_ in [BIP 174, Specification][b174-specification]. Amount and script come from the unsigned transaction. An output map may add `PSBT_OUT_BIP32_DERIVATION`, the data a signer can use to spot change.

_Defined_ in [BIP 371, Specification][b371-specification]. Taproot outputs use `PSBT_OUT_TAP_BIP32_DERIVATION`.

*The model:* `key` stays a claim. It only names a candidate for change.
:::

:::beside
{docstring SignerSpec.KeyPath}

_Defined_ in [BIP 32, Key identifiers][b32-key-identifiers]. A key is identified by the Hash160 of its public key, and the fingerprint is the first 32 bits of that identifier.

_Defined_ in [BIP 32, The key tree][b32-the-key-tree]. Keys form a tree from the master, and a path walks it one child index at a time. Indices from 2^31 up are hardened.
:::

A previous transaction, the PSBT's `non_witness_utxo`, is reduced to what review needs from it. Its txid
alone does not make it a match: its output must also carry the input's amount and script.

:::beside
{docstring SignerSpec.PrevInfo}

_Defined_ in [BIP 174, Specification][b174-specification]. `PSBT_IN_NON_WITNESS_UTXO` carries the whole transaction an input spends, in network serialization. It should be there for non-segwit inputs and may be there for segwit ones.

*The model:* The transaction is reduced to the txid it hashes to and its output at the input's index.
:::

:::beside
{docstring SignerSpec.PrevTx}

_Optional_ in [BIP 174, Specification][b174-specification]. An input may carry both UTXO fields. BIP 174 says both must be allowed, because wallets began asking for the full transaction after PSBT was in use.

*The model:* `PrevTx` records which case an input is in: nothing given, a match, or a mismatch.
:::

:::beside
{docstring SignerSpec.PrevTx.of}

_Required_ in [BIP 174, Data Signers Check For][b174-data-signers-check-for]. If a non-witness UTXO is given, its hash has to equal the txid in the prevout.

*Beyond the BIPs:* Its output must also carry the input's amount and script. BIP 174 allows both UTXO fields and does not ask a signer to compare them.
:::

# What the signer knows

The environment holds what only the seed can answer. `owns` says whether the key at a path makes a script,
and key derivation itself is assumed rather than modelled.

:::beside
{docstring SignerSpec.Env}

_Defined_ in [BIP 32, Key identifiers][b32-key-identifiers]. `fingerprint` is the first 32 bits of the master key's identifier.

_Optional_ in [BIP 174, Signer][b174-signer]. A signer need not sign every input type, and `legacy` says whether this one signs P2PKH.

*Beyond the BIPs:* `owns` means the key is re-derived from the seed. BIP 174 says a signer may only use the UTXOs in the PSBT, and does not say how it decides that an input is its own.
:::

:::beside
{docstring SignerSpec.Multisig}

_Defined_ in [BIP 67, Specification][b67-specification]. Public keys are received compressed and sorted lexicographically before the multisig script is built, so every cosigner builds the same script.

_Defined_ in [BIP 383, Specification][b383-specification]. The `sortedmulti` descriptor sorts the keys that go into the script, after any extended keys are derived.

*Beyond the BIPs:* Registering a wallet on the signer is the model's rule. BIP 174 instead suggests comparing script policies built from the global xpubs.
:::

# The review

`review` either refuses with one error or settles the totals, the fee, the inputs it will sign, and who
owns each output.

:::beside
{docstring SignerSpec.review}

_Required_ in [BIP 174, Data Signers Check For][b174-data-signers-check-for]. A signer has to check its data before it signs. Among those checks, a sighash type it finds unacceptable means failing.

_Optional_ in [BIP 174, Signer][b174-signer]. A signer need not sign every input type. BIP 174 gives signing only segwit inputs as an example.

*The model:* It accepts ALL, and DEFAULT on taproot. It refuses legacy inputs that claim to be ours unless `legacy` is set.
:::

`review` checks in this order and refuses with the first error. `tests/Review.lean` runs one case per row,
so a change to the order or to a rule fails `make check` until this table changes with it.

The last column is what Bitcoin Core's wallet does with the same PSBT, signing with `walletprocesspsbt` and
reporting with `decodepsbt`. `adapters/core-rules.mjs` runs each row through both and fails when either
changes (`make check-core`). Core's wallet does not review: it signs whatever its keys can sign and leaves
the review to its user. So where it signs and the model refuses, the model is the stricter choice a signer
that reviews makes, not Core in error.

The last column is why the model refuses where Core signs. Each refusal is required by a BIP, needed for a
proved guarantee (the theorem is named), refuses what consensus would reject anyway, or is a bound of the
model's own, marked as such.

:::table +header
*
  * Step
  * Refused when
  * Error
  * In the BIPs
  * Bitcoin Core 31.1
  * Why the model refuses
*
  * 1
  * Outside the model's limits, `formatOk`
  * `format`
  * Beyond the BIPs
  * Signs
  * *Model's own:* counts and path depth bound the review. Amounts within 21M BTC read the same as signed and unsigned 64-bit values ({name SignerSpec.formatOk_amounts}`formatOk_amounts`)
*
  * 2
  * The inputs' running total passes 21M BTC
  * `format`
  * Beyond the BIPs
  * Signs; `decodepsbt` reports no fee
  * *Consensus:* nothing spends more than 21M BTC. Every total then fits a uint64 ({name SignerSpec.totals_fit_u64}`totals_fit_u64`)
*
  * 2
  * An input of ours has a script this signer does not sign, or a witness script it does not know
  * `script`
  * _Optional_ in [BIP 174, Signer][b174-signer]: a signer need not sign every input type
  * Signs with its key, which the PSBT's path leads to
  * *Proof:* the guarantees are proved for the scripts the model knows ({name SignerSpec.sig_outputs}`sig_outputs`, {name SignerSpec.sig_amounts}`sig_amounts`); another script could be spent in a way review never saw
*
  * 2
  * An input of ours asks for a sighash other than ALL, or DEFAULT on taproot
  * `sighash`
  * _Required_ in [BIP 174, Data Signers Check For][b174-data-signers-check-for]: fail on an unacceptable sighash
  * Refuses unless asked for that sighash
  * *BIP and proof:* under ALL, or DEFAULT on taproot, a signature commits to every output ({name SignerSpec.signed_sighash}`signed_sighash`, {name SignerSpec.sig_outputs}`sig_outputs`)
*
  * 2
  * The key the seed derives at an input's path does not make its script
  * `notOurs`
  * _Required_ in [BIP 174, Signer][b174-signer]: use only the UTXOs given
  * Signs: the script is its own, whatever path the PSBT gives
  * *Proof:* an input is signed only when the seed makes its script ({name SignerSpec.signed_sound}`signed_sound`)
*
  * 2
  * A multisig input of ours whose witness script is not the registered wallet's
  * `wallet`
  * Beyond the BIPs
  * Signs: nothing is registered
  * *Proof:* change is called ours only when it pays the registered wallet, the quorum the signed inputs belong to ({name SignerSpec.owner_sound}`owner_sound`, {name SignerSpec.p2wsh_binds}`p2wsh_binds`)
*
  * 3
  * No input names our fingerprint
  * `nothingToSign`
  * Beyond the BIPs
  * Signs nothing
  * *None needed:* nothing would be signed, and refusing says so
*
  * 4
  * Any input's previous transaction disagrees with it
  * `prevtxMismatch`
  * _Required_ in [BIP 174, Data Signers Check For][b174-data-signers-check-for] for the txid; the amount and script are beyond the BIPs
  * Signs, taking the amount from the previous transaction
  * *Proof:* the amounts shown are the ones a signature commits to ({name SignerSpec.review_prev}`review_prev`, {name SignerSpec.sig_amounts}`sig_amounts`)
*
  * 4
  * A previous transaction is missing while every one is needed, `checkPrev`
  * `prevtxMissing`
  * _Optional_ in [BIP 174, Signer][b174-signer]; [BIP 371, UTXO Types][b371-utxo-types] exempts taproot
  * Signs
  * *Proof:* otherwise another input's amount, and so the fee, can change under a SegWit v0 signature ({name SignerSpec.sig_amounts}`sig_amounts`, {name SignerSpec.sig_fee}`sig_fee`)
*
  * 5
  * The outputs' running total passes 21M BTC
  * `format`
  * Beyond the BIPs
  * Signs; `decodepsbt` reports no fee
  * *Consensus*, as for the inputs ({name SignerSpec.totals_fit_u64}`totals_fit_u64`)
*
  * 6
  * The outputs pay more than the inputs hold
  * `fee`
  * Beyond the BIPs
  * Signs; `decodepsbt` reports a negative fee
  * *Consensus:* such a transaction is invalid. The fee shown is never negative ({name SignerSpec.review_fee}`review_fee`)
*
  * After
  * Signing a transaction other than the one reviewed, `sign`
  * `notReviewed`
  * Beyond the BIPs
  * No review step
  * *Proof:* a review authorises signing only the transaction it reviewed ({name SignerSpec.sign_requires_review}`sign_requires_review`, {name SignerSpec.sign_other}`sign_other`)
:::

:::beside
{docstring SignerSpec.formatOk}

*Beyond the BIPs:* BIP 174 bounds none of these. The limits keep every total within a uint64.
:::

:::beside
{docstring SignerSpec.scanInputs}
:::

:::beside
{docstring SignerSpec.checkInput}

_Required_ in [BIP 174, Data Signers Check For][b174-data-signers-check-for]. If a witness script is given, the script it spends has to be for it. Here `Env.owns` answers that with the signer's own code.

*The model:* An input whose fingerprint is not ours is left unsigned, not refused.
:::

:::beside
{docstring SignerSpec.Review}

_Optional_ in [BIP 174, Signer][b174-signer]. A signer can compute the addresses, the values and the fee, and can show them as confirmation of intent.

*The model:* Computing them is not optional. A review always settles the totals, the fee, the inputs and each owner.
:::

:::beside
{docstring SignerSpec.Error}

_Required_ in [BIP 174, Signer][b174-signer]. A signer that cannot sign must not add a partial signature.

*The model:* Refusal is all or nothing. One error refuses the whole transaction, which is stricter than signing the inputs that pass.
:::

:::beside
{docstring SignerSpec.Owner}

_Defined_ in [BIP 44, Change][b44-change]. Chain 0 holds addresses meant to be seen outside the wallet. Chain 1 holds internal ones, used for change.

*The model:* `external` covers everything else. `self` is chain 0 on our account, and `change` is chain 1.
:::

:::beside
{docstring SignerSpec.outputOwner}

_Defined_ in [BIP 44, Path levels][b44-path-levels]. A path has five levels: `m / purpose' / coin_type' / account' / change / address_index`. The first three are hardened.

_Defined_ in [BIP 84, Public key derivation][b84-public-key-derivation]. Purpose is 84' for P2WPKH.

_Defined_ in [BIP 49, Public key derivation][b49-public-key-derivation]. Purpose is 49' for P2SH-P2WPKH.

_Defined_ in [BIP 86, Public key derivation][b86-public-key-derivation]. Purpose is 86' for P2TR key spends.

_Defined_ in [BIP 44, Purpose][b44-purpose]. Purpose is 44' for P2PKH, counted only when `legacy` is set.

_Optional_ in [BIP 174, Change Detection][b174-change-detection]. A signer may hide change from its display. For one key, it can check the fingerprint, derive the key at the path and compare it with the output.

*Beyond the BIPs:* The output must also be on the account of an input being signed.
:::

:::beside
{docstring SignerSpec.Input.multisig}

_Defined_ in [BIP 141, Witness program][b141-witness-program]. A witness program may be the redeem script of a P2SH output, and then the P2SH script commits to it.

*Beyond the BIPs:* Telling P2SH-P2WSH from P2SH-P2WPKH by the witness script, and signing it only for a signer whose `nested` is set.
:::

:::beside
{docstring SignerSpec.walletClaims}
:::

:::beside
{docstring SignerSpec.checkPrev}

_Defined_ in [BIP 143, Specification][b143-specification]. The digest includes the amount of the input being signed, and not the amounts of the others.

_Optional_ in [BIP 174, Signer][b174-signer]. A signer may fail on a segwit input with no previous transaction. A note there explains why: amounts of other segwit inputs can change without affecting a signature, so a user who signs twice can be tricked into paying fees.

*Beyond the BIPs:* Refusing is the rule here whenever two or more inputs include one signed under BIP 143.
:::

# The screen

`display` turns a review into what the person sees. Scripts are rendered from their bytes, never from text
the PSBT supplied.

:::beside
{docstring SignerSpec.display}

_Optional_ in [BIP 174, Signer][b174-signer]. Showing addresses, values and fee is something a signer can do.

*The model:* Every review has this screen, built from the transaction and the review alone.
:::

:::beside
{docstring SignerSpec.Display}

_Optional_ in [BIP 174, Signer][b174-signer]. BIP 174 does not define a screen.

*The model:* `spend` is the total of external outputs. The guarantee on it is in {ref "guarantees"}[The screen].
:::

:::beside
{docstring SignerSpec.DisplayOutput}

_Defined_ in [BIP 173, Segwit address format][b173-segwit-address-format]. A version 0 output is written in Bech32, with `bc` on mainnet and `tb` on testnet.

_Defined_ in [BIP 350, Addresses for segregated witness outputs][b350-addresses-for-segregated-witness-outputs]. Version 1 and higher are written in Bech32m.

*Beyond the BIPs:* The `burned` warning.
:::

:::beside
{docstring SignerSpec.unspendable}

*Beyond the BIPs:* No BIP asks for this. It follows Bitcoin Core's `IsUnspendable`: a script starting with `OP_RETURN`, or longer than any script can be.
:::

# Signing

The approval a signer holds between review and signing is the exact transaction reviewed.

:::beside
{docstring SignerSpec.State}

*Beyond the BIPs:* BIP 174 has no approval step between looking at a PSBT and signing it. The model holds the exact transaction reviewed.
:::

:::beside
{docstring SignerSpec.reviewStep}

*Beyond the BIPs:* A passing review is the only thing that creates an approval. A refused review clears it.
:::

:::beside
{docstring SignerSpec.sign}

_Required_ in [BIP 174, Signer][b174-signer]. A signature is added as a partial signature on its input, and a signer that cannot sign adds none. A signer only adds data to a PSBT.

*Beyond the BIPs:* Signing needs the approval from review, for that exact transaction, and uses it up.
:::

[b143-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0143.mediawiki#specification
[b173-segwit-address-format]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0173.mediawiki#segwit-address-format
[b174-change-detection]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#change-detection
[b174-data-signers-check-for]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#data-signers-check-for
[b174-signer]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#signer
[b174-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#specification
[b32-key-identifiers]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0032.mediawiki#key-identifiers
[b32-the-key-tree]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0032.mediawiki#the-key-tree
[b350-addresses-for-segregated-witness-outputs]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0350.mediawiki#addresses-for-segregated-witness-outputs
[b371-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0371.mediawiki#specification
[b383-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0383.mediawiki#specification
[b44-change]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0044.mediawiki#change
[b44-path-levels]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0044.mediawiki#path-levels
[b49-public-key-derivation]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0049.mediawiki#public-key-derivation
[b67-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0067.mediawiki#specification
[b84-public-key-derivation]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0084.mediawiki#public-key-derivation
[b86-public-key-derivation]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0086.mediawiki#public-key-derivation
[b44-purpose]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0044.mediawiki#purpose
[b141-witness-program]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0141.mediawiki#witness-program
[b371-utxo-types]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0371.mediawiki#utxo-types
