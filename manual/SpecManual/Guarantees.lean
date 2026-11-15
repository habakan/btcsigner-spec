import VersoManual
import SignerSpec
import SpecManual.Beside

open Verso.Genre Manual
open SpecManual

set_option verso.docstring.allowMissing false

#doc (Manual) "What the model guarantees" =>
%%%
tag := "guarantees"
%%%

Each section states a guarantee and shows the theorems behind it.

Beside each theorem is what the BIPs say about it, in our words, with a link to the text itself. The BIP text is authoritative. A note marked _Beyond the BIPs_ is the model's own rule or result, so a signer can follow every BIP and still differ from it.

# The fee

The fee is total in minus total out, and every total stays within 21M BTC. So no total wraps a uint64, and
every amount reads the same as a signed or an unsigned 64-bit integer.

:::beside
{docstring SignerSpec.review_fee}

_Optional_ in [BIP 174, Signer][b174-signer]. A signer can compute the fee. BIP 174 does not state how, or require it.

*The model:* The fee is exactly total in minus total out, and it is never negative.
:::

:::beside
{docstring SignerSpec.totals_fit_u64}

*Beyond the BIPs:* 21M BTC is a consensus limit, not a PSBT rule.
:::

:::beside
{docstring SignerSpec.amounts_fit_i64}

*Beyond the BIPs:* BIP 174 fields hold amounts as 64-bit values, and the BIP does not bound them. The model does, so signed and unsigned readers agree.
:::

:::beside
{docstring SignerSpec.formatOk_amounts}

*Beyond the BIPs:* Input and output limits here are the model's own.
:::

# Nothing on the PSBT's word alone

An input is signed, and an output is called ours, only when the key re-derived from the seed produces its
script. An output must also share an account with an input being signed or, for P2WSH and P2SH-P2WSH,
belong to a registered wallet.

:::beside
{docstring SignerSpec.signed_sound}

_Required_ in [BIP 174, Signer][b174-signer]. A signer may only use the UTXOs given in the PSBT to sign inputs.

*Beyond the BIPs:* A derivation in the PSBT is never enough. The key re-derived from the seed has to make the script.
:::

:::beside
{docstring SignerSpec.owner_sound}

_Optional_ in [BIP 174, Change Detection][b174-change-detection]. To detect change a signer can use derivations and global xpubs. For one key it derives the key at the path and compares. For several keys it builds a script policy and looks for outputs that share it with the inputs.

*Beyond the BIPs:* Here change is always checked against the seed, on the account of a signed input or in a registered wallet.
:::

# The screen

The screen shows every output's amount and script as they are, and external outputs + fee + our outputs =
total in.

:::beside
{docstring SignerSpec.display_faithful}

_Optional_ in [BIP 174, Signer][b174-signer]. BIP 174 leaves showing addresses, values and fee to the signer.

*The model:* Every output appears, with its own amount and script, in order.
:::

:::beside
{docstring SignerSpec.display_accounts}

*Beyond the BIPs:* No BIP requires a screen to add up.
:::

An output paying more than zero to a script nobody can spend is flagged burned, is never ours, and so counts
in what leaves the wallet.

:::beside
{docstring SignerSpec.display_burned}

*Beyond the BIPs:* No BIP asks for this warning.
:::

:::beside
{docstring SignerSpec.unspendable_external}

*Beyond the BIPs:* No BIP says how to label these outputs.
:::

As written, two different amounts never read the same, nor two different scripts on one network. Read back,
an address gives its script, and a string gives a script only if it is exactly the one written for it,
checksum included.

:::beside
{docstring SignerSpec.fmtAmount_inj}

*Beyond the BIPs:* No BIP defines how a signer writes amounts. Here they are BTC with eight decimals.
:::

:::beside
{docstring SignerSpec.render_inj}

_Defined_ in [BIP 141, Witness program][b141-witness-program]. A witness program is a version byte and a 2 to 40 byte push.

_Defined_ in [BIP 173, Segwit address format][b173-segwit-address-format]. Bech32 encodes the version and the program, for version 0.

_Defined_ in [BIP 350, Addresses for segregated witness outputs][b350-addresses-for-segregated-witness-outputs]. Bech32m does the same for version 1 and above.

_Defined_ in [BIP 13, Specification][b13-specification]. A P2SH address is Base58Check of a version byte, the 20-byte script hash and a 4-byte checksum.

*Beyond the BIPs:* That this writing is one to one is proved here.
:::

:::beside
{docstring SignerSpec.decode_render}

_Defined_ in [BIP 350, Addresses for segregated witness outputs][b350-addresses-for-segregated-witness-outputs]. A decoder should accept each witness version only with its own encoding.

*The model:* Published vectors from BIP 173 and BIP 350 are checked by `tests/Address.lean`.
:::

:::beside
{docstring SignerSpec.render_decode}

_Required_ in [BIP 350, Addresses for segregated witness outputs][b350-addresses-for-segregated-witness-outputs]. Version 0 goes with Bech32 and version 1 and above with Bech32m, so a string in the wrong encoding is not an address.

*The model:* Only the exact string the screen would write reads back to a script.
:::

# Signing

Signing produces signatures only for the transaction reviewed and only for the inputs review accepted,
each by a key whose script the input's is. It also consumes the approval.

:::beside
{docstring SignerSpec.sign_requires_review}

*Beyond the BIPs:* BIP 174 has no approval step.
:::

:::beside
{docstring SignerSpec.sign_other}

*Beyond the BIPs:* BIP 174 has no approval step. A real signer holds a hash of the transaction, and the model takes that hash to be collision resistant.
:::

:::beside
{docstring SignerSpec.sign_only_reviewed}

_Required_ in [BIP 174, Signer][b174-signer]. A signer that cannot sign an input adds no partial signature for it.

*The model:* Signatures come only for the inputs review accepted.
:::

:::beside
{docstring SignerSpec.sign_all_reviewed}

*Beyond the BIPs:* BIP 174 leaves which inputs a signer signs to the signer. The model signs every input review accepted.
:::

:::beside
{docstring SignerSpec.signKeys_two}

*Beyond the BIPs:* A registered wallet may hold our seed on both paths of an `or_d`, as Nunchuk's reused signers
and Bitcoin Keeper do, and then the input is signed by both keys. No other key signs, and none signs twice.
:::

:::beside
{docstring SignerSpec.sign_consumes}

*Beyond the BIPs:* BIP 174 has no approval step, so it has nothing to consume.
:::

# Input amounts

No input amount is one its previous transaction contradicts. Once two or more inputs include one signed
under BIP143, or any input is signed as legacy P2PKH, every amount is backed by its previous transaction, so a
fee cannot be understated across two signing sessions.

:::beside
{docstring SignerSpec.review_prev}

_Defined_ in [BIP 143, Specification][b143-specification]. A BIP 143 digest includes only the signed input's amount.

_Optional_ in [BIP 174, Signer][b174-signer]. A signer may fail without a previous transaction. Its note describes the attack: a fee can be inflated across signing sessions.

_Required_ in [BIP 174, Signer][b174-signer]. Before signing a non-witness input, a signer must check that its non-witness UTXO hashes to the txid it spends.

*Beyond the BIPs:* Requiring every input's transaction when several inputs include a BIP 143 one, or when any is legacy, and refusing a contradiction.
:::

:::beside
{docstring SignerSpec.prev_matches}

_Required_ in [BIP 174, Data Signers Check For][b174-data-signers-check-for]. The non-witness UTXO's hash has to match the prevout.

*Beyond the BIPs:* The amount and script of its output have to match too.
:::

# Signatures across reviews

Whatever transaction a coordinator assembles in which a signature from review verifies, from however many
reviews, pays the fee that review showed to the outputs it showed. This follows from what BIP143 and BIP341
signatures commit to, and it is why review may skip previous transactions when every input it signs is
taproot.

:::beside
{docstring SignerSpec.sig_fee}

_Defined_ in [BIP 143, Specification][b143-specification]. A signature commits to its input's outpoint and amount, and, under ALL, to every output.

_Defined_ in [BIP 341, Common signature message][b341-common-signature-message]. A signature commits to every input's amount and spent script, and to every output, unless flags narrow it. BIP 341 gives lying to offline signers about the fee as the reason.

*Beyond the BIPs:* The result about what a coordinator can assemble is proved here.
:::

:::beside
{docstring SignerSpec.sig_outputs}

_Defined_ in [BIP 143, Specification][b143-specification]. `hashOutputs` is the double SHA-256 of all outputs when the sighash is neither SINGLE nor NONE.

_Defined_ in [BIP 341, Common signature message][b341-common-signature-message]. `sha_outputs` is the SHA-256 of all outputs.
:::

:::beside
{docstring SignerSpec.sig_amounts}

_Defined_ in [BIP 143, Specification][b143-specification]. The digest has the value of the output this input spends, and no others.

_Defined_ in [BIP 341, Common signature message][b341-common-signature-message]. `sha_amounts` is the SHA-256 of all input amounts.
:::

`SigValid` and `Bound` are what those theorems take as given. Both are derived further down: `SigValid` from
the two digests for a segwit input, `Bound` from the txid. A legacy input's digest is not modelled, so for one
`SigValid` is assumed, in the weakest form: the signature commits to the outputs and to no amount.

:::beside
{docstring SignerSpec.SigValid}

_Defined_ in [BIP 143, Specification][b143-specification]. What a signature on a segwit v0 input commits to.

_Defined_ in [BIP 341, Common signature message][b341-common-signature-message]. What a signature on a taproot input commits to.

*The model:* `sigValid_of_digest` derives this from the two digests, taking SHA-256 to be one to one.
:::

:::beside
{docstring SignerSpec.sigValid_of_digest}

_Defined_ in [BIP 143, Specification][b143-specification]. The digest is a double SHA-256 over version, hashes of the outpoints and sequences, the outpoint, script code, amount, sequence, hash of the outputs, locktime and sighash type.

_Defined_ in [BIP 341, Common signature message][b341-common-signature-message]. `SigMsg` is the message for taproot, built from the same kinds of data with single SHA-256 sub-hashes.
:::

:::beside
{docstring SignerSpec.Bound}

_Required_ in [BIP 174, Data Signers Check For][b174-data-signers-check-for]. A previous transaction has to hash to the prevout.

*The model:* `Bound` states what that gives: a transaction review matched pays what the chain holds at that outpoint.
:::

:::beside
{docstring SignerSpec.bound_of_spends}

*Beyond the BIPs:* Derived here from the txid, taking SHA-256 to be one to one.
:::

A BIP143 digest can stay the same while another input's amount, and so the fee, changes.

:::beside
{docstring SignerSpec.v0_other_amounts}

_Defined_ in [BIP 143, Specification][b143-specification]. Only the signed input's amount is in the digest.

_Background_ in [BIP 174, Signer][b174-signer]. A note there describes the attack that follows.

_Background_ in [BIP 341, Common signature message][b341-common-signature-message]. BIP 341 commits to all amounts for this reason.
:::

# Messages

A message to sign is shown as text only when it is printable ASCII with no space at either end and never two
in a row, and as hex otherwise. To a reader who cannot count spaces, two different messages never look the
same. Printable alone is not enough.

:::beside
{docstring SignerSpec.seen_inj}

_Background_ in [BIP 137, Specification][b137-specification]. A signature format for messages signed with Bitcoin keys.

_Background_ in [BIP 322, Detailed Specification][b322-detailed-specification]. Signed messages based on Script.

*Beyond the BIPs:* Both define signatures. Neither says how a message should be shown to a person, which is what this proves.
:::

:::beside
{docstring SignerSpec.printable_not_enough}

*Beyond the BIPs:* No BIP covers this.
:::

# Mnemonics

Four typed letters name one BIP39 word, and three do not.

:::beside
{docstring SignerSpec.four_letters}

_Defined_ in [BIP 39, Wordlist][b39-wordlist]. The list is built so that typing the first four letters identifies a word without ambiguity.

*The model:* BIP 39 states this as a property of the list. It is checked here against the list itself.
:::

:::beside
{docstring SignerSpec.three_letters_not_enough}

*Beyond the BIPs:* BIP 39 only says four letters are enough. This shows three are not.
:::

A mnemonic and its entropy determine each other, so a CompactSeedQR loses nothing, and a Standard SeedQR reads
back to its words while no other digits read as them.

:::beside
{docstring SignerSpec.toEntropy_toWords}

_Defined_ in [BIP 39, Generating the mnemonic][b39-generating-the-mnemonic]. Entropy of 128 to 256 bits gets a checksum of its SHA-256, entropy length divided by 32 bits long. The result is split into 11-bit groups, each an index into the wordlist.

*The model:* The two directions are proved inverse.
:::

:::beside
{docstring SignerSpec.decodeCompact_toEntropy}

*Beyond the BIPs:* SeedQR is SeedSigner's format, not a BIP. A CompactSeedQR holds the BIP 39 entropy, so the checksum can be rebuilt from it.
:::

:::beside
{docstring SignerSpec.decodeStd_seedqrStd}

*Beyond the BIPs:* SeedQR is SeedSigner's format, not a BIP. A Standard SeedQR writes each word's index as four digits.
:::

:::beside
{docstring SignerSpec.seedqrStd_decodeStd}

*Beyond the BIPs:* SeedQR is SeedSigner's format, not a BIP.
:::

The last words that pass the checksum are exactly `finalWords`: 128 of 2048 with 12 words, so the checksum
misses one wrong last word in 16.

:::beside
{docstring SignerSpec.mem_finalWords}

_Defined_ in [BIP 39, Generating the mnemonic][b39-generating-the-mnemonic]. 12 words carry a 4-bit checksum and 24 words carry 8 bits.

_Background_ in [BIP 39, Shortcomings][b39-shortcomings]. The BIP gives 1 in 256 for random errors the checksum misses. That is the 8-bit checksum of 24 words. With 12 words it is 1 in 16.
:::

:::beside
{docstring SignerSpec.finalWords_length}

_Defined_ in [BIP 39, Generating the mnemonic][b39-generating-the-mnemonic]. The last word holds the checksum bits, so the count of valid last words depends on its length.
:::

# Reading a PSBT

Two readers that accept only bytes their reading writes back, with no key twice in a map, never read one PSBT
two ways. With a key twice, the first value and the last can differ, so one reader may show what another
signs.

:::beside
{docstring SignerSpec.readers_agree}

_Required_ in [BIP 174, Handling Duplicated Keys][b174-handling-duplicated-keys]. Keys in a scope should never repeat, and a PSBT with a repeated key is invalid.

*Beyond the BIPs:* The hypothesis here is that rule. That readers then agree is proved.
:::

:::beside
{docstring SignerSpec.first_last_differ}

_Required_ in [BIP 174, Handling Duplicated Keys][b174-handling-duplicated-keys]. Such a PSBT is invalid, and the BIP's test vectors include one. The same section lets software combining PSBTs pick either value.

*The model:* This is why the model refuses. One reader may show the first value while another signs the last.
:::

# Multisig wallets

A sortedmulti witness script is the same whatever order its keys are given in, and binds the threshold and the
keys up to order. So does its P2WSH output, taking SHA-256 to be one to one. Change that pays a registered
wallet's P2WSH script therefore pays no other quorum. For P2SH-P2WSH this also takes HASH160 to be one to one,
which is not proved here.

:::beside
{docstring SignerSpec.sortedmulti_perm}

_Defined_ in [BIP 67, Specification][b67-specification]. Keys are sorted lexicographically before the script is built.

_Defined_ in [BIP 383, Specification][b383-specification]. `sortedmulti` sorts the keys that go in the script.
:::

:::beside
{docstring SignerSpec.sortedmulti_inj}

_Defined_ in [BIP 67, Specification][b67-specification]. The script holds the threshold, the sorted keys and the key count.

*Beyond the BIPs:* That the script binds these up to order is proved here.
:::

:::beside
{docstring SignerSpec.p2wsh_binds}

_Defined_ in [BIP 141, Witness program][b141-witness-program]. A 32-byte version 0 program is P2WSH: the SHA-256 of the witness script has to equal it.

*Beyond the BIPs:* Binding the quorum follows, taking SHA-256 to be one to one.
:::

[b13-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0013.mediawiki#specification
[b137-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0137.mediawiki#specification
[b141-witness-program]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0141.mediawiki#witness-program
[b143-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0143.mediawiki#specification
[b173-segwit-address-format]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0173.mediawiki#segwit-address-format
[b174-change-detection]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#change-detection
[b174-data-signers-check-for]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#data-signers-check-for
[b174-handling-duplicated-keys]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#handling-duplicated-keys
[b174-signer]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#signer
[b322-detailed-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0322.mediawiki#detailed-specification
[b341-common-signature-message]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0341.mediawiki#common-signature-message
[b350-addresses-for-segregated-witness-outputs]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0350.mediawiki#addresses-for-segregated-witness-outputs
[b383-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0383.mediawiki#specification
[b39-generating-the-mnemonic]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0039.mediawiki#generating-the-mnemonic
[b39-shortcomings]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0039.mediawiki#shortcomings
[b39-wordlist]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0039.mediawiki#wordlist
[b67-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0067.mediawiki#specification
