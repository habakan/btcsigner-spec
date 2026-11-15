import VersoManual

open Verso.Genre Manual

#doc (Manual) "BIP 174, sentence by sentence" =>
%%%
tag := "bip174"
%%%

The other chapters start from the model. This one starts from the BIP: each sentence of BIP 174 that
binds a signer, quoted at commit `ada3419`, with what the model does about it.

 * *Followed:* the model does what the sentence says.
 * *Stricter:* the model does that and refuses more.
 * *Required:* the BIP allows it, and the model always does it.
 * *Differs:* the model does something else for the same end.
 * *Assumed:* the model takes it as answered, by the signer's own code through `Env.owns`.
 * *Not modelled:* outside the model, so nothing here is proved or tested about it.

The last column is what Bitcoin Core's wallet does, from `adapters/core-rules.mjs` and the comparison in
`make check-core`. It is there to show how the reference implementation reads each sentence, not as the rule.

# Signer

From [BIP 174, Signer][b174-signer].

:::table +header
*
  * BIP 174 says
  * The model
  * Where
  * Bitcoin Core 31.1
*
  * "The Signer must only accept a PSBT."
  * *Not modelled.* The model starts from a PSBT already read. Reading it one way is proved separately.
  * `readers_agree`
  * Not checked
*
  * "The Signer must only use the UTXOs provided in the PSBT to produce signatures for inputs."
  * *Stricter.* An input is signed only when the key the seed derives at its path makes its script.
  * `signed_sound`, `Error.notOurs`
  * Signs when the script is its own, whatever path the PSBT gives
*
  * "Before signing a non-witness input, the Signer must verify that the TXID of the non-witness UTXO matches the TXID specified in the unsigned transaction."
  * *Stricter.* Every input's previous transaction, when given, must match its txid, and its output must carry the input's amount and script.
  * `PrevTx.of`, `Error.prevtxMismatch`
  * Takes the amount from the previous transaction, and signs when the witness UTXO contradicts it
*
  * "Before signing a witness input, the Signer must verify that the witnessScript (if provided) matches the hash specified in the UTXO or the redeemScript, and the redeemScript (if provided) matches the hash in the UTXO."
  * *Assumed.* `Env.owns` takes the witness script, and each adapter answers it with the signer's own code. That a sortedmulti P2WSH script binds its quorum is proved; HASH160 for P2SH is not.
  * `checkInput`, `p2wsh_binds`
  * Not checked
*
  * "The Signer may choose to fail to sign a segwit input if a non-witness UTXO is not provided."
  * *Required* when a SegWit v0 input of ours is among two or more inputs, or an input of ours is legacy. Taproot is exempt, as BIP 371 allows.
  * `checkPrev`, `Error.prevtxMissing`
  * Signs SegWit v0 inputs without one
*
  * "The Signer should not need any additional data sources, as all necessary information is provided in the PSBT format."
  * *Differs.* Multisig inputs and change need a wallet registered on the signer beforehand.
  * `Env.wallet`, `Error.wallet`
  * Signs for a multisig nothing registered
*
  * "The Signer must only add data to a PSBT." "Any signatures created by the Signer must be added as a \"Partial Signature\" key-value pair for the respective input it relates to."
  * *Not modelled.* `sign` says which inputs get a signature and with which key, not the PSBT it writes.
  * `sign`
  * Not checked
*
  * "If a Signer cannot sign a transaction, it must not add a Partial Signature."
  * *Stricter.* One error refuses the whole transaction, and signing needs the transaction last reviewed.
  * `Error`, `sign_requires_review`
  * Signs nothing when no input is its own
*
  * "The Signer can additionally compute the addresses and values being sent, and the transaction fee, optionally showing this data to the user as a confirmation of intent and the consequences of signing the PSBT."
  * *Required.* Review always settles the totals and the fee, and the screen shows every output as the transaction has it.
  * `review_fee`, `display_faithful`
  * `decodepsbt` reports the fee, negative when the outputs pay more than the inputs hold
*
  * "Signers do not need to sign for all possible input types."
  * *Followed.* P2WPKH, P2SH-P2WPKH, P2TR key path and P2WSH multisig; P2PKH, P2SH-P2WSH and `or_d` wallets only when the signer says so.
  * `checkInput`, `Error.script`
  * Signs any script its key is in, such as a P2WSH it has no descriptor for
:::

# Data Signers Check For

From [BIP 174, Data Signers Check For][b174-data-signers-check-for].

:::table +header
*
  * BIP 174 says
  * The model
  * Where
  * Bitcoin Core 31.1
*
  * "If a non-witness UTXO is provided, its hash must match the hash specified in the prevout"
  * *Stricter*, as above.
  * `Error.prevtxMismatch`
  * As above
*
  * "If a witness UTXO is provided, no non-witness signature may be created"
  * *Followed*, as Bitcoin Core reads it. A legacy input needs its non-witness UTXO, so with only a witness UTXO it is refused; given both, the non-witness UTXO has to match the amount and script, and decides.
  * `checkPrev`, `Error.prevtxMissing`, `Error.prevtxMismatch`
  * Does not sign a legacy input given only a witness UTXO; signs one given both
*
  * "If a redeemScript is provided, the scriptPubKey must be for that redeemScript"
  * *Assumed*, in `Env.owns`.
  * `checkInput`
  * Not checked
*
  * "If a witnessScript is provided, the scriptPubKey or the redeemScript must be for that witnessScript"
  * *Assumed*, in `Env.owns`, and in `Multisig.inputOk` for a registered wallet.
  * `checkInput`, `Error.wallet`
  * Not checked
*
  * "If a sighash type is provided, the signer must check that the sighash is acceptable. If unacceptable, they must fail."
  * *Followed.* ALL is accepted, and DEFAULT on taproot, on the inputs it signs. Others' inputs may carry any sighash.
  * `checkInput`, `Error.sighash`
  * Refuses a sighash other than the one it is asked for
*
  * "If a sighash type is not provided, the signer should sign using `SIGHASH_ALL`, but may use any sighash type they wish."
  * *Followed* by the reader that builds the model's inputs: ALL, or DEFAULT on taproot.
  * `adapters/psbt.mjs`
  * Not checked
:::

# Change Detection

From [BIP 174, Change Detection][b174-change-detection].

:::table +header
*
  * BIP 174 says
  * The model
  * Where
  * Bitcoin Core 31.1
*
  * "For a single key output, a signer can observe whether the master fingerprint for the public key for that output belongs to itself. If it does, it can then derive the public key at the specified derivation path and check whether that key is the one present in that output."
  * *Stricter.* The path must also be a standard one on our network, and on the account of an input being signed.
  * `outputOwner`, `owner_sound`
  * Names no change
*
  * "Change outputs would then be identified as being the outputs which have the same script policy as the inputs that are being signed."
  * *Differs.* Multisig change has to pay the registered wallet, not a policy built from the global xpubs.
  * `walletClaims`, `p2wsh_binds`
  * Names no change
:::

# Handling Duplicated Keys

From [BIP 174, Handling Duplicated Keys][b174-handling-duplicated-keys].

:::table +header
*
  * BIP 174 says
  * The model
  * Where
  * Bitcoin Core 31.1
*
  * "Keys within each scope should never be duplicated; all keys in the format are unique. PSBTs containing duplicate keys are invalid."
  * *Followed*, and the reason proved: two readers that refuse repeated keys read a PSBT the same way, and with a key twice the first and last value can differ.
  * `readers_agree`, `first_last_differ`
  * Refuses it when parsing
:::

# BIP 371, taproot fields

From [BIP 371, Specification][b371-specification] and [UTXO Types][b371-utxo-types].

:::table +header
*
  * BIP 371 says
  * The model
  * Where
  * Bitcoin Core 31.1
*
  * "Because a Taproot signature will commit to all of the amounts and output scripts spent by the inputs of the transaction, such attacks are prevented as any such lying would result in an invalid signature. Thus Taproot inputs can use just `PSBT_IN_WITNESS_UTXO`."
  * *Followed.* `checkPrev` asks for no previous transaction on account of a taproot input, and the commitment is proved.
  * `checkPrev`, `sig_amounts`
  * Signs taproot inputs without previous transactions
*
  * `PSBT_IN_TAP_BIP32_DERIVATION` and `PSBT_OUT_TAP_BIP32_DERIVATION`
  * *Followed.* They give a taproot input's or output's key path.
  * `Input`, `Output`
  * Not checked
*
  * `PSBT_IN_TAP_LEAF_SCRIPT`, `PSBT_IN_TAP_SCRIPT_SIG` and the other script path fields
  * *Not modelled.* Taproot is signed on the key path only.
  * {ref "limits"}[What this does not prove]
  * Not checked
:::

[b174-signer]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#signer
[b174-data-signers-check-for]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#data-signers-check-for
[b174-change-detection]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#change-detection
[b174-handling-duplicated-keys]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0174.mediawiki#handling-duplicated-keys
[b371-specification]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0371.mediawiki#specification
[b371-utxo-types]: https://github.com/bitcoin/bips/blob/ada341963ab3916e74c98e6de4ba48babc024a75/bip-0371.mediawiki#utxo-types
