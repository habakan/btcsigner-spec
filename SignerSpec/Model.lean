/-!
# A signer's review policy, without the bytes

A transaction as a signer sees it once a PSBT has been read, and what a signer decides about it: which
inputs it signs, what it calls change, the fee, and what it shows. Nothing here is specific to
one signer; an adapter maps a signer's own structures onto these types.

Key derivation and script matching are not modelled. `Env.owns` stands for "re-derive the key from the
seed and check that it produces this script", which each adapter answers with its signer's own code.
-/

namespace SignerSpec

/-- 21 million BTC in satoshis. Every running total is checked against it. -/
def maxMoney : Nat := 2100000000000000

def hardened : Nat := 0x80000000

/-- The highest address index a signer will call its own; anything beyond shows as external. -/
def maxAddressIndex : Nat := 100000

abbrev Script := List UInt8

inductive ScriptKind where
  | p2wpkh | p2shP2wpkh | p2tr | p2wsh | p2pkh | other
  deriving DecidableEq, Repr

def ScriptKind.of : Script → ScriptKind
  | [0x00, 0x14, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => .p2wpkh
  | [0xa9, 0x14, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, 0x87] => .p2shP2wpkh
  | [0x76, 0xa9, 0x14, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, 0x88, 0xac] => .p2pkh
  | s => if s.length = 34 && s[1]? = some 0x20 then
           if s[0]? = some 0x51 then .p2tr else if s[0]? = some 0x00 then .p2wsh else .other
         else .other

/-- A BIP32 origin as the PSBT gives it: the master key's fingerprint and the path from it. -/
structure KeyPath where
  /-- The master key's fingerprint, as a number. -/
  fingerprint : Nat
  /-- Child indices from the master; hardened ones are 2^31 and up. -/
  path : List Nat
  deriving DecidableEq, Repr

/-- What the PSBT's non_witness_utxo says about an input, once compared with its witness_utxo. -/
inductive PrevTx where
  /-- The PSBT carried no non_witness_utxo for this input. -/
  | absent
  /-- It did, and its output at prev_vout has this input's amount and script, and its txid matches. -/
  | matches
  /-- It did, and its txid, or its output's amount or script, disagrees with the input. -/
  | mismatch
  deriving DecidableEq, Repr

/-- A non_witness_utxo once parsed: the txid it hashes to, and its output at the input's prev_vout if it has
one. Hashing is not modelled; equal txids stand for equal transactions, as for `State`. -/
structure PrevInfo where
  /-- The txid the transaction hashes to. -/
  txid : List UInt8
  /-- Its output at the input's prev_vout, amount and script, if it has one. -/
  out : Option (Nat × Script)
  deriving DecidableEq, Repr

/-- The txid binds the previous transaction, not the amount the PSBT states for the input, so the output
at prev_vout has to be compared as well. -/
def PrevTx.of (txid : List UInt8) (amount : Nat) (spk : Script) : Option PrevInfo → PrevTx
  | none => .absent
  | some p => if p.txid = txid ∧ p.out = some (amount, spk) then .matches else .mismatch

/-- An input as review sees it. `amount` and `spk` are what the PSBT states for the output it spends. -/
structure Input where
  /-- The amount, in satoshis, of the output it spends. -/
  amount : Nat
  /-- The script of the output it spends. -/
  spk : Script
  /-- The PSBT's claim that this input is ours; `none` for one not to be signed. -/
  key : Option KeyPath
  /-- `PSBT_IN_SIGHASH_TYPE`: 1 is ALL, 0 is DEFAULT. An absent field is read as ALL, or DEFAULT on taproot. -/
  sighash : Nat
  /-- A P2WSH input's witness script. -/
  wscript : Option Script
  /-- What its non_witness_utxo says, once compared. -/
  prev : PrevTx
  deriving DecidableEq, Repr

/-- An output: its amount and script from the unsigned transaction, and the PSBT's key path for it. -/
structure Output where
  /-- In satoshis. -/
  amount : Nat
  /-- The script it pays. -/
  spk : Script
  /-- The PSBT's claim that this output is ours: a change candidate, never trusted alone. -/
  key : Option KeyPath
  deriving DecidableEq, Repr

/-- A transaction as a signer sees it once its PSBT is read: inputs and outputs, in order. -/
structure Tx where
  /-- In the unsigned transaction's order. -/
  inputs : List Input
  /-- In the unsigned transaction's order. -/
  outputs : List Output
  deriving DecidableEq, Repr

/-- A registered P2WSH multisig wallet. -/
structure Multisig where
  /-- Our key path is in the wallet and the wallet's witness script there is this one. -/
  inputOk : KeyPath → Script → Bool
  /-- The chain (0 receive, 1 change) when the wallet's keys at this path hash to this script. -/
  outputChain : KeyPath → Script → Option Nat
  /-- Our other key in the wallet at this path of ours, when the wallet holds us twice, as an or_d that reuses
  a signer on both paths does. -/
  second : KeyPath → Script → Option KeyPath := fun _ _ => none

/-- What the signer knows apart from the PSBT: its seed, its network, the wallet it has registered, and
which input types it signs. -/
structure Env where
  /-- The coin type in a path: 0 for mainnet, 1 for testnets. -/
  network : Nat
  /-- The seed's master fingerprint. -/
  fingerprint : Nat
  /-- Re-derive the key at this path from the seed: does it produce this script (with this witness script)? -/
  owns : KeyPath → Script → Option Script → Bool
  /-- The multisig wallet registered on the signer, if any. -/
  wallet : Option Multisig
  /-- Whether this signer signs P2PKH inputs. A legacy signature commits to no amount, so it needs every
  input's previous transaction. -/
  legacy : Bool := false
  /-- Whether this signer signs P2SH-P2WSH multisig inputs: a P2SH input with a witness script. -/
  nested : Bool := false
  /-- Whether this signer signs P2WSH inputs whose witness script is an `OrD` wallet's. -/
  orD : Bool := false

/-- Why a transaction is refused. One error refuses all of it. -/
inductive Error where
  /-- Outside what the model reads: no inputs or outputs, more than 16 of either, an amount or a running
  total over 21M BTC, a key path of no steps or more than 8, or a witness script where none belongs. -/
  | format
  /-- An input names our fingerprint, but the key the seed derives at its path does not make its script. -/
  | notOurs
  /-- No input names our fingerprint. -/
  | nothingToSign
  /-- An input of ours asks for a sighash other than ALL, or DEFAULT on taproot. -/
  | sighash
  /-- An input of ours has a script this signer does not sign, or a witness script it does not know. -/
  | script
  /-- A previous transaction is needed for every input and one is missing. See `checkPrev`. -/
  | prevtxMissing
  /-- Some input's previous transaction disagrees with it, whether or not the input is ours. -/
  | prevtxMismatch
  /-- The outputs pay more than the inputs hold. -/
  | fee
  /-- Signing was asked for a transaction that is not the one last reviewed. -/
  | notReviewed
  /-- A multisig input of ours whose witness script is not the registered wallet's. -/
  | wallet
  deriving DecidableEq, Repr

/-- Whose an output is: someone else's, our change (chain 1), or our own receive address (chain 0). -/
inductive Owner where
  /-- Someone else's, or ours where the model cannot confirm it. -/
  | external
  /-- Ours, on chain 1 of an account we sign from, or the registered wallet's change. -/
  | change
  /-- Ours, on chain 0: a receive address of an account we sign from, or of the registered wallet. -/
  | self
  deriving DecidableEq, Repr

/-- What an accepted review settles: both totals, the fee, which inputs are signed, and each output's owner. -/
structure Review where
  /-- The inputs' total, in satoshis. -/
  totalIn : Nat
  /-- The outputs' total, in satoshis. -/
  totalOut : Nat
  /-- `totalIn - totalOut`. -/
  fee : Nat
  /-- Per input, in order: whether it is signed. -/
  willSign : List Bool
  /-- Per output, in order: whose it is. -/
  owners : List Owner
  deriving Repr

/-! ## Review -/

def maxInputs : Nat := 16
def maxOutputs : Nat := 16
def maxDepth : Nat := 8

def keyOk : Option KeyPath → Bool
  | none => true
  | some k => 0 < k.path.length && k.path.length ≤ maxDepth

/-- A P2WSH multisig input, or a P2SH-P2WSH one: a P2SH script with a witness script, which only `formatOk`
lets through for a signer that signs them. -/
def Input.multisig (i : Input) : Bool :=
  ScriptKind.of i.spk == .p2wsh || (ScriptKind.of i.spk == .p2shP2wpkh && i.wscript.isSome)

/-- The limits of what the model reads. A transaction outside them is refused with `Error.format`. -/
def formatOk (nested : Bool) (tx : Tx) : Bool :=
  0 < tx.inputs.length && tx.inputs.length ≤ maxInputs &&
  0 < tx.outputs.length && tx.outputs.length ≤ maxOutputs &&
  tx.inputs.all (fun i => i.amount ≤ maxMoney && keyOk i.key &&
    (i.wscript.isNone || ((ScriptKind.of i.spk == .p2wsh || nested && ScriptKind.of i.spk == .p2shP2wpkh) &&
      i.key.isSome))) &&
  tx.outputs.all (fun o => o.amount ≤ maxMoney && keyOk o.key)

/-- The PSBT names our fingerprint for this input. Whether that is true is `checkInput`'s question. -/
def claimsOurs (env : Env) (i : Input) : Bool :=
  match i.key with
  | some k => k.fingerprint == env.fingerprint
  | none => false

def sighashOk (kind : ScriptKind) (s : Nat) : Bool :=
  if kind = .p2tr then s ≤ 1 else s == 1

/-- How many keys a witness script has when it is OP_m, n distinct compressed keys, OP_n, OP_CHECKMULTISIG
with 1 ≤ m ≤ n; otherwise 0. -/
def multisigKeys (w : Script) : Nat :=
  let n := (w.length - 3) / 34
  let at_ (k : Nat) : Nat := (w.getD k 0).toNat
  let keys := (List.range n).map fun i => (w.drop (2 + 34 * i)).take 33
  if n == 0 || w.length != 3 + 34 * n || at_ 0 < 0x51 || n < at_ 0 - 0x50 || at_ (w.length - 2) != 0x50 + n ||
      at_ (w.length - 1) != 0xae then 0
  else if (List.range n).all (fun i => at_ (1 + 34 * i) == 33 && (at_ (2 + 34 * i) == 2 || at_ (2 + 34 * i) == 3)) &&
      keys.eraseDups.length == n then n
  else 0

/-! ## or_d wallets

`or_d(X,and_v(v:Y,older(n)))`, or `after(n)` for `older(n)`, as Liana writes it: X is `pk` or `multi` of two or
three keys, Y is either of those or `pkh`. `OrD.lean` proves the script binds every field. -/

/-- One spending path: `pk(K)`, `multi(m, keys)`, or `pkh(K)` by its HASH160. -/
inductive Check where
  | pk (key : Script) | multi (m : Nat) (keys : List Script) | pkh (hash : Script)
  deriving DecidableEq, Repr

structure OrD where
  primary : Check
  recovery : Check
  /-- `after(n)`, checked by OP_CHECKLOCKTIMEVERIFY; otherwise `older(n)`, by OP_CHECKSEQUENCEVERIFY. -/
  after : Bool
  lock : Nat
  deriving DecidableEq, Repr

def pushKey (k : Script) : Script := 0x21 :: k

/-- `<K> CHECKSIG`, `m <K>... n CHECKMULTISIG` or `DUP HASH160 <H> EQUALVERIFY CHECKSIG`, or the VERIFY form. -/
def Check.script (verify : Bool) : Check → Script
  | .pk k => pushKey k ++ [if verify then 0xad else 0xac]
  | .multi m ks => UInt8.ofNat (0x50 + m) :: (ks.flatMap pushKey ++ [UInt8.ofNat (0x50 + ks.length), if verify then 0xaf else 0xae])
  | .pkh h => 0x76 :: 0xa9 :: 0x14 :: (h ++ [0x88, if verify then 0xad else 0xac])

def Check.keys : Check → List Script
  | .pk k => [k] | .multi _ ks => ks | .pkh _ => []

def compressedKey (k : Script) : Bool := k.length == 33 && (k.head? == some 2 || k.head? == some 3)

/-- `pkh` only on the recovery path, as Liana writes it. -/
def Check.ok (recovery : Bool) : Check → Bool
  | .pk k => compressedKey k
  | .multi m ks => 2 ≤ ks.length && ks.length ≤ 3 && 1 ≤ m && m ≤ ks.length && ks.all compressedKey
  | .pkh h => recovery && h.length == 20

def leBytes (n : Nat) : List UInt8 := if n = 0 then [] else UInt8.ofNat (n % 256) :: leBytes (n / 256)

def leValue : List UInt8 → Nat
  | [] => 0
  | b :: r => b.toNat + 256 * leValue r

/-- A minimal CScriptNum push of n ≥ 1: OP_n up to 16, else its bytes little-endian with a 0 after them when
the top bit is set, which would make it negative. -/
def scriptNum (n : Nat) : Script :=
  if n ≤ 16 then [UInt8.ofNat (0x50 + n)] else
  let b := leBytes n
  let b := if 0x80 ≤ (b.getLast?.getD 0).toNat then b ++ [0] else b
  UInt8.ofNat b.length :: b

def numOf : Script → Nat
  | [b] => b.toNat - 0x50
  | _ :: r => leValue r
  | [] => 0

def OrD.script (d : OrD) : Script :=
  d.primary.script false ++ (0x73 :: 0x64 :: (d.recovery.script true ++ (scriptNum d.lock ++
    [if d.after then 0xb1 else 0xb2, 0x68])))

/-- Keys distinct, a timelock that is a positive 32-bit script number. -/
def OrD.ok (d : OrD) : Bool :=
  d.primary.ok false && d.recovery.ok true && 1 ≤ d.lock && d.lock < 2 ^ 31 &&
    (d.primary.keys ++ d.recovery.keys).eraseDups.length == (d.primary.keys ++ d.recovery.keys).length

/-- Up to n pushes of 33 bytes. -/
def rdKeys : Nat → Script → List Script × Script
  | n + 1, 0x21 :: r => let (ks, r') := rdKeys n (r.drop 33); (r.take 33 :: ks, r')
  | _, r => ([], r)

/-- Reads one path's fields by its first byte; `orDOf` checks the bytes by writing them back. -/
def rdCheck (verify : Bool) : Script → Option (Check × Script)
  | 0x76 :: r => if verify then some (.pkh ((r.drop 2).take 20), r.drop 24) else none
  | 0x21 :: r => some (.pk (r.take 33), r.drop 34)
  | b :: r => let (ks, r') := rdKeys 3 r; some (.multi (b.toNat - 0x50) ks, r'.drop 2)
  | [] => none

def parseOrD (w : Script) : Option OrD := do
  let (x, r) ← rdCheck false w
  let (y, r) ← rdCheck true (r.drop 2)
  return { primary := x, recovery := y, after := r.getD (r.length - 2) 0 == 0xb1, lock := numOf (r.take (r.length - 2)) }

/-- The or_d wallet a witness script is, when it is exactly one's script. -/
def orDOf (w : Script) : Option OrD :=
  match parseOrD w with
  | some d => if d.ok && d.script == w then some d else none
  | none => none

/-- A witness script this signer knows: a multisig, or an or_d wallet's if it signs those. -/
def wscriptKnown (orD : Bool) (w : Script) : Bool := multisigKeys w != 0 || orD && (orDOf w).isSome

/-- Whether we sign this input, or why the whole transaction is refused. -/
def checkInput (env : Env) (i : Input) : Except Error Bool :=
  match i.key with
  | none => .ok false
  | some k =>
    if k.fingerprint != env.fingerprint then .ok false else
    let kind := ScriptKind.of i.spk
    if kind = .other || (kind = .p2pkh && !env.legacy) || (i.multisig && !(i.wscript.map (wscriptKnown env.orD)).getD false) then
      .error .script
    else if !sighashOk kind i.sighash then .error .sighash
    else if !env.owns k i.spk i.wscript then .error .notOurs
    else match env.wallet, i.multisig, i.wscript with
      | some ms, true, some ws => if ms.inputOk k ws then .ok true else .error .wallet
      | _, _, _ => .ok true

/-- Inputs in order, each adding to the running total before it is checked, so an overflow is reported first. -/
def scanInputs (env : Env) : Nat → List Input → Except Error (Nat × List Bool)
  | t, [] => .ok (t, [])
  | t, i :: rest =>
    if maxMoney < t + i.amount then .error .format else
    match checkInput env i with
    | .error e => .error e
    | .ok s => match scanInputs env (t + i.amount) rest with
      | .error e => .error e
      | .ok (t', ss) => .ok (t', s :: ss)

/-- BIP143 commits only to the amount of the input being signed, and a legacy signature to none, so with two
or more inputs and one of them SegWit v0, or any legacy one, every amount is checked against its transaction. -/
def checkPrev (needed : Bool) : List Input → Except Error Unit
  | [] => .ok ()
  | i :: rest => match i.prev with
    | .mismatch => .error .prevtxMismatch
    | .absent => if needed then .error .prevtxMissing else checkPrev needed rest
    | .matches => checkPrev needed rest

/-- The outputs' total, refused with `Error.format` once a running total passes 21M BTC. -/
def sumOutputs : Nat → List Output → Except Error Nat
  | t, [] => .ok t
  | t, o :: rest => if maxMoney < t + o.amount then .error .format else sumOutputs (t + o.amount) rest

def signed (ins : List Input) (ws : List Bool) : List Input :=
  (ins.zip ws).filterMap fun (i, s) => if s then some i else none

def purposeOf (legacy : Bool) : ScriptKind → Option Nat
  | .p2wpkh => some 84
  | .p2shP2wpkh => some 49
  | .p2tr => some 86
  | .p2pkh => if legacy then some 44 else none
  | _ => none

/-- m/purpose'/coin'/account'/chain/index on our network, with chain 0 or 1. -/
def standardPath (env : Env) (purpose : Nat) (k : KeyPath) : Bool :=
  match k.path with
  | [p, c, a, chain, idx] =>
    p == purpose + hardened && c == env.network + hardened && hardened ≤ a && a < 2 * hardened &&
    chain ≤ 1 && idx < maxAddressIndex
  | _ => false

/-- The input's key path is on the same m/purpose'/coin'/account' as this one. -/
def sameAccount (k : KeyPath) (i : Input) : Bool :=
  match i.key with
  | some ik => ik.path.length == 5 && ik.path.take 3 == k.path.take 3
  | none => false

def chainOwner (chain : Nat) : Owner := if chain == 0 then .self else .change

/-- The registered wallet names this script, at this path of ours, as one of its own. -/
def walletClaims (env : Env) (k : KeyPath) (spk : Script) : Bool :=
  match env.wallet with
  | some ms => (ms.outputChain k spk).isSome
  | none => false

/-- An output is ours only when the re-derived key produces its script, and only on the account of an
input we sign. A P2WSH output, or a P2SH one the registered wallet names as its own, instead needs that
wallet and a multisig input we sign. -/
def outputOwner (env : Env) (signedIns : List Input) (o : Output) : Owner :=
  match o.key with
  | none => .external
  | some k =>
    let kind := ScriptKind.of o.spk
    if kind = .p2wsh ∨ (env.nested = true ∧ kind = .p2shP2wpkh ∧ walletClaims env k o.spk = true) then
      match env.wallet with
      | none => .external
      | some ms => match ms.outputChain k o.spk with
        | none => .external
        | some chain => if signedIns.any Input.multisig then chainOwner chain else .external
    else match purposeOf env.legacy kind with
      | none => .external
      | some p =>
        if !standardPath env p k then .external
        else match signedIns.find? (sameAccount k) with
          | none => .external
          | some _ => if env.owns k o.spk none then chainOwner (k.path.getD 3 0) else .external

/-- Refuse with the first error, in this order, or accept:

1. `formatOk` fails: `format`.
2. Inputs in order (`scanInputs`): a running total over 21M BTC is `format`; otherwise `checkInput`'s error.
3. No input is ours: `nothingToSign`.
4. `checkPrev`, needing every previous transaction when a SegWit v0 input of ours sits among two or more
   inputs, or an input of ours is legacy: `prevtxMismatch` or `prevtxMissing`.
5. The outputs' total over 21M BTC: `format`.
6. Outputs over inputs: `fee`.

Accepted, the fee is inputs minus outputs and each output's owner is `outputOwner`'s. -/
def review (env : Env) (tx : Tx) : Except Error Review :=
  if !formatOk env.nested tx then .error .format else
  match scanInputs env 0 tx.inputs with
  | .error e => .error e
  | .ok (totalIn, ws) =>
    if !ws.any id then .error .nothingToSign else
    let sIns := signed tx.inputs ws
    let hasV0 := sIns.any fun i => ScriptKind.of i.spk != .p2tr
    let hasLegacy := sIns.any fun i => ScriptKind.of i.spk == .p2pkh
    match checkPrev (hasV0 && 1 < tx.inputs.length || hasLegacy) tx.inputs with
    | .error e => .error e
    | .ok () =>
      match sumOutputs 0 tx.outputs with
      | .error e => .error e
      | .ok totalOut =>
        if totalIn < totalOut then .error .fee else
        .ok { totalIn, totalOut, fee := totalIn - totalOut, willSign := ws,
              owners := tx.outputs.map (outputOwner env sIns) }

/-! ## Display and signing -/

/-- Bitcoin Core's `IsUnspendable`: OP_RETURN first, or longer than any script can be. No input can
ever spend such an output. -/
def unspendable (spk : Script) : Bool := spk.head? == some 0x6a || 10000 < spk.length

/-- One output on the screen. -/
structure DisplayOutput where
  /-- In satoshis, as the transaction has it. -/
  amount : Nat
  /-- As review settled it. -/
  owner : Owner
  /-- Rendered from these bytes alone (an address, OP_RETURN data or hex); never text the PSBT supplied. -/
  spk : Script
  /-- A warning that the amount is lost for good: above zero and unspendable. -/
  burned : Bool
  deriving DecidableEq, Repr

/-- Everything the screen shows. -/
structure Display where
  /-- As review settled it. -/
  fee : Nat
  /-- The total of external outputs. -/
  spend : Nat
  /-- Every output, in order. -/
  outputs : List DisplayOutput
  deriving Repr

/-- The screen: the fee, the total sent to others, and each output with its owner, from the transaction's own bytes. -/
def display (tx : Tx) (r : Review) : Display :=
  let outs := (tx.outputs.zip r.owners).map fun (o, w) =>
    { amount := o.amount, owner := w, spk := o.spk, burned := 0 < o.amount && unspendable o.spk }
  { fee := r.fee, outputs := outs,
    spend := (outs.filter (·.owner == .external)).foldr (·.amount + ·) 0 }

/-- The approval a signer holds between review and signing: the exact transaction reviewed. A real signer
holds its hash; equality here assumes SHA-256 is collision resistant. -/
structure State where
  /-- The transaction last reviewed and accepted; `none` when nothing may be signed. -/
  reviewed : Option Tx

/-- Review, keeping the transaction as the approval to sign it when review accepts, and none otherwise. -/
def reviewStep (env : Env) (tx : Tx) : Except Error Review × State :=
  match review env tx with
  | .ok r => (.ok r, ⟨some tx⟩)
  | .error e => (.error e, ⟨none⟩)

/-- The keys an input is signed with: the one the PSBT names, and the registered wallet's second key of ours
when the input's script is that key's too. -/
def signKeys (env : Env) (i : Input) : List KeyPath :=
  if !claimsOurs env i then [] else
  match i.key with
  | none => []
  | some k => k :: match env.wallet, i.multisig, i.wscript with
    | some ms, true, some ws => match ms.second k ws with
      | some k2 => if k2 != k && env.owns k2 i.spk (some ws) then [k2] else []
      | none => []
    | _, _, _ => []

/-- Which inputs signing produces a signature for, by index, and with which key. It checks only the
fingerprint again: the approval it holds is for the transaction review confirmed. -/
def sign (env : Env) (st : State) (tx : Tx) : Except Error (List (Nat × KeyPath)) × State :=
  if st.reviewed = some tx then
    (.ok ((List.range tx.inputs.length).flatMap fun j => ((tx.inputs[j]?.map (signKeys env)).getD []).map (j, ·)),
     ⟨none⟩)
  else (.error .notReviewed, st)

end SignerSpec
