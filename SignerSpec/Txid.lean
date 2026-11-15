import SignerSpec.Sighash

/-!
# What a txid binds

`Sessions.lean` takes as given that a previous transaction the model calls `matches` holds what the
chain holds at that outpoint (`Bound`). This file derives it: a txid is the double SHA-256 of the
transaction without witnesses, that serialization is one to one, so under `HashOk` two transactions with
one txid are the same transaction and pay the same amount at every output.
-/

namespace SignerSpec

structure RawIn where
  /-- txid and vout, 36 bytes. -/
  outpoint : List UInt8
  scriptSig : Script
  sequence : Nat

structure RawTx where
  version : Nat
  inputs : List RawIn
  outputs : List (Nat × Script)
  locktime : Nat

def serIn (x : RawIn) : List UInt8 := x.outpoint ++ varstr x.scriptSig ++ le 4 x.sequence

/-- The serialization a txid hashes: no marker, flag or witnesses. -/
def serTx (t : RawTx) : List UInt8 :=
  le 4 t.version ++ varint t.inputs.length ++ t.inputs.flatMap serIn ++
    varint t.outputs.length ++ t.outputs.flatMap serOut ++ le 4 t.locktime

def txid (H : List UInt8 → List UInt8) (t : RawTx) : List UInt8 := H (H (serTx t))

def RawIn.Ok (x : RawIn) : Prop := x.outpoint.length = 36 ∧ x.scriptSig.length < 2 ^ 64 ∧ x.sequence < 2 ^ 32

def RawTx.Ok (t : RawTx) : Prop :=
  t.version < 2 ^ 32 ∧ t.locktime < 2 ^ 32 ∧ t.inputs.length < 2 ^ 64 ∧ t.outputs.length < 2 ^ 64 ∧
    (∀ x ∈ t.inputs, x.Ok) ∧ ∀ o ∈ t.outputs, OutOk o

theorem serIn_prefix : PrefixFree RawIn.Ok serIn := by
  intro a b r s ha hb h
  simp only [serIn, List.append_assoc] at h
  obtain ⟨h1, h⟩ := fixed_prefix 36 _ _ _ _ ha.1 hb.1 h
  obtain ⟨h2, h⟩ := varstr_prefix _ _ _ _ ha.2.1 hb.2.1 h
  obtain ⟨h3, h⟩ := le_prefix 4 _ _ _ _ (by have := ha.2.2; omega) (by have := hb.2.2; omega) h
  cases a; cases b; simp_all

/-- As many codewords on each side, then anything: the codewords and the rest both match. -/
theorem flatMap_prefix {α} {P : α → Prop} {f : α → List UInt8} (hf : PrefixFree P f) :
    ∀ {l m : List α} {r s : List UInt8}, l.length = m.length → (∀ a ∈ l, P a) → (∀ b ∈ m, P b) →
      l.flatMap f ++ r = m.flatMap f ++ s → l = m ∧ r = s
  | [], [], _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl
  | a :: l, b :: m, r, s, hl, ha, hb, h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨rfl, h'⟩ := hf _ _ _ _ (ha a (by simp)) (hb b (by simp)) h
    obtain ⟨rfl, rfl⟩ := flatMap_prefix hf (by simpa using hl) (fun x hx => ha x (by simp [hx]))
      (fun x hx => hb x (by simp [hx])) h'
    exact ⟨rfl, rfl⟩

theorem serTx_inj {t t' : RawTx} (ht : t.Ok) (ht' : t'.Ok) (h : serTx t = serTx t') : t = t' := by
  obtain ⟨v, lk, ni, no, hi, ho⟩ := ht
  obtain ⟨v', lk', ni', no', hi', ho'⟩ := ht'
  have h4 : (2 : Nat) ^ 32 = 256 ^ 4 := by decide
  simp only [serTx, List.append_assoc] at h
  obtain ⟨e1, h⟩ := le_prefix 4 _ _ _ _ (by omega) (by omega) h
  obtain ⟨e2, h⟩ := varint_prefix _ _ _ _ ni ni' h
  obtain ⟨e3, h⟩ := flatMap_prefix serIn_prefix e2 hi hi' h
  obtain ⟨e4, h⟩ := varint_prefix _ _ _ _ no no' h
  obtain ⟨e5, h⟩ := flatMap_prefix serOut_prefix e4 ho ho' h
  have e6 := le_inj (by omega) (by omega) h
  cases t; cases t'; simp_all

variable {H : List UInt8 → List UInt8}

/-- One txid, one transaction. -/
theorem txid_binds (hH : HashOk H) {t t' : RawTx} (ht : t.Ok) (ht' : t'.Ok) (h : txid H t = txid H t') :
    t = t' :=
  serTx_inj ht ht' (hH.inj _ _ (hH.inj _ _ h))

/-- What `PrevTx.matches` stands for, for every input of `tx`: the PSBT's previous transaction `pt` has
the input's amount and script at prev_vout, and has the txid the input spends, which is that of `ct`,
the transaction the chain holds there and whose output `f` spends. -/
def Spends (H : List UInt8 → List UInt8) (tx : Tx) (f : Final) : Prop :=
  ∀ (j : Nat) (i : Input), tx.inputs[j]? = some i → i.prev = .matches →
    ∃ (pt ct : RawTx) (v : Nat), pt.Ok ∧ ct.Ok ∧ txid H pt = txid H ct ∧
      pt.outputs[v]? = some (i.amount, i.spk) ∧ f.amounts[j]? = (ct.outputs[v]?).map (·.1)

/-- `Bound`, from collision resistance alone. -/
theorem bound_of_spends (hH : HashOk H) {tx : Tx} {f : Final} (h : Spends H tx f) : Bound tx f := by
  intro j i hi hm
  obtain ⟨pt, ct, v, hp, hc, e, hv, ha⟩ := h j i hi hm
  rw [ha, ← txid_binds hH hp hc e, hv]
  rfl

end SignerSpec
