import SignerSpec.Theorems

/-!
# A signature in the transaction it ends up in

A coordinator may collect signatures over several reviews and assemble any transaction they verify in.
What a signature verifies against is what its sighash commits to: BIP143 commits to the amount of its
own input, BIP341 to every input's amount unless ANYONECANPAY, and both to every output under ALL (or
BIP341's DEFAULT). Whatever a coordinator assembles from a reviewed input's signature then pays the fee
that review showed, to the outputs it showed.
-/

namespace SignerSpec

/-- The transaction a coordinator assembles: what the chain holds at each outpoint the reviewed
transaction spends, and the outputs it pays. -/
structure Final where
  amounts : List Nat
  outputs : List (Nat × Script)

def Tx.paid (tx : Tx) : List (Nat × Script) := tx.outputs.map fun o => (o.amount, o.spk)

def Final.fee (f : Final) : Int := ((f.amounts.sum : Nat) : Int) - (((f.outputs.map (·.1)).sum : Nat) : Int)

/-- Whether a signature on input `j` of `tx`, made with that input's sighash, still verifies in `f`. A legacy
signature is taken to commit to no amount at all, the least it could. -/
def SigValid (tx : Tx) (j : Nat) (f : Final) : Prop :=
  ∃ i, tx.inputs[j]? = some i ∧ f.amounts.length = tx.inputs.length ∧
    ((i.sighash = 1 ∨ (ScriptKind.of i.spk = .p2tr ∧ i.sighash = 0)) → f.outputs = tx.paid) ∧
    (if ScriptKind.of i.spk = .p2tr ∧ i.sighash < 0x80 then f.amounts = tx.inputs.map (·.amount)
     else if ScriptKind.of i.spk = .p2pkh then True
     else f.amounts[j]? = some i.amount)

/-- A previous transaction the model calls `matches` holds what the chain holds at that outpoint. Hashing
is not modelled: this is the collision resistance `PrevTx.of` relies on, stated for `f`. -/
def Bound (tx : Tx) (f : Final) : Prop :=
  ∀ (j : Nat) (i : Input), tx.inputs[j]? = some i → i.prev = .matches → f.amounts[j]? = some i.amount

variable {env : Env} {tx : Tx} {r : Review} {f : Final} {j : Nat} {i : Input}

theorem mem_signed {l : List Input} {ss : List Bool} (hi : l[j]? = some i) (hs : ss[j]? = some true) :
    i ∈ signed l ss := by
  induction l generalizing ss j with
  | nil => simp at hi
  | cons a rest ih =>
    cases ss with
    | nil => simp at hs
    | cons s ss' =>
      rw [signed_cons]
      cases j with
      | zero => simp at hi hs; subst hi; subst hs; simp
      | succ j => simp at hi hs; have := ih hi hs; split <;> simp [this]

theorem scanInputs_check {t t' : Nat} {l : List Input} {ss : List Bool} (h : scanInputs env t l = .ok (t', ss))
    (hi : l[j]? = some i) (hs : ss[j]? = some true) : checkInput env i = .ok true := by
  induction l generalizing t t' ss j with
  | nil => simp at hi
  | cons a rest ih =>
    simp only [scanInputs] at h
    by_cases hle : maxMoney < t + a.amount
    · simp [hle] at h
    · cases hb : checkInput env a with
      | error e => simp [hle, hb] at h
      | ok b =>
        cases hr : scanInputs env (t + a.amount) rest with
        | error e => simp [hle, hb, hr] at h
        | ok p =>
          obtain ⟨t'', ss'⟩ := p
          simp [hle, hb, hr] at h
          obtain ⟨rfl, rfl⟩ := h
          cases j with
          | zero => simp at hi hs; subst hi; subst hs; exact hb
          | succ j => simp at hi hs; exact ih hr hi hs

theorem checkInput_sighash (h : checkInput env i = .ok true) : sighashOk (ScriptKind.of i.spk) i.sighash = true := by
  unfold checkInput at h
  cases hk : i.key with
  | none => simp [hk] at h
  | some k =>
    simp only [hk] at h
    by_cases hs : sighashOk (ScriptKind.of i.spk) i.sighash = true
    · exact hs
    · exfalso
      revert h
      simp only [hs]
      repeat' split
      all_goals simp_all

/-- A signed input passed review's checks, so its sighash is ALL, or DEFAULT for a taproot input. -/
theorem signed_sighash (h : review env tx = .ok r) (hi : tx.inputs[j]? = some i) (hs : r.willSign[j]? = some true) :
    i.sighash = 1 ∨ (ScriptKind.of i.spk = .p2tr ∧ i.sighash = 0) := by
  obtain ⟨ss, hscan, rfl, -⟩ := review_ok h
  have := checkInput_sighash (scanInputs_check hscan hi hs)
  unfold sighashOk at this
  split at this <;> simp_all <;> omega

/-! ## 6. Signatures across reviews -/

/-- Wherever a signature from review ends up, the outputs are the ones review showed. -/
theorem sig_outputs (h : review env tx = .ok r) (hi : tx.inputs[j]? = some i) (hs : r.willSign[j]? = some true)
    (hv : SigValid tx j f) : f.outputs = tx.paid := by
  obtain ⟨i', hi', -, ho, -⟩ := hv
  rw [hi] at hi'; cases hi'
  exact ho (signed_sighash h hi hs)

/-- Where every previous transaction matched, a coordinator's amounts are the ones review showed. -/
theorem amounts_of_matches (hb : Bound tx f) (hlen : f.amounts.length = tx.inputs.length)
    (hall : ∀ i ∈ tx.inputs, i.prev = .matches) : f.amounts = tx.inputs.map (·.amount) := by
  apply List.ext_getElem?
  intro k
  cases hk : tx.inputs[k]? with
  | none => simp [hk, List.getElem?_eq_none (by have := List.getElem?_eq_none_iff.mp hk; omega : f.amounts.length ≤ k)]
  | some i' => simp [hk, hb k i' hk (hall i' (List.mem_of_getElem? hk))]

/-- Wherever a signature from review ends up, every input holds the amount review showed: a taproot
signature commits to all of them, and a BIP143 one either is the only input or review checked every
amount against its previous transaction, as it did for any legacy one. -/
theorem sig_amounts (h : review env tx = .ok r) (hb : Bound tx f) (hi : tx.inputs[j]? = some i)
    (hs : r.willSign[j]? = some true) (hv : SigValid tx j f) : f.amounts = tx.inputs.map (·.amount) := by
  obtain ⟨i', hi', hlen, -, ha⟩ := hv
  rw [hi] at hi'; cases hi'
  have hsig := signed_sighash h hi hs
  by_cases ht : ScriptKind.of i.spk = .p2tr
  · have : i.sighash < 0x80 := by omega
    simpa [ht, this] using ha
  · by_cases hl : ScriptKind.of i.spk = .p2pkh
    · exact amounts_of_matches hb hlen ((review_prev h).2 (.inr ⟨i, mem_signed hi hs, hl⟩))
    · simp [ht, hl] at ha
      by_cases hone : tx.inputs.length ≤ 1
      · apply List.ext_getElem?
        intro k
        have hj : j < tx.inputs.length := (List.getElem?_eq_some_iff.mp hi).1
        by_cases hk : k < tx.inputs.length
        · have : k = j := by omega
          subst this; simp [ha, hi]
        · simp [List.getElem?_eq_none (by omega : f.amounts.length ≤ k), List.getElem?_eq_none (by omega : tx.inputs.length ≤ k)]
      · exact amounts_of_matches hb hlen ((review_prev h).2 (.inl ⟨by omega, i, mem_signed hi hs, ht⟩))

/-- So the fee any such transaction pays is the fee review showed. -/
theorem sig_fee (h : review env tx = .ok r) (hb : Bound tx f) (hi : tx.inputs[j]? = some i)
    (hs : r.willSign[j]? = some true) (hv : SigValid tx j f) : f.fee = r.fee := by
  have ha := sig_amounts h hb hi hs hv
  have ho := sig_outputs h hi hs hv
  obtain ⟨h1, h2, -, hle, hfee⟩ := review_fee h
  unfold Final.fee
  rw [ha, ho]
  simp only [Tx.paid, List.map_map]
  have : (List.map ((fun x => x.1) ∘ fun o : Output => (o.amount, o.spk)) tx.outputs) = tx.outputs.map (·.amount) := by
    simp [Function.comp_def]
  rw [this, ← h1, ← h2]
  omega

end SignerSpec
