import SignerSpec.Model

/-!
# What a signer's review guarantees

1. The fee is total in minus total out, and no total exceeds 21M BTC, so none overflows 64 bits.
2. Nothing is signed, and no output is called ours, on the PSBT's word alone.
3. The screen shows every output's amount and script as they are, and accounts for every satoshi.
4. Signing produces signatures only for the transaction reviewed, only for the inputs review accepted,
   each by at most two keys whose script the input's is, and only once.
5. No input amount is one its previous transaction contradicts, and with two or more inputs and one of
   them signed under BIP143, every amount is backed by its previous transaction.
-/

namespace SignerSpec

variable {env : Env} {tx : Tx} {r : Review}

/-! ## Lemmas about the scans -/

theorem checkInput_ok {i : Input} {b : Bool} (h : checkInput env i = .ok b) :
    b = claimsOurs env i ∧ (b = true → ∃ k, i.key = some k ∧ env.owns k i.spk i.wscript = true) := by
  unfold checkInput at h
  unfold claimsOurs
  cases hk : i.key with
  | none => simp [hk] at h; simp [h]
  | some k =>
    simp only [hk] at h
    by_cases hf : k.fingerprint = env.fingerprint
    · cases ho : env.owns k i.spk i.wscript
      · simp [hf, ho] at h
        repeat' split at h
        all_goals simp at h
      · simp [hf, ho] at h ⊢
        repeat' split at h
        all_goals simp_all
    · simp [hf] at h; simp [h, hf]

theorem signed_cons (i : Input) (s : Bool) (l : List Input) (ss : List Bool) :
    signed (i :: l) (s :: ss) = if s then i :: signed l ss else signed l ss := by
  cases s <;> simp [signed]

theorem scanInputs_ok {t t' : Nat} {l : List Input} {ss : List Bool} (h : scanInputs env t l = .ok (t', ss)) :
    t' = t + (l.map (·.amount)).sum ∧ (l ≠ [] → t' ≤ maxMoney) ∧ ss = l.map (claimsOurs env) ∧
    ∀ i ∈ signed l ss, ∃ k, i.key = some k ∧ env.owns k i.spk i.wscript = true := by
  induction l generalizing t t' ss with
  | nil => simp [scanInputs] at h; simp [← h.1, ← h.2, signed]
  | cons i rest ih =>
    simp only [scanInputs] at h
    by_cases hle : maxMoney < t + i.amount
    · simp [hle] at h
    · cases hb : checkInput env i with
      | error e => simp [hle, hb] at h
      | ok b =>
        cases hr : scanInputs env (t + i.amount) rest with
        | error e => simp [hle, hb, hr] at h
        | ok p =>
          obtain ⟨t'', ss'⟩ := p
          simp [hle, hb, hr] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2, h3, h4⟩ := ih hr
          obtain ⟨hb1, hb2⟩ := checkInput_ok hb
          refine ⟨by simp [h1]; omega, fun _ => ?_, by simp [h3, hb1], ?_⟩
          · by_cases hrest : rest = []
            · subst hrest; simp at h1; omega
            · exact h2 hrest
          · intro j hj
            rw [signed_cons] at hj
            cases hs : b
            · simp [hs] at hj; exact h4 j hj
            · simp [hs] at hj
              rcases hj with rfl | hj
              · exact hb2 hs
              · exact h4 j hj

theorem sumOutputs_ok {t t' : Nat} {l : List Output} (h : sumOutputs t l = .ok t') (ht : t ≤ maxMoney) :
    t' = t + (l.map (·.amount)).sum ∧ t' ≤ maxMoney := by
  induction l generalizing t with
  | nil => simp [sumOutputs] at h; subst h; simpa using ht
  | cons o rest ih =>
    simp only [sumOutputs] at h
    split at h
    · simp at h
    · obtain ⟨h1, h2⟩ := ih h (by omega)
      simp [h1]; omega

/-- Everything a successful review is made of. -/
theorem review_ok (h : review env tx = .ok r) :
    ∃ ss, scanInputs env 0 tx.inputs = .ok (r.totalIn, ss) ∧ r.willSign = ss ∧ tx.inputs ≠ [] ∧
      sumOutputs 0 tx.outputs = .ok r.totalOut ∧ r.totalOut ≤ r.totalIn ∧ r.fee = r.totalIn - r.totalOut ∧
      r.owners = tx.outputs.map (outputOwner env (signed tx.inputs ss)) := by
  unfold review at h
  cases hf : formatOk env.nested tx
  · simp [hf] at h
  cases hs : scanInputs env 0 tx.inputs with
  | error e => simp [hf, hs] at h
  | ok p =>
    obtain ⟨totalIn, ss⟩ := p
    cases ha : ss.any id
    · simp [hf, hs, ha] at h
    simp [hf, hs, ha] at h
    split at h
    · simp at h
    · 
      cases ho : sumOutputs 0 tx.outputs with
      | error e => simp [ho] at h
      | ok totalOut =>
        by_cases hlt : totalIn < totalOut
        · simp [ho, hlt] at h
        · simp [ho, hlt] at h
          subst h
          have hne : tx.inputs ≠ [] := by
            intro he; simp [formatOk, he] at hf
          exact ⟨ss, rfl, rfl, hne, rfl, by simp; omega, rfl, rfl⟩
/-! ## 1. The fee -/

/-- An accepted review's totals are the sums of the amounts, within 21M BTC, and the fee is their difference. -/
theorem review_fee (h : review env tx = .ok r) :
    r.totalIn = (tx.inputs.map (·.amount)).sum ∧ r.totalOut = (tx.outputs.map (·.amount)).sum ∧
      r.totalIn ≤ maxMoney ∧ r.totalOut ≤ r.totalIn ∧ r.fee + r.totalOut = r.totalIn := by
  obtain ⟨ss, hs, -, hne, ho, hle, hfee, -⟩ := review_ok h
  obtain ⟨h1, h2, -⟩ := scanInputs_ok hs
  obtain ⟨h3, -⟩ := sumOutputs_ok ho (by decide)
  refine ⟨by simpa using h1, by simpa using h3, h2 hne, hle, by omega⟩

/-- Two totals of at most 21M BTC fit in a uint64 with room to spare, so running sums in a uint64 cannot wrap. -/
theorem totals_fit_u64 : maxMoney + maxMoney < 2 ^ 64 := by decide

/-- An amount of at most 21M BTC reads the same as a signed or an unsigned 64-bit integer, so whichever a
signer's parser uses, every amount the model accepts means the same. -/
theorem amounts_fit_i64 : maxMoney < 2 ^ 63 := by decide

/-- Every amount the model reads fits a signed 64-bit integer. -/
theorem formatOk_amounts {n : Bool} (h : formatOk n tx = true) :
    (∀ i ∈ tx.inputs, i.amount < 2 ^ 63) ∧ ∀ o ∈ tx.outputs, o.amount < 2 ^ 63 := by
  simp only [formatOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have := amounts_fit_i64
  exact ⟨fun i hi => by have := (h.1.2 i hi).1.1; omega, fun o ho => by have := (h.2 o ho).1; omega⟩

/-! ## 2. Nothing on the PSBT's word alone -/

/-- An input is signed only when the PSBT names our fingerprint and the key re-derived from the seed
produces its script. -/
theorem signed_sound (h : review env tx = .ok r) :
    ∀ i ∈ signed tx.inputs r.willSign, ∃ k, i.key = some k ∧ env.owns k i.spk i.wscript = true := by
  obtain ⟨ss, hs, rfl, -⟩ := review_ok h
  exact (scanInputs_ok hs).2.2.2

theorem outputOwner_sound {sIns : List Input} {o : Output} (hne : outputOwner env sIns o ≠ .external) :
    ∃ k, o.key = some k ∧
      ((ScriptKind.of o.spk ≠ .p2wsh ∧ env.owns k o.spk none = true ∧
          (∃ p, purposeOf env.legacy (ScriptKind.of o.spk) = some p ∧ standardPath env p k = true) ∧
          ∃ i ∈ sIns, sameAccount k i = true) ∨
       ((ScriptKind.of o.spk = .p2wsh ∨ (env.nested = true ∧ ScriptKind.of o.spk = .p2shP2wpkh)) ∧
          ∃ ms c, env.wallet = some ms ∧ ms.outputChain k o.spk = some c ∧ ∃ i ∈ sIns, i.multisig = true)) := by
  unfold outputOwner at hne
  cases hk : o.key with
  | none => simp [hk] at hne
  | some k =>
    simp only [hk] at hne
    refine ⟨k, rfl, ?_⟩
    by_cases hc : ScriptKind.of o.spk = .p2wsh ∨
        (env.nested = true ∧ ScriptKind.of o.spk = .p2shP2wpkh ∧ walletClaims env k o.spk = true)
    · rw [if_pos hc] at hne
      right
      cases hms : env.wallet with
      | none => simp [hms] at hne
      | some ms =>
        cases hc' : ms.outputChain k o.spk with
        | none => simp [hms, hc'] at hne
        | some c =>
          cases hany : sIns.any Input.multisig
          · simp [hms, hc', hany] at hne
          · obtain ⟨i, hi, hm⟩ := List.any_eq_true.mp hany
            refine ⟨?_, ms, c, rfl, hc', i, hi, hm⟩
            rcases hc with h | ⟨h1, h2, -⟩
            · exact .inl h
            · exact .inr ⟨h1, h2⟩
    · rw [if_neg hc] at hne
      have hw : ScriptKind.of o.spk ≠ .p2wsh := fun h => hc (.inl h)
      left
      cases hp : purposeOf env.legacy (ScriptKind.of o.spk) with
      | none => simp [hp] at hne
      | some p =>
        cases hstd : standardPath env p k
        · simp [hp, hstd] at hne
        · cases hf : sIns.find? (sameAccount k) with
          | none => simp [hp, hstd, hf] at hne
          | some i =>
            cases hown : env.owns k o.spk none
            · simp [hp, hstd, hf, hown] at hne
            · exact ⟨hw, rfl, ⟨p, rfl, hstd⟩, i, List.mem_of_find?_eq_some hf, List.find?_some hf⟩

theorem mem_zip_map {α β} {f : α → β} {l : List α} {a : α} {b : β} (h : (a, b) ∈ l.zip (l.map f)) :
    a ∈ l ∧ b = f a := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

/-- An output is called ours only when the key re-derived from the seed produces its script (or, for
P2WSH, the registered wallet's keys do) and it belongs with an input we sign. -/
theorem owner_sound {o : Output} {w : Owner} (h : review env tx = .ok r) (hw : (o, w) ∈ tx.outputs.zip r.owners)
    (hne : w ≠ .external) :
    ∃ k, o.key = some k ∧
      ((ScriptKind.of o.spk ≠ .p2wsh ∧ env.owns k o.spk none = true ∧
          (∃ p, purposeOf env.legacy (ScriptKind.of o.spk) = some p ∧ standardPath env p k = true) ∧
          ∃ i ∈ signed tx.inputs r.willSign, sameAccount k i = true) ∨
       ((ScriptKind.of o.spk = .p2wsh ∨ (env.nested = true ∧ ScriptKind.of o.spk = .p2shP2wpkh)) ∧
          ∃ ms c, env.wallet = some ms ∧ ms.outputChain k o.spk = some c ∧
          ∃ i ∈ signed tx.inputs r.willSign, i.multisig = true)) := by
  obtain ⟨ss, -, hws, -, -, -, -, ho⟩ := review_ok h
  rw [ho] at hw
  obtain ⟨-, rfl⟩ := mem_zip_map hw
  rw [hws]
  exact outputOwner_sound hne

/-! ## 3. The screen -/

def sumAmounts (l : List DisplayOutput) : Nat := l.foldr (·.amount + ·) 0

theorem sumAmounts_filter (l : List DisplayOutput) (p : DisplayOutput → Bool) :
    sumAmounts (l.filter p) + sumAmounts (l.filter (fun d => !p d)) = sumAmounts l := by
  induction l with
  | nil => rfl
  | cons d ds ih => cases hp : p d <;> simp [sumAmounts, hp] at ih ⊢ <;> omega

theorem sumAmounts_eq (l : List DisplayOutput) : sumAmounts l = (l.map (·.amount)).sum := by
  induction l with
  | nil => rfl
  | cons d ds ih => simp [sumAmounts, List.foldr_cons] at ih ⊢; omega

/-- The screen shows every output's amount and script as the transaction has them, the owner review settled,
and review's fee. -/
theorem display_faithful (h : review env tx = .ok r) :
    (display tx r).outputs.map (fun d => (d.amount, d.spk)) = tx.outputs.map (fun o => (o.amount, o.spk)) ∧
      (display tx r).outputs.map (·.owner) = r.owners ∧ (display tx r).fee = r.fee := by
  obtain ⟨ss, -, -, -, -, -, -, ho⟩ := review_ok h
  refine ⟨?_, ?_, rfl⟩ <;> simp only [display, List.map_map, ho] <;>
    (generalize tx.outputs = l; induction l <;> simp_all)

/-- What leaves the wallet is exactly what the screen says: the external outputs plus the fee, with
the outputs shown as ours making up the rest of what goes in. -/
theorem display_accounts (h : review env tx = .ok r) :
    (display tx r).spend + (display tx r).fee +
        sumAmounts ((display tx r).outputs.filter fun d => !(d.owner == .external)) = r.totalIn := by
  obtain ⟨h1, -, h3⟩ := display_faithful h
  obtain ⟨-, hout, -, -, hfee⟩ := review_fee h
  have hsum := sumAmounts_filter (display tx r).outputs (fun d => d.owner == .external)
  have hamt : (display tx r).outputs.map (·.amount) = tx.outputs.map (·.amount) := by
    simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) h1
  have htot : sumAmounts (display tx r).outputs = r.totalOut := by rw [sumAmounts_eq, hamt, hout]
  have hspend : (display tx r).spend = sumAmounts ((display tx r).outputs.filter (·.owner == .external)) := rfl
  rw [hspend, h3]
  omega

theorem unspendable_other {s : Script} (h : unspendable s = true) : ScriptKind.of s = .other := by
  simp only [unspendable, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  unfold ScriptKind.of
  split
  · simp_all
  · simp_all
  · simp_all
  · rcases h with h | h <;> cases s <;> simp_all
    all_goals (intro a; omega)

/-- An output nobody can spend is never shown as ours. -/
theorem unspendable_external (env : Env) (ins : List Input) {o : Output} (h : unspendable o.spk = true) :
    outputOwner env ins o = .external := by
  unfold outputOwner
  split
  · rfl
  · simp [unspendable_other h, purposeOf]

theorem sumAmounts_filter_le (l : List DisplayOutput) {p q : DisplayOutput → Bool} (h : ∀ d ∈ l, p d → q d) :
    sumAmounts (l.filter p) ≤ sumAmounts (l.filter q) := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons d ds ih =>
    have ih := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases hp : p d <;> cases hq : q d <;> simp [sumAmounts, hp, hq] at ih ⊢ <;>
      first | omega | exact absurd (h d List.mem_cons_self hp) (by simp [hq])

/-- An output is flagged burned exactly when it pays more than zero to a script nobody can spend, and
what is burned is counted in what the screen says leaves the wallet. -/
theorem display_burned (h : review env tx = .ok r) :
    (display tx r).outputs.map (·.burned) = tx.outputs.map (fun o => 0 < o.amount && unspendable o.spk) ∧
      sumAmounts ((display tx r).outputs.filter (·.burned)) ≤ (display tx r).spend := by
  obtain ⟨ss, -, -, -, -, -, -, ho⟩ := review_ok h
  have pairs : (display tx r).outputs.map (fun d => (d.burned, d.owner)) =
      tx.outputs.map (fun o => (0 < o.amount && unspendable o.spk, outputOwner env (signed tx.inputs ss) o)) := by
    simp only [display, List.map_map, ho]
    generalize tx.outputs = l; induction l <;> simp_all
  refine ⟨by simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) pairs, ?_⟩
  refine sumAmounts_filter_le _ fun d hd hb => ?_
  have hm : (d.burned, d.owner) ∈ (display tx r).outputs.map (fun d => (d.burned, d.owner)) := List.mem_map_of_mem hd
  rw [pairs, List.mem_map] at hm
  obtain ⟨o, -, e⟩ := hm
  simp only [Prod.mk.injEq] at e
  rw [hb] at e
  have hu : unspendable o.spk = true := by simp_all
  simp [← e.2, unspendable_external _ _ hu]

/-! ## 4. Signing -/

/-- Signing produces signatures only for the transaction last reviewed. -/
theorem sign_requires_review {st : State} {js : List (Nat × KeyPath)} (h : (sign env st tx).1 = .ok js) :
    st.reviewed = some tx := by
  unfold sign at h
  split at h
  · assumption
  · simp at h

/-- Signing uses up the approval: afterwards none is held, unless signing was refused. -/
theorem sign_consumes (st : State) : (sign env st tx).1 = .error .notReviewed ∨ (sign env st tx).2.reviewed = none := by
  unfold sign
  split <;> simp

/-- A review of one transaction never authorises signing another. -/
theorem sign_other {tx' : Tx} (hne : tx' ≠ tx) : (sign env (reviewStep env tx).2 tx').1 = .error .notReviewed := by
  unfold sign reviewStep
  split <;> split <;> simp_all

theorem signed_map (l : List Input) : signed l (l.map (claimsOurs env)) = l.filter (claimsOurs env) := by
  induction l with
  | nil => rfl
  | cons i rest ih => rw [List.map_cons, signed_cons, ih]; cases h : claimsOurs env i <;> simp [h]

theorem signKeys_cases {i : Input} {k : KeyPath} (hk : k ∈ signKeys env i) :
    claimsOurs env i = true ∧ (i.key = some k ∨ ∃ ws, i.wscript = some ws ∧ env.owns k i.spk (some ws) = true) := by
  unfold signKeys at hk
  cases hc : claimsOurs env i
  · simp [hc] at hk
  refine ⟨rfl, ?_⟩
  simp only [hc, Bool.not_true] at hk
  cases hkey : i.key with
  | none => simp [hkey] at hk
  | some k1 =>
    simp only [hkey, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact Or.inl rfl
    right
    cases hw : env.wallet <;> cases hm : i.multisig <;> cases hws : i.wscript <;> simp [hw, hm, hws] at hk
    rename_i ms ws
    cases h2 : ms.second k1 ws <;> simp [h2] at hk
    exact ⟨ws, rfl, by simp_all⟩

/-- An input is signed with at most two keys, never one twice. -/
theorem signKeys_two (i : Input) : (signKeys env i).length ≤ 2 ∧ (signKeys env i).Nodup := by
  unfold signKeys
  repeat' split
  all_goals simp only [List.length_cons, List.length_nil, List.nodup_cons, List.nodup_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  all_goals first
    | (simp; done)
    | rename_i h; simp only [Bool.and_eq_true, bne_iff_ne] at h; exact ⟨by omega, fun e => h.1 e.symm, by simp⟩

theorem sign_reviewed_eq (h : review env tx = .ok r) :
    (sign env ⟨some tx⟩ tx).1 = .ok ((List.range tx.inputs.length).flatMap fun j =>
      ((tx.inputs[j]?.map (signKeys env)).getD []).map (j, ·)) ∧ r.willSign = tx.inputs.map (claimsOurs env) ∧
    ∀ i ∈ tx.inputs.filter (claimsOurs env), ∃ k, i.key = some k ∧ env.owns k i.spk i.wscript = true := by
  obtain ⟨ss, hsc, hw, -⟩ := review_ok h
  obtain ⟨-, -, hss, hown⟩ := scanInputs_ok hsc
  rw [hss, signed_map] at hown
  exact ⟨by simp [sign], hw.trans hss, hown⟩

/-- Signatures come only for the inputs review accepted, each by a key whose script the input's is: the key
the PSBT names, or the wallet's second key of ours. -/
theorem sign_only_reviewed (h : review env tx = .ok r) {sigs : List (Nat × KeyPath)}
    (hs : (sign env ⟨some tx⟩ tx).1 = .ok sigs) {j : Nat} {k : KeyPath} (hm : (j, k) ∈ sigs) :
    r.willSign.getD j false = true ∧ ∃ i, tx.inputs[j]? = some i ∧ env.owns k i.spk i.wscript = true := by
  obtain ⟨he, hw, hown⟩ := sign_reviewed_eq h
  rw [he, Except.ok.injEq] at hs
  subst hs
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq] at hm
  obtain ⟨j', hj, k', hk, rfl, rfl⟩ := hm
  rw [List.getElem?_eq_getElem hj] at hk
  obtain ⟨hc, hk⟩ := signKeys_cases (by simpa using hk)
  refine ⟨by simp [hw, List.getD_eq_getElem?_getD, hj, hc], _, List.getElem?_eq_getElem hj, ?_⟩
  rcases hk with hk | ⟨ws, hws, ho⟩
  · obtain ⟨k'', hk'', ho⟩ := hown _ (List.mem_filter.mpr ⟨List.getElem_mem hj, hc⟩)
    rw [hk, Option.some.injEq] at hk''
    exact hk'' ▸ ho
  · rw [hws]; exact ho

/-- Every input review accepted is signed, by the key the PSBT names. -/
theorem sign_all_reviewed (h : review env tx = .ok r) {sigs : List (Nat × KeyPath)}
    (hs : (sign env ⟨some tx⟩ tx).1 = .ok sigs) {j : Nat} (hwj : r.willSign.getD j false = true) :
    ∃ i k, tx.inputs[j]? = some i ∧ i.key = some k ∧ (j, k) ∈ sigs := by
  obtain ⟨he, hw, -⟩ := sign_reviewed_eq h
  rw [he, Except.ok.injEq] at hs
  subst hs
  rw [hw, List.getD_eq_getElem?_getD] at hwj
  have hj : j < tx.inputs.length := Nat.lt_of_not_le fun hn => by simp [List.getElem?_eq_none hn] at hwj
  have hc : claimsOurs env tx.inputs[j] = true := by simpa [hj] using hwj
  obtain ⟨k, hk⟩ : ∃ k, tx.inputs[j].key = some k := by
    unfold claimsOurs at hc; split at hc <;> simp_all
  refine ⟨_, k, List.getElem?_eq_getElem hj, hk, ?_⟩
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  refine ⟨j, hj, k, ?_, rfl, rfl⟩
  simp [List.getElem?_eq_getElem hj, signKeys, hc, hk]

/-! ## 5. Input amounts

BIP143 commits only to the amount of the input being signed, so an understated amount would otherwise
let a coordinator collect signatures over two sessions for a fee the screen never showed. -/

theorem checkPrev_ok {needed : Bool} {l : List Input} (h : checkPrev needed l = .ok ()) :
    ∀ i ∈ l, i.prev ≠ .mismatch ∧ (needed = true → i.prev = .matches) := by
  induction l with
  | nil => simp
  | cons i rest ih =>
    intro j hj
    cases hp : i.prev <;> cases needed <;> simp [checkPrev, hp] at h
    all_goals
      rcases List.mem_cons.mp hj with rfl | hj
      · simp [hp]
      · exact ih h j hj

/-- `matches` means the previous transaction is the one the input spends and its output there has the
input's amount and script. -/
theorem prev_matches {txid : List UInt8} {a : Nat} {s : Script} {p : Option PrevInfo}
    (h : PrevTx.of txid a s p = .matches) : ∃ q, p = some q ∧ q.txid = txid ∧ q.out = some (a, s) := by
  cases p with
  | none => simp [PrevTx.of] at h
  | some q =>
    simp only [PrevTx.of] at h
    split at h
    · exact ⟨q, rfl, by assumption⟩
    · simp at h

/-- The right txid with an amount it does not carry is a mismatch: the txid alone is not enough. -/
example : PrevTx.of [1] 90000 [] (some ⟨[1], some (100000, [])⟩) = .mismatch := by decide

/-- An input amount is never one its previous transaction contradicts. Once two or more inputs include one
signed under BIP143, or any input is signed as legacy, every amount has its previous transaction behind it. -/
theorem review_prev (h : review env tx = .ok r) :
    (∀ i ∈ tx.inputs, i.prev ≠ .mismatch) ∧
    ((1 < tx.inputs.length ∧ ∃ i ∈ signed tx.inputs r.willSign, ScriptKind.of i.spk ≠ .p2tr) ∨
      (∃ i ∈ signed tx.inputs r.willSign, ScriptKind.of i.spk = .p2pkh) → ∀ i ∈ tx.inputs, i.prev = .matches) := by
  have hr := h
  unfold review at h
  cases hf : formatOk env.nested tx
  · simp [hf] at h
  cases hs : scanInputs env 0 tx.inputs with
  | error e => simp [hf, hs] at h
  | ok p =>
    obtain ⟨totalIn, ss⟩ := p
    obtain ⟨ss', hs', hws, -⟩ := review_ok hr
    rw [hs] at hs'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hs')
    cases ha : ss.any id
    · simp [hf, hs, ha] at h
    simp [hf, hs, ha] at h
    split at h
    · simp at h
    · rename_i hc
      have := checkPrev_ok hc
      refine ⟨fun i hi => (this i hi).1, fun hc i hi => (this i hi).2 ?_⟩
      rw [hws] at hc
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq]
      rcases hc with ⟨hlen, j, hj, hk⟩ | ⟨j, hj, hk⟩
      · exact .inl ⟨⟨j, hj, hk⟩, hlen⟩
      · exact .inr ⟨j, hj, hk⟩
end SignerSpec
