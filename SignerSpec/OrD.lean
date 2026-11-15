import SignerSpec.Multisig

/-!
# What an or_d wallet's script binds

`Model.lean` reads an or_d witness script loosely (`parseOrD`) and accepts it only if writing the result back
gives the same bytes (`orDOf`). This file proves the reading is right for every well-formed wallet
(`orDOf_script`), so the script binds both paths' keys, the threshold, the kind of timelock and its value
(`orD_script_inj`), and so does its P2WSH output (`p2wsh_orD_binds`).
-/

namespace SignerSpec

theorem leValue_leBytes (n : Nat) : leValue (leBytes n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold leBytes
    split
    · simp [leValue, *]
    · simp only [leValue]
      rw [ih (n / 256) (by omega)]
      simp; omega

theorem leValue_append_zero (b : List UInt8) : leValue (b ++ [0]) = leValue b := by
  induction b with
  | nil => rfl
  | cons x r ih => simp [leValue, ih]

theorem leBytes_ne_nil {n : Nat} (h : n ≠ 0) : leBytes n ≠ [] := by
  unfold leBytes; simp [h]

theorem toNat_ofNat_small {a : Nat} (h : a < 256) : (UInt8.ofNat a).toNat = a := by
  simp [Nat.mod_eq_of_lt h]

theorem ofNat_ne {a : Nat} {b : UInt8} (ha : a < 256) (h : a ≠ b.toNat) : UInt8.ofNat a ≠ b :=
  fun e => h (by rw [← e, toNat_ofNat_small ha])

theorem numOf_scriptNum {n : Nat} (h1 : 1 ≤ n) (h2 : n < 2 ^ 31) : numOf (scriptNum n) = n := by
  unfold scriptNum
  split
  · rename_i h; simp only [numOf, toNat_ofNat_small (show 0x50 + n < 256 by omega)]; omega
  · dsimp only
    have hb := leBytes_ne_nil (show n ≠ 0 by omega)
    obtain ⟨x, r, e⟩ := List.exists_cons_of_ne_nil hb
    split
    · rw [e, List.cons_append]; simp only [numOf]
      rw [← List.cons_append, ← e, leValue_append_zero, leValue_leBytes]
    · rw [e]; simp only [numOf]; rw [← e, leValue_leBytes]

theorem rdKeys_flatMap {ks : List Script} {n : Nat} (hl : ∀ k ∈ ks, k.length = 33) (hn : ks.length ≤ n)
    {b : UInt8} {rest : Script} (hr : b ≠ 0x21) : rdKeys n (ks.flatMap pushKey ++ b :: rest) = (ks, b :: rest) := by
  induction ks generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ n => simp only [List.flatMap_nil, List.nil_append]; unfold rdKeys; split <;> simp_all
  | cons k ks ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    have hk := hl k (by simp)
    simp only [List.flatMap_cons, pushKey, List.cons_append, List.append_assoc]
    unfold rdKeys
    simp only [List.drop_left' hk, List.take_left' hk]
    rw [ih (fun x hx => hl x (by simp [hx])) (by simp at hn; omega)]

theorem rdCheck_other {b : UInt8} {t : Script} (h1 : b ≠ 0x76) (h2 : b ≠ 0x21) (v : Bool) :
    rdCheck v (b :: t) = some (.multi (b.toNat - 0x50) (rdKeys 3 t).1, (rdKeys 3 t).2.drop 2) := by
  unfold rdCheck
  split
  · rename_i e; exact absurd (List.cons.inj e).1 h1
  · rename_i e; exact absurd (List.cons.inj e).1 h2
  · rename_i e; obtain ⟨rfl, rfl⟩ := List.cons.inj e; cases rdKeys 3 t; rfl
  · rename_i e; exact absurd e (List.cons_ne_nil _ _)

theorem compressedKey_length {k : Script} (h : compressedKey k = true) : k.length = 33 := by
  simp [compressedKey] at h; exact h.1

theorem rdCheck_script {c : Check} {v : Bool} (h : c.ok v = true) (rest : Script) :
    rdCheck v (c.script v ++ rest) = some (c, rest) := by
  cases c with
  | pk k =>
    have hk := compressedKey_length (by simpa [Check.ok] using h)
    simp only [Check.script, pushKey, List.cons_append, List.append_assoc, rdCheck, List.take_left' hk]
    simp [List.drop_append, hk]
  | multi m ks =>
    simp only [Check.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨h2, h3⟩, h1⟩, hm⟩, hks⟩ := h
    have hl : ∀ k ∈ ks, k.length = 33 := fun k hk => compressedKey_length (hks k hk)
    simp only [Check.script, List.cons_append, List.append_assoc]
    rw [rdCheck_other (ofNat_ne (by omega) (by simp; omega)) (ofNat_ne (by omega) (by simp; omega)),
      rdKeys_flatMap hl (by omega) (ofNat_ne (by omega) (by simp; omega))]
    simp [Nat.mod_eq_of_lt (show 80 + m < 256 by omega)]
  | pkh hsh =>
    simp only [Check.ok, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hh⟩ := h
    simp only [Check.script, List.cons_append, List.append_assoc, rdCheck, ite_true, List.drop_succ_cons, List.drop_zero,
      List.take_left' hh]
    simp [List.drop_append, hh]

theorem parseOrD_script {d : OrD} (h : d.ok = true) : parseOrD d.script = some d := by
  simp only [OrD.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hx, hy⟩, h1⟩, h2⟩, -⟩ := h
  simp only [parseOrD, OrD.script]
  rw [rdCheck_script hx]
  simp only [Option.bind_eq_bind, Option.bind_some, List.drop_zero, List.drop_succ_cons]
  rw [rdCheck_script hy]
  simp only [Option.bind_some, Option.pure_def, List.length_append, List.length_cons, List.length_nil]
  have hn : numOf (scriptNum d.lock) = d.lock := numOf_scriptNum h1 h2
  cases d with
  | mk x y after lock =>
    simp only at hn ⊢
    congr 1
    simp only [OrD.mk.injEq, true_and]
    constructor
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      cases after <;> simp
    · rw [show (scriptNum lock).length + (0 + 1 + 1) - 2 = (scriptNum lock).length by omega,
        List.take_left' rfl, hn]

/-- Every well-formed or_d wallet's script is read back as that wallet. -/
theorem orDOf_script {d : OrD} (h : d.ok = true) : orDOf d.script = some d := by
  simp [orDOf, parseOrD_script h, h]

/-- What `orDOf` accepts is a well-formed wallet's script. -/
theorem orDOf_some {w : Script} {d : OrD} (h : orDOf w = some d) : d.ok = true ∧ d.script = w := by
  unfold orDOf at h
  split at h
  · split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h; simpa using hc
    · simp at h
  · simp at h

/-- The script binds both paths, the timelock's kind and its value. -/
theorem orD_script_inj {d d' : OrD} (h : d.ok = true) (h' : d'.ok = true) (e : d.script = d'.script) : d = d' := by
  have := orDOf_script h; rw [e, orDOf_script h'] at this; exact (Option.some.inj this).symm

/-- So does its P2WSH output, taking SHA-256 to be one to one. -/
theorem p2wsh_orD_binds {H : List UInt8 → List UInt8} (hH : HashOk H) {d d' : OrD} (h : d.ok = true)
    (h' : d'.ok = true) (e : p2wshOf H d.script = p2wshOf H d'.script) : d = d' := by
  simp only [p2wshOf, List.cons.injEq, true_and] at e
  exact orD_script_inj h h' (hH.inj _ _ e)

end SignerSpec
