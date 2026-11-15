import SignerSpec.Sighash

/-!
# What a sortedmulti wallet's script binds

`Model.lean` takes a registered wallet as given (`Multisig.outputChain`). This file writes its witness
script: BIP67 `sortedmulti`, the keys sorted bytewise, `OP_m <key>... OP_n OP_CHECKMULTISIG`. The order
the keys are given in does not change it (`sortedmulti_perm`), and the script binds the threshold and the
keys up to order (`sortedmulti_inj`). Under `HashOk`, so does the P2WSH output (`p2wsh_binds`): change
that pays this wallet's script pays no other quorum.
-/

namespace SignerSpec

/-- Bytewise order, as BIP67 sorts keys. -/
def keyLe : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => a.toNat < b.toNat || (a.toNat == b.toNat && keyLe s t)

def opN (n : Nat) : UInt8 := UInt8.ofNat (0x50 + n)

def multiScript (m : Nat) (keys : List Script) : Script :=
  opN m :: keys.flatMap (fun k => 0x21 :: k) ++ [opN keys.length, 0xae]

def sortedmulti (m : Nat) (keys : List Script) : Script := multiScript m (keys.mergeSort keyLe)

def p2wshOf (H : List UInt8 → List UInt8) (ws : Script) : Script := 0x00 :: 0x20 :: H ws

/-- Compressed keys, at most 16 of them, and a threshold that fits. -/
def MultiOk (m : Nat) (keys : List Script) : Prop :=
  1 ≤ m ∧ m ≤ keys.length ∧ keys.length ≤ 16 ∧ ∀ k ∈ keys, k.length = 33

theorem keyLe_total : ∀ a b : List UInt8, (keyLe a b || keyLe b a) = true
  | [], _ => by simp [keyLe]
  | _ :: _, [] => by simp [keyLe]
  | a :: s, b :: t => by
    have := keyLe_total s t
    simp only [keyLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this ⊢
    rcases Nat.lt_trichotomy a.toNat b.toNat with h | h | h
    · exact .inl (.inl h)
    · rcases this with h' | h'
      · exact .inl (.inr ⟨h, h'⟩)
      · exact .inr (.inr ⟨h.symm, h'⟩)
    · exact .inr (.inl h)

theorem keyLe_trans : ∀ a b c : List UInt8, keyLe a b = true → keyLe b c = true → keyLe a c = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [keyLe] at h
  | _ :: _, _ :: _, [], _, h => by simp [keyLe] at h
  | a :: s, b :: t, c :: u, h1, h2 => by
    have ih := keyLe_trans s t u
    simp only [keyLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inr ⟨by omega, ih h1 h2⟩

theorem keyLe_antisymm : ∀ a b : List UInt8, keyLe a b = true → keyLe b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [keyLe] at h
  | _ :: _, [], h, _ => by simp [keyLe] at h
  | a :: s, b :: t, h1, h2 => by
    simp only [keyLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1 h2
    have e : a.toNat = b.toNat := by omega
    have : keyLe s t = true ∧ keyLe t s = true := by
      rcases h1 with h1 | ⟨-, h1⟩ <;> rcases h2 with h2 | ⟨-, h2⟩ <;> first | omega | exact ⟨h1, h2⟩
    rw [UInt8.toNat_inj.mp e, keyLe_antisymm s t this.1 this.2]

/-- The order the keys come in does not change the script. -/
theorem sortedmulti_perm {m : Nat} {ks ks' : List Script} (h : ks.Perm ks') : sortedmulti m ks = sortedmulti m ks' := by
  unfold sortedmulti
  congr 1
  refine List.Perm.eq_of_pairwise (le := fun a b => keyLe a b = true)
    (fun a b _ _ h1 h2 => keyLe_antisymm a b h1 h2)
    (List.pairwise_mergeSort keyLe_trans keyLe_total _) (List.pairwise_mergeSort keyLe_trans keyLe_total _) ?_
  exact (List.mergeSort_perm _ _).trans (h.trans (List.mergeSort_perm _ _).symm)

theorem opN_inj {m n : Nat} (hm : m ≤ 16) (hn : n ≤ 16) (h : opN m = opN n) : m = n := by
  have := ofNat_inj (by omega) (by omega) h; omega

theorem multiScript_inj {m m' : Nat} {ks ks' : List Script} (hk : MultiOk m ks) (hk' : MultiOk m' ks')
    (h : multiScript m ks = multiScript m' ks') : m = m' ∧ ks = ks' := by
  simp only [multiScript, List.cons_append, List.cons.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have len : ∀ l : List Script, (∀ k ∈ l, k.length = 33) → (l.flatMap fun k => (0x21 : UInt8) :: k).length = 34 * l.length := by
    intro l hl; induction l with
    | nil => rfl
    | cons k l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, hl k (by simp)] at ih ⊢
      rw [ih fun x hx => hl x (by simp [hx])]; omega
  obtain ⟨e, -⟩ := List.append_inj h2 (by
    have := congrArg List.length h2
    simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢; omega)
  have code : PrefixFree (fun k : Script => k.length = 33) (fun k => (0x21 : UInt8) :: k) := by
    intro a b r s ha hb h
    simp only [List.cons_append, List.cons.injEq, true_and] at h
    exact List.append_inj h (by rw [ha, hb])
  exact ⟨opN_inj (by have := hk.2; omega) (by have := hk'.2; omega) h1,
    flatMap_inj code (fun _ _ => List.cons_ne_nil _ _) hk.2.2.2 hk'.2.2.2 e⟩

/-- The script binds the threshold, and the keys up to order. -/
theorem sortedmulti_inj {m m' : Nat} {ks ks' : List Script} (hk : MultiOk m ks) (hk' : MultiOk m' ks')
    (h : sortedmulti m ks = sortedmulti m' ks') : m = m' ∧ ks.Perm ks' := by
  have ok : ∀ {m ks}, MultiOk m ks → MultiOk m (ks.mergeSort keyLe) := by
    intro m ks hk
    have p := List.mergeSort_perm ks keyLe
    refine ⟨hk.1, ?_, ?_, fun k hk2 => hk.2.2.2 k (p.subset hk2)⟩ <;> rw [p.length_eq]
    · exact hk.2.1
    · exact hk.2.2.1
  obtain ⟨e1, e2⟩ := multiScript_inj (ok hk) (ok hk') h
  exact ⟨e1, (List.mergeSort_perm ks keyLe).symm.trans (e2 ▸ List.mergeSort_perm ks' keyLe)⟩

/-- So does its P2WSH output, taking SHA-256 to be one to one. -/
theorem p2wsh_binds {H : List UInt8 → List UInt8} (hH : HashOk H) {m m' : Nat} {ks ks' : List Script}
    (hk : MultiOk m ks) (hk' : MultiOk m' ks') (h : p2wshOf H (sortedmulti m ks) = p2wshOf H (sortedmulti m' ks')) :
    m = m' ∧ ks.Perm ks' := by
  simp only [p2wshOf, List.cons.injEq, true_and] at h
  exact sortedmulti_inj hk hk' (hH.inj _ _ h)

end SignerSpec
