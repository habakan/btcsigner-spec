import SignerSpec.Wordlist
import SignerSpec.Notation

/-!
# A mnemonic, typed or scanned

A BIP39 mnemonic is word indices below 2048: the entropy (16 to 32 bytes, `4k` of them) followed by a
`k`-bit checksum, read eleven bits at a time into `3k` words. SHA-256 is a parameter `sha`; its first
byte gives the checksum. Proved here:

- four letters name a word (`four_letters`), three do not (`three_letters_not_enough`)
- a mnemonic and its entropy determine each other (`toEntropy_toWords`), which is what a CompactSeedQR,
  holding only the entropy, relies on
- the last words that complete the others are exactly `finalWords`, `2 ^ (11 - k)` of them, so with 12
  words one last word in 16 passes the checksum and a wrong one goes unnoticed that often (`mem_finalWords`)
- a Standard SeedQR reads back to its words, and only its own digits do (`decodeStd_seedqrStd`,
  `seedqrStd_decodeStd`)
-/

namespace SignerSpec

/-! ## Typing a word -/

/-- The first four letters as a number, a shorter word padded with zeros. -/
def prefixKey (w : String) : Nat :=
  let p := w.toList.take 4
  ofDigits 27 (p.map (·.toNat - 96) ++ List.replicate (4 - p.length) 0)

def ascending : List Nat → Bool
  | a :: b :: r => a < b && ascending (b :: r)
  | _ => true

theorem wordlist_ascending : ascending (wordlist.map prefixKey) = true := by decide +kernel

theorem ascending_lt : ∀ {a : Nat} {r : List Nat}, ascending (a :: r) = true → ∀ y ∈ r, a < y
  | _, [], _, _, hy => by simp at hy
  | a, b :: r, h, y, hy => by
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.1
    · exact Nat.lt_trans h.1 (ascending_lt h.2 y hy)

theorem key_inj : ∀ {l : List String}, ascending (l.map prefixKey) = true →
    ∀ {w w'}, w ∈ l → w' ∈ l → prefixKey w = prefixKey w' → w = w'
  | [], _, _, _, hw, _, _ => by simp at hw
  | x :: l, h, w, w', hw, hw', e => by
    have hl : ascending (l.map prefixKey) = true := by
      cases l with
      | nil => rfl
      | cons y l => simp only [List.map_cons, ascending, Bool.and_eq_true] at h ⊢; exact h.2
    have lt := ascending_lt h
    rcases List.mem_cons.mp hw with rfl | h1 <;> rcases List.mem_cons.mp hw' with rfl | h2
    · rfl
    · exact absurd e (Nat.ne_of_lt (lt _ (List.mem_map_of_mem h2)))
    · exact absurd e.symm (Nat.ne_of_lt (lt _ (List.mem_map_of_mem h1)))
    · exact key_inj hl h1 h2 e

/-- No two words share their first four letters, so four typed letters name one word. -/
theorem four_letters {w w' : String} (hw : w ∈ wordlist) (hw' : w' ∈ wordlist)
    (h : w.toList.take 4 = w'.toList.take 4) : w = w' :=
  key_inj wordlist_ascending hw hw' (by simp only [prefixKey, h])

/-- Three are not: "act" is a word and the start of "action", so entry cannot end at a unique match. -/
theorem three_letters_not_enough : "act" ∈ wordlist ∧ "action" ∈ wordlist := by decide +kernel

/-! ## Entropy and words -/

variable (sha : List UInt8 → List UInt8)

/-- The checksum of `4k` bytes of entropy: the first `k` bits of their SHA-256. -/
def csBits (e : List Nat) : Nat :=
  ((sha (e.map UInt8.ofNat)).headD 0).toNat / 2 ^ (8 - e.length / 4)

def toWords (e : List Nat) : List Nat :=
  fixedDigits 2048 (3 * (e.length / 4)) (ofDigits 256 e * 2 ^ (e.length / 4) + csBits sha e)

def toEntropy (idx : List Nat) : List Nat :=
  fixedDigits 256 (4 * (idx.length / 3)) (ofDigits 2048 idx / 2 ^ (idx.length / 3))

def sizes : List Nat := [12, 15, 18, 21, 24]

def valid (idx : List Nat) : Bool :=
  sizes.contains idx.length && idx.all (· < 2048) && toWords sha (toEntropy idx) == idx

theorem csBits_lt {e : List Nat} (hk : e.length / 4 ≤ 8) : csBits sha e < 2 ^ (e.length / 4) := by
  unfold csBits
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_add, Nat.add_sub_cancel' hk]
  exact UInt8.toNat_lt _

/-- `2048 ^ 3k = 256 ^ 4k * 2 ^ k`: the words hold the entropy and its checksum exactly. -/
theorem words_bound (k : Nat) : 256 ^ (4 * k) * 2 ^ k = 2048 ^ (3 * k) := by
  have h1 : (256 : Nat) = 2 ^ 8 := rfl
  have h2 : (2048 : Nat) = 2 ^ 11 := rfl
  rw [h1, h2, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
  congr 1; omega

theorem sizes_k {n : Nat} (h : sizes.contains n = true) : n = 3 * (n / 3) ∧ 4 ≤ n / 3 ∧ n / 3 ≤ 8 := by
  simp only [sizes, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
  omega

/-- The entropy comes back from its words, and its words are a valid mnemonic. -/
theorem toEntropy_toWords {e : List Nat} (he : sizes.contains (3 * (e.length / 4)) = true)
    (h4 : e.length % 4 = 0) (hd : ∀ d ∈ e, d < 256) :
    toEntropy (toWords sha e) = e ∧ valid sha (toWords sha e) = true := by
  have hk := sizes_k he
  generalize hk' : e.length / 4 = k at hk he
  have hlen : e.length = 4 * k := by omega
  have hc := csBits_lt sha (e := e) (by omega)
  rw [hk'] at hc
  have hE := ofDigits_lt e hd
  rw [hlen] at hE
  have hN : ofDigits 256 e * 2 ^ k + csBits sha e < 2048 ^ (3 * k) := by
    rw [← words_bound]
    have := Nat.mul_le_mul_right (2 ^ k) (Nat.succ_le_of_lt hE)
    rw [Nat.succ_mul] at this; omega
  have hw : toWords sha e = fixedDigits 2048 (3 * k) (ofDigits 256 e * 2 ^ k + csBits sha e) := by
    simp only [toWords, hk']
  have hwl : (toWords sha e).length = 3 * k := by rw [hw, fixedDigits_length]
  have ent : toEntropy (toWords sha e) = e := by
    unfold toEntropy
    rw [hwl, show 3 * k / 3 = k by omega, hw, ofDigits_fixed, Nat.mod_eq_of_lt hN,
      Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hc, Nat.zero_add,
      ← hlen, fixed_ofDigits e hd]
  refine ⟨ent, ?_⟩
  simp only [valid, ent, beq_self_eq_true, Bool.and_true, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, hwl]
  exact ⟨he,
    fun d hd => by rw [hw] at hd; exact fixedDigits_lt (by decide) _ _ d hd⟩

/-! ## The last word -/

/-- The last words that complete `p` with a valid checksum: for each value of the bits the last word
adds to the entropy, the one checksum that fits. -/
def finalWords (p : List Nat) : List Nat :=
  let k := (p.length + 1) / 3
  (List.range (2 ^ (11 - k))).map fun h => h * 2 ^ k + csBits sha (toEntropy (p ++ [h * 2 ^ k]))

/-- The other words fixed, 2^(11 - k) last words pass the checksum, with k checksum bits: 128 for 12 words,
8 for 24. -/
theorem finalWords_length (p : List Nat) : (finalWords sha p).length = 2 ^ (11 - (p.length + 1) / 3) := by
  simp [finalWords]

theorem split2048 {k : Nat} (hk : k ≤ 11) : 2 ^ (11 - k) * 2 ^ k = 2048 := by
  rw [← Nat.pow_add, Nat.sub_add_cancel hk]

/-- The last word adds its top `11 - k` bits to the entropy; the rest is checksum. -/
theorem toEntropy_last {p : List Nat} {w : Nat} (hn : sizes.contains (p.length + 1) = true) :
    toEntropy (p ++ [w]) = fixedDigits 256 (4 * ((p.length + 1) / 3))
      (ofDigits 2048 p * 2 ^ (11 - (p.length + 1) / 3) + w / 2 ^ ((p.length + 1) / 3)) := by
  have hk := sizes_k hn
  unfold toEntropy
  rw [List.length_append, List.length_singleton]
  generalize (p.length + 1) / 3 = k at hk ⊢
  rw [ofDigits_append, ← split2048 (k := k) (by omega),
    ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.add_comm]

/-- A last word is valid exactly when its low `k` bits are the checksum of the entropy it completes. -/
theorem valid_last {p : List Nat} {w : Nat} (hn : sizes.contains (p.length + 1) = true)
    (hp : ∀ d ∈ p, d < 2048) (hw : w < 2048) :
    valid sha (p ++ [w]) = true ↔ w % 2 ^ ((p.length + 1) / 3) = csBits sha (toEntropy (p ++ [w])) := by
  have hk := sizes_k hn
  have he := toEntropy_last (w := w) hn
  generalize hK : (p.length + 1) / 3 = k at hk he ⊢
  have hlen : (p ++ [w]).length = 3 * k := by simp only [List.length_append, List.length_singleton]; omega
  have hpw : ∀ d ∈ p ++ [w], d < 2048 := by
    intro d hd; rcases List.mem_append.mp hd with hd | hd
    · exact hp d hd
    · simp at hd; omega
  have hB : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hAB := split2048 (k := k) (by omega)
  generalize hE : ofDigits 2048 p * 2 ^ (11 - k) + w / 2 ^ k = E at he
  have hP := ofDigits_lt p hp
  have hEl : E < 256 ^ (4 * k) := by
    have pw : 2048 ^ p.length * 2 ^ (11 - k) = 256 ^ (4 * k) := by
      have h1 : (256 : Nat) = 2 ^ 8 := rfl
      have h2 : (2048 : Nat) = 2 ^ 11 := rfl
      rw [h1, h2, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
      congr 1; omega
    have hwb : w / 2 ^ k < 2 ^ (11 - k) := by
      rw [Nat.div_lt_iff_lt_mul hB, hAB]; exact hw
    have := Nat.mul_le_mul_right (2 ^ (11 - k)) (Nat.succ_le_of_lt hP)
    rw [Nat.succ_mul, pw] at this; omega
  have hel : (toEntropy (p ++ [w])).length = 4 * k := by rw [he, fixedDigits_length]
  have hval : ofDigits 256 (toEntropy (p ++ [w])) = E := by rw [he, ofDigits_fixed, Nat.mod_eq_of_lt hEl]
  have hc := csBits_lt sha (e := toEntropy (p ++ [w])) (by rw [hel]; omega)
  rw [hel, show 4 * k / 4 = k by omega] at hc
  have hY : ofDigits 2048 (p ++ [w]) = E * 2 ^ k + w % 2 ^ k := by
    rw [ofDigits_append, ← hE, ← hAB, Nat.add_mul, ← Nat.mul_assoc, Nat.add_assoc, Nat.div_add_mod' w]
  have hX : toWords sha (toEntropy (p ++ [w])) =
      fixedDigits 2048 (3 * k) (E * 2 ^ k + csBits sha (toEntropy (p ++ [w]))) := by
    simp only [toWords, hel, show 4 * k / 4 = k by omega, hval]
  have hv : valid sha (p ++ [w]) = true ↔ toWords sha (toEntropy (p ++ [w])) = p ++ [w] := by
    simp only [valid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨⟨by rw [List.length_append, List.length_singleton]; exact hn, hpw⟩, h⟩⟩
  rw [hv, hX]
  generalize csBits sha (toEntropy (p ++ [w])) = c at hc ⊢
  have hXlt : E * 2 ^ k + c < 2048 ^ (3 * k) := by
    rw [← words_bound]
    have := Nat.mul_le_mul_right (2 ^ k) (Nat.succ_le_of_lt hEl)
    rw [Nat.succ_mul] at this; omega
  constructor
  · intro h
    have := congrArg (ofDigits 2048) h
    rw [ofDigits_fixed, Nat.mod_eq_of_lt hXlt, hY] at this
    omega
  · intro h
    rw [← h, ← hY, ← hlen, fixed_ofDigits _ hpw]

/-- The words `finalWords` offers are exactly the last words with a valid checksum. -/
theorem mem_finalWords {p : List Nat} (hn : sizes.contains (p.length + 1) = true) (hp : ∀ d ∈ p, d < 2048)
    {w : Nat} : w ∈ finalWords sha p ↔ w < 2048 ∧ valid sha (p ++ [w]) = true := by
  have hk := sizes_k hn
  have hlast := fun x => toEntropy_last (p := p) (w := x) hn
  have hlen : ∀ x, (toEntropy (p ++ [x])).length = 4 * ((p.length + 1) / 3) := fun x => by
    rw [hlast x, fixedDigits_length]
  have hvl := fun x (hx : x < 2048) => valid_last sha hn hp hx
  unfold finalWords
  generalize (p.length + 1) / 3 = k at hk hlast hlen hvl ⊢
  have hB : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hAB := split2048 (k := k) (by omega)
  have same : ∀ x, toEntropy (p ++ [x]) = toEntropy (p ++ [x / 2 ^ k * 2 ^ k]) := fun x => by
    rw [hlast x, hlast, Nat.mul_div_cancel _ hB]
  have hc : ∀ x, csBits sha (toEntropy (p ++ [x])) < 2 ^ k := fun x => by
    have := csBits_lt sha (e := toEntropy (p ++ [x])) (by rw [hlen]; omega)
    rwa [hlen, show 4 * k / 4 = k by omega] at this
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have c := hc (h * 2 ^ k)
    have hw : h * 2 ^ k + csBits sha (toEntropy (p ++ [h * 2 ^ k])) < 2048 := by
      rw [← hAB]
      have := Nat.mul_le_mul_right (2 ^ k) (Nat.succ_le_of_lt hh)
      rw [Nat.succ_mul] at this; omega
    refine ⟨hw, (hvl _ hw).mpr ?_⟩
    have hd : (h * 2 ^ k + csBits sha (toEntropy (p ++ [h * 2 ^ k]))) / 2 ^ k = h := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt c, Nat.zero_add]
    rw [same (h * 2 ^ k + _), hd, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt c]
  · rintro ⟨hw, hv⟩
    refine ⟨w / 2 ^ k, by rw [Nat.div_lt_iff_lt_mul hB, hAB]; exact hw, ?_⟩
    rw [← same, ← (hvl w hw).mp hv, Nat.div_add_mod']

/-! ## SeedQR -/

def digitValue (c : Char) : Nat := c.toNat - 48

/-- Standard SeedQR: each word's index as four decimal digits. -/
def seedqrStd (idx : List Nat) : List Char := idx.flatMap fun i => (fixedDigits 10 4 i).map digitChar

def readStd : List Char → List Nat
  | a :: b :: c :: d :: r => ofDigits 10 ([a, b, c, d].map digitValue) :: readStd r
  | _ => []

/-- A SeedQR holds 12 or 24 words; digits read as words only if those are valid and these are their digits. -/
def decodeStd (s : List Char) : Option (List Nat) :=
  let idx := readStd s
  if (idx.length = 12 ∨ idx.length = 24) ∧ valid sha idx = true ∧ seedqrStd idx = s then some idx else none

/-- CompactSeedQR: the entropy's bytes, 16 or 32 of them. The checksum is computed, never read. -/
def decodeCompact (b : List Nat) : Option (List Nat) :=
  if b.length = 16 ∨ b.length = 32 then some (toWords sha b) else none

theorem readStd_cons (l : List Nat) (hl : l.length = 4) (hd : ∀ d ∈ l, d < 10) (r : List Char) :
    readStd (l.map digitChar ++ r) = ofDigits 10 l :: readStd r := by
  have e : ∀ d, d < 10 → digitValue (digitChar d) = d := by decide
  match l, hl with
  | [a, b, c, d], _ =>
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, readStd, List.cons.injEq, and_true]
    congr 1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    simp [e a (hd a (by simp)), e b (hd b (by simp)), e c (hd c (by simp)), e d (hd d (by simp))]

theorem readStd_seedqrStd : ∀ idx : List Nat, (∀ i ∈ idx, i < 2048) → readStd (seedqrStd idx) = idx
  | [], _ => rfl
  | i :: r, h => by
    have hi := h i (by simp)
    simp only [seedqrStd, List.flatMap_cons] at ⊢
    rw [readStd_cons _ (fixedDigits_length _ _ _) (fixedDigits_lt (by decide) _ _), ofDigits_fixed,
      Nat.mod_eq_of_lt (by omega)]
    exact congrArg _ (readStd_seedqrStd r fun x hx => h x (by simp [hx]))

theorem valid_lt {idx : List Nat} (hv : valid sha idx = true) : ∀ i ∈ idx, i < 2048 := by
  simp only [valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  exact hv.1.2

/-- A valid mnemonic's Standard SeedQR reads back as that mnemonic. -/
theorem decodeStd_seedqrStd {idx : List Nat} (hv : valid sha idx = true) (hl : idx.length = 12 ∨ idx.length = 24) :
    decodeStd sha (seedqrStd idx) = some idx := by
  simp [decodeStd, readStd_seedqrStd idx (valid_lt sha hv), hv, hl]

/-- Digits read as a mnemonic only when they are exactly its Standard SeedQR, and it is valid. -/
theorem seedqrStd_decodeStd {s : List Char} {idx : List Nat} (h : decodeStd sha s = some idx) :
    seedqrStd idx = s ∧ valid sha idx = true := by
  simp only [decodeStd] at h
  split at h
  · rename_i hc; cases h; exact ⟨hc.2.2, hc.2.1⟩
  · simp at h

/-- A valid 12 or 24 word mnemonic's CompactSeedQR reads back as it. -/
theorem decodeCompact_toEntropy {idx : List Nat} (hv : valid sha idx = true) (hl : idx.length = 12 ∨ idx.length = 24) :
    decodeCompact sha (toEntropy idx) = some idx := by
  have hw : toWords sha (toEntropy idx) = idx := by
    simp only [valid, Bool.and_eq_true, beq_iff_eq] at hv; exact hv.2
  have hlen : (toEntropy idx).length = 4 * (idx.length / 3) := by simp [toEntropy, fixedDigits_length]
  have h4 : 4 * (idx.length / 3) = 16 ∨ 4 * (idx.length / 3) = 32 := by omega
  simp [decodeCompact, hlen, hw, h4]

end SignerSpec
