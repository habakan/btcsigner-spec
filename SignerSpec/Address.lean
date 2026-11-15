import SignerSpec.Notation

/-!
# Reading an address back

`decode` reads a string the screen could have written back to a script. It undoes each encoding, then
keeps a script only if the screen writes exactly that string for it, so its checksum is the one the
string carries. The screen's string decodes to its script, and no other string decodes to anything
it does not write.
-/

namespace SignerSpec

def hexValue (c : Char) : Nat := hexDigits.idxOf c

def unhex : List Char → List Nat
  | a :: b :: r => (hexValue a * 16 + hexValue b) :: unhex r
  | _ => []

def index32 (c : Char) : Nat := charset32.idxOf c

/-- 5-bit groups back to the bytes they pad. -/
def ungroup (gs : List Nat) : List Nat :=
  fixedDigits 256 (5 * gs.length / 8) (ofDigits 32 gs / 2 ^ (5 * gs.length - 8 * (5 * gs.length / 8)))

/-- The script each encoding would give for `s`, whether or not `s` is written in it. -/
def candidates (net : Net) (s : List Char) : List (List Nat) :=
  let d := (s.drop ((hrp net).length + 1)).map index32
  let data := d.take (d.length - 6)
  let p := fixedDigits 256 25 (value58 s)
  [unshown net (.raw (unhex (s.drop 7))),
    unshown net (.segwit (data.headD 0) (ungroup data.tail)),
    unshown net (.base58 (p.headD 0) (p.tail.take 20))]

def decode (cs : Checksums) (net : Net) (s : List Char) : Option Script :=
  ((candidates net s).map (·.map UInt8.ofNat)).find? fun spk => decide (render cs net spk = s)

theorem unhex_hex : ∀ l : List Nat, (∀ d ∈ l, d < 256) → unhex (hex l) = l
  | [], _ => rfl
  | d :: l, h => by
    have e : ∀ x, x < 16 → hexValue (hexChar x) = x := by decide
    have hd := h d (by simp)
    have : hex (d :: l) = hexChar (d / 16) :: hexChar (d % 16) :: hex l := by simp [hex, hexByte]
    rw [this, unhex, e _ (by omega), e _ (Nat.mod_lt _ (by decide)),
      unhex_hex l fun x hx => h x (List.mem_cons_of_mem _ hx)]
    congr 1; omega

theorem ungroup_groups {p : List Nat} (hp : ∀ d ∈ p, d < 256) : ungroup (groups p) = p := by
  have hl : 5 * groupCount p.length / 8 = p.length := by unfold groupCount; omega
  have pos : 0 < 2 ^ (5 * groupCount p.length - 8 * p.length) := Nat.pow_pos (by decide)
  have lt : ofDigits 256 p * 2 ^ (5 * groupCount p.length - 8 * p.length) < 32 ^ groupCount p.length := by
    rw [← groups_bound]; exact Nat.mul_lt_mul_of_pos_right (ofDigits_lt p hp) pos
  unfold ungroup
  rw [groups_length, hl]
  unfold groups
  rw [ofDigits_fixed, Nat.mod_eq_of_lt lt, Nat.mul_div_cancel _ pos, fixed_ofDigits p hp]

theorem index32_char32 : ∀ d, d < 32 → index32 (char32 d) = d := by decide

theorem mem_candidates (cs : Checksums) (net : Net) {sh : Shown} (g : Good net sh) :
    unshown net sh ∈ candidates net (renderShown cs net sh) := by
  cases sh with
  | raw b =>
    have : ("script:".toList ++ hex b).drop 7 = hex b := List.drop_left' rfl
    simp only [candidates, renderShown, this, unhex_hex b g]
    exact List.mem_cons_self
  | segwit v p =>
    obtain ⟨hv, -, -, hp⟩ := g
    have hdata : ∀ d ∈ v :: groups p, d < 32 := by
      intro d hd; simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · omega
      · exact fixedDigits_lt (by decide) _ _ d hd
    have key : ∀ ck : List Nat, ck.length = 6 →
        (((hrp net ++ '1' :: ((v :: groups p) ++ ck).map char32).drop ((hrp net).length + 1)).map index32).take
          ((((hrp net ++ '1' :: ((v :: groups p) ++ ck).map char32).drop ((hrp net).length + 1)).map index32).length
            - 6) = v :: groups p := by
      intro ck hck
      rw [← List.singleton_append, ← List.append_assoc, List.drop_left' (by simp), List.map_append, List.map_append]
      simp only [List.length_append, List.length_map, hck, Nat.add_sub_cancel]
      rw [List.take_left' (by simp), List.map_map]
      exact map_eq_self fun d hd => index32_char32 d (hdata d hd)
    simp only [candidates, renderShown, segwitAddress]
    rw [key _ (cs.bech32_length _ _ _)]
    simp only [List.headD_cons, List.tail_cons, ungroup_groups hp]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  | base58 v h =>
    obtain ⟨hv, hl, hh⟩ := g
    have ok : ∀ d ∈ v :: h ++ cs.base58 (v :: h), d < 256 := by
      intro d hd
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hd
      rcases hd with rfl | hd | hd
      · exact version_lt net hv
      · exact hh d hd
      · exact cs.base58_lt _ d hd
    have hlen : (v :: h ++ cs.base58 (v :: h)).length = 25 := by simp [hl, cs.base58_length]
    have hp : fixedDigits 256 25 (value58 (base58Address cs v h)) = v :: h ++ cs.base58 (v :: h) := by
      rw [base58Address, value58_base58, ← hlen, fixed_ofDigits _ ok]
    simp only [candidates, renderShown, hp, List.cons_append, List.headD_cons, List.tail_cons]
    rw [List.take_left' hl]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The string the screen writes for a script reads back as that script. -/
theorem decode_render (cs : Checksums) (net : Net) (spk : Script) : decode cs net (render cs net spk) = some spk := by
  have lt : ∀ d ∈ spk.map (·.toNat), d < 256 := by
    intro d hd; simp only [List.mem_map] at hd; obtain ⟨x, -, rfl⟩ := hd; exact x.toNat_lt
  have hm := mem_candidates cs net (shown_good net _ lt)
  rw [unshown_shown] at hm
  have hmem : spk ∈ (candidates net (render cs net spk)).map (·.map UInt8.ofNat) :=
    List.mem_map.mpr ⟨_, hm, by simp [List.map_map, Function.comp_def]⟩
  unfold decode
  cases e : List.find? _ _ with
  | none => exact absurd (List.find?_eq_none.mp e spk hmem) (by simp)
  | some x =>
    have := List.find?_some e
    simp only [decide_eq_true_eq] at this
    rw [render_inj this]

/-- A string reads as a script only when it is exactly what the screen writes for that script. -/
theorem render_decode {cs : Checksums} {net : Net} {s : List Char} {spk : Script} (h : decode cs net s = some spk) :
    render cs net spk = s := by
  simpa using List.find?_some h

end SignerSpec
