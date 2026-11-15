import SignerSpec.Notation

/-!
# What a message review shows

A signed message is bytes. Review shows them as text when a reader can take every byte back from the
screen, and as hex otherwise. A reader is not trusted to count spaces: `squash` is what they take in,
the text without spaces at either end and with every run of spaces read as one. Coldcard refuses a
message with a leading or trailing space or more than three in a row, for the same reason.
-/

namespace SignerSpec

inductive MsgKind where
  | text | hex
  deriving DecidableEq, Repr

def printable (b : UInt8) : Bool := 0x20 ≤ b.toNat && b.toNat ≤ 0x7e

def byteChar (b : UInt8) : Char := Char.ofNat b.toNat

def noDouble : List Char → Bool
  | c :: d :: r => !(c == ' ' && d == ' ') && noDouble (d :: r)
  | _ => true

/-- No space at either end, never two in a row. -/
def plainSpacing (cs : List Char) : Bool :=
  cs.head? != some ' ' && cs.getLast? != some ' ' && noDouble cs

def showMessage (m : List UInt8) : MsgKind × List Char :=
  let cs := m.map byteChar
  if m.all printable && plainSpacing cs then (.text, cs) else (.hex, hex (m.map (·.toNat)))

/-! ## What a reader takes in -/

def collapse : List Char → List Char
  | c :: d :: r => if c = ' ' ∧ d = ' ' then collapse (d :: r) else c :: collapse (d :: r)
  | l => l

def trimSpaces (cs : List Char) : List Char :=
  ((cs.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse

def squash (cs : List Char) : List Char := trimSpaces (collapse cs)

def seen (s : MsgKind × List Char) : MsgKind × List Char := (s.1, squash s.2)

theorem collapse_noDouble : ∀ {cs : List Char}, noDouble cs = true → collapse cs = cs
  | [], _ => rfl
  | [_], _ => rfl
  | c :: d :: r, h => by
    simp only [noDouble, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
    have hcd : ¬(c = ' ' ∧ d = ' ') := by rcases h.1 with h1 | h1 <;> simp [h1]
    simp only [collapse, hcd, ↓reduceIte, collapse_noDouble h.2]

theorem dropWhile_head {l : List Char} (h : l.head? ≠ some ' ') : l.dropWhile (· == ' ') = l := by
  cases l with
  | nil => rfl
  | cons c r => simp_all

theorem squash_plain {cs : List Char} (h : plainSpacing cs = true) : squash cs = cs := by
  simp only [plainSpacing, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hh, hl⟩, hn⟩ := h
  rw [squash, collapse_noDouble hn, trimSpaces, dropWhile_head hh, dropWhile_head (by rwa [List.head?_reverse]),
    List.reverse_reverse]

theorem hexChar_ne_space (d : Nat) : hexChar d ≠ ' ' := by
  unfold hexChar
  by_cases h : d < 16
  · exact (by decide : ∀ d, d < 16 → hexDigits.getD d '?' ≠ ' ') d h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show hexDigits.length ≤ d by simp [hexDigits]; omega)]

theorem noDouble_of_noSpace : ∀ {cs : List Char}, (∀ c ∈ cs, c ≠ ' ') → noDouble cs = true
  | [], _ => rfl
  | [_], _ => rfl
  | c :: d :: r, h => by
    have ih := noDouble_of_noSpace (cs := d :: r) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp [noDouble, h c (by simp), ih]

theorem plain_of_noSpace {cs : List Char} (h : ∀ c ∈ cs, c ≠ ' ') : plainSpacing cs = true := by
  simp only [plainSpacing, Bool.and_eq_true, bne_iff_ne, ne_eq, noDouble_of_noSpace h, and_true]
  constructor
  · intro e; exact h _ (List.mem_of_head? e) rfl
  · intro e; exact h _ (List.mem_of_getLast? e) rfl

theorem hex_noSpace (l : List Nat) : ∀ c ∈ hex l, c ≠ ' ' := by
  intro c hc
  simp only [hex, List.mem_flatMap, hexByte, List.mem_cons, List.mem_nil_iff, or_false] at hc
  obtain ⟨_, -, rfl | rfl⟩ := hc <;> exact hexChar_ne_space _

theorem byteChar_toNat {b : UInt8} (h : printable b = true) : (byteChar b).toNat = b.toNat := by
  have : b.toNat < 0xd800 := by simp [printable] at h; omega
  simp [byteChar, Char.ofNat, Char.ofNatAux, this, Nat.isValidChar, Char.toNat]

/-! ## One to one -/

/-- Different messages never look the same, to a reader who cannot count spaces. -/
theorem seen_inj {m m' : List UInt8} (h : seen (showMessage m) = seen (showMessage m')) : m = m' := by
  unfold showMessage seen at h
  by_cases hm : (m.all printable && plainSpacing (m.map byteChar)) = true <;>
    by_cases hm' : (m'.all printable && plainSpacing (m'.map byteChar)) = true <;>
    simp only [hm, hm', ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq, reduceCtorEq, false_and] at h
  · simp only [Bool.and_eq_true, List.all_eq_true] at hm hm'
    rw [squash_plain hm.2, squash_plain hm'.2] at h
    have := congrArg (List.map Char.toNat) h.2
    simp only [List.map_map] at this
    rw [List.map_congr_left (f := Char.toNat ∘ byteChar) (g := UInt8.toNat) (fun b hb => byteChar_toNat (hm.1 b hb)),
      List.map_congr_left (f := Char.toNat ∘ byteChar) (g := UInt8.toNat) (fun b hb => byteChar_toNat (hm'.1 b hb))]
      at this
    exact map_toNat_inj this
  · rw [squash_plain (plain_of_noSpace (hex_noSpace _)), squash_plain (plain_of_noSpace (hex_noSpace _))] at h
    refine map_toNat_inj (hex_inj ?_ ?_ h.2) <;> simpa using fun b _ => UInt8.toNat_lt b

/-- Printable alone is not enough: "a" and "a " look the same. -/
theorem printable_not_enough :
    ∃ m m' : List UInt8, m ≠ m' ∧ m.all printable ∧ m'.all printable ∧
      squash (m.map byteChar) = squash (m'.map byteChar) :=
  ⟨[0x61], [0x61, 0x20], by decide⟩

end SignerSpec
