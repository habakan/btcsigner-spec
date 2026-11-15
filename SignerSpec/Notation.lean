import SignerSpec.Model

/-!
# What the screen writes

An amount is shown in BTC as decimal digits, a point and eight decimals; an output as its address on
the signer's network, or as `script:` and hex when it has none. Both are one to one: two different
amounts, or two different scripts, never look the same. Checksums are parameters, since what they
are does not matter for that.
-/

namespace SignerSpec

/-! ## Digits -/

/-- The last `k` base-`b` digits of `n`, most significant first. -/
def fixedDigits (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => fixedDigits b k (n / b) ++ [n % b]

def ofDigits (b : Nat) (l : List Nat) : Nat := l.foldl (fun acc d => acc * b + d) 0

theorem ofDigits_append (b : Nat) (l : List Nat) (d : Nat) : ofDigits b (l ++ [d]) = ofDigits b l * b + d := by
  simp [ofDigits, List.foldl_append]

theorem fixedDigits_length (b k n : Nat) : (fixedDigits b k n).length = k := by
  induction k generalizing n <;> simp [fixedDigits, *]

theorem fixedDigits_lt {b : Nat} (hb : 0 < b) (k n : Nat) : ∀ d ∈ fixedDigits b k n, d < b := by
  induction k generalizing n with
  | zero => simp [fixedDigits]
  | succ k ih =>
    intro d hd
    simp only [fixedDigits, List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact ih _ d hd
    · exact Nat.mod_lt _ hb

theorem ofDigits_fixed (b k n : Nat) : ofDigits b (fixedDigits b k n) = n % b ^ k := by
  induction k generalizing n with
  | zero => simp [fixedDigits, ofDigits, Nat.mod_one]
  | succ k ih =>
    rw [fixedDigits, ofDigits_append, ih, Nat.pow_succ, Nat.mul_comm (b ^ k) b, Nat.mod_mul,
      Nat.mul_comm b, Nat.add_comm]

theorem fixedDigits_inj {b k m n : Nat} (hm : m < b ^ k) (hn : n < b ^ k)
    (h : fixedDigits b k m = fixedDigits b k n) : m = n := by
  have := congrArg (ofDigits b) h
  rwa [ofDigits_fixed, ofDigits_fixed, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at this

/-- How many base-`b` digits `n` takes, at least one. -/
def numDigits (b n : Nat) : Nat :=
  if h : 2 ≤ b ∧ b ≤ n then numDigits b (n / b) + 1 else 1
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem lt_pow_numDigits {b : Nat} (hb : 2 ≤ b) (n : Nat) : n < b ^ numDigits b n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold numDigits
    by_cases h : b ≤ n
    · simp only [hb, h, and_self, ↓reduceDIte, Nat.pow_succ]
      have h1 := ih (n / b) (Nat.div_lt_self (by omega) (by omega))
      have h2 := Nat.lt_mul_div_succ n (show 0 < b by omega)
      have h3 : b * (n / b + 1) ≤ b ^ numDigits b (n / b) * b := by
        rw [Nat.mul_comm (b ^ _) b]; exact Nat.mul_le_mul_left _ h1
      exact Nat.lt_of_lt_of_le h2 h3
    · simp only [h, and_false, ↓reduceDIte, Nat.pow_one]; omega

/-! ## Amounts -/

def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

theorem digitChar_inj' : ∀ d, d < 10 → ∀ e, e < 10 → digitChar d = digitChar e → d = e := by
  decide

theorem digitChar_inj {d e : Nat} (hd : d < 10) (he : e < 10) (h : digitChar d = digitChar e) : d = e :=
  digitChar_inj' d hd e he h

/-- Satoshis in a bitcoin. -/
def coin : Nat := 100000000

/-- Satoshis as BTC: the whole coins, a point, and eight decimals. -/
def fmtAmount (n : Nat) : List Char :=
  (fixedDigits 10 (numDigits 10 (n / coin)) (n / coin)).map digitChar ++
    '.' :: (fixedDigits 10 8 (n % coin)).map digitChar

theorem map_digitChar_inj : ∀ {l m : List Nat}, (∀ d ∈ l, d < 10) → (∀ d ∈ m, d < 10) →
    l.map digitChar = m.map digitChar → l = m
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | d :: l, e :: m, hl, hm, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [digitChar_inj (hl d (by simp)) (hm e (by simp)) h.1,
      map_digitChar_inj (fun x hx => hl x (by simp [hx])) (fun x hx => hm x (by simp [hx])) h.2]

/-- Two different amounts are never written the same. -/
theorem fmtAmount_inj {a b : Nat} (h : fmtAmount a = fmtAmount b) : a = b := by
  unfold fmtAmount at h
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_map, fixedDigits_length] at hlen
  obtain ⟨hw, hf⟩ := List.append_inj h (by simp only [List.length_map, fixedDigits_length]; omega)
  simp only [List.cons.injEq, true_and] at hf
  have lt := fixedDigits_lt (show 0 < 10 by decide)
  have hw' := map_digitChar_inj (lt _ _) (lt _ _) hw
  have hf' := map_digitChar_inj (lt _ _) (lt _ _) hf
  have hwlen := congrArg List.length hw'
  simp only [fixedDigits_length] at hwlen
  rw [hwlen] at hw'
  have e1 := fixedDigits_inj (by rw [← hwlen]; exact lt_pow_numDigits (b := 10) (by decide) _)
    (lt_pow_numDigits (b := 10) (by decide) _) hw'
  have hc : coin = 10 ^ 8 := rfl
  have e2 := fixedDigits_inj (b := 10) (k := 8) (by rw [← hc]; exact Nat.mod_lt _ (by decide))
    (by rw [← hc]; exact Nat.mod_lt _ (by decide)) hf'
  have := Nat.div_add_mod a coin
  have := Nat.div_add_mod b coin
  rw [← this, ← e1, ← e2]
  exact (Nat.div_add_mod a coin).symm

/-! ## Bytes as one number -/

theorem fixed_ofDigits {b : Nat} (l : List Nat) (h : ∀ d ∈ l, d < b) : fixedDigits b l.length (ofDigits b l) = l := by
  suffices ∀ n (l : List Nat), l.length = n → (∀ d ∈ l, d < b) → fixedDigits b n (ofDigits b l) = l from
    this _ l rfl h
  intro n
  induction n with
  | zero => intro l hl _; simp [List.length_eq_zero_iff.mp hl, fixedDigits]
  | succ n ih =>
    intro l hl h
    have hne : l ≠ [] := by intro e; simp [e] at hl
    have hsplit := List.dropLast_concat_getLast hne
    have hd : l.getLast hne < b := h _ (List.getLast_mem hne)
    have hb : 0 < b := by omega
    rw [← hsplit, fixedDigits, ofDigits_append, Nat.add_comm (ofDigits b _ * b), Nat.add_mul_div_right _ _ hb,
      Nat.div_eq_of_lt hd, Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd,
      ih _ (by simp [List.length_dropLast, hl]) (fun x hx => h x (hsplit ▸ List.mem_append_left _ hx))]

theorem ofDigits_inj {b : Nat} {l m : List Nat} (hl : ∀ d ∈ l, d < b) (hm : ∀ d ∈ m, d < b)
    (hlen : l.length = m.length) (h : ofDigits b l = ofDigits b m) : l = m := by
  rw [← fixed_ofDigits l hl, ← fixed_ofDigits m hm, h, hlen]

theorem ofDigits_lt {b : Nat} (l : List Nat) (h : ∀ d ∈ l, d < b) : ofDigits b l < b ^ l.length := by
  have e : ofDigits b l % b ^ l.length = ofDigits b l := by rw [← ofDigits_fixed, fixed_ofDigits l h]
  have hb : 0 < b ^ l.length := by
    cases l with
    | nil => simp
    | cons d _ => exact Nat.pow_pos (Nat.lt_of_le_of_lt (Nat.zero_le d) (h d (by simp)))
  rw [← e]; exact Nat.mod_lt _ hb

theorem ofDigits_zeros (b z : Nat) (l : List Nat) : ofDigits b (List.replicate z 0 ++ l) = ofDigits b l := by
  have : ∀ z, (List.replicate z 0).foldl (fun acc d => acc * b + d) 0 = 0 := by
    intro z; induction z <;> simp_all [List.replicate_succ]
  simp [ofDigits, List.foldl_append, this]

theorem numDigits_le {b : Nat} (hb : 2 ≤ b) {n m : Nat} (h : n < b ^ m) (hm : 1 ≤ m) : numDigits b n ≤ m := by
  induction n using Nat.strongRecOn generalizing m with
  | _ n ih =>
    unfold numDigits
    by_cases hn : b ≤ n
    · simp only [hb, hn, and_self, ↓reduceDIte]
      cases m with
      | zero => omega
      | succ m =>
        have : n / b < b ^ m := by
          rw [Nat.div_lt_iff_lt_mul (by omega), ← Nat.pow_succ]; exact h
        have hm' : 1 ≤ m := by
          cases m with
          | zero => simp at this; omega
          | succ m => omega
        have := ih (n / b) (Nat.div_lt_self (by omega) (by omega)) this hm'
        omega
    · simp only [hn, and_false, ↓reduceDIte]; exact hm

/-! ## Hex, for a script with no address -/

def hexDigits : List Char := "0123456789abcdef".toList

def hexChar (d : Nat) : Char := hexDigits.getD d '?'

theorem hexChar_inj' : ∀ d, d < 16 → ∀ e, e < 16 → hexChar d = hexChar e → d = e := by decide

def hexByte (d : Nat) : List Char := [hexChar (d / 16), hexChar (d % 16)]

def hex (l : List Nat) : List Char := l.flatMap hexByte

theorem hexByte_inj {d e : Nat} (hd : d < 256) (he : e < 256) (h : hexByte d = hexByte e) : d = e := by
  simp only [hexByte, List.cons.injEq, and_true] at h
  have h1 := hexChar_inj' _ (by omega) _ (by omega) h.1
  have h2 := hexChar_inj' _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) h.2
  have := Nat.div_add_mod d 16
  have := Nat.div_add_mod e 16
  omega

theorem hex_length (l : List Nat) : (hex l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [hex, hexByte] at ih ⊢; omega

theorem hex_inj : ∀ {l m : List Nat}, (∀ d ∈ l, d < 256) → (∀ d ∈ m, d < 256) → hex l = hex m → l = m
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [hex, hexByte] at h
  | _ :: _, [], _, _, h => by simp [hex, hexByte] at h
  | d :: l, e :: m, hl, hm, h => by
    simp only [hex, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hexByte])
    rw [hexByte_inj (hl d (by simp)) (hm e (by simp)) h1,
      hex_inj (fun x hx => hl x (by simp [hx])) (fun x hx => hm x (by simp [hx])) h2]

theorem hexChar_ne_colon (d : Nat) : hexChar d ≠ ':' := by
  unfold hexChar
  by_cases h : d < 16
  · exact (by decide : ∀ d, d < 16 → hexDigits.getD d '?' ≠ ':') d h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show hexDigits.length ≤ d by simp [hexDigits]; omega)]

/-! ## Addresses -/

inductive Net where
  | main | test | regtest
  deriving DecidableEq, Repr

def hrp : Net → List Char
  | .main => ['b', 'c']
  | .test => ['t', 'b']
  | .regtest => ['b', 'c', 'r', 't']

/-- base58check version bytes for P2PKH and P2SH. -/
def pkhVersion : Net → Nat
  | .main => 0x00
  | .test | .regtest => 0x6f

def shVersion : Net → Nat
  | .main => 0x05
  | .test | .regtest => 0xc4

/-- What the checksums are does not matter for telling outputs apart, only their lengths. -/
structure Checksums where
  /-- bech32 (`false`) or bech32m (`true`) over the human-readable part and the 5-bit data -/
  bech32 : Bool → List Char → List Nat → List Nat
  /-- A bech32 checksum is six characters. -/
  bech32_length : ∀ m h d, (bech32 m h d).length = 6
  /-- the first four bytes of the payload's double SHA-256 -/
  base58 : List Nat → List Nat
  /-- A Base58Check checksum is four bytes. -/
  base58_length : ∀ p, (base58 p).length = 4
  /-- Each of them a byte. -/
  base58_lt : ∀ p, ∀ x ∈ base58 p, x < 256

def charset32 : List Char := "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList

def char32 (d : Nat) : Char := charset32.getD d '?'

theorem char32_inj' : ∀ d, d < 32 → ∀ e, e < 32 → char32 d = char32 e → d = e := by decide

theorem map_char32_inj : ∀ {l m : List Nat}, (∀ d ∈ l, d < 32) → (∀ d ∈ m, d < 32) →
    l.map char32 = m.map char32 → l = m
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | d :: l, e :: m, hl, hm, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [char32_inj' d (hl d (by simp)) e (hm e (by simp)) h.1,
      map_char32_inj (fun x hx => hl x (by simp [hx])) (fun x hx => hm x (by simp [hx])) h.2]

/-- How many 5-bit groups a program of `n` bytes takes. -/
def groupCount (n : Nat) : Nat := (8 * n + 4) / 5

/-- A witness program as 5-bit groups: its bytes as one number, padded with zero bits to whole groups. -/
def groups (prog : List Nat) : List Nat :=
  fixedDigits 32 (groupCount prog.length) (ofDigits 256 prog * 2 ^ (5 * groupCount prog.length - 8 * prog.length))

def segwitAddress (cs : Checksums) (net : Net) (ver : Nat) (prog : List Nat) : List Char :=
  let data := ver :: groups prog
  hrp net ++ '1' :: (data ++ cs.bech32 (ver != 0) (hrp net) data).map char32

def charset58 : List Char := "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz".toList

def char58 (d : Nat) : Char := charset58.getD d '?'

def index58 (c : Char) : Nat := charset58.idxOf c

theorem index58_char58 : ∀ d, d < 58 → index58 (char58 d) = d := by decide

/-- base58: a '1' for each leading zero byte, then the payload as one number in base 58. -/
def base58 (payload : List Nat) : List Char :=
  let n := ofDigits 256 payload
  List.replicate (payload.takeWhile (· == 0)).length '1' ++
    (if n = 0 then [] else (fixedDigits 58 (numDigits 58 n) n).map char58)

def base58Address (cs : Checksums) (ver : Nat) (h : List Nat) : List Char :=
  base58 (ver :: h ++ cs.base58 (ver :: h))

/-- An output's script as the screen classifies it. -/
inductive Shown where
  | segwit (ver : Nat) (prog : List Nat)
  | base58 (ver : Nat) (hash : List Nat)
  | raw (bytes : List Nat)
  deriving DecidableEq, Repr

/-- A witness program's version: OP_0 or OP_1..OP_16, then a single push of 2 to 40 bytes that ends the
script (BIP141), version 0 taking only 20 or 32. BIP350 writes every version as an address. -/
def witness : List Nat → Option Nat
  | op :: n :: prog =>
    if n = prog.length ∧ 2 ≤ n ∧ n ≤ 40 then
      if op = 0 then (if n = 20 ∨ n = 32 then some 0 else none)
      else if 0x51 ≤ op ∧ op ≤ 0x60 then some (op - 0x50) else none
    else none
  | _ => none

def shown (net : Net) (b : List Nat) : Shown :=
  match witness b with
  | some v => .segwit v (b.drop 2)
  | none =>
    if b.length = 25 ∧ b.take 3 = [0x76, 0xa9, 0x14] ∧ b.drop 23 = [0x88, 0xac] then
      .base58 (pkhVersion net) ((b.drop 3).take 20)
    else if b.length = 23 ∧ b.take 2 = [0xa9, 0x14] ∧ b.drop 22 = [0x87] then
      .base58 (shVersion net) ((b.drop 2).take 20)
    else .raw b

def unshown (net : Net) : Shown → List Nat
  | .segwit v prog => (if v = 0 then 0 else v + 0x50) :: prog.length :: prog
  | .base58 v hash => if v = pkhVersion net then [0x76, 0xa9, 0x14] ++ hash ++ [0x88, 0xac]
                      else [0xa9, 0x14] ++ hash ++ [0x87]
  | .raw b => b

def renderShown (cs : Checksums) (net : Net) : Shown → List Char
  | .segwit v prog => segwitAddress cs net v prog
  | .base58 v hash => base58Address cs v hash
  | .raw b => "script:".toList ++ hex b

/-- What the screen writes for an output script on `net`. -/
def render (cs : Checksums) (net : Net) (spk : Script) : List Char :=
  renderShown cs net (shown net (spk.map (·.toNat)))

/-! ## One address, one script -/

theorem groupCount_inj {m n : Nat} (h : groupCount m = groupCount n) : m = n := by
  unfold groupCount at h; omega

theorem groups_length (prog : List Nat) : (groups prog).length = groupCount prog.length := by
  simp [groups, fixedDigits_length]

/-- The padded number fits its groups: `256 ^ n * 2 ^ pad = 32 ^ groupCount n`. -/
theorem groups_bound (n : Nat) : 256 ^ n * 2 ^ (5 * groupCount n - 8 * n) = 32 ^ groupCount n := by
  have h1 : (256 : Nat) = 2 ^ 8 := rfl
  have h2 : (32 : Nat) = 2 ^ 5 := rfl
  rw [h1, h2, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
  congr 1; unfold groupCount; omega

theorem groups_inj {p q : List Nat} (hp : ∀ d ∈ p, d < 256) (hq : ∀ d ∈ q, d < 256)
    (h : groups p = groups q) : p = q := by
  have hlen := congrArg List.length h
  rw [groups_length, groups_length] at hlen
  have hl := groupCount_inj hlen
  unfold groups at h
  rw [hl] at h
  have pos : 0 < 2 ^ (5 * groupCount q.length - 8 * q.length) := Nat.pow_pos (by decide)
  have bp := ofDigits_lt p hp
  have bq := ofDigits_lt q hq
  rw [hl] at bp
  have e := fixedDigits_inj
    (by rw [← groups_bound]; exact Nat.mul_lt_mul_of_pos_right bp pos)
    (by rw [← groups_bound]; exact Nat.mul_lt_mul_of_pos_right bq pos) h
  exact ofDigits_inj hp hq hl (Nat.eq_of_mul_eq_mul_right pos e)

theorem segwitAddress_inj {cs : Checksums} {net : Net} {v w : Nat} {p q : List Nat} (hv : v < 32) (hw : w < 32)
    (hp : ∀ d ∈ p, d < 256) (hq : ∀ d ∈ q, d < 256)
    (h : segwitAddress cs net v p = segwitAddress cs net w q) : v = w ∧ p = q := by
  simp only [segwitAddress, List.append_cancel_left_eq, List.cons.injEq, true_and, List.map_append] at h
  obtain ⟨hd, -⟩ := List.append_inj h (by
    have := congrArg List.length h
    simp only [List.length_append, List.length_map, cs.bech32_length] at this ⊢; omega)
  have lt := fixedDigits_lt (show 0 < 32 by decide)
  have hd' := map_char32_inj (l := v :: groups p) (m := w :: groups q)
    (by intro d hd; simp at hd; rcases hd with rfl | hd; exact hv; exact lt _ _ d hd)
    (by intro d hd; simp at hd; rcases hd with rfl | hd; exact hw; exact lt _ _ d hd) hd
  simp only [List.cons.injEq] at hd'
  exact ⟨hd'.1, groups_inj hp hq hd'.2⟩

theorem map_eq_self {f : Nat → Nat} : ∀ {l : List Nat}, (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | a :: l, h => by
    have ih : l.map f = l := map_eq_self (l := l) fun x hx => h x (List.mem_cons_of_mem a hx)
    simp [h a (by simp), ih]

/-- base58 read back as a number: a leading '1' is a zero digit, which adds nothing. -/
def value58 (s : List Char) : Nat := ofDigits 58 (s.map index58)

theorem value58_base58 (p : List Nat) : value58 (base58 p) = ofDigits 256 p := by
  unfold value58 base58
  simp only [List.map_append, List.map_replicate]
  have h1 : index58 '1' = 0 := by decide
  rw [h1, ofDigits_zeros]
  split
  · simp_all [ofDigits]
  · rename_i hn
    rw [List.map_map]
    have : (fixedDigits 58 (numDigits 58 (ofDigits 256 p)) (ofDigits 256 p)).map (index58 ∘ char58) =
        fixedDigits 58 (numDigits 58 (ofDigits 256 p)) (ofDigits 256 p) := by
      exact map_eq_self fun d hd => index58_char58 d (fixedDigits_lt (by decide) _ _ d hd)
    rw [this, ofDigits_fixed, Nat.mod_eq_of_lt (lt_pow_numDigits (by decide) _)]

theorem base58Address_inj {cs : Checksums} {v w : Nat} {p q : List Nat} (hv : v < 256) (hw : w < 256)
    (hp : ∀ d ∈ p, d < 256) (hq : ∀ d ∈ q, d < 256) (hpl : p.length = 20) (hql : q.length = 20)
    (h : base58Address cs v p = base58Address cs w q) : v = w ∧ p = q := by
  have e := congrArg value58 h
  simp only [base58Address, value58_base58] at e
  have ok : ∀ u r, u < 256 → (∀ d ∈ r, d < 256) → ∀ d ∈ u :: r ++ cs.base58 (u :: r), d < 256 := by
    intro u r hu hr d hd
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hd
    rcases hd with rfl | hd | hd
    · exact hu
    · exact hr d hd
    · exact cs.base58_lt _ d hd
  have e' := ofDigits_inj (ok v p hv hp) (ok w q hw hq) (by simp [cs.base58_length, hpl, hql]) e
  obtain ⟨e'', -⟩ := List.append_inj e' (by simp [hpl, hql])
  simp only [List.cons.injEq] at e''
  exact e''

theorem char32_ne_colon (d : Nat) : char32 d ≠ ':' := by
  unfold char32
  by_cases h : d < 32
  · exact (by decide : ∀ d, d < 32 → charset32.getD d '?' ≠ ':') d h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show charset32.length ≤ d by simp [charset32]; omega)]

theorem char58_ne_colon (d : Nat) : char58 d ≠ ':' := by
  unfold char58
  by_cases h : d < 58
  · exact (by decide : ∀ d, d < 58 → charset58.getD d '?' ≠ ':') d h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show charset58.length ≤ d by simp [charset58]; omega)]

theorem colon_not_segwit (cs : Checksums) (net : Net) (v : Nat) (p : List Nat) : ':' ∉ segwitAddress cs net v p := by
  intro h
  simp only [segwitAddress, List.mem_append, List.mem_cons, List.mem_map] at h
  rcases h with h | h | ⟨d, -, hd⟩
  · cases net <;> revert h <;> decide
  · exact absurd h (by decide)
  · exact char32_ne_colon d hd

theorem colon_not_base58 (cs : Checksums) (v : Nat) (p : List Nat) : ':' ∉ base58Address cs v p := by
  intro h
  simp only [base58Address, base58, List.mem_append, List.mem_replicate] at h
  rcases h with ⟨-, h⟩ | h
  · exact absurd h (by decide)
  · split at h
    · simp at h
    · simp only [List.mem_map] at h; obtain ⟨d, -, hd⟩ := h; exact char58_ne_colon d hd

theorem colon_raw (b : List Nat) : ':' ∈ "script:".toList ++ hex b := List.mem_append_left _ (by decide)

/-- What `shown` produces from a script's bytes. -/
def Good (net : Net) : Shown → Prop
  | .segwit v p => v ≤ 16 ∧ 2 ≤ p.length ∧ p.length ≤ 40 ∧ ∀ d ∈ p, d < 256
  | .base58 v h => (v = pkhVersion net ∨ v = shVersion net) ∧ h.length = 20 ∧ ∀ d ∈ h, d < 256
  | .raw b => ∀ d ∈ b, d < 256

theorem version_lt (net : Net) {v : Nat} (h : v = pkhVersion net ∨ v = shVersion net) : v < 256 := by
  cases net <;> rcases h with rfl | rfl <;> decide

theorem foldl_digits (b : Nat) : ∀ (l : List Nat) (a : Nat),
    l.foldl (fun acc d => acc * b + d) a = a * b ^ l.length + l.foldl (fun acc d => acc * b + d) 0
  | [], a => by simp
  | x :: l, a => by
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [foldl_digits b l (a * b + x), foldl_digits b l x, Nat.pow_succ, Nat.add_mul, Nat.add_assoc,
      Nat.mul_right_comm a b, Nat.mul_assoc a]

theorem ofDigits_cons (b d : Nat) (l : List Nat) : ofDigits b (d :: l) = d * b ^ l.length + ofDigits b l := by
  unfold ofDigits
  rw [List.foldl_cons, Nat.zero_mul, Nat.zero_add, foldl_digits]

theorem head_fixedDigits (b : Nat) : ∀ k n, (fixedDigits b (k + 1) n).head? = some (n / b ^ k % b)
  | 0, n => by simp [fixedDigits]
  | k + 1, n => by
    rw [fixedDigits, List.head?_append, head_fixedDigits b k (n / b), Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    rfl

theorem numDigits_eq {b k n : Nat} (hb : 2 ≤ b) (lo : b ^ k ≤ n) (hi : n < b ^ (k + 1)) : numDigits b n = k + 1 := by
  have h1 := numDigits_le hb hi (by omega)
  have h2 := lt_pow_numDigits hb n
  have : k < numDigits b n := by
    apply Nat.lt_of_not_le
    intro hc
    have := Nat.pow_le_pow_right (show 0 < b by omega) hc
    omega
  omega

/-- A base58check payload's first base58 character, when its version byte puts the payload in
`[v * 256 ^ 24, (v + 1) * 256 ^ 24)`: that range fixes the digit count and the leading digit's span. -/
theorem base58_lead {v k : Nat} {rest : List Nat} (hv : 0 < v) (hl : rest.length = 24) (hr : ∀ d ∈ rest, d < 256)
    (lo : 58 ^ k ≤ v * 256 ^ 24) (hi : (v + 1) * 256 ^ 24 ≤ 58 ^ (k + 1)) :
    ∃ d, v * 256 ^ 24 / 58 ^ k ≤ d ∧ d ≤ ((v + 1) * 256 ^ 24 - 1) / 58 ^ k ∧
      (base58 (v :: rest)).head? = some (char58 d) := by
  have hn : ofDigits 256 (v :: rest) = v * 256 ^ 24 + ofDigits 256 rest := by rw [ofDigits_cons, hl]
  have hrest := ofDigits_lt rest hr
  rw [hl] at hrest
  have hz : (v :: rest).takeWhile (· == 0) = [] := by
    simp only [List.takeWhile_cons]; rw [ite_eq_right (by simp; omega)]
  have hP0 : 0 < (256 : Nat) ^ 24 := Nat.pow_pos (by decide)
  generalize (256 : Nat) ^ 24 = P at hn hrest lo hi hP0 ⊢
  generalize hN : ofDigits 256 (v :: rest) = N at hn
  have nlo : v * P ≤ N := by omega
  have nhi : N < (v + 1) * P := by rw [Nat.add_mul, Nat.one_mul]; omega
  have hne : N ≠ 0 := by have := Nat.mul_pos hv hP0; omega
  have hk := numDigits_eq (b := 58) (by decide) (Nat.le_trans lo nlo) (Nat.lt_of_lt_of_le nhi hi)
  have hlt : N / 58 ^ k < 58 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_succ']; exact Nat.lt_of_lt_of_le nhi hi
  refine ⟨N / 58 ^ k, Nat.div_le_div_right nlo, Nat.div_le_div_right (by omega), ?_⟩
  simp only [base58, hz, List.length_nil, List.replicate_zero, List.nil_append]
  rw [hN, ite_eq_right hne, hk, List.head?_map, head_fixedDigits, Nat.mod_eq_of_lt hlt]
  rfl

theorem segwit_head (cs : Checksums) (net : Net) (v : Nat) (p : List Nat) :
    (segwitAddress cs net v p).head? = (hrp net).head? := by
  cases net <;> rfl

/-- A base58 address on a network never starts with the letter a segwit address there starts with. -/
theorem base58_head (cs : Checksums) (net : Net) {v : Nat} {h : List Nat} (hv : v = pkhVersion net ∨ v = shVersion net)
    (hl : h.length = 20) (hd : ∀ d ∈ h, d < 256) : (base58Address cs v h).head? ≠ (hrp net).head? := by
  have rl : (h ++ cs.base58 (v :: h)).length = 24 := by simp [hl, cs.base58_length]
  have rd : ∀ d ∈ h ++ cs.base58 (v :: h), d < 256 := by
    intro d hm; rcases List.mem_append.mp hm with hm | hm
    · exact hd d hm
    · exact cs.base58_lt _ d hm
  have lead : ∀ k, 0 < v → 58 ^ k ≤ v * 256 ^ 24 → (v + 1) * 256 ^ 24 ≤ 58 ^ (k + 1) →
      (∀ d, d < 58 → v * 256 ^ 24 / 58 ^ k ≤ d → d ≤ ((v + 1) * 256 ^ 24 - 1) / 58 ^ k → [char58 d].head? ≠ (hrp net).head?) →
      (base58Address cs v h).head? ≠ (hrp net).head? := by
    intro k hv0 lo hi hc
    obtain ⟨d, d1, d2, e⟩ := base58_lead hv0 rl rd lo hi
    unfold base58Address
    rw [List.cons_append, e]
    have : d < 58 := by
      have : ((v + 1) * 256 ^ 24 - 1) / 58 ^ k < 58 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_succ']
        have := Nat.pow_pos (n := k + 1) (show 0 < 58 by decide)
        generalize (v + 1) * 256 ^ 24 = Q at hi ⊢
        omega
      omega
    exact hc d this d1 d2
  cases net <;> rcases hv with rfl | rfl
  · -- version 0: the leading zero byte is written as '1'
    unfold base58Address base58
    simp only [pkhVersion, List.cons_append, List.takeWhile_cons, beq_self_eq_true, ↓reduceIte,
      List.length_cons, List.replicate_succ, List.cons_append, List.head?_cons, hrp]
    decide
  · exact lead 33 (by decide) (by decide) (by decide) (by decide)
  · exact lead 33 (by decide) (by decide) (by decide) (by decide)
  · exact lead 34 (by decide) (by decide) (by decide) (by decide)
  · exact lead 33 (by decide) (by decide) (by decide) (by decide)
  · exact lead 34 (by decide) (by decide) (by decide) (by decide)

theorem renderShown_inj {cs : Checksums} {net : Net} {s t : Shown} (gs : Good net s) (gt : Good net t)
    (h : renderShown cs net s = renderShown cs net t) : s = t := by
  cases s with
  | segwit v p =>
    cases t with
    | segwit w q =>
      obtain ⟨e1, e2⟩ := segwitAddress_inj (Nat.lt_of_le_of_lt gs.1 (by decide)) (Nat.lt_of_le_of_lt gt.1 (by decide))
        gs.2.2.2 gt.2.2.2 h
      rw [e1, e2]
    | base58 w q =>
      have e := congrArg List.head? h
      simp only [renderShown] at e
      exact (base58_head cs net gt.1 gt.2.1 gt.2.2 (e ▸ segwit_head cs net v p)).elim
    | raw b =>
      have hc := colon_raw b
      exact (colon_not_segwit cs net v p (by rw [show segwitAddress cs net v p = _ from h]; exact hc)).elim
  | base58 v p =>
    cases t with
    | segwit w q =>
      have e := congrArg List.head? h
      simp only [renderShown] at e
      exact (base58_head cs net gs.1 gs.2.1 gs.2.2 (e.symm ▸ segwit_head cs net w q)).elim
    | base58 w q =>
      obtain ⟨e1, e2⟩ := base58Address_inj (version_lt net gs.1) (version_lt net gt.1) gs.2.2 gt.2.2 gs.2.1 gt.2.1 h
      rw [e1, e2]
    | raw b =>
      have hc := colon_raw b
      exact (colon_not_base58 cs v p (by rw [show base58Address cs v p = _ from h]; exact hc)).elim
  | raw b =>
    cases t with
    | segwit w q =>
      have hc := colon_raw b
      exact (colon_not_segwit cs net w q (by rw [show segwitAddress cs net w q = _ from h.symm]; exact hc)).elim
    | base58 w q =>
      have hc := colon_raw b
      exact (colon_not_base58 cs w q (by rw [show base58Address cs w q = _ from h.symm]; exact hc)).elim
    | raw c =>
      simp only [renderShown, List.append_cancel_left_eq] at h
      rw [hex_inj gs gt h]

theorem witness_some {b : List Nat} {v : Nat} (h : witness b = some v) :
    ∃ op prog, b = op :: prog.length :: prog ∧ 2 ≤ prog.length ∧ prog.length ≤ 40 ∧ v ≤ 16 ∧
      op = (if v = 0 then 0 else v + 0x50) := by
  cases b with
  | nil => simp [witness] at h
  | cons op t =>
    cases t with
    | nil => simp [witness] at h
    | cons n prog =>
      simp only [witness] at h
      by_cases hc : n = prog.length ∧ 2 ≤ n ∧ n ≤ 40
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
        obtain ⟨rfl, h2, h40⟩ := hc
        by_cases h0 : op = 0
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)] at h
          split at h
          · cases h; exact ⟨op, prog, rfl, h2, h40, by decide, by simp [h0]⟩
          · simp at h
        · rw [ite_eq_right h0] at h
          split at h
          · rename_i hr
            cases h
            refine ⟨op, prog, rfl, h2, h40, by omega, ?_⟩
            rw [ite_eq_right (by omega)]
            omega
          · simp at h
      · rw [ite_eq_right hc] at h; simp at h

theorem shown_good (net : Net) (b : List Nat) (hb : ∀ d ∈ b, d < 256) : Good net (shown net b) := by
  have hd : ∀ n, ∀ d ∈ b.drop n, d < 256 := fun n d h => hb d (List.mem_of_mem_drop h)
  have ht : ∀ n m, ∀ d ∈ (b.drop n).take m, d < 256 := fun n m d h => hd n d (List.mem_of_mem_take h)
  unfold shown
  split
  · rename_i v hw
    obtain ⟨op, prog, rfl, h2, h40, hv, -⟩ := witness_some hw
    exact ⟨hv, h2, h40, hd 2⟩
  split
  · rename_i h; exact ⟨Or.inl rfl, by simp [h.1], ht 3 20⟩
  split
  · rename_i h; exact ⟨Or.inr rfl, by simp [h.1], ht 2 20⟩
  · exact hb

theorem sh_ne_pkh (net : Net) : shVersion net ≠ pkhVersion net := by cases net <;> decide

theorem unshown_shown (net : Net) (b : List Nat) : unshown net (shown net b) = b := by
  unfold shown
  split
  · rename_i v hw
    obtain ⟨op, prog, rfl, -, -, -, rfl⟩ := witness_some hw
    rfl
  split
  · rename_i h
    simp only [unshown, ↓reduceIte, ← h.2.1, ← h.2.2, List.append_assoc]
    have : b.drop 23 = (b.drop 3).drop 20 := by simp [List.drop_drop]
    rw [this, List.take_append_drop, List.take_append_drop]
  split
  · rename_i h
    simp only [unshown, sh_ne_pkh, ↓reduceIte, ← h.2.1, ← h.2.2, List.append_assoc]
    have : b.drop 22 = (b.drop 2).drop 20 := by simp [List.drop_drop]
    rw [this, List.take_append_drop, List.take_append_drop]
  · rfl

theorem map_toNat_inj : ∀ {s t : Script}, s.map (·.toNat) = t.map (·.toNat) → s = t
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: s, c :: t, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [UInt8.toNat_inj.mp h.1, map_toNat_inj h.2]

/-- Two different output scripts are never written the same on a network's screen. -/
theorem render_inj {cs : Checksums} {net : Net} {s t : Script} (h : render cs net s = render cs net t) : s = t := by
  have lt : ∀ u : Script, ∀ d ∈ u.map (·.toNat), d < 256 := by
    intro u d hd; simp only [List.mem_map] at hd; obtain ⟨x, -, rfl⟩ := hd; exact x.toNat_lt
  have e := renderShown_inj (shown_good net _ (lt s)) (shown_good net _ (lt t)) h
  have := congrArg (unshown net) e
  rw [unshown_shown, unshown_shown] at this
  exact map_toNat_inj this

end SignerSpec
