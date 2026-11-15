import SignerSpec.Sessions
import SignerSpec.Notation

/-!
# What a signature commits to

`Sessions.lean` takes as given what a signature verifies against (`SigValid`). This file derives it
from the BIP143 and BIP341 digests themselves. SHA-256 is a parameter `H` assumed one to one with
32-byte output: collision resistance, which is not provable, stated as the only assumption.

BIP143 does not commit to the amounts of other inputs: `v0_other_amounts` shows a digest that stays the
same while the fee changes. BIP341 commits to all of them (`tr_binds`). The model's rule that a BIP143
signer with several inputs checks every previous transaction rests on the first; `Sessions.lean` needs both.
-/

namespace SignerSpec

/-! ## Encodings -/

/-- `n` as `k` little-endian bytes. -/
def le (k n : Nat) : List UInt8 := ((fixedDigits 256 k n).map UInt8.ofNat).reverse

/-- Bitcoin's CompactSize. -/
def varint (n : Nat) : List UInt8 :=
  if n < 0xfd then [UInt8.ofNat n]
  else if n < 2 ^ 16 then 0xfd :: le 2 n
  else if n < 2 ^ 32 then 0xfe :: le 4 n
  else 0xff :: le 8 n

def varstr (s : List UInt8) : List UInt8 := varint s.length ++ s

def serOut (o : Nat × Script) : List UInt8 := le 8 o.1 ++ varstr o.2

theorem le_length (k n : Nat) : (le k n).length = k := by simp [le, fixedDigits_length]

theorem map_toNat_ofNat : ∀ {l : List Nat}, (∀ d ∈ l, d < 256) → (l.map UInt8.ofNat).map UInt8.toNat = l
  | [], _ => rfl
  | d :: l, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨by simpa using Nat.mod_eq_of_lt (h d (by simp)), map_toNat_ofNat fun e he => h e (by simp [he])⟩

theorem le_inj {k m n : Nat} (hm : m < 256 ^ k) (hn : n < 256 ^ k) (h : le k m = le k n) : m = n := by
  have h1 := congrArg (List.map UInt8.toNat) (List.reverse_inj.mp (by simpa [le] using h))
  rw [map_toNat_ofNat (fixedDigits_lt (by omega) k m), map_toNat_ofNat (fixedDigits_lt (by omega) k n)] at h1
  exact fixedDigits_inj hm hn h1

theorem ofNat_inj {m n : Nat} (hm : m < 256) (hn : n < 256) (h : UInt8.ofNat m = UInt8.ofNat n) : m = n := by
  have := congrArg UInt8.toNat h
  simpa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] using this

/-- A code is prefix-free on `P`: an encoding never starts another one. -/
def PrefixFree {α} (P : α → Prop) (f : α → List UInt8) : Prop :=
  ∀ a b r s, P a → P b → f a ++ r = f b ++ s → a = b ∧ r = s

theorem varint_prefix : PrefixFree (· < 2 ^ 64) varint := by
  intro a b r s ha hb h
  have hd : ∀ {x y k : Nat}, x < 256 ^ k → y < 256 ^ k →
      le k x ++ r = le k y ++ s → x = y ∧ r = s := by
    intro x y k hx hy h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [le_length])
    exact ⟨le_inj hx hy h1, h2⟩
  have c : ∀ {x : Nat}, x < 0xfd → ∀ {c : UInt8}, c.toNat ≥ 0xfd → UInt8.ofNat x ≠ c := by
    intro x hx c hc he
    have := congrArg UInt8.toNat he
    simp [Nat.mod_eq_of_lt (show x < 256 by omega)] at this
    omega
  unfold varint at h
  by_cases a1 : a < 0xfd <;> by_cases b1 : b < 0xfd <;> simp only [a1, b1, ↓reduceIte] at h
  · simp only [List.singleton_append, List.cons.injEq] at h
    exact ⟨ofNat_inj (by omega) (by omega) h.1, h.2⟩
  all_goals
    by_cases a2 : a < 2 ^ 16 <;> by_cases b2 : b < 2 ^ 16 <;> simp only [a2, b2, ↓reduceIte] at h
  all_goals
    try (by_cases a3 : a < 2 ^ 32 <;> simp only [a3, ↓reduceIte] at h)
  all_goals
    try (by_cases b3 : b < 2 ^ 32 <;> simp only [b3, ↓reduceIte] at h)
  all_goals simp only [List.cons_append, List.cons.injEq] at h
  all_goals
    first
    | exact absurd h.1 (c a1 (by decide))
    | exact absurd h.1.symm (c b1 (by decide))
    | exact absurd h.1 (by decide)
    | exact hd (by omega) (by omega) h.2

theorem varstr_prefix : PrefixFree (fun s : List UInt8 => s.length < 2 ^ 64) varstr := by
  intro a b r s ha hb h
  simp only [varstr, List.append_assoc] at h
  obtain ⟨hl, h⟩ := varint_prefix _ _ _ _ ha hb h
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  exact ⟨h1, h2⟩

theorem fixed_prefix (k : Nat) : PrefixFree (fun s : List UInt8 => s.length = k) id := by
  intro a b r s ha hb h
  exact List.append_inj h (by simp [ha, hb])

theorem le_prefix (k : Nat) : PrefixFree (· < 256 ^ k) (le k) := by
  intro a b r s ha hb h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [le_length])
  exact ⟨le_inj ha hb h1, h2⟩

def OutOk (o : Nat × Script) : Prop := o.1 < 2 ^ 64 ∧ o.2.length < 2 ^ 64

theorem serOut_prefix : PrefixFree OutOk serOut := by
  intro a b r s ha hb h
  simp only [serOut, List.append_assoc] at h
  obtain ⟨h1, h⟩ := le_prefix 8 _ _ _ _ (by have := ha.1; omega) (by have := hb.1; omega) h
  obtain ⟨h2, h⟩ := varstr_prefix _ _ _ _ ha.2 hb.2 h
  exact ⟨Prod.ext h1 h2, h⟩

/-- Concatenating codewords of a prefix-free code loses nothing. -/
theorem flatMap_inj {α} {P : α → Prop} {f : α → List UInt8} (hf : PrefixFree P f) (hne : ∀ a, P a → f a ≠ []) :
    ∀ {l m : List α}, (∀ a ∈ l, P a) → (∀ b ∈ m, P b) → l.flatMap f = m.flatMap f → l = m
  | [], [], _, _, _ => rfl
  | [], b :: _, _, hm, h => by
    simp only [List.flatMap_nil, List.flatMap_cons] at h
    exact absurd (List.append_eq_nil_iff.mp h.symm).1 (hne b (hm b (by simp)))
  | a :: _, [], hl, _, h => by
    simp only [List.flatMap_nil, List.flatMap_cons] at h
    exact absurd (List.append_eq_nil_iff.mp h).1 (hne a (hl a (by simp)))
  | a :: l, b :: m, hl, hm, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨rfl, h'⟩ := hf _ _ _ _ (hl a (by simp)) (hm b (by simp)) h
    rw [flatMap_inj hf hne (fun x hx => hl x (by simp [hx])) (fun x hx => hm x (by simp [hx])) h']

theorem le_ne_nil {k n : Nat} (hk : 0 < k) : le k n ≠ [] := by
  intro h; have := congrArg List.length h; simp [le_length] at this; omega

theorem varint_ne_nil (n : Nat) : varint n ≠ [] := by
  unfold varint; split
  · simp
  · split
    · simp
    · split <;> simp

theorem flatMap_congr {α β} {l m : List α} (g : α → β) (F : β → List UInt8) (h : l.map g = m.map g) :
    l.flatMap (fun x => F (g x)) = m.flatMap (fun x => F (g x)) := by
  induction l generalizing m with
  | nil => cases m <;> simp_all
  | cons a l ih =>
    cases m with
    | nil => simp at h
    | cons b m =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.flatMap_cons, h.1, ih h.2]

/-! ## The two digests -/

structure TxIn where
  /-- txid and vout, 36 bytes. -/
  outpoint : List UInt8
  sequence : Nat
  amount : Nat
  spk : Script

structure SigTx where
  version : Nat
  locktime : Nat
  inputs : List TxIn
  outputs : List (Nat × Script)

def InOk (x : TxIn) : Prop := x.outpoint.length = 36 ∧ x.sequence < 2 ^ 32 ∧ x.amount < 2 ^ 64 ∧ x.spk.length < 2 ^ 64

/-- What a transaction can hold at all: fixed-width fields fit their width. -/
def SigTx.Ok (t : SigTx) : Prop := (∀ x ∈ t.inputs, InOk x) ∧ ∀ o ∈ t.outputs, OutOk o

variable (H : List UInt8 → List UInt8)

def SigTx.outpoints (t : SigTx) : List UInt8 := t.inputs.flatMap (·.outpoint)
def SigTx.sequences (t : SigTx) : List UInt8 := t.inputs.flatMap (le 4 ·.sequence)
def SigTx.amounts (t : SigTx) : List UInt8 := t.inputs.flatMap (le 8 ·.amount)
def SigTx.spks (t : SigTx) : List UInt8 := t.inputs.flatMap (varstr ·.spk)
def SigTx.outs (t : SigTx) : List UInt8 := t.outputs.flatMap serOut

/-- BIP143 under SIGHASH_ALL, for input `j` with this script code; ECDSA signs its double SHA-256. -/
def preV0 (t : SigTx) (j : Nat) (code : Script) : List UInt8 :=
  match t.inputs[j]? with
  | none => []
  | some x => le 4 t.version ++ H (H t.outpoints) ++ H (H t.sequences) ++ x.outpoint ++ varstr code ++
      le 8 x.amount ++ le 4 x.sequence ++ H (H t.outs) ++ le 4 t.locktime ++ le 4 1

/-- BIP341 key path under SIGHASH_DEFAULT (`ht = 0`) or ALL, no annex; Schnorr signs its tagged hash. -/
def preTr (t : SigTx) (j ht : Nat) : List UInt8 :=
  [0, UInt8.ofNat ht] ++ le 4 t.version ++ le 4 t.locktime ++ H t.outpoints ++ H t.amounts ++ H t.spks ++
    H t.sequences ++ H t.outs ++ [0] ++ le 4 j

def digestV0 (t : SigTx) (j : Nat) (code : Script) : List UInt8 := H (H (preV0 H t j code))

def digestTr (t : SigTx) (j ht : Nat) : List UInt8 :=
  let tag := H "TapSighash".toUTF8.toList
  H (tag ++ tag ++ preTr H t j ht)

/-! ## BIP143 does not see the other inputs' amounts -/

/-- Two transactions that differ only in the amounts of inputs other than `j` give input `j` the same
BIP143 digest, whatever those amounts are, and so whatever fee they make. -/
theorem v0_other_amounts {t t' : SigTx} {j : Nat} (code : Script) (hv : t'.version = t.version)
    (hl : t'.locktime = t.locktime) (ho : t'.outputs = t.outputs)
    (hp : t'.inputs.map (fun x => (x.outpoint, x.sequence)) = t.inputs.map (fun x => (x.outpoint, x.sequence)))
    (hj : t'.inputs[j]? = t.inputs[j]?) : digestV0 H t' j code = digestV0 H t j code := by
  have hop : t'.outpoints = t.outpoints := by
    have := flatMap_congr _ (fun p => p.1) hp
    simpa only [SigTx.outpoints] using this
  have hsq : t'.sequences = t.sequences := by
    have := flatMap_congr _ (fun p => le 4 p.2) hp
    simpa only [SigTx.sequences] using this
  unfold digestV0 preV0 SigTx.outs
  rw [hj, hv, hl, ho, hop, hsq]

/-- Changing the amount of another input: the BIP143 digest of input `j` stays, the fee does not. -/
theorem v0_blind {t : SigTx} {j k : Nat} (code : Script) (hk : k ≠ j) (x : TxIn) (hx : t.inputs[k]? = some x)
    (a : Nat) :
    let t' := { t with inputs := t.inputs.set k { x with amount := a } }
    digestV0 H t' j code = digestV0 H t j code ∧
      (t'.inputs.map (·.amount)).sum + x.amount = (t.inputs.map (·.amount)).sum + a := by
  intro t'
  have hkl : k < t.inputs.length := (List.getElem?_eq_some_iff.mp hx).1
  have hxk : t.inputs[k] = x := by simpa [hkl] using hx
  refine ⟨v0_other_amounts H code rfl rfl rfl ?_ ?_, ?_⟩
  · apply List.ext_getElem?
    intro n
    simp only [t', List.getElem?_map, List.getElem?_set]
    split <;> simp_all
  · simp [t', hk]
  · simp only [t', List.map_set]
    have hs : ∀ (l : List Nat) (i : Nat) (h : i < l.length) (v : Nat), (l.set i v).sum + l[i] = l.sum + v := by
      intro l; induction l with
      | nil => intro i h; simp at h
      | cons y l ih =>
        intro i h v
        cases i with
        | zero => simp; omega
        | succ i => simp at h ⊢; have := ih i h v; omega
    have := hs (t.inputs.map (·.amount)) k (by simpa using hkl) a
    simpa [hxk] using this

/-! ## What each digest binds -/

/-- Collision resistance, as the model takes it: SHA-256 is one to one, 32 bytes out. -/
structure HashOk : Prop where
  /-- One to one. -/
  inj : ∀ a b, H a = H b → a = b
  /-- 32 bytes out. -/
  len : ∀ m, (H m).length = 32

theorem flatMap_map' {α β} (l : List α) (g : α → β) (F : β → List UInt8) :
    l.flatMap (fun x => F (g x)) = (l.map g).flatMap F := by
  induction l <;> simp_all

theorem pow64 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide

variable {H}

theorem amounts_inj {t t' : SigTx} (ht : t.Ok) (ht' : t'.Ok) (h : t.amounts = t'.amounts) :
    t.inputs.map (·.amount) = t'.inputs.map (·.amount) := by
  simp only [SigTx.amounts, flatMap_map' _ TxIn.amount (le 8)] at h
  refine flatMap_inj (le_prefix 8) (fun _ _ => le_ne_nil (by decide)) ?_ ?_ h <;>
    simp only [List.mem_map] <;> rintro _ ⟨x, hx, rfl⟩
  · rw [← pow64]; exact (ht.1 x hx).2.2.1
  · rw [← pow64]; exact (ht'.1 x hx).2.2.1

theorem outs_inj {t t' : SigTx} (ht : t.Ok) (ht' : t'.Ok) (h : t.outs = t'.outs) : t.outputs = t'.outputs :=
  flatMap_inj serOut_prefix (fun _ _ h => le_ne_nil (k := 8) (by decide) (List.append_eq_nil_iff.mp h).1)
    ht.2 ht'.2 h

theorem outpoints_inj {t t' : SigTx} (ht : t.Ok) (ht' : t'.Ok) (h : t.outpoints = t'.outpoints) :
    t.inputs.map (·.outpoint) = t'.inputs.map (·.outpoint) := by
  have e : ∀ l : List TxIn, l.flatMap (·.outpoint) = (l.map (·.outpoint)).flatMap id :=
    fun l => flatMap_map' l TxIn.outpoint id
  simp only [SigTx.outpoints] at h
  rw [e, e] at h
  refine flatMap_inj (fixed_prefix 36) (fun a ha h => by simp only [id] at h; simp [h] at ha) ?_ ?_ h <;>
    simp only [List.mem_map] <;> rintro _ ⟨x, hx, rfl⟩
  · exact (ht.1 x hx).1
  · exact (ht'.1 x hx).1

theorem spks_inj {t t' : SigTx} (ht : t.Ok) (ht' : t'.Ok) (h : t.spks = t'.spks) :
    t.inputs.map (·.spk) = t'.inputs.map (·.spk) := by
  simp only [SigTx.spks, flatMap_map' _ TxIn.spk varstr] at h
  refine flatMap_inj varstr_prefix (fun a _ h => varint_ne_nil a.length (List.append_eq_nil_iff.mp h).1) ?_ ?_ h <;>
    simp only [List.mem_map] <;> rintro _ ⟨x, hx, rfl⟩
  · exact (ht.1 x hx).2.2.2
  · exact (ht'.1 x hx).2.2.2

/-- A BIP341 digest fixes every input's amount and script, the outpoints spent and every output. -/
theorem tr_binds (hH : HashOk H) {t t' : SigTx} {j j' ht ht' : Nat} (hok : t.Ok) (hok' : t'.Ok)
    (h : digestTr H t j ht = digestTr H t' j' ht') :
    t.inputs.map (·.amount) = t'.inputs.map (·.amount) ∧ t.inputs.map (·.spk) = t'.inputs.map (·.spk) ∧
      t.inputs.map (·.outpoint) = t'.inputs.map (·.outpoint) ∧ t.outputs = t'.outputs := by
  have h := List.append_cancel_left (hH.inj _ _ h)
  simp only [preTr, List.append_assoc] at h
  obtain ⟨-, h⟩ := List.append_inj h rfl
  obtain ⟨-, h⟩ := List.append_inj h (by simp [le_length])
  obtain ⟨-, h⟩ := List.append_inj h (by simp [le_length])
  obtain ⟨hop, h⟩ := List.append_inj h (by simp [hH.len])
  obtain ⟨ham, h⟩ := List.append_inj h (by simp [hH.len])
  obtain ⟨hsp, h⟩ := List.append_inj h (by simp [hH.len])
  obtain ⟨-, h⟩ := List.append_inj h (by simp [hH.len])
  obtain ⟨hout, -⟩ := List.append_inj h (by simp [hH.len])
  exact ⟨amounts_inj hok hok' (hH.inj _ _ ham), spks_inj hok hok' (hH.inj _ _ hsp),
    outpoints_inj hok hok' (hH.inj _ _ hop), outs_inj hok hok' (hH.inj _ _ hout)⟩

/-- A BIP143 digest fixes the outpoints spent, every output, and the amount of its own input. -/
theorem v0_binds (hH : HashOk H) {t t' : SigTx} {j : Nat} {code : Script} {x x' : TxIn} (hok : t.Ok)
    (hok' : t'.Ok) (hx : t.inputs[j]? = some x) (hx' : t'.inputs[j]? = some x')
    (h : digestV0 H t j code = digestV0 H t' j code) :
    x.amount = x'.amount ∧ t.inputs.map (·.outpoint) = t'.inputs.map (·.outpoint) ∧ t.outputs = t'.outputs := by
  have h := hH.inj _ _ (hH.inj _ _ h)
  simp only [preV0, hx, hx', List.append_assoc] at h
  have hxo : x.outpoint.length = 36 := (hok.1 x (List.mem_of_getElem? hx)).1
  have hxo' : x'.outpoint.length = 36 := (hok'.1 x' (List.mem_of_getElem? hx')).1
  obtain ⟨-, h⟩ := List.append_inj h (by simp [le_length])
  obtain ⟨hop, h⟩ := List.append_inj h (by simp [hH.len])
  obtain ⟨-, h⟩ := List.append_inj h (by simp [hH.len])
  obtain ⟨-, h⟩ := List.append_inj h (by simp [hxo, hxo'])
  obtain ⟨-, h⟩ := List.append_inj h rfl
  obtain ⟨ham, h⟩ := List.append_inj h (by simp [le_length])
  obtain ⟨-, h⟩ := List.append_inj h (by simp [le_length])
  obtain ⟨hout, -⟩ := List.append_inj h (by simp [hH.len])
  have ha := (hok.1 x (List.mem_of_getElem? hx)).2.2.1
  have ha' := (hok'.1 x' (List.mem_of_getElem? hx')).2.2.1
  exact ⟨le_inj (by rw [← pow64]; exact ha) (by rw [← pow64]; exact ha') ham,
    outpoints_inj hok hok' (hH.inj _ _ (hH.inj _ _ hop)), outs_inj hok hok' (hH.inj _ _ (hH.inj _ _ hout))⟩

/-! ## `SigValid`, derived -/

/-- `s` is the transaction review saw, written out, and `s'` the one a coordinator assembles, `f`
its amounts and outputs. If input `j`'s signature verifies in `s'`, its digest there is the one signed,
and `SigValid` holds: what `Sessions.lean` assumed follows from the digests and collision resistance. A legacy
input's digest is not modelled, so for one `SigValid` stays an assumption. -/
theorem sigValid_of_digest (hH : HashOk H) {tx : Tx} {j : Nat} {i : Input} {f : Final} {s s' : SigTx}
    (hok : s.Ok) (hok' : s'.Ok) (hi : tx.inputs[j]? = some i)
    (ham : s.inputs.map (·.amount) = tx.inputs.map (·.amount)) (hout : s.outputs = tx.paid)
    (hfa : f.amounts = s'.inputs.map (·.amount)) (hfo : f.outputs = s'.outputs)
    (hsig : i.sighash = 1 ∨ (ScriptKind.of i.spk = .p2tr ∧ i.sighash = 0)) (hl : ScriptKind.of i.spk ≠ .p2pkh)
    (hd : if ScriptKind.of i.spk = .p2tr then digestTr H s j i.sighash = digestTr H s' j i.sighash
          else ∃ code, digestV0 H s j code = digestV0 H s' j code) :
    SigValid tx j f := by
  have hlen : s.inputs.length = tx.inputs.length := by simpa using congrArg List.length ham
  have hj : j < s.inputs.length := hlen ▸ (List.getElem?_eq_some_iff.mp hi).1
  have hxa : s.inputs[j].amount = i.amount := by
    have := congrArg (·[j]?) ham
    simp only [List.getElem?_map, hi, List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq] at this
    exact this
  -- Both digests fix the outpoints, so `s'` spends as many inputs, and every output
  have common : s.inputs.map (·.outpoint) = s'.inputs.map (·.outpoint) ∧ s.outputs = s'.outputs →
      f.amounts.length = tx.inputs.length ∧ f.outputs = tx.paid := fun ⟨hop, ho⟩ =>
    ⟨by rw [hfa, ← hlen]; simpa using (congrArg List.length hop).symm, by rw [hfo, ← ho, hout]⟩
  refine ⟨i, hi, ?_⟩
  by_cases ht : ScriptKind.of i.spk = .p2tr
  · simp only [ht, ite_true] at hd
    obtain ⟨ha, -, hop, ho⟩ := tr_binds hH hok hok' hd
    obtain ⟨hl, hp⟩ := common ⟨hop, ho⟩
    have : i.sighash < 0x80 := by omega
    simp only [ht, this, and_self, ite_true]
    exact ⟨hl, fun _ => hp, by rw [hfa, ← ha, ham]⟩
  · simp only [ht, ite_false] at hd
    obtain ⟨code, hd⟩ := hd
    have hj' : j < s'.inputs.length := by
      cases e : s'.inputs[j]? with
      | some _ => exact (List.getElem?_eq_some_iff.mp e).1
      | none =>
        have := congrArg List.length (hH.inj _ _ (hH.inj _ _ hd))
        simp [preV0, e, List.getElem?_eq_getElem hj, le_length] at this
    obtain ⟨ha, hop, ho⟩ := v0_binds hH hok hok' (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj') hd
    obtain ⟨hl', hp⟩ := common ⟨hop, ho⟩
    simp only [ht, hl, false_and, ite_false]
    exact ⟨hl', fun _ => hp, by rw [hfa, List.getElem?_map, List.getElem?_eq_getElem hj', Option.map_some, ← ha, hxa]⟩

end SignerSpec
