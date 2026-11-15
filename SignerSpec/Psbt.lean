import SignerSpec.Txid

/-!
# Reading a PSBT one way

A PSBT (BIP174, version 0) is the magic, a global map, then one map per input and per output of the
unsigned transaction the global map holds. A map is key-value pairs, each key and value with its
length in front, ended by a zero byte; a key is never empty, so no pair starts with that byte.

Two readers that each accept only what writes back to the same bytes, with no key twice in a map, read
every PSBT they both accept the same way (`readers_agree`). With a key twice, the first and the last
value can differ (`first_last_differ`): a signer that shows one and signs another is the risk.
-/

namespace SignerSpec

abbrev KV := List UInt8 × List UInt8

def serKV (kv : KV) : List UInt8 := varstr kv.1 ++ varstr kv.2

def serMap (m : List KV) : List UInt8 := m.flatMap serKV ++ [0]

structure Psbt where
  global : List KV
  inputs : List (List KV)
  outputs : List (List KV)
  deriving DecidableEq, Repr, Inhabited

def magic : List UInt8 := [0x70, 0x73, 0x62, 0x74, 0xff]

def serPsbt (p : Psbt) : List UInt8 :=
  magic ++ serMap p.global ++ p.inputs.flatMap serMap ++ p.outputs.flatMap serMap

def KVOk (kv : KV) : Prop := kv.1 ≠ [] ∧ kv.1.length < 2 ^ 64 ∧ kv.2.length < 2 ^ 64

def MapOk (m : List KV) : Prop := (∀ kv ∈ m, KVOk kv) ∧ (m.map (·.1)).Nodup

/-- `counts` reads the input and output counts from the global map's unsigned transaction. -/
def Psbt.Ok (counts : List KV → Nat × Nat) (p : Psbt) : Prop :=
  MapOk p.global ∧ (∀ m ∈ p.inputs, MapOk m) ∧ (∀ m ∈ p.outputs, MapOk m) ∧
    (p.inputs.length, p.outputs.length) = counts p.global

theorem serKV_prefix : PrefixFree KVOk serKV := by
  intro a b r s ha hb h
  simp only [serKV, List.append_assoc] at h
  obtain ⟨h1, h⟩ := varstr_prefix _ _ _ _ ha.2.1 hb.2.1 h
  obtain ⟨h2, h⟩ := varstr_prefix _ _ _ _ ha.2.2 hb.2.2 h
  exact ⟨Prod.ext h1 h2, h⟩

/-- A pair never starts with the zero byte that ends a map: its key's length is at least one. -/
theorem serKV_head {kv : KV} (h : KVOk kv) : ∃ c t, serKV kv = c :: t ∧ c ≠ 0 := by
  obtain ⟨hk, hl, -⟩ := h
  have hpos : 0 < kv.1.length := List.length_pos_iff.mpr hk
  unfold serKV varstr varint
  split
  · rename_i h1
    refine ⟨_, _, rfl, fun e => ?_⟩
    have : kv.1.length % 256 = 0 := by simpa using congrArg UInt8.toNat e
    omega
  · split
    · exact ⟨_, _, rfl, by decide⟩
    · split <;> exact ⟨_, _, rfl, by decide⟩

theorem serMap_prefix : PrefixFree (fun m : List KV => ∀ kv ∈ m, KVOk kv) serMap := by
  intro a b r s ha hb h
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa [serMap] using h
    | cons y b =>
      obtain ⟨c, t, e, hc⟩ := serKV_head (hb y (by simp))
      simp [serMap, e] at h
      exact absurd h.1.symm hc
  | cons x a ih =>
    cases b with
    | nil =>
      obtain ⟨c, t, e, hc⟩ := serKV_head (ha x (by simp))
      simp [serMap, e] at h
      exact absurd h.1 hc
    | cons y b =>
      simp only [serMap, List.flatMap_cons, List.append_assoc] at h
      obtain ⟨rfl, h⟩ := serKV_prefix _ _ _ _ (ha x (by simp)) (hb y (by simp)) h
      obtain ⟨rfl, rfl⟩ := ih b (fun kv hk => ha kv (by simp [hk])) (fun kv hk => hb kv (by simp [hk]))
        (by simpa [serMap, List.append_assoc] using h)
      exact ⟨rfl, rfl⟩

/-- One PSBT per byte string, among those whose map counts follow their unsigned transaction. -/
theorem serPsbt_inj {counts : List KV → Nat × Nat} {p q : Psbt} (hp : p.Ok counts) (hq : q.Ok counts)
    (h : serPsbt p = serPsbt q) : p = q := by
  obtain ⟨g, i, o, c⟩ := hp
  obtain ⟨g', i', o', c'⟩ := hq
  simp only [serPsbt, List.append_assoc, List.append_cancel_left_eq] at h
  obtain ⟨e1, h⟩ := serMap_prefix _ _ _ _ g.1 g'.1 h
  rw [e1, ← c'] at c
  simp only [Prod.mk.injEq] at c
  obtain ⟨e2, h⟩ := flatMap_prefix serMap_prefix c.1 (fun m hm => (i m hm).1) (fun m hm => (i' m hm).1) h
  obtain ⟨e3, -⟩ := flatMap_prefix serMap_prefix c.2 (fun m hm => (o m hm).1) (fun m hm => (o' m hm).1)
    (r := []) (s := []) (by simpa using h)
  cases p; cases q; simp_all

/-- A reader that accepts bytes only when they are what its reading writes back, every map well formed. -/
def Faithful (counts : List KV → Nat × Nat) (read : List UInt8 → Option Psbt) : Prop :=
  ∀ s p, read s = some p → serPsbt p = s ∧ p.Ok counts

/-- Two such readers never read the same bytes differently. -/
theorem readers_agree {counts : List KV → Nat × Nat} {read read' : List UInt8 → Option Psbt}
    (hr : Faithful counts read) (hr' : Faithful counts read') {s : List UInt8} {p p' : Psbt}
    (h : read s = some p) (h' : read' s = some p') : p = p' := by
  obtain ⟨e, ok⟩ := hr s p h
  obtain ⟨e', ok'⟩ := hr' s p' h'
  exact serPsbt_inj ok ok' (e.trans e'.symm)

theorem nodup_map_inj {α β} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup → ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, h, a, b, ha, hb, e => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    rcases List.mem_cons.mp ha with rfl | h1 <;> rcases List.mem_cons.mp hb with rfl | h2
    · rfl
    · exact absurd e.symm (h.1 b h2)
    · exact absurd e (h.1 a h1)
    · exact nodup_map_inj h.2 h1 h2 e

/-- With no key twice, the first value for a key is the last. -/
theorem first_last_agree {m : List KV} (h : (m.map (·.1)).Nodup) (k : List UInt8) :
    m.find? (·.1 == k) = m.reverse.find? (·.1 == k) := by
  cases e : m.find? (·.1 == k) with
  | none =>
    rw [eq_comm, List.find?_eq_none]
    intro x hx
    exact List.find?_eq_none.mp e x (List.mem_reverse.mp hx)
  | some x =>
    have hx := List.mem_of_find?_eq_some e
    have kx := List.find?_some e
    cases e' : m.reverse.find? (·.1 == k) with
    | none => exact absurd (List.find?_eq_none.mp e' x (List.mem_reverse.mpr hx)) (by simp [kx])
    | some y =>
      have hy := List.mem_reverse.mp (List.mem_of_find?_eq_some e')
      have ky := List.find?_some e'
      simp only [beq_iff_eq] at kx ky
      exact congrArg some (nodup_map_inj h hx hy (kx.trans ky.symm))

/-- With a key twice they need not be. -/
theorem first_last_differ :
    let m : List KV := [([1], [0x0a]), ([1], [0x0b])]
    m.find? (·.1 == [1]) ≠ m.reverse.find? (·.1 == [1]) := by decide

end SignerSpec
