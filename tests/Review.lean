import SignerSpec.Model
/-! One case per row of the manual's table of review's checks, in its order. -/
open SignerSpec

def wpkh (n : Nat) : Script := [0x00, 0x14] ++ List.replicate 20 (UInt8.ofNat n)
def wsh : Script := [0x00, 0x20] ++ List.replicate 32 7
/-- 1-of-1 multisig: OP_1 <key> OP_1 OP_CHECKMULTISIG. -/
def ms1 : Script := [0x51, 0x21, 0x02] ++ List.replicate 32 9 ++ [0x51, 0xae]

def at_ (i : Nat) : KeyPath := ⟨1, [84 + hardened, hardened, hardened, 0, i]⟩
def env : Env := { network := 0, fingerprint := 1, wallet := none,
                   owns := fun k spk ws => ws.isSome || spk == wpkh (k.path.getLast?.getD 0) }
def ours (i : Nat) (amount : Nat := 1000) : Input := ⟨amount, wpkh i, some (at_ i), 1, none, .absent⟩
def pay (amount : Nat) : Output := ⟨amount, wpkh 99, none⟩

def err : Except Error α → Option Error
  | .error e => some e
  | .ok _ => none

-- 1. formatOk
#guard err (review env ⟨[ours 0], []⟩) == some .format
-- 2. inputs in order: running total, then checkInput
#guard err (review env ⟨[ours 0 maxMoney, ours 1 maxMoney], [pay 1]⟩) == some .format
#guard err (review env ⟨[{ ours 0 with spk := [0x6a] }], [pay 1]⟩) == some .script
#guard err (review env ⟨[{ ours 0 with sighash := 3 }], [pay 1]⟩) == some .sighash
#guard err (review env ⟨[{ ours 0 with spk := wpkh 5 }], [pay 1]⟩) == some .notOurs
#guard err (review { env with wallet := some ⟨fun _ _ => false, fun _ _ => none, fun _ _ => none⟩ }
  ⟨[{ ours 0 with spk := wsh, wscript := some ms1 }], [pay 1]⟩) == some .wallet
-- 3. nothing of ours
#guard err (review env ⟨[{ ours 0 with key := some ⟨2, (at_ 0).path⟩ }], [pay 1]⟩) == some .nothingToSign
-- 4. checkPrev
#guard err (review env ⟨[{ ours 0 with prev := .mismatch }], [pay 1]⟩) == some .prevtxMismatch
#guard err (review env ⟨[ours 0, ours 1], [pay 1]⟩) == some .prevtxMissing
-- 5. outputs' total
#guard err (review env ⟨[ours 0], [pay maxMoney, pay maxMoney]⟩) == some .format
-- 6. fee
#guard err (review env ⟨[ours 0], [pay 2000]⟩) == some .fee
-- accepted, with one input and no previous transaction needed
#guard (match review env ⟨[ours 0], [pay 900]⟩ with | .ok r => r.fee == 100 | .error _ => false)
-- signing without that review
#guard err (sign env ⟨none⟩ ⟨[ours 0], [pay 900]⟩).1 == some .notReviewed
