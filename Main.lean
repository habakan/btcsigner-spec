import Lean.Data.Json
import SignerSpec.Model
import SignerSpec.Checksums
import SignerSpec.Message

/-! The model as an executable: one JSON case per line on stdin, one JSON verdict per line on stdout.
The format is in spec/README.md; `adapters/` produce it from a signer's own structures. -/

open Lean SignerSpec

def hexDigit (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
  else .error s!"not hex: {c}"

def unhexChars : List Char → Except String Script
  | a :: b :: rest => do return UInt8.ofNat (16 * (← hexDigit a) + (← hexDigit b)) :: (← unhexChars rest)
  | [] => .ok []
  | _ => .error "odd-length hex"

def unhex (s : String) : Except String Script := unhexChars s.toList

def getAmount (j : Json) : Except String Nat := do
  let s ← j.getObjValAs? String "amount"
  match s.toNat? with
  | some n => return n
  | none => throw s!"not an amount: {s}"

def getKey (j : Json) : Except String (Option KeyPath) :=
  match j.getObjValD "key" with
  | .null => .ok none
  | k => do return some { fingerprint := ← k.getObjValAs? Nat "fp", path := ← k.getObjValAs? (List Nat) "path" }

def getScriptOpt (j : Json) (field : String) : Except String (Option Script) :=
  match j.getObjValD field with
  | .null => .ok none
  | v => do return some (← unhex (← v.getStr?))

def getInput (j : Json) : Except String Input := do
  let amount ← getAmount j
  let spk ← unhex (← j.getObjValAs? String "spk")
  let info ← match j.getObjValD "prev" with
    | .null => pure none
    | p => do
      let out ← match p.getObjValD "out" with
        | .null => pure none
        | o => do pure (some (← getAmount o, ← unhex (← o.getObjValAs? String "spk")))
      pure (some { txid := ← unhex (← p.getObjValAs? String "txid"), out : PrevInfo })
  return { amount, spk, key := ← getKey j, sighash := ← j.getObjValAs? Nat "sighash",
           wscript := ← getScriptOpt j "ws", prev := PrevTx.of (← unhex (← j.getObjValAs? String "txid")) amount spk info }

def getOutput (j : Json) : Except String Output := do
  return { amount := ← getAmount j, spk := ← unhex (← j.getObjValAs? String "spk"), key := ← getKey j }

def getKeyPath (e : Json) : Except String KeyPath := do
  return ⟨← e.getObjValAs? Nat "fp", ← e.getObjValAs? (List Nat) "path"⟩

/-- The registered wallet answers only for the inputs and outputs the adapter listed as its own. -/
def getWallet (j : Json) : Except String (Option Multisig) :=
  match j.getObjValD "wallet" with
  | .null => .ok none
  | w => do
    let ins ← (← w.getObjValAs? (Array Json) "inputs").toList.mapM fun e => do
      let second ← match e.getObjValD "second" with
        | .null => pure none
        | k => some <$> getKeyPath k
      return (← getKeyPath e, ← unhex (← e.getObjValAs? String "ws"), second)
    let outs ← (← w.getObjValAs? (Array Json) "outputs").toList.mapM fun e => do
      return (← getKeyPath e, ← unhex (← e.getObjValAs? String "spk"), ← e.getObjValAs? Nat "chain")
    return some { inputOk := fun k ws => ins.any fun (k', ws', _) => k' == k && ws' == ws,
                  outputChain := fun k s => (outs.find? fun (k', s', _) => k' == k && s' == s).map (·.2.2),
                  second := fun k ws => (ins.find? fun (k', ws', _) => k' == k && ws' == ws).bind (·.2.2) }

/-- `owns` answers only for the (key, script, witness script) triples the adapter listed as owned. -/
def getEnv (j : Json) : Except String Env := do
  let owned ← (← j.getObjValAs? (Array Json) "owns").toList.mapM fun e => do
    return (← getKeyPath e, ← unhex (← e.getObjValAs? String "spk"), ← getScriptOpt e "ws")
  return { network := ← j.getObjValAs? Nat "network", fingerprint := ← j.getObjValAs? Nat "fingerprint",
           owns := fun k s w => owned.contains (k, s, w), wallet := ← getWallet j,
           legacy := (j.getObjValAs? Bool "legacy").toOption.getD false,
           nested := (j.getObjValAs? Bool "nested").toOption.getD false,
           orD := (j.getObjValAs? Bool "orD").toOption.getD false }

def errorName : Error → String
  | .format => "FORMAT" | .notOurs => "NOT_OURS" | .nothingToSign => "NOTHING_TO_SIGN" | .sighash => "SIGHASH"
  | .script => "SCRIPT" | .prevtxMissing => "PREVTX_MISSING" | .prevtxMismatch => "PREVTX_MISMATCH"
  | .fee => "FEE" | .notReviewed => "NOT_REVIEWED" | .wallet => "WALLET"

def ownerCode : Owner → Nat
  | .external => 0 | .change => 1 | .self => 2

def runCase (j : Json) : Except String Json := do
  let env ← getEnv j
  let tx : Tx := { inputs := ← (← j.getObjValAs? (Array Json) "inputs").toList.mapM getInput,
                   outputs := ← (← j.getObjValAs? (Array Json) "outputs").toList.mapM getOutput }
  return match review env tx with
    | .error e => Json.mkObj [("error", errorName e)]
    | .ok r => Json.mkObj [("ok", Json.mkObj [
        ("totalIn", toString r.totalIn), ("totalOut", toString r.totalOut), ("fee", toString r.fee),
        ("willSign", toJson r.willSign), ("owners", toJson (r.owners.map ownerCode))]),
        ("sigs", match (sign env ⟨some tx⟩ tx).1 with
          | .ok l => toJson (l.map fun (j, k) => Json.mkObj [("input", j), ("fp", k.fingerprint), ("path", toJson k.path)])
          | .error _ => Json.null)]

def getNet (j : Json) : Except String Net := do
  match ← j.getObjValAs? String "network" with
  | "main" => pure .main
  | "test" => pure .test
  | "regtest" => pure .regtest
  | n => throw s!"unknown network: {n}"

/-- `{"render": {"network", "spk"}}` → `{"address"}`: what `Notation.lean` writes for that script. -/
def runRender (j : Json) : Except String Json := do
  let spk ← unhex (← j.getObjValAs? String "spk")
  return Json.mkObj [("address", String.ofList (render realChecksums (← getNet j) spk))]

/-- `{"message": hex}` → `{"kind", "text"}`: what `Message.lean` shows for those bytes. -/
def runMessage (j : Json) : Except String Json := do
  let (k, t) := showMessage (← unhex (← j.getStr?))
  return Json.mkObj [("kind", if k = .text then "text" else "hex"), ("text", String.ofList t)]

def runLine (j : Json) : Except String Json :=
  match j.getObjVal? "render", j.getObjVal? "message" with
  | .ok r, _ => runRender r
  | _, .ok m => runMessage m
  | _, _ => runCase j

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let out := match Json.parse line >>= runLine with
    | .ok v => v
    | .error e => Json.mkObj [("fatal", e)]
  stdout.putStrLn out.compress
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
