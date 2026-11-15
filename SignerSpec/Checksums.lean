import SignerSpec.Notation

/-!
# The checksums addresses carry

`Notation.lean` takes them as parameters; these are the real ones (BIP173/BIP350 polymod, and the first
four bytes of a double SHA-256), so the executable writes addresses a user would see. Nothing here is
proved: `tests/Notation.lean` checks them against published vectors.
-/

namespace SignerSpec

/-! ## bech32 and bech32m -/

def polymod (values : List Nat) : Nat :=
  let gen := [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
  values.foldl (fun chk v =>
    let b := chk >>> 25
    let chk := ((chk &&& 0x1ffffff) <<< 5) ^^^ v
    (List.range 5).foldl (fun c i => if (b >>> i) &&& 1 == 1 then c ^^^ gen[i]! else c) chk) 1

def hrpExpand (hrp : List Char) : List Nat :=
  hrp.map (·.toNat >>> 5) ++ [0] ++ hrp.map (·.toNat &&& 31)

/-- bech32 (`m = false`) or bech32m checksum: six 5-bit values. -/
def bech32Checksum (m : Bool) (hrp : List Char) (data : List Nat) : List Nat :=
  let pm := polymod (hrpExpand hrp ++ data ++ [0, 0, 0, 0, 0, 0]) ^^^ (if m then 0x2bc830a3 else 1)
  (List.range 6).map fun i => (pm >>> (5 * (5 - i))) &&& 31

/-! ## SHA-256 -/

def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def word (b : Array UInt8) (i : Nat) : UInt32 :=
  (b[i]!.toUInt32 <<< 24) ||| (b[i + 1]!.toUInt32 <<< 16) ||| (b[i + 2]!.toUInt32 <<< 8) ||| b[i + 3]!.toUInt32

def compress (h : Array UInt32) (block : Array UInt8) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := (List.range 16).toArray.map fun i => word block (4 * i)
  for i in [16:64] do
    let s0 := rotr w[i - 15]! 7 ^^^ rotr w[i - 15]! 18 ^^^ (w[i - 15]! >>> 3)
    let s1 := rotr w[i - 2]! 17 ^^^ rotr w[i - 2]! 19 ^^^ (w[i - 2]! >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut v := h
  for i in [0:64] do
    let (a, b, c, d, e, f, g, hh) := (v[0]!, v[1]!, v[2]!, v[3]!, v[4]!, v[5]!, v[6]!, v[7]!)
    let t1 := hh + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) + sha256K[i]! + w[i]!
    let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    v := #[t1 + t2, a, b, c, d + t1, e, f, g]
  return (List.range 8).toArray.map fun i => h[i]! + v[i]!

def sha256 (msg : List UInt8) : List UInt8 := Id.run do
  let len := msg.length
  let padLen := (64 + 56 - (len + 1) % 64) % 64
  let bits := 8 * len
  let tail : List UInt8 := (List.range 8).reverse.map fun i => UInt8.ofNat (bits >>> (8 * i))
  let padded : Array UInt8 := (msg ++ [(0x80 : UInt8)] ++ List.replicate padLen (0 : UInt8) ++ tail).toArray
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for k in [0:padded.size / 64] do
    h := compress h (padded.extract (64 * k) (64 * k + 64))
  return h.toList.flatMap fun x => [24, 16, 8, 0].map fun s => (x >>> s).toUInt8

def realChecksums : Checksums where
  bech32 := bech32Checksum
  bech32_length _ _ _ := by simp [bech32Checksum]
  base58 p := (List.range 4).map fun i => ((sha256 (sha256 (p.map UInt8.ofNat))).getD i 0).toNat
  base58_length _ := by simp
  base58_lt _ x hx := by
    simp only [List.mem_map] at hx
    obtain ⟨_, -, rfl⟩ := hx
    exact UInt8.toNat_lt _

end SignerSpec
