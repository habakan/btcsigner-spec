import SignerSpec.Txid
import SignerSpec.Checksums
/-! `serTx` and `txid`, with the real SHA-256, against raw mainnet transactions: each read, written back
byte for byte, and hashed to its known txid. -/
open SignerSpec

def bytes (s : String) : List UInt8 :=
  let ds := s.toList.map fun c => if c.isDigit then c.toNat - 48 else c.toNat - 87
  (List.range (ds.length / 2)).map fun i => UInt8.ofNat (ds[2 * i]! * 16 + ds[2 * i + 1]!)

def num (l : List UInt8) : Nat := l.foldr (fun b acc => acc * 256 + b.toNat) 0

partial def readTx (raw : List UInt8) : RawTx := Id.run do
  let vi (l : List UInt8) : Nat × List UInt8 := match l with
    | 0xfd :: r => (num (r.take 2), r.drop 2) | b :: r => (b.toNat, r) | [] => (0, [])
  let (n, r) := vi (raw.drop 4)
  let mut r := r
  let mut ins : List RawIn := []
  for _ in List.range n do
    let (sl, r1) := vi (r.drop 36)
    ins := ins ++ [{ outpoint := r.take 36, scriptSig := r1.take sl, sequence := num ((r1.drop sl).take 4) }]
    r := r1.drop (sl + 4)
  let (m, r1) := vi r
  r := r1
  let mut outs : List (Nat × Script) := []
  for _ in List.range m do
    let (sl, r1) := vi (r.drop 8)
    outs := outs ++ [(num (r.take 8), r1.take sl)]
    r := r1.drop sl
  return { version := num (raw.take 4), inputs := ins, outputs := outs, locktime := num r }

def checks (raw id : String) : Bool :=
  let t := readTx (bytes raw)
  serTx t == bytes raw && (txid sha256 t).reverse == bytes id

-- the genesis block's coinbase
#guard checks ("01000000010000000000000000000000000000000000000000000000000000000000000000ffffffff4d04ffff001d0104" ++
  "455468652054696d65732030332f4a616e2f32303039204368616e63656c6c6f72206f6e206272696e6b206f66207365636f6e64" ++
  "206261696c6f757420666f722062616e6b73ffffffff0100f2052a01000000434104678afdb0fe5548271967f1a67130b7105cd6" ++
  "a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5fac00000000")
  "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"

-- the first payment between two people (block 170): two outputs
#guard checks ("0100000001c997a5e56e104102fa209c6a852dd90660a20b2d9c352423edce25857fcd3704000000004847304402204e" ++
  "45e16932b8af514961a1d3a1a25fdf3f4f7732e9d624c6c61548ab5fb8cd410220181522ec8eca07de4860a4acdd12909d831cc56c" ++
  "bbac4622082221a8768d1d0901ffffffff0200ca9a3b00000000434104ae1a62fe09c5f51b13905f07f06b99a2f7159b2225f374cd" ++
  "378d71302fa28414e7aab37397f554a7df5f142c21c1b7303b8a0626f1baded5c72a704f7e6cd84cac00286bee0000000043410411" ++
  "db93e1dcdb8a016b49840f8c53bc1eb68a382e97b1482ecad7b148a6909a5cb2e0eaddfb84ccf9744464f82e160bfa9b8b64f9d4c0" ++
  "3f999b8643f656b412a3ac00000000")
  "f4184fc596403b9d638783cf57adfe4c75c605f6356fbc91338530e9831e9e16"
