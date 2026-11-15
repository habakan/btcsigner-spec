import SignerSpec.Psbt
/-! PSBTs from bitwasm-signer's vectors read into maps, checked well formed and written back byte for byte;
a key repeated in a map is refused. -/
open SignerSpec

def bytes (s : String) : List UInt8 :=
  let ds := s.toList.map fun c => if c.isDigit then c.toNat - 48 else c.toNat - 87
  (List.range (ds.length / 2)).map fun i => UInt8.ofNat (ds[2 * i]! * 16 + ds[2 * i + 1]!)

def num (l : List UInt8) : Nat := l.foldr (fun b acc => acc * 256 + b.toNat) 0

def vi (l : List UInt8) : Nat × List UInt8 := match l with
  | 0xfd :: r => (num (r.take 2), r.drop 2) | b :: r => (b.toNat, r) | [] => (0, [])

/-- The input and output counts of the global map's unsigned transaction. -/
partial def counts (g : List KV) : Nat × Nat := Id.run do
  let some (_, tx) := g.find? (·.1 == [0]) | return (0, 0)
  let (n, r) := vi (tx.drop 4)
  let mut r := r
  for _ in List.range n do
    let (sl, r1) := vi (r.drop 36)
    r := r1.drop (sl + 4)
  return (n, (vi r).1)

partial def readMap (r : List UInt8) : List KV × List UInt8 := Id.run do
  let mut m : List KV := []
  let mut r := r
  repeat
    let (n, r1) := vi r
    if n = 0 then return (m, r1)
    let (vl, r2) := vi (r1.drop n)
    m := m ++ [(r1.take n, r2.take vl)]
    r := r2.drop vl
  return (m, r)

def readMaps (k : Nat) (r : List UInt8) : List (List KV) × List UInt8 :=
  (List.range k).foldl (fun (ms, r) _ => let (m, r) := readMap r; (ms ++ [m], r)) ([], r)

def read (s : List UInt8) : Option Psbt :=
  let (g, r) := readMap (s.drop 5)
  let (ins, r) := readMaps (counts g).1 r
  let (outs, _) := readMaps (counts g).2 r
  let p : Psbt := { global := g, inputs := ins, outputs := outs }
  let nodup (m : List KV) := (m.map (·.1)).eraseDups.length == m.length
  if serPsbt p == s && nodup g && ins.all nodup && outs.all nodup then some p else none

def own := bytes ("70736274ff01007102000000012ddc24b039a8d994e8f01740563b4240e9866436892dc35d1e0694e650bb680c0000000000" ++
  "fdffffff0260ea000000000000160014a5a739ef69cf8c068e94456322671139dab876ea58980000000000001600143e3498" ++
  "5dca6fddc9fb369940e4c7d8e2873f529c000000000001011fa086010000000000160014c0cebcd6c3d3ca8c75dc5ec62ebe" ++
  "55330ef910e222060330d54fd0dd420a6e5f8d3624f5f3482cae350f79d5f0753bf5beef9c2d91af3c1873c5da0a54000080" ++
  "000000800000008000000000000000000000220203025324888e429ab8e3dbaf1f7802648b9cd01e9b418485c5fa4c1b9b57" ++
  "00e1a61873c5da0a540000800000008000000080010000000000000000")
def rpc := bytes ("70736274ff0100750200000001268171371edff285e937adeea4b37b78000c0566cbb3ad64641713ca42171bf60000000000" ++
  "feffffff02d3dff505000000001976a914d0c59903c5bac2868760e90fd521a4665aa7652088ac00e1f5050000000017a914" ++
  "3545e6e33b832c47050f24d3eeb93c9c03948bc787b32e1300000100fda5010100000000010289a3c71eab4d20e0371bbba4" ++
  "cc698fa295c9463afa2e397f8533ccb62f9567e50100000017160014be18d152a9b012039daf3da7de4f53349eecb985ffff" ++
  "ffff86f8aa43a71dff1448893a530a7237ef6b4608bbb2dd2d0171e63aec6a4890b40100000017160014fe3e9ef1a745e974" ++
  "d902c4355943abcb34bd5353ffffffff0200c2eb0b000000001976a91485cff1097fd9e008bb34af709c62197b38978a4888" ++
  "ac72fef84e2c00000017a914339725ba21efd62ac753a9bcd067d6c7a6a39d05870247304402202712be22e0270f394f5683" ++
  "11dc7ca9a68970b8025fdd3b240229f07f8a5f3a240220018b38d7dcd314e734c9276bd6fb40f673325bc4baa144c800d2f2" ++
  "f02db2765c012103d2e15674941bad4a996372cb87e1856d3652606d98562fe39c5e9e7e413f210502483045022100d12b85" ++
  "2d85dcd961d2f5f4ab660654df6eedcc794c0c33ce5cc309ffb5fce58d022067338a8e0e1725c197fb1a88af59f51e44e425" ++
  "5b20167c8684031c05d1f2592a01210223b72beef0965d10be0778efecd61fcac6f79a4ea169393380734464f84f2ab30000" ++
  "0000000000")

#guard (read own).isSome && (read rpc).isSome
#guard (read own).map (fun p => (p.inputs.length, p.outputs.length)) == some (1, 2)

-- the first input's first pair once more, with another value
#guard let p := (read own).get!
  let m := p.inputs.head!
  read (serPsbt { p with inputs := (m ++ [(m.head!.1, [0])]) :: p.inputs.tail }) == none
-- trailing bytes
#guard read (own ++ [0]) == none
