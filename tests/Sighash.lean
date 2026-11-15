import SignerSpec.Sighash
import SignerSpec.Checksums
/-! `preV0` and `preTr`, hashed with the real SHA-256, against the BIP143 and BIP341 vectors. -/
open SignerSpec

def bytes (s : String) : List UInt8 :=
  let ds := s.toList.map fun c => if c.isDigit then c.toNat - 48 else c.toNat - 87
  (List.range (ds.length / 2)).map fun i => UInt8.ofNat (ds[2 * i]! * 16 + ds[2 * i + 1]!)

def num (l : List UInt8) : Nat := l.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- A transaction without witnesses, with the amounts and scripts its inputs spend. -/
partial def readTx (raw : List UInt8) (spent : List (Nat × String)) : SigTx := Id.run do
  let take (l : List UInt8) (n : Nat) := (l.take n, l.drop n)
  let vi (l : List UInt8) : Nat × List UInt8 := match l with
    | 0xfd :: r => (num (r.take 2), r.drop 2) | b :: r => (b.toNat, r) | [] => (0, [])
  let (v, r) := take raw 4
  let (n, r) := vi r
  let mut r := r
  let mut ins : List TxIn := []
  for (amount, spk) in spent.take n do
    let (op, r1) := take r 36
    let (sl, r2) := vi r1
    let (seq, r3) := take (r2.drop sl) 4
    ins := ins ++ [{ outpoint := op, sequence := num seq, amount, spk := bytes spk }]
    r := r3
  let (m, r') := vi r
  r := r'
  let mut outs : List (Nat × Script) := []
  for _ in List.range m do
    let (a, r1) := take r 8
    let (sl, r2) := vi r1
    outs := outs ++ [(num a, r2.take sl)]
    r := r2.drop sl
  return { version := num v, locktime := num (r.take 4), inputs := ins, outputs := outs }

def bip143 := readTx (bytes ("0100000002fff7f7881a8099afa6940d42d1e7f6362bec38171ea3edf433541db4e4ad969f0000000000eeff" ++
  "ffffef51e1b804cc89d182d279655c3aa89e815b1b309fe287d9b2b55d57b90ec68a0100000000ffffffff02202cb206000000001976a914" ++
  "8280b37df378db99f66f85c95a783a76ac7a6d5988ac9093510d000000001976a9143bde42dbee7e4dbe6a21b2d50ce2f0167faa815988ac11000000"))
  [(625000000, "2103c9f4836b9a4f77fc0d81f7bcb01b7f1b35916864b9476c241ce9fc198bd25432ac"),
   (600000000, "00141d0f172a0ecb48aee1be1f2687d2963ae33f71a1")]

#guard digestV0 sha256 bip143 1 (bytes "76a9141d0f172a0ecb48aee1be1f2687d2963ae33f71a188ac") ==
  bytes "c37af31116d1b27caf68aae9e3ac82f1477929014d5b917657d0eb49478cb670"

def bip341 := readTx (bytes ("02000000097de20cbff686da83a54981d2b9bab3586f4ca7e48f57f5b55963115f3b334e9c010000000000000000" ++
  "d7b7cab57b1393ace2d064f4d4a2cb8af6def61273e127517d44759b6dafdd990000000000fffffffff8e1f583384333689228c5d28eac1336" ++
  "6be082dc57441760d957275419a418420000000000fffffffff0689180aa63b30cb162a73c6d2a38b7eeda2a83ece74310fda0843ad604853b" ++
  "0100000000feffffffaa5202bdf6d8ccd2ee0f0202afbbb7461d9264a25e5bfd3c5a52ee1239e0ba6c0000000000feffffff956149bdc66faa96" ++
  "8eb2be2d2faa29718acbfe3941215893a2a3446d32acd050000000000000000000e664b9773b88c09c32cb70a2a3e4da0ced63b7ba3b22f8485" ++
  "31bbb1d5d5f4c94010000000000000000e9aa6b8e6c9de67619e6a3924ae25696bb7b694bb677a632a74ef7eadfd4eabf0000000000ffffffff" ++
  "a778eb6a263dc090464cd125c466b5a99667720b1c110468831d058aa1b82af10100000000ffffffff0200ca9a3b000000001976a91406afd46b" ++
  "cdfd22ef94ac122aa11f241244a37ecc88ac807840cb0000000020ac9a87f5594be208f8532db38cff670c450ed2fea8fcdefcc9a663f78bab96" ++
  "2b0065cd1d"))
  [(420000000, "512053a1f6e454df1aa2776a2814a721372d6258050de330b3c6d10ee8f4e0dda343"),
   (462000000, "5120147c9c57132f6e7ecddba9800bb0c4449251c92a1e60371ee77557b6620f3ea3"),
   (294000000, "76a914751e76e8199196d454941c45d1b3a323f1433bd688ac"),
   (504000000, "5120e4d810fd50586274face62b8a807eb9719cef49c04177cc6b76a9a4251d5450e"),
   (630000000, "512091b64d5324723a985170e4dc5a0f84c041804f2cd12660fa5dec09fc21783605"),
   (378000000, "00147dd65592d0ab2fe0d0257d571abf032cd9db93dc"),
   (672000000, "512075169f4001aa68f15bbed28b218df1d0a62cbbcf1188c6665110c293c907b831"),
   (546000000, "5120712447206d7a5238acc7ff53fbe94a3b64539ad291c7cdbc490b7577e4b17df5"),
   (588000000, "512077e30a5522dd9f894c3f8b8bd4c4b2cf82ca7da8a3ea6a239655c39c050ab220")]

#guard digestTr sha256 bip341 3 1 == bytes "bf013ea93474aa67815b1b6cc441d23b64fa310911d991e713cd34c7f5d46669"
#guard digestTr sha256 bip341 4 0 == bytes "4f900a0bae3f1446fd48490c2958b5a023228f01661cda3496a11da502a7f7ef"
