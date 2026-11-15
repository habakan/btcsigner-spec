import SignerSpec.OrD
/-! `orDOf` on bitwasm-signer's or_d vectors (parser/tests/vectors), and on a few broken copies of them. -/
open SignerSpec

def bytes (s : String) : List UInt8 :=
  let ds := s.toList.map fun c => if c.isDigit then c.toNat - 48 else c.toNat - 87
  (List.range (ds.length / 2)).map fun i => UInt8.ofNat (ds[2 * i]! * 16 + ds[2 * i + 1]!)

def lockOf (s : String) : Option (Bool × Nat) := (orDOf (bytes s)).map fun d => (d.after, d.lock)

-- Liana: pk, then pkh with older(52596) / older(144), whose push needs a 0 after 0x90
#guard lockOf "2103dc1953c2756c7c58d4f48ca1bbba767f414fd236bf4d662b67721ac626c514e0ac736476a914a4181cd34eeca10b68629756cd51360d5185a37088ad0374cd00b268" == some (false, 52596)
#guard lockOf "210254689c4a585b8f3d9ddea8e9e68d0e8f49f75709fa6e7d075657573815958a81ac736476a9144b47031bbf50a9b3b7be4ecc548e0637eee2434888ad029000b268" == some (false, 144)
-- multi(2,3 keys), then pkh with after(900000)
#guard lockOf "522103dc1953c2756c7c58d4f48ca1bbba767f414fd236bf4d662b67721ac626c514e0210254689c4a585b8f3d9ddea8e9e68d0e8f49f75709fa6e7d075657573815958a8121028e818df63d6f2dce9308d7455fd4c85cbb39d703608b8fbed647d75e262322d853ae736476a914cac00799cd0755d9d2d68455eb8f984a64184e6788ad03a0bb0db168" == some (true, 900000)
-- multi(2,3 keys) on both paths with after(1700000000): the longest, 219 bytes
#guard lockOf "52210254689c4a585b8f3d9ddea8e9e68d0e8f49f75709fa6e7d075657573815958a8121028e818df63d6f2dce9308d7455fd4c85cbb39d703608b8fbed647d75e262322d82103229cb34fe3eb1af43b6dd2a2e1b31681039b71d9303ded36b3128ef359e379bd53ae7364522103e762c58a58500170daf6a9c739087445045c25b01eb1960e7f7ec3b770d5125c21027fea83cba9510d4c21bf9fa7fca1d10f9e116a923653830d9c1dec41b70ea30c2102a6dd7f84904c4dd24d242cd35053595f911d48fd4f07cfc78420895e12704c8953af0400f15365b168" == some (true, 1700000000)
-- pk on both paths
#guard lockOf "210254689c4a585b8f3d9ddea8e9e68d0e8f49f75709fa6e7d075657573815958a81ac73642103e762c58a58500170daf6a9c739087445045c25b01eb1960e7f7ec3b770d5125cad0340420fb168" == some (true, 1000000)
#guard lockOf "2103dc1953c2756c7c58d4f48ca1bbba767f414fd236bf4d662b67721ac626c514e0ac7364210254689c4a585b8f3d9ddea8e9e68d0e8f49f75709fa6e7d075657573815958a81ad03800040b268" == some (false, 4194432)

-- 144 without its 0 is -16; the same key on both paths; CHECKSIG where CHECKSIGVERIFY belongs; a 4-byte key
#guard lockOf "210254689c4a585b8f3d9ddea8e9e68d0e8f49f75709fa6e7d075657573815958a81ac736476a9144b47031bbf50a9b3b7be4ecc548e0637eee2434888ad0190b268" == none
#guard lockOf "2103dc1953c2756c7c58d4f48ca1bbba767f414fd236bf4d662b67721ac626c514e0ac73642103dc1953c2756c7c58d4f48ca1bbba767f414fd236bf4d662b67721ac626c514e0ad03800040b268" == none
#guard lockOf "2103dc1953c2756c7c58d4f48ca1bbba767f414fd236bf4d662b67721ac626c514e0ac7364210254689c4a585b8f3d9ddea8e9e68d0e8f49f75709fa6e7d075657573815958a81ac03800040b268" == none
#guard lockOf "0403dc1953ac7364210254689c4a585b8f3d9ddea8e9e68d0e8f49f75709fa6e7d075657573815958a81ad03800040b268" == none

-- a signer that does not sign or_d wallets still knows only multisig scripts
#guard !wscriptKnown false (bytes "2103dc1953c2756c7c58d4f48ca1bbba767f414fd236bf4d662b67721ac626c514e0ac7364210254689c4a585b8f3d9ddea8e9e68d0e8f49f75709fa6e7d075657573815958a81ad03800040b268")
