import SignerSpec.Mnemonic
import SignerSpec.Checksums
/-! The wordlist against its published hash, words and entropy against the BIP39 vectors (trezor/python-mnemonic),
and SeedQR against SeedSigner's vectors, with the real SHA-256. -/
open SignerSpec

def hexb (s : String) : List Nat :=
  let ds := s.toList.map fun c => if c.isDigit then c.toNat - 48 else c.toNat - 87
  (List.range (ds.length / 2)).map fun i => ds[2 * i]! * 16 + ds[2 * i + 1]!

def idx (m : String) : List Nat := (m.splitOn " ").map wordlist.idxOf

def bip39 (e m : String) : Bool :=
  toWords sha256 (hexb e) == idx m && toEntropy (idx m) == hexb e && valid sha256 (idx m)

def seedqr (m d c : String) : Bool :=
  seedqrStd (idx m) == d.toList && decodeStd sha256 d.toList == some (idx m) &&
    toEntropy (idx m) == hexb c && decodeCompact sha256 (hexb c) == some (idx m)

#guard (sha256 ("\n".intercalate wordlist ++ "\n").toUTF8.toList).map (·.toNat) ==
  hexb "2f5eed53a4727b4bf8880d8f3f199efc90e58503646d9ff8eff3a2ed3b24dbda"

#guard bip39 "00000000000000000000000000000000"
  "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about"
#guard bip39 "7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f"
  "legal winner thank year wave sausage worth useful legal winner thank yellow"
#guard bip39 "80808080808080808080808080808080"
  "letter advice cage absurd amount doctor acoustic avoid letter advice cage above"
#guard bip39 "ffffffffffffffffffffffffffffffff"
  "zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo wrong"
#guard bip39 "000000000000000000000000000000000000000000000000"
  "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon agent"
#guard bip39 "7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f"
  "legal winner thank year wave sausage worth useful legal winner thank year wave sausage worth useful legal will"
#guard bip39 "808080808080808080808080808080808080808080808080"
  "letter advice cage absurd amount doctor acoustic avoid letter advice cage absurd amount doctor acoustic avoid letter always"
#guard bip39 "ffffffffffffffffffffffffffffffffffffffffffffffff"
  "zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo when"
#guard bip39 "0000000000000000000000000000000000000000000000000000000000000000"
  "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon art"
#guard bip39 "7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f"
  "legal winner thank year wave sausage worth useful legal winner thank year wave sausage worth useful legal winner thank year wave sausage worth title"
#guard bip39 "8080808080808080808080808080808080808080808080808080808080808080"
  "letter advice cage absurd amount doctor acoustic avoid letter advice cage absurd amount doctor acoustic avoid letter advice cage absurd amount doctor acoustic bless"
#guard bip39 "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
  "zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo vote"
#guard bip39 "9e885d952ad362caeb4efe34a8e91bd2"
  "ozone drill grab fiber curtain grace pudding thank cruise elder eight picnic"
#guard bip39 "6610b25967cdcca9d59875f5cb50b0ea75433311869e930b"
  "gravity machine north sort system female filter attitude volume fold club stay feature office ecology stable narrow fog"
#guard bip39 "68a79eaca2324873eacc50cb9c6eca8cc68ea5d936f98787c60c7ebc74e6ce7c"
  "hamster diagram private dutch cause delay private meat slide toddler razor book happy fancy gospel tennis maple dilemma loan word shrug inflict delay length"
#guard bip39 "c0ba5a8e914111210f2bd131f3d5e08d"
  "scheme spot photo card baby mountain device kick cradle pact join borrow"
#guard bip39 "6d9be1ee6ebd27a258115aad99b7317b9c8d28b6d76431c3"
  "horn tenant knee talent sponsor spell gate clip pulse soap slush warm silver nephew swap uncle crack brave"
#guard bip39 "9f6a2878b2520799a44ef18bc7df394e7061a224d2c33cd015b157d746869863"
  "panda eyebrow bullet gorilla call smoke muffin taste mesh discover soft ostrich alcohol speed nation flash devote level hobby quick inner drive ghost inside"
#guard bip39 "23db8160a31d3e0dca3688ed941adbf3"
  "cat swing flag economy stadium alone churn speed unique patch report train"
#guard bip39 "8197a4a47f0425faeaa69deebc05ca29c0a5b5cc76ceacc0"
  "light rule cinnamon wrap drastic word pride squirrel upgrade then income fatal apart sustain crack supply proud access"
#guard bip39 "066dca1a2bb7e8a1db2832148ce9933eea0f3ac9548d793112d9a95c9407efad"
  "all hour make first leader extend hole alien behind guard gospel lava path output census museum junior mass reopen famous sing advance salt reform"
#guard bip39 "f30f8c1da665478f49b001d94c5fc452"
  "vessel ladder alter error federal sibling chat ability sun glass valve picture"
#guard bip39 "c10ec20dc3cd9f652c7fac2f1230f7a3c828389a14392f05"
  "scissors invite lock maple supreme raw rapid void congress muscle digital elegant little brisk hair mango congress clump"
#guard bip39 "f585c11aec520db57dd353c69554b21a89b20fb0650966fa0a9d6f74fd989d8f"
  "void come effort suffer camp survey warrior heavy shoot primary clutch crush open amazing screen patrol group space point ten exist slush involve unfold"

#guard seedqr "attack pizza motion avocado network gather crop fresh patrol unusual wild holiday candy pony ranch winter theme error hybrid van cereal salon goddess expire"
  "011513251154012711900771041507421289190620080870026613431420201617920614089619290300152408010643"
  "0e74b64107f94cc0ccfae6a13dcbec3662154fec67e0e00999c07892597d190a"
#guard seedqr "atom solve joy ugly ankle message setup typical bean era cactus various odor refuse element afraid meadow quick medal plate wisdom swap noble shallow"
  "011416550964188800731119157218870156061002561932122514430573003611011405110613292018175411971576"
  "0e59dde276009317f1275f1389888078c99368d1e82489b5f629531fc5b6a56e"
#guard seedqr "sound federal bonus bleak light raise false engage round stock update render quote truck quality fringe palace foot recipe labor glow tortoise potato still"
  "166206750203018810361417065805941507171219081456140818651401074412730727143709940798183613501710"
  "cfca8c658bc81962549252bc7ac3ba5b0b01d26bcae89f2b5ecebe263dcb2a36"
#guard seedqr "forum undo fragile fade shy sign arrest garment culture tube off merit"
  "073318950739065415961602009907670428187212261116"
  "5bbd9d71a8ec7990831aff359d426545"
#guard seedqr "good battle boil exact add seed angle hurry success glad carbon whisper"
  "080301540200062600251559007008931730078802752004"
  "6462686427203385c2337dd84c5089fd"
#guard seedqr "approve fruit lens brass ring actual stool coin doll boss strong rate"
  "008607501025021714880023171503630517020917211425"
  "0acbba008d9ba005f5996b40a3475cd9"
#guard seedqr "dignity utility vacant shiver thought canoe feel multiply item youth actor coyote"
  "049619221923158517990268067811630950204300210397"
  "3e1e0bc1e31e0e4315348b76dfec0a98"
#guard seedqr "corn voice scrap arrow original diamond trial property benefit choose junk lock"
  "038719631547010112530489185713790169032209701051"
  "307eaf058659ca7a7a0d63152509e541"
#guard seedqr "vocal tray giggle tool duck letter category pattern train magnet excite swamp"
  "196218530783182905421028028912901848107106301753"
  "f55cf587f2543d01090d0ae710bd3b6d"

def eleven : List Nat := List.replicate 11 0

-- the last words after eleven "abandon": 128, "about" among them, each valid, and no other valid one
#guard (finalWords sha256 eleven).length == 128 && (finalWords sha256 eleven).contains 3
#guard (finalWords sha256 eleven).all fun w => valid sha256 (eleven ++ [w])
#guard ((List.range 2048).filter fun w => valid sha256 (eleven ++ [w])) == (finalWords sha256 eleven).mergeSort

-- a wrong last word, an index past 2047, and 15 words read as nothing
#guard decodeStd sha256 (String.join (List.replicate 12 "0000")).toList == none
#guard decodeStd sha256 ("0000000000000000000000000000000000000000000000000000000000000000000000000000000000002048").toList == none
#guard decodeStd sha256 (seedqrStd (idx "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon address")) == none
#guard valid sha256 (idx "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon address")

