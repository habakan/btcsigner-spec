import SignerSpec.Checksums
/-! The screen's notation, with real checksums, against published vectors: SHA-256 (FIPS 180-2), bech32
(BIP173), bech32m (BIP350), and base58check. -/
open SignerSpec

def bytes (s : String) : Script :=
  let ds := s.toList.map fun c => if c.isDigit then c.toNat - 48 else c.toNat - 87
  (List.range (ds.length / 2)).map fun i => UInt8.ofNat (ds[2 * i]! * 16 + ds[2 * i + 1]!)

def addr (net : Net) (spk : String) : String := String.ofList (render realChecksums net (bytes spk))

#guard sha256 "abc".toUTF8.toList == bytes "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8.toList ==
  bytes "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard addr .main "0014751e76e8199196d454941c45d1b3a323f1433bd6" == "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4"
#guard addr .test "00201863143c14c5166804bd19203356da136c985678cd4d27a1b8c6329604903262" ==
  "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7"
#guard addr .main "512079be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798" ==
  "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0"
#guard addr .main "76a914010966776006953d5567439e5e39f86a0d273bee88ac" == "16UwLL9Risc3QfPqBUvKofHmBQ7wMtjvM"
#guard addr .main "a914748284390f9e263a4b766a75d0633c50426eb87587" == "3CK4fEwbMP7heJarmU4eqA3sMbVJyEnU3V"
#guard addr .main "6a0568656c6c6f" == "script:6a0568656c6c6f"
#guard String.ofList (fmtAmount 2100000000000000) == "21000000.00000000"
#guard String.ofList (fmtAmount 12345) == "0.00012345"
#guard String.ofList (fmtAmount 0) == "0.00000000"
#guard addr .regtest "0014751e76e8199196d454941c45d1b3a323f1433bd6" == "bcrt1qw508d6qejxtdg4y5r3zarvary0c5xw7kygt080"
#guard addr .test "76a914010966776006953d5567439e5e39f86a0d273bee88ac" == "mfcSEPR8EkJrpX91YkTJ9iscdAzppJrG9j"
#guard addr .main "6002751e" == "bc1sw50qgdz25j"
#guard addr .main "5210751e76e8199196d454941c45d1b3a323" == "bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs"
#guard addr .main "5128751e76e8199196d454941c45d1b3a323f1433bd6751e76e8199196d454941c45d1b3a323f1433bd6" ==
  "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y"
#guard addr .main "0013751e76e8199196d454941c45d1b3a323f1433b" == "script:0013751e76e8199196d454941c45d1b3a323f1433b"
#guard addr .main "5101ff" == "script:5101ff"
