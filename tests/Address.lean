import SignerSpec.Checksums
import SignerSpec.Address
/-! `decode` against the BIP350 vectors (lowercase, the form the screen writes) and base58check. -/
open SignerSpec

def bytes (s : String) : Script :=
  let ds := s.toList.map fun c => if c.isDigit then c.toNat - 48 else c.toNat - 87
  (List.range (ds.length / 2)).map fun i => UInt8.ofNat (ds[2 * i]! * 16 + ds[2 * i + 1]!)

def reads (net : Net) (a : String) : Option Script := decode realChecksums net a.toList

#guard reads .main "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4" == some (bytes "0014751e76e8199196d454941c45d1b3a323f1433bd6")
#guard reads .test "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7" ==
  some (bytes "00201863143c14c5166804bd19203356da136c985678cd4d27a1b8c6329604903262")
#guard reads .main "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y" ==
  some (bytes "5128751e76e8199196d454941c45d1b3a323f1433bd6751e76e8199196d454941c45d1b3a323f1433bd6")
#guard reads .main "bc1sw50qgdz25j" == some (bytes "6002751e")
#guard reads .main "bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs" == some (bytes "5210751e76e8199196d454941c45d1b3a323")
#guard reads .test "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy" ==
  some (bytes "0020000000c4a5cad46221b2a187905e5266362b99d5e91c6ce24d165dab93e86433")
#guard reads .test "tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c" ==
  some (bytes "5120000000c4a5cad46221b2a187905e5266362b99d5e91c6ce24d165dab93e86433")
#guard reads .main "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0" ==
  some (bytes "512079be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
#guard reads .main "16UwLL9Risc3QfPqBUvKofHmBQ7wMtjvM" == some (bytes "76a914010966776006953d5567439e5e39f86a0d273bee88ac")
#guard reads .main "3CK4fEwbMP7heJarmU4eqA3sMbVJyEnU3V" == some (bytes "a914748284390f9e263a4b766a75d0633c50426eb87587")
#guard reads .test "mfcSEPR8EkJrpX91YkTJ9iscdAzppJrG9j" == some (bytes "76a914010966776006953d5567439e5e39f86a0d273bee88ac")
#guard reads .regtest "bcrt1qw508d6qejxtdg4y5r3zarvary0c5xw7kygt080" ==
  some (bytes "0014751e76e8199196d454941c45d1b3a323f1433bd6")
#guard reads .main "script:6a0568656c6c6f" == some (bytes "6a0568656c6c6f")

-- BIP350's invalid addresses, lowercased where they were not about case
#guard [("tc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq5zuyut", Net.test),
  ("bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd", .main),
  ("tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf", .test),
  ("bc1s0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq54well", .main),
  ("bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh", .main),
  ("tb1q0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq24jc47", .test),
  ("bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4", .main),
  ("bc130xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq7zws8r", .main),
  ("bc1pw5dgrnzv", .main),
  ("bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav253zgeav", .main),
  ("bc1qr508d6qejxtdg4y5r3zarvaryv98gj9p", .main),
  ("tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq", .test),
  ("bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf", .main),
  ("tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j", .test),
  ("bc1gmk9yu", .main)].all fun (a, net) => reads net a == none

-- the screen writes lowercase only; a wrong checksum, network or hex digit reads as nothing
#guard reads .main "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4" == none
#guard reads .main "16UwLL9Risc3QfPqBUvKofHmBQ7wMtjvN" == none
#guard reads .main "mfcSEPR8EkJrpX91YkTJ9iscdAzppJrG9j" == none
#guard reads .test "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4" == none
#guard reads .main "script:6A0568656c6c6f" == none
#guard reads .main "script:6a0568656c6c6" == none
