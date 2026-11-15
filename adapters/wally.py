"""libwally-core's handling of a PSBT, one JSON request per line on stdin and one verdict per line on stdout.
It has no fee function: a wallet built on it adds up psbt_get_input_best_utxo (witness_utxo
first, else the non_witness_utxo's output) once psbt_sign_bip32 has signed with the test seed."""
import json
import sys

import wallycore as w

seed = w.bip39_mnemonic_to_seed512("abandon " * 11 + "about", None)
hd = w.bip32_key_from_seed_alloc(seed, w.BIP32_VER_MAIN_PRIVATE, 0)


def review(b64):
    try:
        psbt = w.psbt_from_base64(b64, w.WALLY_PSBT_PARSE_FLAG_STRICT)
    except Exception as e:
        return {"error": "parse", "detail": str(e)}
    before = w.psbt_to_base64(psbt, 0)
    try:
        w.psbt_sign_bip32(psbt, hd, 0)
    except Exception as e:
        return {"error": "sign", "detail": str(e)}
    if w.psbt_to_base64(psbt, 0) == before:
        return {"error": "sign", "detail": "nothing signed"}
    total = 0
    for i in range(w.psbt_get_num_inputs(psbt)):
        try:
            total += w.tx_output_get_satoshi(w.psbt_get_input_best_utxo_alloc(psbt, i))
        except Exception as e:
            return {"error": "fee", "detail": f"input {i} has no utxo: {e}"}
    tx = w.psbt_get_global_tx_alloc(psbt)
    spend = sum(w.tx_get_output_satoshi(tx, j) for j in range(w.tx_get_num_outputs(tx)))
    fee = total - spend
    return {"ok": {"input": str(total), "spend": str(spend), "change": "0", "fee": str(fee), "outputs": [], "warnings": [],
                   "addresses": addresses(tx)}}


def addresses(tx):
    """Segwit scripts through addr_segwit_from_bytes, others through scriptpubkey_to_address."""
    shown = []
    for j in range(w.tx_get_num_outputs(tx)):
        spk = w.tx_get_output_script(tx, j)
        try:
            kind = w.scriptpubkey_get_type(spk)
            if kind in (w.WALLY_SCRIPT_TYPE_P2WPKH, w.WALLY_SCRIPT_TYPE_P2WSH, w.WALLY_SCRIPT_TYPE_P2TR):
                shown.append({"index": j, "address": w.addr_segwit_from_bytes(spk, "bc", 0)})
            else:
                shown.append({"index": j, "address": w.scriptpubkey_to_address(spk, w.WALLY_NETWORK_BITCOIN_MAINNET)})
        except Exception:
            pass
    return shown


for line in sys.stdin:
    print(json.dumps(review(json.loads(line)["psbt"])), flush=True)
