"""Krux's review of a PSBT, one JSON request per line on stdin and one verdict per line on stdout.

Runs Krux's own PSBTSigner under CPython with the device modules stubbed, as Krux's own tests do
(tests/conftest.py). What the sign page does around it (pages/home_pages/home.py: the warnings, then
outputs(), then add_signatures() when signing) is followed in `review`.
Usage: python krux.py <krux checkout>
"""
import base64
import json
import sys
import time
from unittest.mock import MagicMock

KRUX = sys.argv[1]
# This file's own directory would shadow Krux's package, which has no __init__.py
sys.path[0:1] = [KRUX + "/src", KRUX + "/tests"]

# The device's modules, stubbed as tests/conftest.py stubs them; BC-UR is never used for raw PSBT bytes
sys.modules["pyqrcode"] = MagicMock()
from shared_mocks import board_amigo  # noqa: E402
from embit.util import secp256k1  # noqa: E402
import random  # noqa: E402

for name in ["qrcode", "flash", "machine", "sensor", "lcd", "Maix", "fpioa_manager", "pmu", "image",
             "ucryptolib", "shannon", "uos", "deflate", "uhashlib_hw", "base32", "base43", "uUR"]:
    sys.modules[name] = MagicMock()
sys.modules["uUR"].UR = type("UR", (), {})  # PSBTSigner tells raw bytes from a UR with isinstance
sys.modules["secp256k1"] = MagicMock(wraps=secp256k1)
sys.modules["urandom"] = random
sys.modules["ujson"] = json
sys.modules["board"] = board_amigo()
time.sleep_ms = lambda *_: None
time.ticks_ms = lambda: 1
sys.print_exception = lambda *_: None

from embit.networks import NETWORKS  # noqa: E402
from krux.key import Key, TYPE_SINGLESIG, TYPE_MULTISIG  # noqa: E402
from krux.psbt import PSBTSigner, get_policy, CHANGE, SELF_TRANSFER  # noqa: E402
from krux.qr import FORMAT_NONE  # noqa: E402
from krux.wallet import Wallet  # noqa: E402

MNEMONIC = "abandon " * 11 + "about"
wallets = {}


def wallet_for(config):
    """A single-sig wallet of one script type, or a multisig one with its descriptor loaded"""
    key = json.dumps(config, sort_keys=True)
    if key not in wallets:
        if config["descriptor"]:
            # Krux derives its cosigner key from the script type, so a nested descriptor needs its own
            script = "p2sh-p2wsh" if config["descriptor"].startswith("sh(wsh(") else "p2wsh"
            w = Wallet(Key(MNEMONIC, TYPE_MULTISIG, NETWORKS["main"], script_type=script))
            w.load(config["descriptor"], FORMAT_NONE)
        else:
            w = Wallet(Key(MNEMONIC, TYPE_SINGLESIG, NETWORKS["main"], script_type=config["script"]))
        wallets[key] = w
    return wallets[key]


def review(req):
    wallet = wallet_for(req["config"])
    try:
        signer = PSBTSigner(wallet, base64.b64decode(req["psbt"]), FORMAT_NONE)
    except Exception as e:
        return {"error": "load", "detail": f"{type(e).__name__}: {e}"[:120]}
    warnings = []
    try:
        if signer.path_mismatch():
            warnings.append("path mismatch")
        if wallet.key.fingerprint != b"\x00\x00\x00\x00" and signer.fill_zero_fingerprint():
            warnings.append("fingerprint unset in PSBT")
        _, fee_percent = signer.outputs()
        if signer.unverified_input_amounts():
            warnings.append("unverified input amounts")
        if fee_percent >= 10.0:
            warnings.append("high fees")
        # outputs() renders text; the same classification, for its totals
        try:
            xpubs, origin_less = signer.xpubs()
        except Exception:
            xpubs, origin_less = [], None
        ours, spend, change = [], 0, 0
        for i, out in enumerate(signer.psbt.outputs):
            vout = signer.psbt.tx.vout[i]
            kind = signer._classify_output(get_policy(out, vout.script_pubkey, xpubs, origin_less), out)
            if kind in (CHANGE, SELF_TRANSFER):
                ours.append({"index": i, "verified": True})
                change += vout.value
            else:
                spend += vout.value
        inputs = sum(inp.utxo.value for inp in signer.psbt.inputs)
    except Exception as e:
        return {"error": "review", "detail": f"{type(e).__name__}: {e}"[:120]}
    try:
        signer.add_signatures()
    except Exception as e:
        return {"error": "sign", "detail": f"{type(e).__name__}: {e}"[:120]}
    # outputs() writes each address with format_address(), a space every four characters
    addresses = []
    for i, vout in enumerate(signer.psbt.tx.vout):
        try:
            addresses.append({"index": i, "address": vout.script_pubkey.address(network=wallet.key.network)})
        except Exception:
            pass
    return {"ok": {"input": str(inputs), "spend": str(spend), "change": str(change),
                   "fee": str(inputs - spend - change), "outputs": ours, "warnings": warnings, "addresses": addresses}}


for line in sys.stdin:
    print(json.dumps(review(json.loads(line))), flush=True)
