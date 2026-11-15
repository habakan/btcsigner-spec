"""Specter DIY's review of a PSBT, one JSON request per line on stdin and one verdict per line on stdout.

Runs WalletManager.sign_psbt itself under CPython, with the device modules stubbed as Specter's native
tests stub them (test/native_support.py). Its screens are replaced by ones that record what they show and
let the user go on, so a verdict is what the confirmation screen showed after every warning was accepted.
Usage: python specter.py <specter-diy checkout>
"""
import asyncio
import base64
import json
import sys
import tempfile
from io import BytesIO

SPECTER = sys.argv[1]
# As test/run_native_tests.py orders them; this file's own directory would shadow Specter's platform module
sys.path[0:1] = [SPECTER + "/src", SPECTER + "/f469-disco/libs/common/embit/src", SPECTER + "/test"]
sys.path += [SPECTER + "/f469-disco/libs/common", SPECTER + "/f469-disco/libs/unix"]

from native_support import setup_native_stubs  # noqa: E402

setup_native_stubs()

shown = []


class Prompt:
    def __init__(self, title, message, *args, **kwargs):
        self.title, self.message = title, message


class TransactionScreen:
    def __init__(self, title, meta):
        self.title, self.meta = title, meta


from app import BaseApp  # noqa: E402
import apps.wallets.manager as manager  # noqa: E402
from apps.wallets.manager import WalletManager, RAW_STREAM  # noqa: E402
from keystore.ram import RAMKeyStore  # noqa: E402

# The stubs above already imported the manager, so its screens are swapped where it looks them up
manager.Prompt, manager.TransactionScreen = Prompt, TransactionScreen

MNEMONIC = "abandon " * 11 + "about"
BaseApp.TEMPDIR = tempfile.mkdtemp()
keystore = RAMKeyStore()
keystore.show_loader = lambda *args, **kwargs: None
keystore.set_mnemonic(MNEMONIC)
SINGLE = {"p2wpkh": ("wpkh(%s)", "84h"), "p2sh-p2wpkh": ("sh(wpkh(%s))", "49h"), "p2tr": ("tr(%s)", "86h"),
          "p2pkh": ("pkh(%s)", "44h")}
managers = {}


def single(script):
    template, purpose = SINGLE[script]
    xpub = keystore.get_xpub("m/%s/0h/0h" % purpose).to_base58()
    return template % ("[%s/%s/0h/0h]%s/{0,1}/*" % (keystore.fingerprint.hex(), purpose, xpub))


def manager_for(config):
    """The default P2WPKH wallet a device creates, and the one the config names besides it"""
    key = json.dumps(config, sort_keys=True)
    if key not in managers:
        m = WalletManager(tempfile.mkdtemp())
        m.init(keystore, "main", lambda *args, **kwargs: None, None)
        desc = config["descriptor"] or (single(config["script"]) if config["script"] != "p2wpkh" else None)
        if desc:
            w = m.WalletClass.parse("Wallet&" + desc, m.path + "/1")
            w.save(keystore)
            m.wallets.append(w)
        managers[key] = m
    return managers[key]


async def show(screen):
    shown.append(screen)
    return True


def review(req):
    m = manager_for(req["config"])
    shown.clear()
    try:
        signed = asyncio.run(m.sign_psbt(BytesIO(base64.b64decode(req["psbt"])), show, encoding=RAW_STREAM))
    except Exception as e:
        return {"error": type(e).__name__, "detail": str(e).strip().split("\n")[0][:120]}
    final = [s for s in shown if isinstance(s, TransactionScreen)]
    if not signed or not final:
        return {"error": "cancelled", "detail": "no confirmation screen"}
    meta = final[-1].meta
    warnings = [s.message.strip().split("\n")[0] for s in shown if isinstance(s, Prompt)]
    warnings += meta.get("warnings", [])
    ours, spend, change, addresses = [], 0, 0, []
    for i, out in enumerate(meta["outputs"]):
        warnings += out.get("warnings", [])
        if out["change"]:
            ours.append({"index": i, "verified": True})
            change += out["value"]
        else:
            spend += out["value"]
        addresses.append({"index": i, "address": out["address"]})
    inputs = sum(inp["value"] for inp in meta["inputs"])
    return {"ok": {"input": str(inputs), "spend": str(spend), "change": str(change), "fee": str(meta["fee"]),
                   "outputs": ours, "warnings": warnings, "addresses": addresses}}


for line in sys.stdin:
    print(json.dumps(review(json.loads(line))), flush=True)
