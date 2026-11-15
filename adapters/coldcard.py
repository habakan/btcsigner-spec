"""Coldcard's review of a PSBT, one JSON request per line on stdin and one verdict per line on stdout.

Runs Coldcard's desktop simulator, the device's own firmware under MicroPython, and asks it over its USB protocol for
the text of the approval screen (STXN_VISUALIZE), the screen the user presses OK on. Amounts are in sats (setting rz).
The screen shows no input total, so it is taken as what it shows sent, the change and the fee.
Usage: python coldcard.py <Coldcard firmware checkout>
"""
import base64
import json
import os
import re
import subprocess
import sys
import time

SRC = sys.argv[1]
sys.path.insert(0, SRC + "/external/ckcc-protocol")

from ckcc.client import ColdcardDevice  # noqa: E402
from ckcc.constants import STXN_VISUALIZE  # noqa: E402
from ckcc.protocol import CCProtocolPacker, CCProtoError, CCUserRefused  # noqa: E402

MNEMONIC = "abandon " * 11 + "about"
# Records, beside the text, which outputs the firmware took as change and how it named each one
HOOK = """
import auth
def _summary(self, msg, _orig=auth.ApproveTransaction.output_summary_text):
    import auth
    auth.SPEC_OUTS = [(i, self.psbt.outputs[i].is_change, self.render_output(o)[1]) for i, o in self.psbt.output_iter()]
    return _orig(self, msg)
auth.ApproveTransaction.output_summary_text = _summary
"""

sim, dev, current = None, None, None


def start(config):
    """A fresh simulator for each config, so a wallet registered for one is not there for the next"""
    global sim, dev
    stop()
    sim = subprocess.Popen([sys.executable, "simulator.py", "--headless", "--eff", "--segregate", "--seed", MNEMONIC],
                           cwd=SRC + "/unix", stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, start_new_session=True)
    sock = "/tmp/ckcc-simulator-%d.sock" % sim.pid
    for _ in range(300):
        try:
            dev = ColdcardDevice(sn=sock, is_simulator=True)
            break
        except Exception:
            time.sleep(0.1)
    else:
        raise RuntimeError("simulator did not start")
    for line in ("settings.set('chain', 'BTC')", "settings.set('rz', 0)"):
        assert run(line) == "", line
    assert run(HOOK) == ""
    if config.get("descriptor"):
        enroll(config["descriptor"])


def stop():
    if sim and sim.poll() is None:
        os.killpg(sim.pid, 15)
        sim.wait()


def run(code):
    return dev.send_recv(b"EXEC" + code.encode(), timeout=60000, encrypt=False).decode()


def story():
    return run("import sim_display; RV.write('\\0'.join(sim_display.story or []))").split("\0")


def enroll(descriptor):
    data = descriptor.encode()
    dev.send_recv(CCProtocolPacker.multisig_enroll(*dev.upload_file(data)))
    for _ in range(100):
        if "Create new multisig" in " ".join(story()):
            break
        time.sleep(0.05)
    dev.send_recv(CCProtocolPacker.sim_keypress(b"y"))
    time.sleep(0.2)


def sats(text, label):
    m = re.search(label + r"(\d+) sats", text)
    return int(m.group(1)) if m else None


def review(req):
    global current
    key = json.dumps(req["config"], sort_keys=True)
    if key != current:
        start(req["config"])
        current = key
    psbt = base64.b64decode(req["psbt"])
    run("import auth; auth.SPEC_OUTS = None")
    try:
        dev.send_recv(CCProtocolPacker.sign_transaction(*dev.upload_file(psbt), flags=STXN_VISUALIZE))
        done, t0 = None, time.time()
        while done is None:
            done = dev.send_recv(CCProtocolPacker.get_signed_txn(), timeout=None)
            if done is None and time.time() - t0 > 20:
                # A question before the screen, such as importing a multisig wallet the PSBT names
                shown = " ".join(story()).strip()
                dev.send_recv(CCProtocolPacker.sim_keypress(b"x"))
                return {"error": "prompt", "detail": shown.split("\n")[0][:120]}
            time.sleep(0.01)
    except (CCProtoError, CCUserRefused) as e:
        return {"error": type(e).__name__, "detail": str(e).replace("Coldcard Error: ", "").strip().split("\n")[0][:120]}
    text = dev.download_file(*done).decode()
    outs = json.loads(run("import auth, ujson; RV.write(ujson.dumps(auth.SPEC_OUTS))") or "null")
    warnings = re.findall(r"^- ([^:\n]+): ", text.split("---WARNING---", 1)[1], re.M) if "---WARNING---" in text else []
    fee = sats(text, "Network fee ")
    if fee is None or outs is None:
        return {"error": "unparsed", "detail": text[:120].replace("\n", " ")}
    change = sats(text, "Change back:\n") or 0
    spend = sats(text, "Sending ")
    if spend is None:
        spend = 0  # "Consolidating ... within wallet": everything goes back as change
    return {"ok": {"input": str(spend + change + fee), "spend": str(spend), "change": str(change), "fee": str(fee),
                   "outputs": [{"index": i, "verified": True} for i, ch, _ in outs if ch],
                   "warnings": warnings,
                   "addresses": [{"index": i, "address": a.lstrip("\x02")} for i, ch, a in outs]}}


try:
    for line in sys.stdin:
        print(json.dumps(review(json.loads(line))), flush=True)
finally:
    stop()
