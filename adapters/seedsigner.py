"""SeedSigner's review of a PSBT, one JSON request per line on stdin and one verdict per line on stdout.

Runs SeedSigner's own PSBTParser. What its screens then do with a change output (PSBTChangeDetailsView in
views/psbt_views.py) is mirrored in `verify`, since the view itself needs the GUI.
Usage: python seedsigner.py <seedsigner checkout>/src
"""
import base64
import json
import sys

sys.path.insert(0, sys.argv[1])

from embit import script  # noqa: E402
from embit.descriptor import Descriptor  # noqa: E402
from embit.networks import NETWORKS  # noqa: E402
from embit.psbt import PSBT  # noqa: E402
from seedsigner.models.psbt_parser import PSBTParser  # noqa: E402
from seedsigner.models.seed import Seed  # noqa: E402
from seedsigner.models.settings import SettingsConstants  # noqa: E402

# The math screen (gui/screens/psbt_screens.py PSBTMathScreen) writes its amounts before it draws: its own
# __post_init__ runs with the display's modules stubbed, as tests/base.py stubs them, and stops at the first draw
from unittest.mock import MagicMock  # noqa: E402
for name in ["PIL", "RPi", "RPi.GPIO", "qrcode", "qrcode.image", "qrcode.image.styledpil", "qrcode.image.styles",
             "qrcode.image.styles.moduledrawers", "seedsigner.gui.renderer", "seedsigner.hardware.buttons"]:
    sys.modules.setdefault(name, MagicMock())
import contextlib  # noqa: E402
with contextlib.redirect_stdout(sys.stderr):  # it prints the locale it sets, and stdout carries the verdicts
    from seedsigner.gui.screens import psbt_screens
    from seedsigner.gui.screens.screen import ButtonListScreen


class Drawn(Exception):
    pass


def first_draw(*_):
    raise Drawn


ButtonListScreen.__post_init__ = lambda self: None
psbt_screens.Image.new = first_draw


def math_screen(input_amount, spend, fee, change, recipients):
    """Each amount as the math screen writes it, with the denomination it names for the column"""
    s = psbt_screens.PSBTMathScreen.__new__(psbt_screens.PSBTMathScreen)
    s.input_amount, s.num_inputs, s.spend_amount, s.fee_amount, s.change_amount, s.num_recipients = \
        input_amount, 1, spend, fee, change, recipients
    s.canvas_width, s.buttons, s.top_nav = 240, [MagicMock()], MagicMock()
    try:
        s.__post_init__()
    except Drawn as e:
        tb = e.__traceback__
        while tb.tb_frame.f_locals.get("self") is not s:
            tb = tb.tb_next
        unit = tb.tb_frame.f_locals["denomination"]
    # Past 1M sats the column is btc but the fee stays in sats, written with no unit
    fee_unit = "" if unit == "btc" else " " + unit
    rows = [(input_amount, s.input_amount, " " + unit)] + ([(spend, s.spend_amount, " " + unit)] if recipients else []) + \
        [(fee, s.fee_amount, fee_unit), (change, s.change_amount, " " + unit)]
    return [{"sats": str(v), "text": t.strip() + u} for v, t, u in rows]


NETWORK = SettingsConstants.MAINNET
seed = Seed(("abandon " * 11 + "about").split())
FP = seed.get_fingerprint(NETWORK)


def verify(parser, n, change, descriptor):
    """True, False (the address verification failed screen), "unverified" (multisig with no descriptor
    loaded, which the user may skip) or "unsupported" (no derivation of ours: NotYetImplementedView)"""
    if FP not in change["fingerprint"]:
        return "unsupported"
    path = change["derivation_path"][change["fingerprint"].index(FP)]
    if parser.is_multisig:
        return parser.verify_multisig_output(descriptor, change_num=n) if descriptor else "unverified"
    script_type = script.address_to_scriptpubkey(change["address"]).script_type()
    xpub = seed.get_xpub(wallet_path="/".join(path.split("/")[:-2]), network=NETWORK)
    key = xpub.derive("/".join(path.split("/")[-2:])).key
    net = NETWORKS[SettingsConstants.map_network_to_embit(NETWORK)]
    if script_type == "p2sh":
        calc = script.p2sh(script.p2wpkh(key)).address(network=net)
    else:
        calc = getattr(script, script_type)(key).address(network=net)
    return change["address"] == calc


def review(req):
    try:
        p = PSBT.parse(base64.b64decode(req["psbt"]))
    except Exception as e:
        return {"error": "parse", "detail": f"{type(e).__name__}: {e}"[:120]}
    if not PSBTParser.has_matching_input_fingerprint(psbt=p, seed=seed, network=NETWORK):
        return {"error": "no-matching-fingerprint"}
    try:
        parser = PSBTParser(p=p, seed=seed, network=NETWORK)
        d = req["config"]["descriptor"]
        descriptor = Descriptor.from_string(d) if d else None
        change = [{"index": c["output_index"], "verified": verify(parser, n, c, descriptor)}
                  for n, c in enumerate(parser.change_data)]
    except Exception as e:
        return {"error": "parser", "detail": f"{type(e).__name__}: {e}"[:120]}
    # Destinations are listed in output order, skipping change and OP_RETURN, as the parser fills them
    shown = {c["output_index"]: c["address"] for c in parser.change_data}
    rest = [i for i, o in enumerate(p.tx.vout) if i not in shown and o.script_pubkey.data[:1] != b"\x6a"]
    shown.update(zip(rest, parser.destination_addresses))
    # Newer parsers show what OP_RETURN outputs burn on its own line; it leaves the wallet like a spend
    spend = parser.spend_amount + getattr(parser, "op_return_amount", 0)
    return {"ok": {"input": str(parser.input_amount), "spend": str(spend),
                   "change": str(parser.change_amount), "fee": str(parser.fee_amount), "outputs": change,
                   "addresses": [{"index": i, "address": a} for i, a in sorted(shown.items())],
                   "amounts": math_screen(parser.input_amount, spend, parser.fee_amount, parser.change_amount,
                                          parser.num_destinations)}}


def format_edges(req):
    """Each edge value as the input total, and beside a 2 BTC input as the fee, the spend and the change"""
    amounts = []
    for v in map(int, req["format"]):
        amounts += math_screen(v, 0, 0, 0, 0)[:1]
        amounts += math_screen(200000000, v, v, v, 1)[1:]
    return {"amounts": amounts}


for line in sys.stdin:
    req = json.loads(line)
    print(json.dumps(format_edges(req) if "format" in req else review(req)), flush=True)
