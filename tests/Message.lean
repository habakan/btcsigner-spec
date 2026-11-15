import SignerSpec.Message
/-! What a message review shows, on the cases that decide it. -/
open SignerSpec

def shown (s : String) : MsgKind × String := let (k, t) := showMessage s.toUTF8.toList; (k, String.ofList t)

#guard shown "Hello, world" == (MsgKind.text, "Hello, world")
#guard shown "" == (MsgKind.text, "")
#guard shown "a " == (MsgKind.hex, "6120")
#guard shown " a" == (MsgKind.hex, "2061")
#guard shown "a  b" == (MsgKind.hex, "61202062")
#guard shown "a\nb" == (MsgKind.hex, "610a62")
#guard shown "café" == (MsgKind.hex, "636166c3a9")
