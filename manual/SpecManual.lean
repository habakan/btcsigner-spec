import VersoManual
import SpecManual.Beside
import SpecManual.Model
import SpecManual.Guarantees
import SpecManual.Limits
import SpecManual.Comparing
import SpecManual.Bip174

open Verso.Genre Manual
open SpecManual

#doc (Manual) "btcsigner-spec" =>
%%%
authors := ["habakan"]
shortTitle := "btcsigner-spec"
%%%

Before a Bitcoin signer signs, it decides what a transaction spends, what it pays and to whom, and what
fee it leaves, and it shows that to a person. If that review is wrong, the person approves one thing and
signs another.

btcsigner-spec writes that review down as a model in Lean 4, proves what the model guarantees, and runs
real signers against it. The model has no dependencies. Each signer runs its own code at a pinned commit.

This manual is built against the model itself. Every definition and theorem shown here is read from the
compiled source, so a renamed or removed theorem fails the manual's build.



The whole path is below. Boxes link to their definitions, and the numbers link to the guarantees.

```svg
<svg viewBox="0 0 760 648" role="img" aria-labelledby="f-t" style="display:block;width:100%;max-width:760px;margin:1rem 0"><title id="f-t">A PSBT is read by adapters into Tx and Env. review either refuses with an Error or leads to display and State. A person approves the screen, sign produces signatures, and a coordinator assembles the transaction.</title><style>.f-band{font:600 12px var(--verso-text-font-family,sans-serif);fill:#44606f}.f-title{font:600 14px var(--verso-text-font-family,sans-serif);fill:#111}.f-code{font:600 14px var(--verso-code-font-family,monospace);fill:#111}.f-sub{font:12px var(--verso-text-font-family,sans-serif);fill:#333}.f-step{font:12.5px var(--verso-text-font-family,sans-serif);fill:#333}.f-mono{font:600 12.5px var(--verso-code-font-family,monospace);fill:#111}.f-num{fill:#777 !important}.f-chip{font:700 11px sans-serif;fill:#fff}.f-link{fill:#111}a:hover rect{fill:#e3f0f6}</style><defs><marker id="f-arrow" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="8" markerHeight="8" orient="auto"><path d="M0 0L8 4L0 8z" fill="#44606f"/></marker></defs><rect x="1" y="1" width="758" height="104" rx="10" fill="#f5f5f5" stroke="#cfcfcf"/><text x="744" y="21" text-anchor="end" class="f-band">Tested, not proved</text><rect x="20" y="34" width="150" height="54" rx="6" fill="#fff" stroke="#6f96aa"/><text x="95.0" y="56.0" text-anchor="middle" class="f-title">PSBT</text><text x="95.0" y="74.0" text-anchor="middle" class="f-sub">BIP 174 bytes</text><rect x="230" y="34" width="300" height="54" rx="6" fill="#fff" stroke="#6f96aa"/><text x="380.0" y="56.0" text-anchor="middle" class="f-title">Adapters</text><text x="380.0" y="74.0" text-anchor="middle" class="f-sub">read the PSBT, and work out what the seed owns</text><path d="M170 61H226" fill="none" stroke="#44606f" stroke-width="1.4" marker-end="url(#f-arrow)"/><rect x="1" y="116" width="758" height="388" rx="10" fill="#eef5f8" stroke="#9db8c7"/><text x="744" y="136" text-anchor="end" class="f-band">The model: proved in Lean</text><a href="The-model/#SignerSpec___Tx___mk"><rect x="20" y="148" width="200" height="52" rx="6" fill="#fff" stroke="#6f96aa"/><text x="120.0" y="169.0" text-anchor="middle" class="f-code">Tx</text><text x="120.0" y="187.0" text-anchor="middle" class="f-sub">what the PSBT says, not trusted</text></a><a href="The-model/#SignerSpec___Env___mk"><rect x="240" y="148" width="200" height="52" rx="6" fill="#fff" stroke="#6f96aa"/><text x="340.0" y="169.0" text-anchor="middle" class="f-code">Env</text><text x="340.0" y="187.0" text-anchor="middle" class="f-sub">what the seed answers</text></a><path d="M340 88V118H120V144" fill="none" stroke="#44606f" stroke-width="1.4" marker-end="url(#f-arrow)"/><path d="M380 88V144" fill="none" stroke="#44606f" stroke-width="1.4" marker-end="url(#f-arrow)"/><a href="The-model/#SignerSpec___review"><rect x="20" y="224" width="420" height="176" rx="6" fill="#fff" stroke="#6f96aa"/><text x="36" y="247" class="f-code">review env tx</text></a><text x="36" y="274" class="f-step f-num">1</text><text x="52" y="274" class="f-mono">formatOk</text><text x="196" y="274" class="f-step">sizes, amounts within 21M BTC</text><text x="36" y="296" class="f-step f-num">2</text><text x="52" y="296" class="f-mono">scanInputs</text><text x="196" y="296" class="f-step">ours? sighash? wallet?</text><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Nothing-on-the-PSBT___s-word-alone"><circle cx="420" cy="292" r="10" fill="#2f6f8f"/><text x="420" y="296" text-anchor="middle" class="f-chip">2</text></a><text x="36" y="318" class="f-step f-num">3</text><text x="52" y="318" class="f-mono">any input to sign?</text><text x="196" y="318" class="f-step"></text><text x="36" y="340" class="f-step f-num">4</text><text x="52" y="340" class="f-mono">checkPrev</text><text x="196" y="340" class="f-step">previous transactions agree</text><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Input-amounts"><circle cx="420" cy="336" r="10" fill="#2f6f8f"/><text x="420" y="340" text-anchor="middle" class="f-chip">5</text></a><text x="36" y="362" class="f-step f-num">5</text><text x="52" y="362" class="f-mono">sumOutputs</text><text x="196" y="362" class="f-step">totals, fee not negative</text><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--The-fee"><circle cx="420" cy="358" r="10" fill="#2f6f8f"/><text x="420" y="362" text-anchor="middle" class="f-chip">1</text></a><text x="36" y="384" class="f-step f-num">6</text><text x="52" y="384" class="f-mono">outputOwner</text><text x="196" y="384" class="f-step">external, change or self</text><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Nothing-on-the-PSBT___s-word-alone"><circle cx="420" cy="380" r="10" fill="#2f6f8f"/><text x="420" y="384" text-anchor="middle" class="f-chip">2</text></a><a href="The-model/#SignerSpec___Error___format"><rect x="500" y="281" width="240" height="62" rx="6" fill="#fff" stroke="#6f96aa"/><text x="620.0" y="307.0" text-anchor="middle" class="f-code">Error</text><text x="620.0" y="325.0" text-anchor="middle" class="f-sub">one reason, and nothing is signed</text></a><path d="M440 312H496" fill="none" stroke="#44606f" stroke-width="1.4" marker-end="url(#f-arrow)"/><text x="448" y="303" class="f-sub">refuse</text><a href="The-model/#SignerSpec___display"><rect x="20" y="436" width="190" height="52" rx="6" fill="#fff" stroke="#6f96aa"/><text x="115.0" y="457.0" text-anchor="middle" class="f-code">display</text><text x="115.0" y="475.0" text-anchor="middle" class="f-sub">fee, spend, every output</text></a><a href="The-model/#SignerSpec___State___mk"><rect x="230" y="436" width="190" height="52" rx="6" fill="#fff" stroke="#6f96aa"/><text x="325.0" y="457.0" text-anchor="middle" class="f-code">State</text><text x="325.0" y="475.0" text-anchor="middle" class="f-sub">the exact transaction approved</text></a><a href="The-model/#SignerSpec___sign"><rect x="500" y="436" width="240" height="52" rx="6" fill="#fff" stroke="#6f96aa"/><text x="620.0" y="457.0" text-anchor="middle" class="f-code">sign</text><text x="620.0" y="475.0" text-anchor="middle" class="f-sub">only reviewed inputs, once</text></a><path d="M115 400V432" fill="none" stroke="#44606f" stroke-width="1.4" marker-end="url(#f-arrow)"/><text x="121" y="420" class="f-sub">ok</text><path d="M325 400V432" fill="none" stroke="#44606f" stroke-width="1.4" marker-end="url(#f-arrow)"/><text x="331" y="420" class="f-sub">ok</text><path d="M420 462H496" fill="none" stroke="#44606f" stroke-width="1.4" marker-end="url(#f-arrow)"/><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--The-screen"><circle cx="204" cy="442" r="10" fill="#2f6f8f"/><text x="204" y="446" text-anchor="middle" class="f-chip">3</text></a><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Signing"><circle cx="734" cy="442" r="10" fill="#2f6f8f"/><text x="734" y="446" text-anchor="middle" class="f-chip">4</text></a><rect x="1" y="516" width="758" height="88" rx="10" fill="#fbf7ef" stroke="#dccfae"/><text x="400" y="536" text-anchor="middle" class="f-band">Outside the signer</text><rect x="20" y="544" width="190" height="50" rx="6" fill="#fff" stroke="#6f96aa"/><text x="115.0" y="564.0" text-anchor="middle" class="f-title">Person</text><text x="115.0" y="582.0" text-anchor="middle" class="f-sub">reads the screen and approves</text><rect x="590" y="544" width="150" height="50" rx="6" fill="#fff" stroke="#6f96aa"/><text x="665.0" y="564.0" text-anchor="middle" class="f-title">Coordinator</text><text x="665.0" y="582.0" text-anchor="middle" class="f-sub">assembles the transaction</text><path d="M115 488V540" fill="none" stroke="#44606f" stroke-width="1.4" marker-end="url(#f-arrow)"/><path d="M210 569H540V492" fill="none" stroke="#44606f" stroke-width="1.4" marker-end="url(#f-arrow)"/><text x="350" y="562" class="f-sub">approve</text><path d="M665 488V540" fill="none" stroke="#44606f" stroke-width="1.4" marker-end="url(#f-arrow)"/><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Signatures-across-reviews"><circle cx="734" cy="550" r="10" fill="#2f6f8f"/><text x="734" y="554" text-anchor="middle" class="f-chip">6</text></a><text x="16" y="632" class="f-band">Proved separately</text><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Messages"><circle cx="150" cy="628" r="10" fill="#2f6f8f"/><text x="150" y="632" text-anchor="middle" class="f-chip">7</text></a><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Messages"><text x="165" y="632" class="f-sub f-link">Messages</text></a><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Mnemonics"><circle cx="270" cy="628" r="10" fill="#2f6f8f"/><text x="270" y="632" text-anchor="middle" class="f-chip">8</text></a><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Mnemonics"><text x="285" y="632" class="f-sub f-link">Mnemonics</text></a><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Reading-a-PSBT"><circle cx="400" cy="628" r="10" fill="#2f6f8f"/><text x="400" y="632" text-anchor="middle" class="f-chip">9</text></a><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Reading-a-PSBT"><text x="415" y="632" class="f-sub f-link">Reading a PSBT</text></a><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Multisig-wallets"><circle cx="560" cy="628" r="10" fill="#2f6f8f"/><text x="560" y="632" text-anchor="middle" class="f-chip">10</text></a><a href="What-the-model-guarantees/#btcsigner-spec--What-the-model-guarantees--Multisig-wallets"><text x="575" y="632" class="f-sub f-link">Multisig wallets</text></a></svg>
```

Two kinds of claim appear here, and they are different:

 * What the model guarantees is *proved*. See {ref "guarantees"}[the guarantees].
 * Whether a signer behaves like the model is *tested*, not proved. See {ref "comparing"}[comparing a signer].

{ref "limits"}[What this does not prove] lists what the model leaves out and what the proofs assume.

Links to the BIPs are to the text at commit `ada3419` of `bitcoin/bips`, so they keep pointing at what was read.

To check every proof and the published test vectors yourself, with the toolchain in `lean-toolchain`:

```
make check
```

{include 1 SpecManual.Model}

{include 1 SpecManual.Guarantees}

{include 1 SpecManual.Limits}

{include 1 SpecManual.Comparing}

{include 1 SpecManual.Bip174}
