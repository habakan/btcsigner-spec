import VersoManual

open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace SpecManual

def besideCss := r#"
.beside { display: grid; grid-template-columns: minmax(0, 1fr); align-items: start; }
.beside > .beside-note { font-size: 0.9rem; line-height: 1.45; border-left: 2px solid #9db8c7; padding-left: 0.75rem; margin: 0 0 1rem; }
/* Long signatures scroll rather than clip. */
.beside .signature { overflow-x: auto; }
.beside > .beside-note:empty { display: none; }
.beside > .beside-note ul { margin: 0 0 0.6rem; padding-left: 1rem; }
.beside > .beside-note li { margin-bottom: 0.3rem; }
.beside > .beside-note p { margin: 0 0 0.6rem; }
@container main (width >= 860px) {
  .beside { grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); column-gap: 1.5rem; width: min(calc(100cqi - 3rem), 62rem); }
  .beside > .beside-note { margin-top: 1rem; }
  .beside .wide-only { display: none; }
  .beside .narrow-only { display: block; }
}
/* Past this width the text column is centered, so the pair spreads evenly from it. */
@container main (width >= 1212px) {
  .beside { --beside-width: min(calc(100cqi - 3rem), 68rem); width: var(--beside-width); margin-left: calc((100% - var(--beside-width)) / 2); }
}
"#

block_extension Block.beside where
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [besideCss]
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ _ content => do
      let code ← (content.extract 0 1).mapM goB
      let note ← (content.extract 1 content.size).mapM goB
      pure {{<div class="beside"><div class="beside-code">{{code}}</div><aside class="beside-note">{{note}}</aside></div>}}

/-- The first block, normally a definition, with the rest beside it as a note. -/
@[directive]
def beside : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.beside #[$[$(← contents.mapM elabBlock)],*])

block_extension Block.svg (source : String) where
  data := source
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some fun _ _ _ data _ => do
      let .str source := data
        | reportError s!"Expected SVG source, got {data.compress}" *> pure .empty
      pure (Verso.Output.Html.text false source)

/-- Inline SVG, for a figure links can sit in. -/
@[code_block]
def svg : CodeBlockExpanderOf Unit
  | (), str => ``(Verso.Doc.Block.other (Block.svg $(Lean.quote str.getString)) #[])

end SpecManual
