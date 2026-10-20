/-
  File:      Grammatik/Gen/Druck/Einheit.lean
  Subject:   A WHOLE UNIT as Gabbro source text: the declaration of a member of the family (`Spez`, plain data) and a
             skeleton of the generator, printed as a `module` with its tables, statics, atomics, locks, foreign bodies,
             functions and the `concurrent` list of the declared starts.

  The bodies are printed by `Druck.lean`. What this file adds is what the model keeps outside the bodies and the language
  writes next to them: the `effects` clause of every function (the reads, writes and locks of its body and, transitively,
  of every function it calls -- the checker of the language demands it), a generous `costs <= N ops` and `held <= N ops`
  (the model has no cost; the bound is only large enough not to be the reason of a refusal), `requires Held(L)` for the
  locks a signature holds, and the layout.

  Partial like the body printer: a declaration feature without a clause (a function with reasons or a floor, a mark, a
  handler flag, a parameter of a type other than an integer range or a truth value) makes the whole unit unprintable and
  says which feature it was. The unit is then skipped, never printed wrongly.
-/
import Grammatik.Gen.Druck.Druck
import Grammatik.Gen.Abdeckung.Waehlen

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Gen.Druck

/-- The bound of every `costs` and `held` clause: large, so that it is never the reason a unit is refused. -/
def kostenGrenze : String := "100000"

/-- A type as source text; `none` for a type the printer does not know. -/
def Spez.druckTy : Ty → Except String String
  | .int lo hi => .ok (if lo ≥ 0 then s!"u64 in {lo} .. {hi}" else s!"i64 in {lo} .. {hi}")
  | .bool => .ok "bool"
  | .never => .ok "never"
  | _ => .error "unsupported type"

/-- The names of the entities of a member. -/
def Spez.namen (z : Spez) : Namen z.deklaration where
  tab := fun t => s!"T{(show Fin z.tabs.length from t).val}"
  feld := fun _ f => s!"f{(show Fin _ from f).val}"
  glob := fun g => s!"g{(show Fin z.globs.length from g).val}"
  lock := fun L => s!"L{(show Fin z.locks.length from L).val}"
  fn := fun f => s!"fn{(show Fin z.fns.length from f).val}"
  ax := fun a => s!"ax{(show Fin z.axs.length from a).val}"

/-- A comma list. -/
private def kommas (xs : List String) : String := String.intercalate ", " xs

/-- The initial value of a static of type `ty`: zero if the range holds it, else the nearest bound. -/
def Spez.anfang : Ty → String
  | .int lo hi => if lo > 0 then toString lo else if hi < 0 then s!"({hi})" else "0"
  | .bool => "false"
  | _ => "0"

/-- The effect items of a function BODY, before the closure over the callees. -/
def Spez.eigeneEffekte (z : Spez) (P : Programm z.deklaration) (f : z.deklaration.Fn) : List String :=
  letI : Zahlen := z.zahlen
  let n := z.fns.get f
  let nm := z.namen
  let lesen : List String := (Extraktion.endblockOrte (P.rumpf f)).map fun
    | .inl t => s!"reads {nm.tab t}.slots"
    | .inr g => s!"reads {nm.glob g}"
  let schreiben : List String :=
    ((List.finRange z.tabs.length).filter fun t => z.schreibt n t).map (fun t => s!"writes {nm.tab t}.slots") ++
    ((List.finRange z.globs.length).filter fun g => (z.sigRoh n).gschreibt.contains g.val).map (fun g => s!"writes {nm.glob g}")
  let sperren : List String :=
    ((List.finRange z.locks.length).filter fun L => nimmtB P f L || (z.haelt n).contains L).map
      fun L => s!"locks {nm.lock L}"
  lesen ++ schreiben ++ sperren

/-- The effect items of every function after `n` rounds of the closure over the callees. -/
def Spez.effekte (z : Spez) (P : Programm z.deklaration) : List (List String) :=
  letI : Zahlen := z.zahlen
  let fns : List z.deklaration.Fn := z.fnListe
  let eigen := fns.map (z.eigeneEffekte P)
  (List.range (fns.length + 1)).foldl
    (fun cur _ =>
      fns.map fun f =>
        let i := (fns.findIdx? (· == f)).getD 0
        let von := (fns.filter fun g => ruftB P f g).flatMap fun g => cur.getD ((fns.findIdx? (· == g)).getD 0) []
        ((eigen.getD i []) ++ von).eraseDups)
    eigen

/-- The call depth of every function: 0 for a function that calls nothing, one more than its deepest callee; a call of a
    foreign body counts as depth 1. A cycle ends at the number of functions. -/
def Spez.ebenen (z : Spez) (P : Programm z.deklaration) : List Nat :=
  letI : Zahlen := z.zahlen
  let fns : List z.deklaration.Fn := z.fnListe
  (List.range (fns.length + 1)).foldl
    (fun cur _ => fns.map fun f =>
      let von := (fns.filter fun g => ruftB P f g).map fun g => cur.getD ((fns.findIdx? (· == g)).getD 0) 0
      let ax := if (P.rumpf f).ants.isEmpty then 0 else 1
      Nat.max ax (if von.isEmpty then 0 else von.foldl Nat.max 0 + 1))
    (fns.map fun _ => 0)

/-- The `costs` bound of a function of call depth `e`: each level multiplies by 10 000, so a body that calls the level
    below any number of times below 10 000 stays inside it. -/
def kostenVon (e : Nat) : String := toString (10000 ^ (e + 1))

/-- One function as source text. -/
def Spez.druckFn (z : Spez) [Zahlen] (h : Haut z.deklaration) (eff : List String) (kosten : String) (f : z.deklaration.Fn) :
    Except String String := do
  let n := z.fns.get f
  let s := z.sigRoh n
  if s.gruende != 0 then throw "unsupported feature: function with reasons"
  -- The floor is not written in the language: it is the least rank the body itself takes in `locks` blocks. A declared
  -- floor is printable only when it is that one.
  let genommen := (List.finRange z.locks.length).filter fun L => nimmtB h.programm f L
  let abgeleitet : Option Int := (genommen.map fun L => (z.locks.get L).rang).foldl
    (fun a r => match a with | none => some r | some m => some (if m < r then m else r)) none
  if abgeleitet != s.boden then throw "unsupported feature: the declared floor is not the one the body derives (the model is wider than the language here)"
  if !s.konsumiert.isEmpty || !s.produziert.isEmpty then throw "unsupported feature: marks"
  let np := s.params.length
  let ps ← (s.params.zipIdx.map fun (t, j) => do
    pure s!"v{np - 1 - j} : {← Spez.druckTy t}").mapM id
  let erg ← match s.erg with
    | none => pure ""
    | some t => do pure s!" -> {← Spez.druckTy t}"
  let nm := z.namen
  let requires := ((z.haelt n).map fun L => s!"Held({nm.lock L})")
  let reqS := if requires.isEmpty then "" else s!"\n    requires {kommas requires}"
  let effS := if eff.isEmpty then "pure" else kommas eff
  let koerper ← Druck.druckEnd (vertragVon z.deklaration f) nm "    " (h.rumpf f)
  pure s!"impl fn {nm.fn f}({kommas ps}){erg}{reqS}\n    effects \{ {effS} }\n    costs   <= {kosten} ops\n\{\n{koerper}}\n"

/-- One foreign body as source text. -/
def Spez.druckAx (z : Spez) (a : z.deklaration.Ax) : Except String String := do
  let x := z.axs.get a
  if x.gruende != 0 then throw "unsupported feature: foreign body with reasons"
  let nm := z.namen
  let np := x.params.length
  let ps ← (x.params.zipIdx.map fun (t, j) => do
    pure s!"p{np - 1 - j} : {← Spez.druckTy t}").mapM id
  let erg ← match x.erg with
    | none => pure ""
    | some t => do pure s!" -> {← Spez.druckTy t}"
  let eff :=
    ((List.finRange z.tabs.length).filter fun t => x.schreibt.contains t.val).map (fun t => s!"writes {nm.tab t}.slots") ++
    ((List.finRange z.globs.length).filter fun g => x.gschreibt.contains g.val).map (fun g => s!"writes {nm.glob g}")
  let eff := if x.erg == some .never then eff ++ ["diverges"] else eff
  pure s!"extern fn {nm.ax a}({kommas ps}){erg} effects \{ {if eff.isEmpty then "pure" else kommas eff} } costs <= {kostenVon 0} ops;\n"

/-- The unit, under the numeric scheme of the member (the instance is an argument so that the `do` block stays one). -/
def Spez.quelltextMit (z : Spez) [Zahlen] (h : Haut z.deklaration) (ws : List z.deklaration.Fn) (name : String) :
    Except String String := do
  let nm := z.namen
  if !z.marken.isEmpty then throw "unsupported feature: marks"
  if !z.invs.isEmpty then throw "unsupported feature: invariants"
  if !z.regs.isEmpty then throw "unsupported feature: registers"
  let tabs ← (List.finRange z.tabs.length).mapM fun t => do
    let tz := z.tabs.get t
    let fs ← (tz.felder.zipIdx.map fun (fz, j) => do pure s!"        f{j} : {← Spez.druckTy fz.typ},").mapM id
    pure s!"table {nm.tab t} count {tz.count} \{\n    slot \{\n{String.intercalate "\n" fs}\n    }\n}\n"
  let globs ← (List.finRange z.globs.length).mapM fun g => do
    let gz := z.globs.get g
    let ty ← Spez.druckTy gz.typ
    if gz.atomar then
      pure s!"atomic {nm.glob g} : {ty} {if gz.nutzlast.isEmpty then "relaxed" else "release"};\n"
    else
      pure s!"static mut {nm.glob g} : {ty} = {Spez.anfang gz.typ};\n"
  let ebenen := z.ebenen h.programm
  let locks ← (List.finRange z.locks.length).mapM fun L => do
    let lz := z.locks.get L
    let schuetzt :=
      ((List.finRange z.tabs.length).filter fun t => (z.tabs.get t).sperre == some L.val).map nm.tab ++
      ((List.finRange z.globs.length).filter fun g => (z.globs.get g).sperre == some L.val).map nm.glob
    if schuetzt.isEmpty then throw "unsupported feature: lock protecting nothing (`protects` needs a place)"
    pure s!"lock {nm.lock L} protects \{ {kommas schuetzt} } rank {lz.rang} held <= {kostenVon (ebenen.foldl Nat.max 0)} ops{if lz.maskiert then " masks irqs" else ""};\n"
  let axs ← (List.finRange z.axs.length).mapM (z.druckAx)
  let eff := z.effekte h.programm
  if ebenen.any (· ≥ 4) then throw "unsupported feature: call chain deeper than 3 (cost bound would not fit 64 bits)"
  let fns ← z.fnListe.mapM fun f => do
    let i := (z.fnListe.findIdx? (· == f)).getD 0
    z.druckFn h (eff.getD i []) (kostenVon (ebenen.getD i 0)) f
  let start := if ws.isEmpty then "" else s!"concurrent \{ {kommas (ws.map nm.fn)} };\n"
  -- a function the hardware enters: an `entry … via idt` item that dispatches to it
  let eintritte := (z.fnListe.filter fun f => h.unterbricht f).map fun f =>
    let i := (show Fin z.fns.length from f).val
    s!"entry ent{i} vector {32 + i} via idt arch x86_64 \{\n    regs in  \{ }\n    regs out \{ }\n    preserves \{ rbx, rbp, r12, r13, r14, r15 }\n    clobbers  \{ rax, rcx, rdx, rsi, rdi, r8, r9, r10, r11 }\n    stack stk{i} per cpu nested never\n    dispatch zellen::{name}::{nm.fn f};\n}\n"
  pure s!"module zellen::{name} \{\n\n{String.intercalate "\n" tabs}{String.join globs}{String.join locks}{String.join axs}\n{String.intercalate "\n" fns}\n{start}{String.join eintritte}\n}\n"

/-- **The unit** of a member and a skeleton under the declared starts `ws`, as one `module`. -/
def Spez.quelltext (z : Spez) (h : Haut z.deklaration) (ws : List z.deklaration.Fn) (name : String) :
    Except String String :=
  @Spez.quelltextMit z z.zahlen h ws name

end Gabbro.Grammatik.Gen
