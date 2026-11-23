/-
  File:      Grammatik/Zielsatz/Waechter/Formen.lean
  Subject:   GUARD 4 (B24 step 0, `dokumente/PERFECT-MODEL.md` §6.5): ONE SATISFIABILITY LEMMA PER FORM. Every constructor of `Stmt`,
             `Block`, `Endblock` and `Expr` is covered by an `_erfuellbar` lemma -- an instance in which the form
             occurs and the premises of the theorems over it hold jointly -- or stands on the ratchet list of
             today's uncovered constructors. A NEW constructor without a lemma fails the build.

  REGISTRY. `deckt` maps each registered lemma to the constructors it is meant to cover. The table is checked:
  * every name resolves at elaboration (the double-backtick names), every lemma is a theorem named `*_erfuellbar`
    or `*_erfuellbar_*`, every constructor belongs to one of the four families;
  * every claim is VERIFIED: the constructor occurs in the lemma's instance -- its statement, its proof term, or the
    body of a closed definition reached from them (a definition with no explicit argument: a witness program, its
    bodies, its declaration). Definitions with explicit arguments (elaborators, rewriters, checkers) are not
    followed, so a lemma about a translation function does not cover every form the function can build.
  The proof terms are read through `import all` of the lemma modules (the module system exports theorems without
  their proofs).
  RATCHET: `offen` lists today's uncovered constructors; a constructor that becomes covered fails until it is
  removed from the list, so the list only shrinks.
-/
module
public import Grammatik.Zielsatz.Waechter.Grundlagen
public import Grammatik.Bausteine.Arena.BlockScope
import all Grammatik.Bausteine.Arena.BlockScope
public import Grammatik.Bausteine.Kernzelle.Erfuellbarkeit
import all Grammatik.Bausteine.Kernzelle.Erfuellbarkeit
public import Grammatik.Kern.Syntax.Marken.Owner.Erfuellbarkeit
import all Grammatik.Kern.Syntax.Marken.Owner.Erfuellbarkeit
public import Grammatik.Korpus.Programme.Einheit104
import all Grammatik.Korpus.Programme.Einheit104
public import Grammatik.Parser.Elab.UebersetzeAllg.ValueSlices
import all Grammatik.Parser.Elab.UebersetzeAllg.ValueSlices
public import Grammatik.Parser.Elab.UebersetzeAllg.ArithmeticSlices
import all Grammatik.Parser.Elab.UebersetzeAllg.ArithmeticSlices
public import Grammatik.Parser.Elab.UebersetzeAllg.RecordLaws
import all Grammatik.Parser.Elab.UebersetzeAllg.RecordLaws
public import Grammatik.Parser.Elab.UebersetzeAllg.StringSliceObservations
import all Grammatik.Parser.Elab.UebersetzeAllg.StringSliceObservations
public import Grammatik.Parser.Elab.UebersetzeAllg.RuntimeSlices
import all Grammatik.Parser.Elab.UebersetzeAllg.RuntimeSlices
public import Grammatik.Parser.Elab.Modules.EffectGroups
import all Grammatik.Parser.Elab.Modules.EffectGroups
public import Grammatik.Parser.Elab.Uebersetze.Folds.SpecArguments
import all Grammatik.Parser.Elab.Uebersetze.Folds.SpecArguments
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
public import Grammatik.Parser.Elab.Uebersetze.Records.Update
import all Grammatik.Parser.Elab.Uebersetze.Records.Update
public import Grammatik.Code.Conc.Erfuellbarkeit
import all Grammatik.Code.Conc.Erfuellbarkeit
public import Grammatik.Isabelle.Table_Induktion
import all Grammatik.Isabelle.Table_Induktion
public import Grammatik.Logik.Ruf.Maschine.Erfuellbarkeit
import all Grammatik.Logik.Ruf.Maschine.Erfuellbarkeit
public import Grammatik.Niedrig.Erfuellbarkeit.Satz
import all Grammatik.Niedrig.Erfuellbarkeit.Satz
public import Grammatik.Niedrig.Konstrukte.Schnitt
import all Grammatik.Niedrig.Konstrukte.Schnitt
public import Grammatik.Niedrig.Konstrukte.SliceCheck
import all Grammatik.Niedrig.Konstrukte.SliceCheck
public import Grammatik.Niedrig.Konstrukte.SliceCarrier
import all Grammatik.Niedrig.Konstrukte.SliceCarrier
public import Grammatik.Nebenlaeufigkeit.Async.Regeln
import all Grammatik.Nebenlaeufigkeit.Async.Regeln
public import Grammatik.Nebenlaeufigkeit.Async.Representation.CheckedDispatch
import all Grammatik.Nebenlaeufigkeit.Async.Representation.CheckedDispatch
public import Grammatik.Zielsatz.Kern.Erfuellbarkeit
import all Grammatik.Zielsatz.Kern.Erfuellbarkeit
public import Grammatik.Zielsatz.Atomar.Erfuellbarkeit
import all Grammatik.Zielsatz.Atomar.Erfuellbarkeit
meta import Lean
meta import Grammatik.Zielsatz.Waechter.Grundlagen
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Waechter.Formen

open Lean Meta

/-- The families whose constructors are the forms. -/
def familien : List Name := [``Stmt, ``Block, ``Endblock, ``Expr]

/-- Is the name a satisfiability lemma by the convention of AGENTS.md §3 (`NAME_erfuellbar`)? -/
def istErfuellbarName (n : Name) : Bool :=
  let s := (n.componentsRev.headD .anonymous).toString
  s.endsWith "_erfuellbar" || (s.splitOn "_erfuellbar_").length > 1

/-- Has the type explicit arguments? -/
def explizit : Lean.Expr → Bool
  | .forallE _ _ b bi => bi == .default || explizit b
  | _ => false

/-- The constructors of the families occurring in the instance of a lemma: its statement and proof, then the
    bodies of closed definitions (no explicit argument) reached from them. -/
partial def instanz (env : Environment) (lemma : Name) : Std.HashSet Name := Id.run do
  let mut gesehen : Std.HashSet Name := {}
  let mut ks : Std.HashSet Name := {}
  let mut offen := [lemma]
  while !offen.isEmpty do
    match offen with
    | [] => pure ()
    | n :: rest =>
      offen := rest
      if gesehen.contains n || !imProjekt env n then continue
      gesehen := gesehen.insert n
      match env.find? n with
      | some (.ctorInfo c) => if familien.contains c.induct then ks := ks.insert n
      | some (.thmInfo t) =>
        if n == lemma then offen := (t.type.getUsedConstants ++ t.value.getUsedConstants).toList ++ offen
      | some (.defnInfo d) =>
        if !explizit d.type then offen := (d.type.getUsedConstants ++ d.value.getUsedConstants).toList ++ offen
      | _ => pure ()
  return ks

/-- The registry: lemma ↦ the constructors it covers. -/
def deckt : List (Name × List Name) :=
  [(``Gabbro.Code.Lower.WitC.stmt_gx_erfuellbar,
    [``Gabbro.Grammatik.Expr.lit, ``Gabbro.Grammatik.Expr.widen, ``Gabbro.Grammatik.Stmt.assignSlot]),
  (``Gabbro.Grammatik.AtomarErfuellbarkeit.gabbro_ziel_atomar_erfuellbar,
    [``Gabbro.Grammatik.Block.cons, ``Gabbro.Grammatik.Block.nil, ``Gabbro.Grammatik.Endblock.cons, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.eq, ``Gabbro.Grammatik.Expr.glob, ``Gabbro.Grammatik.Expr.lit, ``Gabbro.Grammatik.Expr.slot, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Expr.widen, ``Gabbro.Grammatik.Stmt.assignGlob, ``Gabbro.Grammatik.Stmt.assignSlot, ``Gabbro.Grammatik.Stmt.ite]),
  (``Gabbro.Grammatik.AtomarErfuellbarkeit.gabbro_ziel_atomar_schwach_erfuellbar,
    [``Gabbro.Grammatik.Block.cons, ``Gabbro.Grammatik.Block.nil, ``Gabbro.Grammatik.Endblock.cons, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.eq, ``Gabbro.Grammatik.Expr.glob, ``Gabbro.Grammatik.Expr.lit, ``Gabbro.Grammatik.Expr.slot, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Expr.widen, ``Gabbro.Grammatik.Stmt.assignGlob, ``Gabbro.Grammatik.Stmt.assignSlot, ``Gabbro.Grammatik.Stmt.ite]),
  (``Gabbro.Grammatik.EscrowWitness.owner_aufruf_erfuellbar,
    [``Gabbro.Grammatik.Endblock.cons, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Stmt.call]),
  (``Gabbro.Grammatik.Kernzelle.akku_erfuellbar,
    [``Gabbro.Grammatik.Endblock.bindAxiom, ``Gabbro.Grammatik.Endblock.bindCall, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.lit, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Expr.var, ``Gabbro.Grammatik.Expr.widen]),
  (``Gabbro.Grammatik.LowLevel.Construct.rangeArrayCarrierExpr_erfuellbar,
    [``Gabbro.Grammatik.Expr.var]),
  (``Gabbro.Grammatik.LowLevel.Construct.stringSliceBounds_erfuellbar,
    [``Gabbro.Grammatik.Expr.strLen, ``Gabbro.Grammatik.Expr.var]),
  (``Gabbro.Grammatik.Parser.UebersetzeAllg.arraySlice_erfuellbar,
    [``Gabbro.Grammatik.Expr.var]),
  (``Gabbro.Grammatik.Parser.UebersetzeAllg.specArrayLocal_erfuellbar,
    [``Gabbro.Grammatik.Expr.arrCons, ``Gabbro.Grammatik.Expr.arrNil, ``Gabbro.Grammatik.Expr.fls, ``Gabbro.Grammatik.Expr.strWeit, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Expr.var, ``Gabbro.Grammatik.Expr.widen]),
  (``Gabbro.Grammatik.Zielsatz.gabbro_ziel_erfuellbar,
    [``Gabbro.Grammatik.Block.cons, ``Gabbro.Grammatik.Block.nil, ``Gabbro.Grammatik.Endblock.cons, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.and, ``Gabbro.Grammatik.Expr.eq, ``Gabbro.Grammatik.Expr.forallSlots, ``Gabbro.Grammatik.Expr.le, ``Gabbro.Grammatik.Expr.lit, ``Gabbro.Grammatik.Expr.slot, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Expr.var, ``Gabbro.Grammatik.Expr.widen, ``Gabbro.Grammatik.Stmt.assignSlot, ``Gabbro.Grammatik.Stmt.call, ``Gabbro.Grammatik.Stmt.locks]),
  (``Gabbro.Grammatik.Zielsatz.probeB_erfuellbar_gilt,
    [``Gabbro.Grammatik.Block.cons, ``Gabbro.Grammatik.Block.nil, ``Gabbro.Grammatik.Endblock.bind, ``Gabbro.Grammatik.Endblock.cons, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.eq, ``Gabbro.Grammatik.Expr.lit, ``Gabbro.Grammatik.Expr.slot, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Expr.var, ``Gabbro.Grammatik.Expr.widen, ``Gabbro.Grammatik.Stmt.assignSlot, ``Gabbro.Grammatik.Stmt.call, ``Gabbro.Grammatik.Stmt.locks]),
  (``Gabbro.Grammatik.Zielsatz.probeB_erfuellbar_haupt,
    [``Gabbro.Grammatik.Block.cons, ``Gabbro.Grammatik.Block.nil, ``Gabbro.Grammatik.Endblock.bind, ``Gabbro.Grammatik.Endblock.cons, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.eq, ``Gabbro.Grammatik.Expr.lit, ``Gabbro.Grammatik.Expr.slot, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Expr.var, ``Gabbro.Grammatik.Expr.widen, ``Gabbro.Grammatik.Stmt.assignSlot, ``Gabbro.Grammatik.Stmt.call, ``Gabbro.Grammatik.Stmt.locks]),
  (``Gabbro.Grammatik.Zielsatz.probeC_erfuellbar_gilt,
    [``Gabbro.Grammatik.Block.cons, ``Gabbro.Grammatik.Block.nil, ``Gabbro.Grammatik.Endblock.bind, ``Gabbro.Grammatik.Endblock.cons, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.eq, ``Gabbro.Grammatik.Expr.le, ``Gabbro.Grammatik.Expr.lit, ``Gabbro.Grammatik.Expr.oldS, ``Gabbro.Grammatik.Expr.slot, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Expr.var, ``Gabbro.Grammatik.Expr.widen, ``Gabbro.Grammatik.Stmt.assignSlot, ``Gabbro.Grammatik.Stmt.call, ``Gabbro.Grammatik.Stmt.locks]),
  (``Gabbro.Grammatik.Zielsatz.probeC_erfuellbar_haupt,
    [``Gabbro.Grammatik.Block.cons, ``Gabbro.Grammatik.Block.nil, ``Gabbro.Grammatik.Endblock.bind, ``Gabbro.Grammatik.Endblock.cons, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.eq, ``Gabbro.Grammatik.Expr.le, ``Gabbro.Grammatik.Expr.lit, ``Gabbro.Grammatik.Expr.oldS, ``Gabbro.Grammatik.Expr.slot, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Expr.var, ``Gabbro.Grammatik.Expr.widen, ``Gabbro.Grammatik.Stmt.assignSlot, ``Gabbro.Grammatik.Stmt.call, ``Gabbro.Grammatik.Stmt.locks]),
  (``Gabbro.Grammatik.Zielsatz.zweiFaeden_erfuellbar_gilt,
    [``Gabbro.Grammatik.Block.cons, ``Gabbro.Grammatik.Block.nil, ``Gabbro.Grammatik.Endblock.cons, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.and, ``Gabbro.Grammatik.Expr.eq, ``Gabbro.Grammatik.Expr.forallSlots, ``Gabbro.Grammatik.Expr.le, ``Gabbro.Grammatik.Expr.lit, ``Gabbro.Grammatik.Expr.slot, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Expr.var, ``Gabbro.Grammatik.Expr.widen, ``Gabbro.Grammatik.Stmt.assignSlot, ``Gabbro.Grammatik.Stmt.call, ``Gabbro.Grammatik.Stmt.locks]),
  (``Gabbro.Grammatik.ruf_erreichbar_erfuellbar,
    [``Gabbro.Grammatik.Endblock.cons, ``Gabbro.Grammatik.Endblock.ret, ``Gabbro.Grammatik.Expr.tru, ``Gabbro.Grammatik.Stmt.call])]

/-- RATCHET: today's constructors without a registered lemma. -/
def offen : List String :=
  ["Gabbro.Grammatik.Stmt.assignThru",
   "Gabbro.Grammatik.Stmt.putBytes",
   "Gabbro.Grammatik.Stmt.assignVar",
   "Gabbro.Grammatik.Stmt.shift",
   "Gabbro.Grammatik.Stmt.onOption",
   "Gabbro.Grammatik.Stmt.onTag",
   "Gabbro.Grammatik.Stmt.onWhy",
   "Gabbro.Grammatik.Stmt.callInd",
   "Gabbro.Grammatik.Stmt.breaking",
   "Gabbro.Grammatik.Stmt.traverse",
   "Gabbro.Grammatik.Stmt.retry",
   "Gabbro.Grammatik.Stmt.forever",
   "Gabbro.Grammatik.Stmt.axiomCall",
   "Gabbro.Grammatik.Stmt.regWrite",
   "Gabbro.Grammatik.Stmt.transition",
   "Gabbro.Grammatik.Stmt.publish",
   "Gabbro.Grammatik.Stmt.advances",
   "Gabbro.Grammatik.Stmt.retires",
   "Gabbro.Grammatik.Stmt.ret",
   "Gabbro.Grammatik.Stmt.retWhy",
   "Gabbro.Grammatik.Stmt.leave",
   "Gabbro.Grammatik.Stmt.next",
   "Gabbro.Grammatik.Stmt.assignSlotRef",
   "Gabbro.Grammatik.Stmt.consumeTraverse",
   "Gabbro.Grammatik.Stmt.retScoped",
   "Gabbro.Grammatik.Stmt.retWhyScoped",
   "Gabbro.Grammatik.Stmt.axiomCallElse",
   "Gabbro.Grammatik.Stmt.callIndElse",
   "Gabbro.Grammatik.Stmt.assignThruOwn",
   "Gabbro.Grammatik.Block.bind",
   "Gabbro.Grammatik.Block.bindCall",
   "Gabbro.Grammatik.Block.bindCallInd",
   "Gabbro.Grammatik.Block.bindCallElse",
   "Gabbro.Grammatik.Block.bindAxiom",
   "Gabbro.Grammatik.Block.bindAxiomElse",
   "Gabbro.Grammatik.Block.regRead",
   "Gabbro.Grammatik.Block.regReadElse",
   "Gabbro.Grammatik.Block.awaits",
   "Gabbro.Grammatik.Block.exchange",
   "Gabbro.Grammatik.Block.narrow",
   "Gabbro.Grammatik.Block.check",
   "Gabbro.Grammatik.Block.float",
   "Gabbro.Grammatik.Block.floatLit",
   "Gabbro.Grammatik.Block.floatOf",
   "Gabbro.Grammatik.Block.floatNarrow",
   "Gabbro.Grammatik.Block.narrowRequired",
   "Gabbro.Grammatik.Block.bindAxiomOpt",
   "Gabbro.Grammatik.Block.bindAxiomOptElse",
   "Gabbro.Grammatik.Block.bindCallIndElse",
   "Gabbro.Grammatik.Endblock.retWhy",
   "Gabbro.Grammatik.Endblock.leave",
   "Gabbro.Grammatik.Endblock.next",
   "Gabbro.Grammatik.Endblock.bindCallElse",
   "Gabbro.Grammatik.Endblock.bindAxiomElse",
   "Gabbro.Grammatik.Endblock.regRead",
   "Gabbro.Grammatik.Endblock.regReadElse",
   "Gabbro.Grammatik.Endblock.awaits",
   "Gabbro.Grammatik.Endblock.bindCallInd",
   "Gabbro.Grammatik.Endblock.narrow",
   "Gabbro.Grammatik.Endblock.exchange",
   "Gabbro.Grammatik.Endblock.ite",
   "Gabbro.Grammatik.Endblock.narrowRequired",
   "Gabbro.Grammatik.Endblock.retScoped",
   "Gabbro.Grammatik.Endblock.retWhyScoped",
   "Gabbro.Grammatik.Endblock.bindAxiomOpt",
   "Gabbro.Grammatik.Endblock.bindAxiomOptElse",
   "Gabbro.Grammatik.Endblock.bindCallIndElse",
   "Gabbro.Grammatik.Endblock.float",
   "Gabbro.Grammatik.Endblock.floatLit",
   "Gabbro.Grammatik.Endblock.floatOf",
   "Gabbro.Grammatik.Endblock.floatNarrow",
   "Gabbro.Grammatik.Expr.thru",
   "Gabbro.Grammatik.Expr.ptrOf",
   "Gabbro.Grammatik.Expr.fnref",
   "Gabbro.Grammatik.Expr.oldG",
   "Gabbro.Grammatik.Expr.add",
   "Gabbro.Grammatik.Expr.sub",
   "Gabbro.Grammatik.Expr.neg",
   "Gabbro.Grammatik.Expr.mul",
   "Gabbro.Grammatik.Expr.div",
   "Gabbro.Grammatik.Expr.rem",
   "Gabbro.Grammatik.Expr.sdiv",
   "Gabbro.Grammatik.Expr.srem",
   "Gabbro.Grammatik.Expr.getBytes",
   "Gabbro.Grammatik.Expr.band",
   "Gabbro.Grammatik.Expr.bor",
   "Gabbro.Grammatik.Expr.bxor",
   "Gabbro.Grammatik.Expr.shl",
   "Gabbro.Grammatik.Expr.shr",
   "Gabbro.Grammatik.Expr.lt",
   "Gabbro.Grammatik.Expr.fllt",
   "Gabbro.Grammatik.Expr.flle",
   "Gabbro.Grammatik.Expr.or",
   "Gabbro.Grammatik.Expr.not",
   "Gabbro.Grammatik.Expr.none",
   "Gabbro.Grammatik.Expr.some",
   "Gabbro.Grammatik.Expr.istSome",
   "Gabbro.Grammatik.Expr.case",
   "Gabbro.Grammatik.Expr.why",
   "Gabbro.Grammatik.Expr.existsSlots",
   "Gabbro.Grammatik.Expr.reaches",
   "Gabbro.Grammatik.Expr.refEq",
   "Gabbro.Grammatik.Expr.slotRef",
   "Gabbro.Grammatik.Expr.arrGet",
   "Gabbro.Grammatik.Expr.arrSet",
   "Gabbro.Grammatik.Expr.strLit",
   "Gabbro.Grammatik.Expr.strCat",
   "Gabbro.Grammatik.Expr.strGet",
   "Gabbro.Grammatik.Expr.strEq",
   "Gabbro.Grammatik.Expr.strLt",
   "Gabbro.Grammatik.Expr.wenn",
   "Gabbro.Grammatik.Expr.eng",
   "Gabbro.Grammatik.Expr.intBuiltin1",
   "Gabbro.Grammatik.Expr.intBuiltin2",
   "Gabbro.Grammatik.Expr.count",
   "Gabbro.Grammatik.Expr.prod",
   "Gabbro.Grammatik.Expr.prodGet",
   "Gabbro.Grammatik.Expr.prodSet",
   "Gabbro.Grammatik.Expr.thruOwn"]

def pruefe : MetaM Unit := do
  let env ← getEnv
  let mut alle : Array Name := #[]
  for f in familien do
    if let some (.inductInfo i) := env.find? f then alle := alle ++ i.ctors.toArray
  let mut befunde : List String := []
  let mut gedeckt : Std.HashSet Name := {}
  for (l, ks) in deckt do
    unless env.find? l matches some (.thmInfo _) && istErfuellbarName l do
      befunde := befunde ++ [s!"not a satisfiability theorem (or its proof is not imported): {l}"]
    let inst := instanz env l
    for k in ks do
      unless alle.contains k do befunde := befunde ++ [s!"{l}: {k} is not a form"]
      if inst.contains k then gedeckt := gedeckt.insert k
      else befunde := befunde ++ [s!"{l} claims {k}, which does not occur in its instance"]
  let ungedeckt := (alle.filter (!gedeckt.contains ·)).toList.map toString
  befunde := befunde ++ (ratscheMenge ungedeckt offen).map ("uncovered forms: " ++ ·)
  -- the measurement that seeds and reviews the registry
  let mut vorschlag : List String := []
  for (n, ci) in env.constants.toList do
    if ci matches .thmInfo _ && istErfuellbarName n && imProjekt env n then
      let ks := (sortiert (instanz env n)).toList
      unless ks.isEmpty do vorschlag := vorschlag ++ [s!"({n}: {ks.length}) {ks}"]
  melde s!"satisfiability per form ({alle.size} forms, {gedeckt.size} covered)" befunde
    ("add an `_erfuellbar` lemma for a new form and register it in `deckt`; shrink `offen` where a form became " ++
     s!"covered. Measured:\noffen := {alsNamen ungedeckt}\noccurrences per lemma:\n{String.intercalate "\n" vorschlag}")

run_meta pruefe

end Gabbro.Grammatik.Zielsatz.Waechter.Formen
