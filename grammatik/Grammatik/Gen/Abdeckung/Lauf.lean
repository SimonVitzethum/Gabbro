/-
  File:      Grammatik/Gen/Abdeckung/Lauf.lean
  Subject:   The DRIVER of the coverage measurement:

               lean --run Grammatik/Gen/Abdeckung/Lauf.lean MEMBERS.tsv NB KMAX KMUT [I:NB:KMAX:KMUT ...]

             generates, for every member of the family, every skeleton up to size `KMAX` (bodies of size at most `NB`),
             classifies it by the ten components of the checker's Bool, derives refusals by one change from the valid
             programs up to size `KMUT`, and prints per declaration and size the counts and, at the end, the coverage of
             the register: per member the number of valid programs and of single-fault refusals that contain it, the
             least size at which it occurs, and the members covered by neither with the reason.

             The exit code is 1 if a register member is covered by neither valid nor refused programs and is not on the
             list of KNOWN GAPS (`bekannteLuecken`, each with its reason), or if a member on the list is covered (the
             list is exact). A new constructor of the model therefore stops the build in `Mitglieder.lean` (the match is
             total) and, once named there, shows up here as a gap until a program contains it or it is listed.
-/
import Grammatik.Gen.Abdeckung.Messung
import Grammatik.Gen.Abdeckung.Zustaende

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- The members of the register in the tsv, in file order. -/
def registerMitglieder (inhalt : String) : List String :=
  (inhalt.splitOn "\n").filterMap fun zeile =>
    if zeile.startsWith "#" || zeile.trimAscii.isEmpty then none else (zeile.splitOn "\t").head?

/-- Reasons of the known gaps. Each is a statement about the bounds and the family, not a claim about the model. -/
def G_MARKE : String :=
  "needs a declaration member with marks (typestate), ghost state or result/why contracts that is not in the family; " ++
  "no member exercises it within the bounds"
def G_INV : String :=
  "`Programm.invariante` is the predicate of an invariant; the generator takes it as true (the contracts-true workhorse), " ++
  "so no generated program carries a non-trivial one"
def G_ZAHL : String :=
  "the type of the bound value (a float range, a narrowed or checked integer) is outside the member's finite " ++
  "alphabet (`bindOk`), so the form is not generated within the bounds"
def G_ZUSTAND : String :=
  "needs a program with marks, a `why` type or a continuation/arena state that no member of the family declares"
def G_GROESSE : String :=
  "not reached within the bounds: the form needs a larger body or program (calls, axiom calls, register reads, " ++
  "exchanges, several functions), or a typed context the family lacks"

def G_REGION : String :=
  "the open region (PLAN-DYNAMIC 14): the bounded family declares no open table; the region is exercised by the fine " ++
  "member `region` (Gen/Fein/Mitglieder) and the witnesses GRegion and UebersetzeProben40"

def G_AGGREGAT : String :=
  "aggregate values (THEOREM-MAP 99): the generator gives arrays and strings the size `unendlich` and never draws " ++
  "them (TODO.md §2, generator support for aggregates)"

def G_WENN : String :=
  "the conditional and the narrowed value (THEOREM-MAP 103): the generator gives it the size `unendlich` and never draws it"

def G_ENDFORM : String :=
  "end-block forms (THEOREM-MAP 102): the generator gives them the size `unendlich` and never draws them; each " ++
  "unfolds to its block form (`Endblock.alsBlock`), whose cells are drawn"

/-- **The known gaps**: members of the register that no generated program contains within the bounds, each with the
    reason. The list is exact: a gap that is closed is removed, a new gap is a failure. -/
def bekannteLuecken : List (String × String) :=
  [
   ("Signatur.erg", G_MARKE),
   ("Signatur.gruende", G_MARKE),
   ("Signatur.konsumiert", G_MARKE),
   ("Signatur.produziert", G_MARKE),
   ("Deklaration.Marke", G_MARKE),
   ("Deklaration.stufen", G_MARKE),
   ("Deklaration.eigner", G_MARKE),
   ("Deklaration.eigner_nie_erzeugt", G_MARKE),
   ("Deklaration.geist", G_MARKE),
   ("Deklaration.ggeist", G_MARKE),
   ("Res.marke", G_MARKE),
   ("Vertrag.erg", G_MARKE),
   ("Vertrag.gruende", G_MARKE),
   ("Vertrag.produziert", G_MARKE),
   ("RufPasst.hk", G_MARKE),
   ("RufPasst.hx", G_MARKE),
   ("Expr.reaches", G_GROESSE),
   ("ErgExpr.val", G_GROESSE),
   ("GleitOp.add", G_ZAHL),
   ("GleitOp.sub", G_ZAHL),
   ("GleitOp.mul", G_ZAHL),
   ("GleitOp.div", G_ZAHL),
   ("Stmt.assignThru", G_GROESSE),
   ("Stmt.onTag", G_ZUSTAND),
   ("Stmt.onWhy", G_ZUSTAND),
   ("Stmt.advances", G_ZUSTAND),
   ("Stmt.retires", G_ZUSTAND),
   ("Stmt.retWhy", G_ZUSTAND),
   ("Stmt.leave", G_ZUSTAND),
   ("Stmt.next", G_ZUSTAND),
   ("Block.cons", G_GROESSE),
   ("Block.bindCall", G_GROESSE),
   ("Block.bindCallInd", G_GROESSE),
   ("Block.bindCallElse", G_GROESSE),
   ("Endblock.bindCall", G_GROESSE),
   ("Endblock.bindCallElse", G_GROESSE),
   ("Block.bindAxiom", G_GROESSE),
   ("Block.bindAxiomElse", G_GROESSE),
   ("Block.regRead", G_GROESSE),
   ("Block.regReadElse", G_GROESSE),
   ("Block.exchange", G_GROESSE),
   ("Block.narrow", G_ZAHL),
   ("Block.check", G_ZAHL),
   ("Block.float", G_ZAHL),
   ("Block.floatOf", G_ZAHL),
   ("Block.floatNarrow", G_ZAHL),
   ("Endblock.retWhy", G_ZUSTAND),
   ("Endblock.leave", G_ZUSTAND),
   ("Endblock.next", G_ZUSTAND),
   ("Endblock.bindAxiomElse", G_GROESSE),
   ("Endblock.bindCallInd", G_GROESSE),
   ("Endblock.narrow", G_ENDFORM),
   ("Endblock.exchange", G_ENDFORM),
   ("Endblock.ite", G_ENDFORM),
   ("Arms.nil", G_GROESSE),
   ("Arms.cons", G_GROESSE),
   ("GrundArms.nil", G_GROESSE),
   ("GrundArms.cons", G_GROESSE),
   ("Programm.invariante", G_INV),
   ("Ty.ref", G_REGION),
   ("Deklaration.offen", G_REGION),
   ("Deklaration.anbieter", G_REGION),
   ("Deklaration.anbieter_passt", G_REGION),
   ("Expr.refEq", G_REGION),
   ("Expr.slotRef", G_REGION),
   ("Stmt.assignSlotRef", G_REGION),
   ("Ty.arr", G_AGGREGAT),
   ("Ty.str", G_AGGREGAT),
   ("Expr.arrNil", G_AGGREGAT),
   ("Expr.arrCons", G_AGGREGAT),
   ("Expr.arrGet", G_AGGREGAT),
   ("Expr.arrSet", G_AGGREGAT),
   ("Expr.strLit", G_AGGREGAT),
   ("Expr.strLen", G_AGGREGAT),
   ("Expr.strCat", G_AGGREGAT),
   ("Expr.strGet", G_AGGREGAT),
   ("Expr.strEq", G_AGGREGAT),
   ("Expr.strLt", G_AGGREGAT),
   ("Expr.strWeit", G_AGGREGAT),
   ("Expr.wenn", G_WENN),
   ("Expr.eng", G_WENN),
  ]

/-- The members that are execution residues of the replay machine G: not terms of a program. -/
def istRest (m : String) : Bool := m.startsWith "GRest."

/-- The members that are states of the arena semantics, enumerated by `Zustaende.lean`. -/
def istZustand (m : String) : Bool := m.startsWith "DynArena." || m.startsWith "FreiZustand."

/-- The statement constructors. -/
def stmtNamen : List String :=
  ["assignSlot", "assignThru", "assignGlob", "putBytes", "assignVar", "shift", "ite", "onOption", "onTag", "onWhy",
   "call", "callInd", "locks", "breaking", "traverse", "retry", "forever", "axiomCall", "regWrite", "transition",
   "publish", "advances", "retires", "ret", "retWhy", "leave", "next"].map ("Stmt." ++ ·)

/-- The containers of statements (a statement with blocks) and the blocks with an `else` end block. -/
def behaelter : List String :=
  ["Stmt.ite", "Stmt.onOption", "Stmt.onTag", "Stmt.onWhy", "Stmt.locks", "Stmt.breaking", "Stmt.traverse",
   "Stmt.retry", "Stmt.forever", "Block.bindCallElse", "Block.bindAxiomElse", "Block.regReadElse", "Block.narrow",
   "Block.check", "Block.floatNarrow"]

/-- **The cells**: a statement in a loop body or under a held lock, a statement directly inside a container. -/
def zellen : List String :=
  stmtNamen.flatMap (fun s => [s ++ "@loop", s ++ "@held"]) ++
  behaelter.flatMap fun b => stmtNamen.map fun s => b ++ ">" ++ s

/-- Print a line and flush (progress must be visible while a long run goes on). -/
def sag (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- One size of one declaration: the classification and the time. -/
def messeGroesse (z : Spez) (st1 st2 st3 : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))))
    (k : Nat) (ws : List z.deklaration.Fn) : IO Klasse := do
  let t0 ← IO.monoMsNow
  let a := z.klassiere st1 k ws
  let b := z.klassiere st2 k ws
  let c := z.klassiere st3 k ws
  -- the stream that prunes both components decides every component but 3 and 8; the other two give exactly those
  let ges : Klasse := { a with nur := (a.nur.set! 3 (b.nur.getD 3 {})).set! 8 (c.nur.getD 8 {}) }
  let t1 ← IO.monoMsNow
  let nurN := (List.range 10).map fun i => (ges.nur.getD i {}).n
  sag s!"    size {k}: skeletons {a.alle} valid {ges.gueltig.n} only-by {nurN} several {a.mehr}  ({t1 - t0} ms)"
  return ges

/-- The bounds of one declaration: bodies of size at most `nb`, skeletons up to `kmax`, one-change refusals up to `kmut`. -/
structure Grenzen where
  nb : Nat
  kmax : Nat
  kmut : Nat

def main (args : List String) : IO UInt32 := do
  match args with
  | tsv :: nb :: kmax :: kmut :: rest =>
    let standard : Grenzen := ⟨nb.toNat!, kmax.toNat!, kmut.toNat!⟩
    let ueber : List (Nat × Grenzen) := rest.filterMap fun s =>
      match s.splitOn ":" with
      | [i, a, b, c] => some (i.toNat!, ⟨a.toNat!, b.toNat!, c.toNat!⟩)
      | _ => none
    let mut G : Zaehl := {}
    let mut Bc : Array Zaehl := Array.replicate 10 {}
    let mut Bm : Zaehl := {}
    let mut summeG := 0
    let mut summeB := 0
    let nur : Option (List Nat) := (← IO.getEnv "LAUF_NUR").map fun v => (v.splitOn ",").filterMap String.toNat?
    for i in List.range familie.length do
      let z := familie.getD i {}
      let gewaehlt := match nur with | some l => l.contains i | none => true
      if !gewaehlt then continue
      let gr := ((ueber.find? (·.1 == i)).map (·.2)).getD standard
      sag s!"declaration {i}: {z.tabs.length} tables {z.globs.length} statics {z.locks.length} locks {z.fns.length} functions  (bodies <= {gr.nb}, skeletons <= {gr.kmax}, one-change <= {gr.kmut})"
      -- the declared starts the question is asked for: the first root alone, and every root
      let wsA : List z.deklaration.Fn := z.wurzeln.take 1
      let wsB : List z.deklaration.Fn := z.wurzeln
      let wsListe : List (List z.deklaration.Fn) := if wsA == wsB then [wsA] else [wsA, wsB]
      let ws := wsA
      let t0 := z.tabellen gr.nb false false
      let t1 := z.filtere true true t0
      let t2 := z.filtere false true t0
      let t3 := z.filtere true false t0
      let mut dG := 0
      let mut dB := 0
      for w in wsListe do
        sag s!"  starts {w.length} of {z.wurzeln.length} roots"
        for k in List.range (gr.kmax + 1) do
          if k ≥ 1 then
            let kl ← messeGroesse z t1 t2 t3 k w
            G := G.plus kl.gueltig
            dG := dG + kl.gueltig.n
            for c in List.range 10 do
              Bc := Bc.set! c ((Bc.getD c {}).plus (kl.nur.getD c {}))
              dB := dB + (kl.nur.getD c {}).n
        for k in List.range (gr.kmut + 1) do
          if k ≥ 1 then
            let (v, kl) := z.mutanten t1 k w
            let n := (List.range 10).foldl (fun a c => a + (kl.nur.getD c {}).n) 0
            if v > 0 then
              sag s!"    one change, size {k}: {v} valid programs changed, refused by exactly one component {(List.range 10).map fun c => (kl.nur.getD c {}).n}"
            for c in List.range 10 do
              Bc := Bc.set! c ((Bc.getD c {}).plus (kl.nur.getD c {}))
            dB := dB + n
      -- programs with every contract, at small bounds (the unreduced statement)
      if i < 3 then
        for k in List.range (gr.kmut + 4) do
          if k ≥ 1 then
            let (alle, g) := z.mitVertraegen 3 2 k ws
            if g.n > 0 then
              sag s!"    contracts included, size {k}: {alle} programs, {g.n} valid"
              G := G.plus g
              dG := dG + g.n
      if dG > 0 then G := G.nenne 0 z.mitglieder
      if dB > 0 then Bm := Bm.nenne 0 z.mitglieder
      summeG := summeG + dG
      summeB := summeB + dB
    let inhalt ← IO.FS.readFile tsv
    let register := registerMitglieder inhalt
    let B := Bc.foldl Zaehl.plus Bm
    -- the report: per member the valid count, the refused count, the least size
    IO.println "member\tvalid\trefused\tleast-size-valid\tleast-size-refused\tstatus"
    let mut gedeckt := 0
    let mut gedecktG := 0
    let mut gedecktB := 0
    let mut zustand := 0
    let mut rest' := 0
    let mut fehler : List String := []
    for m in register do
      let g := G.m.getD m 0
      let b := B.m.getD m 0
      let kg := G.kl.getD m 0
      let kb := B.kl.getD m 0
      let st :=
        if g > 0 && b > 0 then "valid+refused"
        else if g > 0 then "valid"
        else if b > 0 then "refused"
        else if istZustand m then "state (enumerated)"
        else if istRest m then "residue of machine G (not a term)"
        else match bekannteLuecken.find? (·.1 == m) with
          | some (_, grund) => "GAP: " ++ grund
          | none => "GAP: not reached within the bounds"
      if g > 0 || b > 0 then gedeckt := gedeckt + 1
      if g > 0 then gedecktG := gedecktG + 1
      if b > 0 then gedecktB := gedecktB + 1
      if istZustand m && g == 0 && b == 0 then zustand := zustand + 1
      if istRest m && g == 0 && b == 0 then rest' := rest' + 1
      let unbekannt := g == 0 && b == 0 && !istZustand m && !istRest m && (bekannteLuecken.find? (·.1 == m)).isNone
      let veraltet := (g > 0 || b > 0) && (bekannteLuecken.find? (·.1 == m)).isSome
      if unbekannt then fehler := fehler ++ [m]
      if veraltet then fehler := fehler ++ [m ++ " (on the list of known gaps, but covered)"]
      IO.println s!"{m}\t{g}\t{b}\t{kg}\t{kb}\t{st}"
    -- the cells
    let mut zG := 0
    let mut zB := 0
    for c in zellen do
      if G.m.getD c 0 > 0 then zG := zG + 1
      if B.m.getD c 0 > 0 then zB := zB + 1
    IO.println s!"cells: {zellen.length}, covered by valid programs {zG}, by refusals {zB}"
    IO.println s!"register members: {register.length}; covered by valid programs {gedecktG}; by single-fault refusals {gedecktB}; by either {gedeckt}; states {zustand}; residues {rest'}"
    IO.println s!"valid programs: {summeG}; single-fault refusals: {summeB} ({(Bc.map (·.n)).toList})"
    IO.println s!"dynamic arenas (ceiling <= 3): {(dynZustaende 3).length}; free-list states (mark <= 3): {(freiZustaende 3).length}"
    if fehler.isEmpty then return 0
    else
      IO.eprintln s!"coverage failure: {fehler}"
      return 1
  | _ =>
    IO.eprintln "usage: Lauf.lean MEMBERS.tsv NB KMAX KMUT [I:NB:KMAX:KMUT ...]"
    return 2
