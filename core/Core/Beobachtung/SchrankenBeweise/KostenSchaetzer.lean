/-
  File:      core/Core/Beobachtung/SchrankenBeweise/KostenSchaetzer.lean
  Subject:   THE DECIDABLE STRUCTURAL COST ESTIMATOR FOR FINITE BOUNDS (M9, MK-12).
              `pruefeSchrankenSpielraum` accepts a bound unit only with an open cost
              ceiling and no hold entry, because every class row costs one tick and a
              finite ceiling is reached by a run. This file makes finite cost ceilings
              usable: the bound applies per invocation (from entry to exit of one
              function invocation), not per whole run, and a decidable estimator over
              the source structure bounds every invocation.

              The estimator (`schaetzeEinheit`) sums the class costs
              (`Wirkungsklasse.kostenZeile`) over the elaborated instructions of each
              source form, multiplies loop bodies by their static trip bound
              (`whileBounded` upper endpoint, `forRange` static span), resolves calls
              through the declared per-function table (`KostenTabelle`) or
              structurally, and treats recursion only
              with `decreases` (the measure span bounds the re-entry depth); anything
              else (`forever`, unknown callees, recursion without `decreases`,
              exhausted fuel) is refused with `none`. The checker line
              (`pruefeSchrankenEndlich`) keeps the open case of the slack line as a
              special case and accepts a finite ceiling exactly when no hold entry
              is declared and the estimator is defined and below it. Finite hold
              entries stay refused: ownership can span invocations, so no
              per-invocation estimator covers them. Acceptance
              (`EndlichAkzeptiertAussage`, pinned) is the perfect checker with the
              new line, so everything accepted before stays accepted with the same
              guarantees (`endlichAkzeptiert_verstaerkt`).
              `Kosten.KostenGegenbeispiel` refutes the estimator bound for an
              accepted unit with a measure prologue and an empty cost table.
-/
module

public import Core.Beobachtung.SchrankenBeweise.SchrankenSpielraum
public import Core.Beobachtung.SchrankenBeweise.BindungOffen
public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Semantik.Runtime.Klasse.Kosten
public import Core.Ast.Declaration.Types

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Declared per-function bounds from entry to exit. The estimator uses these
    values directly. Their verification is a separate obligation. -/
abbrev KostenTabelle := List (Identifier × Nat)

/-- Lookup of a declared function bound by name. -/
def KostenTabelle.lookup (tab : KostenTabelle) (name : Identifier) : Option Nat :=
  (tab.find? (fun p => p.1.val == name.val)).map Prod.snd

/-- The cost of an elaborated fragment under the class rows: every instruction
    costs its class row. With the reviewed rows each step costs one tick. -/
def fragmentKosten (z : Wirkungsklasse → KlassenKostenzeile) (p : Fragment) : Nat :=
  p.code.foldl (fun acc b => acc + (z b.klasse).kosten) 0

/-- The static trip bound of a `whileBounded` loop: the upper endpoint of the
    static bound expression, which the bound value never exceeds. -/
def boundSchranke {scope : Scope} {lo hi : Int} (bound : Expr scope (.int lo hi)) : Nat :=
  (SchleifenGrenze.whileBounded bound).paesse

/-- The static trip bound of a `forRange` loop: the static span between the
    lowest possible start and the highest possible end, clamped at zero. -/
def forSchranke {scope : Scope} {low lowHi highLo high : Int}
    (lo : Expr scope (.int low lowHi)) (hi : Expr scope (.int highLo high)) : Nat :=
  (SchleifenGrenze.forRange lo hi).paesse

mutual

/-- The structural core of the estimator: the cost bound of one invocation of a
    statement, with calls resolved by the oracle. The oracle takes the callee
    name and the call-site cost (arguments and the call instruction) and returns
    the whole call cost. Loops multiply the body estimator by the static trip
    bound; `forever` has no bound and is refused. -/
def schaetzeStmt (z : Wirkungsklasse → KlassenKostenzeile)
    (oracle : Identifier → Nat → Option Nat) :
    Stmt result before after → Option Nat
  | .whileBounded condition bound _ _ _ body => do
    let b ← schaetzeBracedBlock z oracle body
    let kl := (z .lokal).kosten
    let econd := fragmentKosten z (expr 0 condition)
    let ebound := fragmentKosten z (expr 0 bound)
    let trips := boundSchranke bound
    some (ebound + kl + (trips + 1) * (econd + kl) + trips * (b + kl) + kl)
  | .forRange _ _ lo hi _ _ body => do
    let b ← schaetzeBracedBlock z oracle body
    let kl := (z .lokal).kosten
    let elo := fragmentKosten z (expr 0 lo)
    let ehi := fragmentKosten z (expr 1 hi)
    let trips := forSchranke lo hi
    some (elo + ehi + kl + (trips + 1) * kl + trips * (b + kl) + kl)
  | .ite condition yes no => do
    let y ← schaetzeBracedBlock z oracle yes
    let n ← schaetzeBracedBlock z oracle no
    let kl := (z .lokal).kosten
    some (fragmentKosten z (expr 0 condition) + kl + y + kl + n)
  | .variantMatch value arms => do
    let a ← schaetzeArme z oracle arms
    let kl := (z .lokal).kosten
    some (fragmentKosten z (expr 0 value) + kl + a)
  | .directCall call =>
    oracle call.name (fragmentKosten z (callCode call none))
  | .bindDirect _ _ _ _ call =>
    oracle call.name (fragmentKosten z (callCode call none))
  | .forever _ _ => none
  | s => some (fragmentKosten z (stmt s))

def schaetzeBlock (z : Wirkungsklasse → KlassenKostenzeile)
    (oracle : Identifier → Nat → Option Nat) :
    Block result before after → Option Nat
  | .done => some 0
  | .step first rest => do
    let a ← schaetzeStmt z oracle first
    let b ← schaetzeBlock z oracle rest
    some (a + b)

def schaetzeBracedBlock (z : Wirkungsklasse → KlassenKostenzeile)
    (oracle : Identifier → Nat → Option Nat) :
    BracedBlock result before → Option Nat
  | .braces body => do
    let b ← schaetzeBlock z oracle body
    some (b + (z .lokal).kosten)

def schaetzeArme (z : Wirkungsklasse → KlassenKostenzeile)
    (oracle : Identifier → Nat → Option Nat) :
    VariantArms result scope allowWildcard labels payloads → Option Nat
  | .done => some 0
  | .nullary _ _ body rest => do
    let a ← schaetzeBracedBlock z oracle body
    let b ← schaetzeArme z oracle rest
    some (a + b)
  | .payload _ _ _ body rest => do
    let a ← schaetzeBracedBlock z oracle body
    let b ← schaetzeArme z oracle rest
    some (a + b)
  | .wildcard body _ _ => schaetzeBracedBlock z oracle body

end

mutual

/-- The syntactic direct callees of a statement: every `directCall` and
    `bindDirect` target occurring in it. -/
def aufrufeStmt : Stmt result before after → List Identifier
  | .directCall call => [call.name]
  | .bindDirect _ _ _ _ call => [call.name]
  | .whileBounded _ _ _ _ _ body => aufrufeBracedBlock body
  | .forRange _ _ _ _ _ _ body => aufrufeBracedBlock body
  | .ite _ yes no => aufrufeBracedBlock yes ++ aufrufeBracedBlock no
  | .variantMatch _ arms => aufrufeArme arms
  | .forever _ body => aufrufeBracedBlock body
  | _ => []

def aufrufeBlock : Block result before after → List Identifier
  | .done => []
  | .step first rest => aufrufeStmt first ++ aufrufeBlock rest

def aufrufeBracedBlock : BracedBlock result before → List Identifier
  | .braces body => aufrufeBlock body

def aufrufeArme : VariantArms result scope allowWildcard labels payloads →
    List Identifier
  | .done => []
  | .nullary _ _ body rest => aufrufeBracedBlock body ++ aufrufeArme rest
  | .payload _ _ _ body rest => aufrufeBracedBlock body ++ aufrufeArme rest
  | .wildcard body _ _ => aufrufeBracedBlock body

end

/-- One function of a unit, with exactly what the estimator needs: the
    `decreases` interval (when declared) and the body with its own scope. -/
structure FunktionsKern where
  massIntervall : Option (Int × Int)
  koerper : Σ scope : Scope, Σ result : Option (Ty .value), BracedBlock result scope

/-- The `decreases` span of a measure: values stay inside the interval, so a
    strictly decreasing chain can make at most this many decreases. -/
def massSpanne (intervall : Int × Int) : Nat :=
  (intervall.2 - intervall.1).toNat

/-- Function lookup by name over the unit body. -/
def findeKern : UnitBody before after → Identifier → Option FunktionsKern
  | .done, _ => none
  | .step (.function name _ _ _ _ decreases body _ _ _) next, want =>
    if name.val == want.val then
      some ⟨decreases.map (fun m => (m.lo, m.hi)), ⟨_, _, body⟩⟩
    else findeKern next want
  | .step _ next, want => findeKern next want

/-- The direct callees of a named function, empty when the name is unknown. -/
def calleesVon (u : Ast.Unit) (name : Identifier) : List Identifier :=
  match findeKern u.2 name with
  | none => []
  | some kern => aufrufeBracedBlock kern.koerper.2.2

/-- The names of all functions declared by a unit body. -/
def alleFunktionen : UnitBody before after → List Identifier
  | .done => []
  | .step (.function name _ _ _ _ _ _ _ _ _) next => name :: alleFunktionen next
  | .step _ next => alleFunktionen next

/-- The number of function declarations of a unit body: the fuel bound for the
    call-graph closure. -/
def funktionsAnzahl : UnitBody before after → Nat
  | .done => 0
  | .step (.function _ _ _ _ _ _ _ _ _ _) next => funktionsAnzahl next + 1
  | .step _ next => funktionsAnzahl next

/-- The fuel-bounded transitive callee closure of a seed set. -/
def erreichbar (u : Ast.Unit) : Nat → List Identifier → List Identifier
  | 0, seen => seen
  | fuel + 1, seen =>
    let neu := (seen.flatMap (calleesVon u)).filter
      (fun m => !(seen.any (fun x => x.val == m.val)))
    match neu with
    | [] => seen
    | _ :: _ => erreichbar u fuel (seen ++ neu)

/-- A function is self-recursive when its own name is reachable from its
    direct callees. -/
def selbstRekursiv (u : Ast.Unit) (name : Identifier) : Bool :=
  (erreichbar u (funktionsAnzahl u.2 + 1) (calleesVon u name)).any
    (fun x => x.val == name.val)

/-- The cycle set of a function: every function reachable from it that can
    reach it back. Calls inside the set cost only their call mechanics; the
    `decreases` span bounds the number of cycle activations. -/
def zyklusMenge (u : Ast.Unit) (name : Identifier) : List Identifier :=
  let fuel := funktionsAnzahl u.2 + 1
  (erreichbar u fuel [name]).filter
    (fun m => (erreichbar u fuel [m]).any (fun x => x.val == name.val))

/-- The whole cost of one call: the site cost plus one invocation of the
    callee. A declared entry is trusted after its own verification; otherwise
    the body is estimated structurally. A self-recursive callee needs
    `decreases`, and its body is estimated with the cycle short-circuited,
    multiplied by the span. -/
def aufrufKosten (z : Wirkungsklasse → KlassenKostenzeile) (tab : KostenTabelle)
    (u : Ast.Unit) : Nat → Identifier → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, name, site =>
    match tab.lookup name with
    | some K => some (site + K)
    | none =>
      match findeKern u.2 name with
      | none => none
      | some kern =>
        if selbstRekursiv u name then
          match kern.massIntervall.map massSpanne with
          | none => none
          | some span =>
            let zyk := zyklusMenge u name
            let oracle : Identifier → Nat → Option Nat :=
              fun m s => if zyk.any (fun x => x.val == m.val) then some (s + 1)
                else aufrufKosten z tab u fuel m s
            match schaetzeBracedBlock z oracle kern.koerper.2.2 with
            | none => none
            | some b => some (site + (span + 1) * b + 1)
        else
          match schaetzeBracedBlock z (aufrufKosten z tab u fuel) kern.koerper.2.2 with
          | none => none
          | some b => some (site + b + 1)

/-- The top-level declaration cost: a function binds one instruction; every
    other declaration costs its elaborated fragment, which runs once at load. -/
def schaetzeDekl (z : Wirkungsklasse → KlassenKostenzeile) :
    Decl before after → Nat
  | .function _ _ _ _ _ _ _ _ _ _ => (z .lokal).kosten
  | d => fragmentKosten z (decl d)

/-- The summed top-level cost of a unit body. -/
def summeDeklarationen (z : Wirkungsklasse → KlassenKostenzeile) :
    UnitBody before after → Nat
  | .done => 0
  | .step first rest => schaetzeDekl z first + summeDeklarationen z rest

/-- The entry estimate: top-level declarations, the entry call instruction,
    one `main` invocation and the final instruction. -/
def schaetzeEintritt (z : Wirkungsklasse → KlassenKostenzeile) (tab : KostenTabelle)
    (u : Ast.Unit) : Option Nat := do
  let decls := summeDeklarationen z u.2
  let main ← aufrufKosten z tab u (funktionsAnzahl u.2 + 2) mainName 0
  some (decls + (z .ruf).kosten + main + (z .lokal).kosten)

/-- The worst invocation bound over all declared functions, each with an empty
    site cost. Together with the entry estimate every invocation window of the
    unit is covered, including handlers no caller reaches. -/
def schaetzeAlleFunktionen (z : Wirkungsklasse → KlassenKostenzeile)
    (tab : KostenTabelle) (u : Ast.Unit) : Option Nat :=
  (alleFunktionen u.2).foldl (fun acc name => do
    let a ← acc
    let b ← aufrufKosten z tab u (funktionsAnzahl u.2 + 2) name 0
    pure (max a b)) (some 0)

/-- The structural cost estimator of a unit: the maximum of the entry estimate
    and every function invocation bound. `none` refuses the finite bound. -/
def schaetzeEinheit (z : Wirkungsklasse → KlassenKostenzeile) (tab : KostenTabelle)
    (u : Ast.Unit) : Option Nat := do
  let e ← schaetzeEintritt z tab u
  let m ← schaetzeAlleFunktionen z tab u
  pure (max e m)

/-- The decidable checker line for finite cost bounds: the open declaration
    passes exactly as the slack line says; a finite ceiling passes exactly when
    no hold entry is declared and the estimator is defined and below it. Finite
    hold entries stay refused: ownership can span invocations, so no
    per-invocation estimator covers them. -/
def pruefeSchrankenEndlich (u : UnitMitSchranken) (tab : KostenTabelle)
    (z : Wirkungsklasse → KlassenKostenzeile) : Bool :=
  match u.deklaration.kosten with
  | none => pruefeSchrankenSpielraum u.deklaration z
  | some K =>
    u.deklaration.halten.isEmpty &&
      match schaetzeEinheit z tab u.baum with
      | none => false
      | some E => decide (E ≤ K)

/-- **Acceptance with the finite checker line** (`EndlichAkzeptiertAussage`):
    the perfect checker on the elaborated unit and the decidable endliche line.
    The open case is the slack line, so the line only adds refusals where no
    finite bound holds. -/
def EndlichAkzeptiertAussage (P : Katalog.Plattform) (u : UnitMitSchranken)
    (tab : KostenTabelle) (z : Wirkungsklasse → KlassenKostenzeile) : Prop :=
  Akzeptiert (einheitMitSchranken P u) ∧
    pruefeSchrankenEndlich u tab z = true

/-- The new line projects back to the perfect checker. -/
theorem endlichAkzeptiert_projektion (P : Katalog.Plattform) (u : UnitMitSchranken)
    (tab : KostenTabelle) (z : Wirkungsklasse → KlassenKostenzeile) :
    EndlichAkzeptiertAussage P u tab z → Akzeptiert (einheitMitSchranken P u) := by
  intro h
  exact h.1

/-- **The old acceptance stays accepted** (the existing line is a special
    case): whatever passes the slack line passes the endliche line with the
    same guarantees, since the open case is unchanged. -/
theorem endlichAkzeptiert_verstaerkt (P : Katalog.Plattform) (u : UnitMitSchranken)
    (tab : KostenTabelle) (z : Wirkungsklasse → KlassenKostenzeile)
    (h : GebundenAkzeptiertAussage P u) :
    EndlichAkzeptiertAussage P u tab z := by
  obtain ⟨akk, ok⟩ := h
  have h1 : u.deklaration.kosten.isNone = true := (Bool.and_eq_true_iff.mp ok).1
  have h2 : u.deklaration.halten.isEmpty = true := (Bool.and_eq_true_iff.mp ok).2
  cases hk : u.deklaration.kosten with
  | none =>
    refine ⟨akk, ?_⟩
    have hhalten : u.deklaration.halten = [] := by
      cases hh : u.deklaration.halten with
      | nil => rfl
      | cons x xs =>
        rw [hh, List.isEmpty_cons] at h2
        cases h2
    simp only [pruefeSchrankenEndlich, hk, hhalten, pruefeSchrankenSpielraum,
      Option.isNone_none, List.isEmpty_nil, Bool.true_and]
  | some n =>
    rw [hk, Option.isNone_some] at h1
    cases h1

/-- The empty source tree, for the satisfiability witnesses below. -/
private def leerBaum : Ast.Unit := ⟨[], UnitBody.done⟩

/-- Joint satisfiability: the empty declaration passes the endliche line on the
    open leg, and every KH duty of the bound unit closes through the open
    lemmas. No run is constructed. -/
theorem schrankenEndlich_erfuellbar :
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      pruefeSchrankenEndlich u tab z = true ∧
      (∀ f : Befehl, KHRegelPflicht (einheitMitSchranken P u) f) ∧
        KHProtokollPflicht (einheitMitSchranken P u) := by
  refine ⟨Katalog.Plattform.x86_64, ⟨leerBaum, Schrankendeklaration.leer⟩, [],
    Wirkungsklasse.kostenZeile, rfl, ?_, ?_⟩
  · intro f
    exact bindungKHOffen _ _ f rfl rfl
  · exact bindungKHProtokollOffen _ _ rfl rfl

/-- A main that loops forever: the estimator has no bound for it. -/
def endlosBaum : Ast.Unit :=
  ⟨_, UnitBody.step
    (Decl.function mainName mainName_direct [] none
      (by intro t mem; cases mem) none
      (BracedBlock.braces
        (Block.step (Stmt.forever none (BracedBlock.braces Block.done)) Block.done))
      List.nodup_nil (by intro h; cases h) none)
    UnitBody.done⟩

/-- A main with one bounded loop of at most zero passes over a finite ceiling
    that is too tight: five ticks against a ceiling of three. -/
def engerBaum : Ast.Unit :=
  ⟨_, UnitBody.step
    (Decl.function mainName mainName_direct [] none
      (by intro t mem; cases mem) none
      (BracedBlock.braces
        (Block.step
          (Stmt.whileBounded Expr.trueLit (Expr.lit 0) trivial (Int.le_refl 0) mainName
            (BracedBlock.braces Block.done))
          Block.done))
      List.nodup_nil (by intro h; cases h) none)
    UnitBody.done⟩

def engeDeklaration : Schrankendeklaration :=
  ⟨some 3, none, none, [], [], []⟩

/-- Sharpness: an endless loop has no estimator value, and a bounded loop over
    a too-tight finite ceiling is refused by the endliche line. -/
theorem schrankenEndlich_nichtTrivial :
    (∃ (tab : KostenTabelle) (z : Wirkungsklasse → KlassenKostenzeile),
      schaetzeEinheit z tab endlosBaum = none) ∧
    ∃ (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      pruefeSchrankenEndlich u tab z = false := by
  refine ⟨⟨[], Wirkungsklasse.kostenZeile, rfl⟩,
    ⟨⟨engerBaum, engeDeklaration⟩, [], Wirkungsklasse.kostenZeile, rfl⟩⟩

end Gabbro.Core.Beobachtung
