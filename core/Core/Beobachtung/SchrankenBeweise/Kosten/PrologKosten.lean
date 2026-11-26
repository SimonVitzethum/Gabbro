module

public import Core.Beobachtung.SchrankenBeweise.KostenSchaetzer

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Sequencing fragments adds their instruction costs. -/
theorem fragmentKosten_anhaengen (z : Wirkungsklasse → KlassenKostenzeile)
    (a b : Fragment) :
    fragmentKosten z (a.anhaengen b) = fragmentKosten z a + fragmentKosten z b := by
  let f := fun (acc : Nat) (i : Befehl) => acc + (z i.klasse).kosten
  have shift (code : List Befehl) (start base : Nat) :
      code.foldl f (start + base) = start + code.foldl f base := by
    induction code generalizing base with
    | nil => rfl
    | cons i rest ih =>
      simp only [List.foldl_cons, f] at *
      rw [Nat.add_assoc, ih]
  change (a.code ++ b.code).foldl f 0 = a.code.foldl f 0 + b.code.foldl f 0
  rw [List.foldl_append]
  simpa only [Nat.add_zero] using shift b.code (a.code.foldl f 0) 0

theorem fragmentKosten_einzel (z : Wirkungsklasse → KlassenKostenzeile) (b : Befehl) :
    fragmentKosten z (.einzel b) = (z b.klasse).kosten := by
  exact Nat.zero_add _

/-- The prologue charges the expression and the final check. -/
theorem measurePrologue_kosten (z : Wirkungsklasse → KlassenKostenzeile)
    (m : Measure scope) :
    fragmentKosten z (measurePrologue (some m)) =
      fragmentKosten z (expr 0 m.expression) + (z .lokal).kosten := by
  simp only [measurePrologue, fragmentKosten_anhaengen, fragmentKosten_einzel, Befehl.klasse]

/-- The charged prologue is the prefix of the elaborated function code. -/
theorem functionCode_prologKosten (z : Wirkungsklasse → KlassenKostenzeile)
    (result : Option WrittenType) (mass : Option (Measure scope))
    (body : BracedBlock (writtenResult result) scope) :
    fragmentKosten z (functionCode result mass body) =
      (FunktionsKern.mk ⟨scope, writtenResult result, body⟩ mass).prologKosten z +
        fragmentKosten z (bracedBlock body) + (z .lokal).kosten := by
  simp only [functionCode, fragmentKosten_anhaengen, fragmentKosten_einzel,
    FunktionsKern.prologKosten, Befehl.klasse]

/-- A cycle edge charges the target's prologue at that site. -/
theorem zyklusAufrufKosten_prolog (z : Wirkungsklasse → KlassenKostenzeile)
    (u : Ast.Unit) (name : Identifier) (site : Nat) (kern : FunktionsKern)
    (found : findeKern u.2 name = some kern) :
    zyklusAufrufKosten z u name site = some (site + kern.prologKosten z + 1) := by
  simp only [zyklusAufrufKosten, found, Option.map_some]

/-- A successful estimate for a known callee covers its site and initial
    prologue in both the table and structural branches. -/
theorem aufrufKosten_prolog_le (z : Wirkungsklasse → KlassenKostenzeile)
    (tab : KostenTabelle) (u : Ast.Unit) (fuel : Nat) (name : Identifier)
    (site estimate : Nat) (kern : FunktionsKern)
    (found : findeKern u.2 name = some kern)
    (estimated : aufrufKosten z tab u fuel name site = some estimate) :
    site + kern.prologKosten z ≤ estimate := by
  cases fuel with
  | zero => cases estimated
  | succ fuel =>
    rw [aufrufKosten] at estimated
    cases ht : tab.lookup name with
    | some k =>
      simp only [ht, found, Option.map_some, Option.getD_some, Option.some.injEq] at estimated
      rw [← estimated]
      exact Nat.add_le_add_left (Nat.le_max_right _ _) _
    | none =>
      simp only [ht, found] at estimated
      split at estimated
      · split at estimated
        · cases estimated
        · split at estimated
          · cases estimated
          · cases estimated
            omega
      · split at estimated
        · cases estimated
        · cases estimated
          omega

/-- The loader estimate includes the initial prologue of its entry function. -/
theorem schaetzeEintritt_prolog_le (z : Wirkungsklasse → KlassenKostenzeile)
    (tab : KostenTabelle) (u : Ast.Unit) (estimate : Nat) (kern : FunktionsKern)
    (found : findeKern u.2 mainName = some kern)
    (estimated : schaetzeEintritt z tab u = some estimate) :
    kern.prologKosten z ≤ estimate := by
  cases hm : aufrufKosten z tab u (funktionsAnzahl u.2 + 2) mainName 0 with
  | none =>
    simp only [schaetzeEintritt, hm, Option.bind_none] at estimated
    cases estimated
  | some cost =>
    have h := aufrufKosten_prolog_le z tab u _ mainName 0 cost kern found hm
    simp only [schaetzeEintritt, hm, Option.bind_some] at estimated
    have he : summeDeklarationen z u.2 + (z .ruf).kosten + cost + (z .lokal).kosten =
        estimate := Option.some.inj estimated
    omega

/-- The measured entry with an empty body has a two-instruction prologue.
    Its static estimate is seven, so a ceiling of five is refused. -/
theorem prologKosten_erfuellbar :
    ∃ u : Ast.Unit, schaetzeEinheit Wirkungsklasse.kostenZeile [] u = some 7 ∧
      pruefeSchrankenEndlich
        ⟨u, { Schrankendeklaration.leer with kosten := some 5 }⟩
        [] Wirkungsklasse.kostenZeile = false := by
  let measure : Measure [] := ⟨6, 6, Expr.lit 6, by omega⟩
  let entry := Decl.function mainName mainName_direct [] none
    (by intro t mem; cases mem) (some measure) (BracedBlock.braces Block.done)
    List.nodup_nil (by intro h; cases h) none
  exact ⟨⟨[], UnitBody.step entry UnitBody.done⟩, rfl, rfl⟩

end Gabbro.Core.Beobachtung
