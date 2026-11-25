/-
  File:      core/Core/Beobachtung/SchrankenBeweise/BindungRessourcen.lean
  Subject:   The resource start obligation family of `SchrankenbindungOffenAussage` over
             bound units. The loader of an elaborated program builds a start state with
             empty continuation frames and an empty booking. With `stapelTiefe` set to
             the frame count, both declared ceilings are therefore met at cut zero for
             every declaration. This discharges `ressourcenStart_unterLade`'s premise
             for bound units; the protocol and per-form resource families are not
             vacuous and are treated separately.
-/
module

public import Core.Beobachtung.SchrankenBeweise.Bindung
public import Core.Beobachtung.SchrankenBeweise.RessourcenEinheit
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The loader of a bound unit establishes the stack and memory bounds: its start state
    has no continuation frame and books no allocation cell. -/
theorem bindungLadeSchranken (P : Katalog.Plattform) (u : UnitMitSchranken) :
    ∀ (a : AussenStart) (p : Ladung) {s : Zustand Nat Zelle Int Nat Rahmen PUnit},
      (einheitMitSchranken P u).laden a p = some s →
        StapelZustand (einheitMitSchranken P u) s ∧
          SpeicherZustand (einheitMitSchranken P u) s := by
  intro a p s geladen
  change (laden (programm u.baum).eingang (programm u.baum).eintritte
    (programm u.baum).speicher P a p) = some s at geladen
  unfold laden at geladen
  by_cases ok : p.starts 0 = some 0 ∧ p.bytes 0 = some 0
  · rw [if_pos ok] at geladen
    let d := startdaten (programm u.baum).eingang (programm u.baum).eintritte
      (a.assignment 0) P a.regions
    let s0 : Zustand Nat Zelle Int Nat Rahmen PUnit := Zustand.start d.lokal d.status
      d.kerne d.rechte
        (einrichtung (programm u.baum).eingang (programm u.baum).eintritte
          (programm u.baum).speicher).initial (.leer (startmedium a))
    have hs : s = s0 := by
      dsimp only [s0]
      exact (Option.some.inj geladen).symm
    subst s
    constructor
    · intro c n bound
      dsimp only [s0, d, startdaten, Zustand.start, Rahmen.start]
      exact Nat.zero_le n
    · intro n bound
      have nichtsLebt : LebendeZellen s0 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z mem
        change s0.rechte.lebt z.1 = true ∧ z.2 < (s0.buchung.umfang z.1).length at mem
        have hleer : s0.buchung.umfang z.1 = [] := rfl
        rw [hleer] at mem
        simp only [List.length_nil] at mem
        exact Nat.not_lt_zero _ mem.2
      rw [nichtsLebt, Set.encard_empty]
      exact zero_le
  · rw [if_neg ok] at geladen
    cases geladen

/-- The resource start duty of every bound unit: the loader premise above is exactly the
    one the general theorem `ressourcenStart_unterLade` asks for. -/
theorem bindungRessourcenStart (P : Katalog.Plattform) (u : UnitMitSchranken) :
    ressourcenStartAussage (einheitMitSchranken P u) :=
  ressourcenStart_unterLade (bindungLadeSchranken P u)

end Gabbro.Core.Beobachtung
