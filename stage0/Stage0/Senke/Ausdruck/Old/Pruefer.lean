/- `accepts` meets the goal theorem's checker on certifiable units.

    Stage 0 checks a unit with `accepts`: `AkzeptiertX` with empty arena,
    accumulator and check admissions and the certified guest descriptors.
    The goal theorem's checker (`akzeptiertX_pruefer`) decides the same
    `AkzeptiertX` on the unit's declared checks (`E.pruefungen`) and
    additionally requires the ownership start (`besitzB`) and the neutral
    accumulator start (`akkuStartB`).

    This file defines `einheitVon` (an `Einheit` with empty arenas,
    accumulators and checks), the Bool `zertifizierbar` saying the unit has no
    arena table, no accumulator storage and no declared check (exactly the
    cases where the two sides can differ), and the step theorem: a successful
    `accepts` gives the goal checker's `true` on `einheitVon`, with the
    compiled entry `main` among the judged starts (`judgedRoots`). The bridge
    on the unit's judged `Einheit` (`einheitDer`), which uses
    `zertifizierbar`, is in JudgedUnit.lean. -/
module
public import Stage0.Senke.Ausdruck.Old.Source
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Parser.Elab.UebersetzeAllg3.Guest.Export
public import Grammatik.Zielsatz.Atomar.AtomarZiel
public import Grammatik.Bausteine.Kernzelle.Start
public import Grammatik.Zielsatz.Kern.Akzeptiert.Guest
@[expose] public section


namespace Gabbro.Stage0.OldSource
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz Gabbro.Grammatik.Zielsatz

/-- Substring test without recursion: some window of the haystack of the
    needle's length equals the needle. -/
def enthaelt (nadel hay : String) : Bool :=
  let n := nadel.toList
  let h := hay.toList
  (List.range (h.length + 1)).any fun i => decide ((h.drop i).take n.length = n)

/-- A unit is certifiable when it has no arena table, no declared check and
    no accumulator storage: exactly the cases where `accepts` (which runs
    `AkzeptiertX` with empty arena, accumulator and check admissions) and the
    goal checker's `akzeptiertX_pruefer` (which additionally judges the
    ownership and accumulator starts) can differ. Computed from the unit,
    never carried: accumulator storage always carries the generated `#zelle`
    cells and `#sperre` locks, and `#` never occurs in a source name. -/
def zertifizierbar (u : UProg) : Bool :=
  (u.tabs.all fun t => !t.arena) && u.checks.isEmpty &&
    (u.globs.all fun g => !enthaelt "#zelle" g.name) &&
    (u.locks.all fun l => !enthaelt "#sperre" l.name)

/-- The four conjuncts of `zertifizierbar`. The Bool is left-nested,
    `((A && B) && C) && D`, so three `Bool.and_eq_true` steps take it apart. -/
theorem zertifizierbar_teile {u : UProg} (h : zertifizierbar u = true) :
    (u.tabs.all fun t => !t.arena) = true ∧ u.checks.isEmpty = true ∧
      (u.globs.all fun g => !enthaelt "#zelle" g.name) = true ∧
      (u.locks.all fun l => !enthaelt "#sperre" l.name) = true := by
  have h1 := (Bool.and_eq_true _ _).mp h
  have h2 := (Bool.and_eq_true _ _).mp h1.1
  have h3 := (Bool.and_eq_true _ _).mp h2.1
  exact ⟨h3.1, h3.2, h2.2, h1.2⟩

/-- A certifiable unit has no arena table. -/
theorem zertifizierbar_ohne_arena (u : UProg) (h : zertifizierbar u = true)
    (t : UTab) (hm : t ∈ u.tabs) : t.arena = false := by
  have h1 : (!t.arena) = true := (List.all_eq_true.mp (zertifizierbar_teile h).1) t hm
  cases ht : t.arena with
  | true =>
    rw [ht, Bool.not_true] at h1
    cases h1
  | false => rfl

/-- A certifiable unit declares no check. -/
theorem zertifizierbar_ohne_checks (u : UProg) (h : zertifizierbar u = true) :
    u.checks = [] :=
  List.isEmpty_iff.mp (zertifizierbar_teile h).2.1

/-- A certifiable unit carries no accumulator storage. -/
theorem zertifizierbar_ohne_akku (u : UProg) (h : zertifizierbar u = true) :
    (u.globs.all fun g => !enthaelt "#zelle" g.name) = true ∧
      (u.locks.all fun l => !enthaelt "#sperre" l.name) = true :=
  (zertifizierbar_teile h).2.2

/-- The `Einheit` a Stage-0 unit and its restored program stand for in the
    goal theorem: the restored program, the unit's lock family, the caller's
    start memory and foreign answers, and the caller's start roots (declared
    entry roots and run-time roots, each with its start environment).
    Arenas, accumulators and declared checks are empty: faithful exactly on
    certifiable units (`zertifizierbar_ohne_arena`, `zertifizierbar_ohne_akku`,
    `zertifizierbar_ohne_checks`). -/
def einheitVon (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u))
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w))) :
    Einheit (declOf u) :=
  { P := P, S := sperrFamilie u, Q := Q, starts := starts, sp0 := sp,
    gestartet := gestartet, arenen := [], akku := [], pruefungen := [] }

/-- The `Einheit` carries the restored program. -/
theorem einheitVon_P (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u))
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w))) :
    (einheitVon u P Q sp starts gestartet).P = P := rfl

/-- The `Einheit` carries the unit's lock family. -/
theorem einheitVon_S (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u))
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w))) :
    (einheitVon u P Q sp starts gestartet).S = sperrFamilie u := rfl

/-- The `Einheit` declares no arena. -/
theorem einheitVon_arenen (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u))
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w))) :
    (einheitVon u P Q sp starts gestartet).arenen = [] := rfl

/-- The `Einheit` declares no accumulator. -/
theorem einheitVon_akku (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u))
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w))) :
    (einheitVon u P Q sp starts gestartet).akku = [] := rfl

/-- The `Einheit` declares no check. -/
theorem einheitVon_pruefungen (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u))
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w))) :
    (einheitVon u P Q sp starts gestartet).pruefungen = [] := rfl

/-- The `Einheit` judges the caller's start roots. -/
theorem einheitVon_ws (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u))
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w))) :
    (einheitVon u P Q sp starts gestartet).ws =
      (starts ++ gestartet ++ gestartet).map (·.1) := rfl

/-- `AkzeptiertX` does not depend on the chosen equality procedures
    (`bindetAxE_inst` for the same fact about the binding observation). -/
theorem akzeptiertX_inst (D : Deklaration) (fnEq₁ fnEq₂ : DecidableEq D.Fn)
    (axEq₁ axEq₂ : DecidableEq D.Ax) (P : Programm D) (S : SperrInv D)
    (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (aks : List (Kernzelle.AccumulatorDecl D))
    (checks : List (CheckDecl D)) (aqs : List D.Ax) (guests : List (GuestBoundary D)) :
    @AkzeptiertX D fnEq₁ axEq₁ P S fs ls cs ws aks checks aqs guests =
      @AkzeptiertX D fnEq₂ axEq₂ P S fs ls cs ws aks checks aqs guests := by
  cases Subsingleton.elim fnEq₁ fnEq₂
  cases Subsingleton.elim axEq₁ axEq₂
  rfl

/-- **The step behind the bridge**: a successful `accepts` gives the goal checker's `true` on
    `einheitVon`, whose arenas, accumulators and checks are empty, for EVERY unit. It says nothing
    about a unit's own arenas, accumulators or checks: the bridge on the unit's judged `Einheit`
    is `accepts_gibt_pruefer` (JudgedUnit.lean), which uses `zertifizierbar`. The guest
    descriptors `accepts` certifies ride along unchanged (`akzeptiertX_guest_eq`); the ownership
    and accumulator starts hold vacuously over the empty lists (`besitzB_leer`,
    `akkuStartB_leer`); the two sides use different equality procedures, bridged by
    `akzeptiertX_inst`. `hws` says the starts are exactly the roots `accepts` judged, the
    compiled entry `main` among them (`judgedRoots`). -/
theorem accepts_gibt_einheitVon (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (starts gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (hFn : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length)))
    (hws : (starts ++ gestartet ++ gestartet).map (·.1) = judgedRoots u main)
    (h : accepts u P main = .ok true) :
    akzeptiertX_pruefer.akzeptiert (einheitVon u P Q sp starts gestartet)
      (List.finRange u.fns.length) (List.finRange u.locks.length)
      ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr) = true := by
  unfold accepts at h
  split at h
  · cases h
  · cases hg : sourceGuests u with
    | error e => simp [hg, Functor.map, Except.map] at h
    | ok guests =>
      simp only [hg, bind, Except.bind, Functor.map, Except.map, pure, Except.pure,
        Except.ok.injEq] at h
      -- `h` carries the equality procedures `accepts` fixes with `letI`; the guest
      -- split is instantiated with exactly these, all other arguments come from `h`.
      have hsplit := (@akzeptiertX_guest_eq (declOf u)
        (inferInstanceAs (DecidableEq (Fin u.fns.length)))
        (inferInstanceAs (DecidableEq (Fin u.axs.length)))
        P (sperrFamilie u) _ _ _ _ _ _ _ _).symm.trans h
      have hpre := ((Bool.and_eq_true _ _).mp hsplit).1
      -- The goal checker decides with the caller's `hFn` and a classical procedure
      -- for `Ax` (`akzeptiertX_pruefer`); `akzeptiertX_inst` changes both.
      have hX : @AkzeptiertX (declOf u) hFn (fun x y => Classical.propDecidable (x = y)) P
          (sperrFamilie u) (List.finRange u.fns.length) (List.finRange u.locks.length)
          ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr)
          (einheitVon u P Q sp starts gestartet).ws [] [] [] [] = true := by
        rw [einheitVon_ws, hws]
        exact (akzeptiertX_inst (declOf u) _ hFn _ (fun x y => Classical.propDecidable (x = y))
          P (sperrFamilie u) _ _ _ _ _ _ _ _).symm.trans hpre
      have hB : besitzB (einheitVon u P Q sp starts gestartet)
          (List.finRange u.fns.length) = true :=
        besitzB_leer (einheitVon_arenen u P Q sp starts gestartet)
      have hA : Kernzelle.akkuStartB (einheitVon u P Q sp starts gestartet)
          (einheitVon u P Q sp starts gestartet).akku = true :=
        Kernzelle.akkuStartB_leer (einheitVon u P Q sp starts gestartet)
      show (@AkzeptiertX (declOf u) hFn (fun x y => Classical.propDecidable (x = y))
          (einheitVon u P Q sp starts gestartet).P
          (einheitVon u P Q sp starts gestartet).S (List.finRange u.fns.length)
          (List.finRange u.locks.length)
          ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr)
          (einheitVon u P Q sp starts gestartet).ws
          (einheitVon u P Q sp starts gestartet).akku
          (einheitVon u P Q sp starts gestartet).pruefungen [] [] &&
          besitzB (einheitVon u P Q sp starts gestartet) (List.finRange u.fns.length) &&
          Kernzelle.akkuStartB (einheitVon u P Q sp starts gestartet)
            (einheitVon u P Q sp starts gestartet).akku) = true
      exact (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨hX, hB⟩, hA⟩

/-- A minimal certifiable unit: one parameterless function declared as the
    only root. Hand-built; it covers `zertifizierbar` alone. The joint witness
    of the bridge on a compiled unit is `GoalCheckerWitness.bridge_zeuge`
    (Zeugen/Pruefung/GoalCheckerWitness.lean). -/
def zeugenFn : UFn :=
  { name := "main", params := [], kinds := [], res := none, held := [], puts := [],
    gives := [], body := [], ret := .empty }

def zeugenEinheit : UProg :=
  { tabs := [], locks := [], fns := [zeugenFn], roots := ["main"] }

/-- The minimal unit is certifiable. -/
theorem zertifizierbar_zeuge : zertifizierbar zeugenEinheit = true := by decide

end Gabbro.Stage0.OldSource
