/- The `Einheit` the compiler's check judged, and the bridge to the goal checker on it.

    `einheitDer` is the unit as the goal theorem sees it, built from what the elaborator
    exports: the restored program, the unit's lock family, its derived check descriptors
    (`uCheckDecls`, the elaborator's own derivation, C16) and its declared starts with the
    compiled entry `main` FIRST (the image starts `main` beside every other root, so the entry
    is a declared start of the judged unit, not an extra thread outside it).

    What the elaborator does not export stays out, and the bridge is restricted to units that
    have none of it (`zertifizierbar`):
    * arenas: no exporter builds the ownership interfaces (`ArenaIface`) of a `UProg`;
    * accumulators: `uAkkuDecl` needs the source item and resolved cell/lock/function bindings
      that a `UProg` does not carry (it keeps only the generated `#zelle`/`#sperre` storage,
      which `zertifizierbar` detects; every admitted accumulator has at least one cell,
      `uAkkuAnzahl`);
    * the initial grant inventory (`grants0`, C08): no exporter; the goal checker does not read
      it.
    On a certifiable unit the derived checks are empty, so `einheitDer` IS `einheitVon` with
    the entry as first start (`einheitDer_eq`): that equation is where `zertifizierbar` is used.
-/
module
public import Stage0.Senke.Ausdruck.Old.Pruefer
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
@[expose] public section

namespace Gabbro.Stage0.OldSource
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz Gabbro.Grammatik.Zielsatz

/-- **The judged `Einheit`** of a compiled unit: the restored program `P`, the unit's lock
    family, the caller's foreign answers `Q` and start memory `sp`, the declared starts with the
    compiled entry `main` (started with `args`) first and then the declared roots `roots`, the
    run-time roots `gestartet`, and the unit's derived check descriptors `checks`
    (`uCheckDecls u = .ok checks` in every theorem about it). Arenas and accumulators are
    empty: no exporter exists for them (module header); the bridge requires `zertifizierbar`. -/
def einheitDer (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u))) : Einheit (declOf u) :=
  { P := P, S := sperrFamilie u, Q := Q, starts := ⟨main, args⟩ :: roots, sp0 := sp,
    gestartet := gestartet, arenen := [], akku := [], pruefungen := checks }

/-- The judged `Einheit` starts the compiled entry first. -/
theorem einheitDer_starts (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u))) :
    (einheitDer u P Q sp main args roots gestartet checks).starts = ⟨main, args⟩ :: roots := rfl

/-- The judged `Einheit` carries the unit's derived checks. -/
theorem einheitDer_pruefungen (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u))) :
    (einheitDer u P Q sp main args roots gestartet checks).pruefungen = checks := rfl

/-- A unit without a declared check derives no check descriptor. -/
theorem uCheckDecls_ohne_checks (u : UProg) (h : u.checks = []) : uCheckDecls u = .ok [] := by
  unfold uCheckDecls uSondenPruef
  rw [h] <;> rfl

/-- A certifiable unit derives no check descriptor. -/
theorem uCheckDecls_zertifizierbar (u : UProg) (hZ : zertifizierbar u = true) :
    uCheckDecls u = .ok [] :=
  uCheckDecls_ohne_checks u (zertifizierbar_ohne_checks u hZ)

/-- **On a certifiable unit the judged `Einheit` is `einheitVon`** with the entry as first
    start: the derived checks are empty (`uCheckDecls_zertifizierbar`), and the unit has no
    arena table and no accumulator storage (`zertifizierbar_ohne_arena`,
    `zertifizierbar_ohne_akku`), so the empty arena and accumulator lists of both sides forget
    nothing the unit declares. -/
theorem einheitDer_eq (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u)))
    (hZ : zertifizierbar u = true) (hC : uCheckDecls u = .ok checks) :
    einheitDer u P Q sp main args roots gestartet checks =
      einheitVon u P Q sp (⟨main, args⟩ :: roots) gestartet := by
  have hcs : checks = [] := Except.ok.inj (hC.symm.trans (uCheckDecls_zertifizierbar u hZ))
  subst hcs
  rfl

/-- **The judged starts are the roots `accepts` judged**: the entry, then starts naming the
    unit's declared roots, then the run-time roots twice (`judgedRoots`). -/
theorem einheitDer_ws (u : UProg) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (hr : roots.map (·.1) = u.roots.filterMap fun n => wurzelIdx u n)
    (hg : gestartet.map (·.1) = u.gestartet.filterMap fun n => wurzelIdx u n) :
    ((⟨main, args⟩ :: roots) ++ gestartet ++ gestartet).map (·.1) = judgedRoots u main := by
  have key : ∀ (x : (declOf u).Fn) (f : String → Option (declOf u).Fn) (a b : List String),
      x :: (List.filterMap f a ++ List.filterMap f b ++ List.filterMap f b) =
        x :: List.filterMap f (a ++ b ++ b) := by
    intro x f a b
    simp only [List.filterMap_append]
  simp only [judgedRoots, List.cons_append, List.map_cons, List.map_append, hr, hg]
  exact key _ _ _ _

/-- **A unit whose only start is the entry**: without declared roots and run-time roots
    (a plain `main`: `uWurzeln` and `uStartNamen` find nothing) the empty root lists name
    exactly the unit's roots. -/
theorem roots_leer (u : UProg) (h : u.roots = []) :
    ([] : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w))).map (·.1) =
      u.roots.filterMap fun n => wurzelIdx u n := by
  simp only [h, List.map_nil, List.filterMap_nil]
  rfl

/-- Without run-time roots, the empty list names exactly the unit's run-time roots. -/
theorem gestartet_leer (u : UProg) (h : u.gestartet = []) :
    ([] : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w))).map (·.1) =
      u.gestartet.filterMap fun n => wurzelIdx u n := by
  simp only [h, List.map_nil, List.filterMap_nil]
  rfl

/-- **The bridge**: on a certifiable unit, a successful `accepts` with entry `main` gives the
    goal checker's `true` on the judged `Einheit` — the entry started with `args`, the starts
    `roots` naming the unit's declared roots, the run-time roots `gestartet`, the unit's own
    derived checks — with the complete enumerations of functions, locks and carriers. -/
theorem accepts_gibt_pruefer (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u)))
    (hFn : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length)))
    (hZ : zertifizierbar u = true) (hC : uCheckDecls u = .ok checks)
    (hr : roots.map (·.1) = u.roots.filterMap fun n => wurzelIdx u n)
    (hg : gestartet.map (·.1) = u.gestartet.filterMap fun n => wurzelIdx u n)
    (h : accepts u P main = .ok true) :
    akzeptiertX_pruefer.akzeptiert (einheitDer u P Q sp main args roots gestartet checks)
      (List.finRange u.fns.length) (List.finRange u.locks.length)
      ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr) = true := by
  rw [einheitDer_eq u P Q sp main args roots gestartet checks hZ hC]
  exact accepts_gibt_einheitVon u P Q sp main (⟨main, args⟩ :: roots) gestartet hFn
    (einheitDer_ws u main args roots gestartet hr hg) h

/-- **The bridge for a unit whose only start is the entry**: no declared roots, no run-time
    roots; the judged `Einheit` starts `main` alone and carries no check. -/
theorem accepts_gibt_pruefer_main (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (hFn : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length)))
    (hZ : zertifizierbar u = true) (hr : u.roots = []) (hg : u.gestartet = [])
    (h : accepts u P main = .ok true) :
    akzeptiertX_pruefer.akzeptiert (einheitDer u P Q sp main args [] [] [])
      (List.finRange u.fns.length) (List.finRange u.locks.length)
      ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr) = true :=
  accepts_gibt_pruefer u P Q sp main args [] [] [] hFn hZ (uCheckDecls_zertifizierbar u hZ)
    (roots_leer u hr) (gestartet_leer u hg) h

end Gabbro.Stage0.OldSource
