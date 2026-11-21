module
public import Stage0.Senke.Ausdruck.Old.Pruefer
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
@[expose] public section

namespace Gabbro.Stage0.OldSource
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz Gabbro.Grammatik.Zielsatz

/-- Export the judged unit with the compiled entry first, followed by its
    declared starts. Its check descriptors are the ones accepted by the
    production checker. -/
abbrev einheitDer (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u))) : Einheit (declOf u) :=
  einheitVon u P Q sp (⟨main, args⟩ :: roots) gestartet checks

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

/-- A successful `accepts` with entry `main` gives the
    goal checker's `true` on the judged `Einheit` — the entry started with `args`, the starts
    `roots` naming the unit's declared roots, the run-time roots `gestartet`, the unit's own
    derived checks — with the complete enumerations of functions, locks and carriers. -/
theorem accepts_gibt_pruefer (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
    (checks : List (CheckDecl (declOf u)))
    (hFn : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length)))
    (hC : uCheckDecls u = .ok checks)
    (hr : roots.map (·.1) = u.roots.filterMap fun n => wurzelIdx u n)
    (hg : gestartet.map (·.1) = u.gestartet.filterMap fun n => wurzelIdx u n)
    (h : accepts u P main = .ok true)
    (hStart : unitStartGeprueftB (einheitDer u P Q sp main args roots gestartet checks)
      (List.finRange u.fns.length) (List.finRange u.locks.length) = true) :
    akzeptiertX_pruefer.akzeptiert (einheitDer u P Q sp main args roots gestartet checks)
      (List.finRange u.fns.length) (List.finRange u.locks.length)
      ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr) = true := by
  exact accepts_gibt_einheitVon u P Q sp main (⟨main, args⟩ :: roots) gestartet checks hC hFn
    (einheitDer_ws u main args roots gestartet hr hg) h hStart

/-- **The bridge for a unit whose only start is the entry**: no declared or
    run-time roots. The judged unit retains all derived checks. -/
theorem accepts_gibt_pruefer_main (u : UProg) (P : Programm (declOf u)) (Q : AxEns (declOf u))
    (sp : Speicher (declOf u)) (main : (declOf u).Fn)
    (args : Env (declOf u) ((declOf u).params main))
    (hFn : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length)))
    (checks : List (CheckDecl (declOf u))) (hC : uCheckDecls u = .ok checks)
    (hr : u.roots = []) (hg : u.gestartet = [])
    (h : accepts u P main = .ok true)
    (hStart : unitStartGeprueftB (einheitDer u P Q sp main args [] [] checks)
      (List.finRange u.fns.length) (List.finRange u.locks.length) = true) :
    akzeptiertX_pruefer.akzeptiert (einheitDer u P Q sp main args [] [] checks)
      (List.finRange u.fns.length) (List.finRange u.locks.length)
      ((List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr) = true :=
  accepts_gibt_pruefer u P Q sp main args [] [] checks hFn hC
    (roots_leer u hr) (gestartet_leer u hg) h hStart

end Gabbro.Stage0.OldSource
