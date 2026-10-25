import Grammatik.Zielsatz.Projekte.Komposition

/-!
  File:      Grammatik/Zielsatz/Projekte/Ziel.lean
  Subject:   THE GOAL FOR A PROGRAM LINKED FROM PROJECTS (`BUILD-SYSTEM.md` §7.5, L6).

  `GabbroZielProjekte`: for every checker for the rely, every link declaration `B` and every list
  of projects that cover the program's functions, share the link declaration and are accepted
  TOGETHER (the checker decides the composed unit -- the whole program), from each project's own
  user obligation (`NutzerTeilO`, reusable: the open-world rely), the named hardware assumptions
  of the composed unit (every project's axiom ensures at once) and the runtime's start of the
  composed unit: every leg of `ZielFX` on every reachable thread machine over GX -- shared atomics
  across projects, ownership over the arenas of ALL projects, callbacks, threads in both
  directions, every lock -- because the conclusion is `GabbroZiel`'s own, over the composed unit.

  Nothing is new in the conclusion and nothing is dropped: the proof is `gabbro_ziel` with (b)
  composed from the projects (`nutzerPflichtA_komponiere`).
-/

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

/-- **GABBRO_ZIEL FOR PROJECTS.** -/
def GabbroZielProjekte : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (B : Einheit D) (ps : List (Projekt D))
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    (∀ p ∈ ps, Passend B p) → ps ≠ [] → Deckend ps → DeckendS ps → -- one link declaration, all owned
    C.akzeptiert (komponiere B ps) fs.1 ls.1 cs.1 = true →     -- (a) the WHOLE program
    (∀ p ∈ ps, NutzerTeilO p) →                                -- (b) each project, once
    ∀ O : Orakel D, HardwareAnnahmen O (komponiere B ps).Q →   -- (c) all projects' ensures
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit (komponiere B ps) sp init →                     -- (d) the linked program
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX (komponiere B ps).P.mitRuhe O.mitRuhe passes
          (GeteiltV (D := D) (komponiere B ps).P (komponiere B ps).ws)
          (FadenStart (komponiere B ps).P.mitRuhe sp init lebt0) K →
          ZielFX (komponiere B ps).P.mitRuhe (komponiere B ps).S.mitRuhe O.mitRuhe passes
            (GeteiltV (D := D) (komponiere B ps).P (komponiere B ps).ws)
            (RufStartG (komponiere B ps).P.mitRuhe sp init)
            ((komponiere B ps).arenen.map (·.mitRuhe)) K

/-- **GABBRO_ZIEL FOR PROJECTS, PROVED.** -/
theorem gabbro_ziel_projekte : GabbroZielProjekte := by
  intro C D _ B ps fs ls cs hV hne hD hDS hC hN O hH passes sp init hL lebt0 K hK
  exact gabbro_ziel C D (komponiere B ps) fs ls cs hC (nutzerPflichtA_komponiere hV hne hD hDS hN)
    O hH passes sp init hL lebt0 K hK

#print axioms gabbro_ziel_projekte

end Gabbro.Grammatik.Zielsatz
