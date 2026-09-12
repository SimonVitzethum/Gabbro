/-
  Lane-21 audit probe 4: the chain-machine identification is assumed, and the
  single-thread induction step closes ownership by arithmetic.

  Claim under test:
  (a) `kette_ist_maschinenwelt` (§13) concludes three properties of the chain
      worlds `J.welten` by rewriting with the premise `hW : J.welten = M.welten`
      and citing the generated-side lemmas. Demonstrated: the conclusion is
      the generated-side triple transported along `hW` — set `J.welten` to
      `M.welten` definitionally and the proof is the triple itself.
  (b) `kette_aus_maschinenlauf_schritt` (§14) derives `Gesittet M'.lauf` and
      `BeschraenkteVerschraenkung` from `hsingle : ∀ s ∈ M.lauf, s.faden = f`
      by `hfaden.i.trans hfaden.j.symm`, discarding the mark/carrier/access
      equations (`intro ... _ _` twice). Demonstrated: the same close works
      for ANY two predicates of thread pairs — the step equations are unused.
-/
import Grammatik.Maschine

open Gabbro.Grammatik

variable {D : Deklaration}

/-- (a) Under the identification, the chain triple IS the generated triple. -/
theorem audit21_kette_is_transport (P : Programm D) (O : Orakel D)
    (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    M.welten.length = M.tiefe + 1 ∧
    (∀ W ∈ M.welten, ∀ e ∈ W.spur, e.gut) ∧
    (∃ f, M.welten.getLast? = some (M.speicher.welt (M.spuren f))) := by
  have hG : GenErreichbar P O passes (GenStart sp) M :=
    pcReach_gen P O passes prog (GenStart sp) M pc h
  exact ⟨genWelten_laenge P O passes hO sp M hG,
    genWelten_gut P O passes hO sp M hG,
    genWelten_letzte P O passes hO sp M hG⟩

/-- The in-file theorem agrees with the transport on the nose: rewriting with
    `hW` first makes them definitionally equal. -/
theorem audit21_kette_agrees (P : Programm D) (O : Orakel D)
    (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hW : J.welten = M.welten) :
    J.welten.length = M.tiefe + 1 ∧
    (∀ W ∈ J.welten, ∀ e ∈ W.spur, e.gut) ∧
    (∃ f, J.welten.getLast? = some (M.speicher.welt (M.spuren f))) :=
  -- The in-file proof is `rw [hW]; exact <generated triple>`: each conjunct
  -- is the generated-side lemma transported along `hW`. This restatement has
  -- exactly the conclusion shape of `kette_ist_maschinenwelt`.
  by rw [hW]; exact audit21_kette_is_transport P O passes hO prog sp M pc h

/-- (b) Single-threadedness closes ANY distinct-thread conclusion: the access
    equations are irrelevant once every step belongs to `f`. This is the
    proof shape `kette_aus_maschinenlauf_schritt` uses for `marke_eindeutig`
    and `ungeteilt` (there: `intro i j g1 g2 m s s' e1 e2 hi hj _ _`). -/
theorem audit21_single_thread_closes_any
    (run : Lauf (D := D)) (f : Faden)
    (hsingle : ∀ s ∈ run, s.faden = f)
    (i j : Nat) (g1 g2 : Faden) (e1 e2 : Ereignis D)
    (hi : run[i]? = some (Schritt.mk g1 e1))
    (hj : run[j]? = some (Schritt.mk g2 e2)) :
    g1 = g2 := by
  have h1 : g1 = f := hsingle _ (List.mem_of_getElem? hi)
  have h2 : g2 = f := hsingle _ (List.mem_of_getElem? hj)
  exact h1.trans h2.symm

/- 
CUTS:
- (a) shows the transport shape, not that `hW` is unprovable: §14 derives it
  for the zero-step base and single-thread lock steps. The audit point is
  only that §13 itself derives nothing beyond the rewrite.
- (b) shows the arithmetic close in isolation; the in-file use additionally
  needs `gen_eigen_getElem` to extend `hsingle` over the appended step —
  that extension is genuine and NOT challenged here.
- `audit21_kette_agrees` restates the conclusion of `kette_ist_maschinenwelt`
  as the transported generated triple; it does not unfold the in-file proof.
-/
#print axioms audit21_kette_is_transport
#print axioms audit21_kette_agrees
#print axioms audit21_single_thread_closes_any
