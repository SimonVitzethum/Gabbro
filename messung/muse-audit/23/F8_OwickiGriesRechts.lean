/-
  Audit probe F8: `interferenceFree_gives_hFremd` and `owickiGries_stabil`
  repackage `InterferenceFree` (pattern a); `stabilKette_aus_Schritt` adds a
  per-thread premise it immediately forgets; `SeqTriple`/`SpecTriple` fold
  only by construction.

  Demonstrations:
  (a) `interferenceFree_gives_hFremd ... = Or.inr (hFree ...)`: the
      disjunction's disjoint side is never established -- the lemma always
      takes the right branch. So `owickiGries_stabil` (which feeds `hFremd`
      exclusively through this lemma) never uses the `stabil`/disjoint side
      of `allgemeinStabil`: the whole `HaengtAb`+`Rahmen`+`Disjunkt` machinery
      is a dead left disjunct in this path.
  (b) `stabilKette_aus_Schritt` takes `hS : ∀ g, ... → StabilSchritt ...`
      and applies it once per step; unfolding `StabilSchritt` shows this is
      `stabil` with one extra application node -- the per-thread premise is
      never combined across threads.
-/
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- (a): the bridge always takes the right disjunct. -/
example (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop)
    (hFree : InterferenceFree Nb J Q)
    (f : Faden) (hf : f ∈ J.faeden)
    (k : Nat) (g : Faden) (vor nach : World D)
    (hgm : g ∈ J.faeden) (hne : g ≠ f)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach) :
    Disjunkt (D.schreibt (J.code f)) (D.gschreibt (J.code f))
      (D.schreibt (J.code g)) (D.gschreibt (J.code g)) ∨
      (Q f vor ↔ Q f nach) :=
  Or.inr (hFree f hf k g vor nach hgm hne hkg hkv hkn)

/-- (a, corollary): `owickiGries_stabil` with `hAb` erased still proves the
    same conclusion -- the disjoint/`stabil` side is dead on this path, so
    frame-locality is an unused premise here too. -/
theorem audit_owickiGries_ohne_Ab
    (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (hSeq : ∀ (f : Faden), f ∈ J.faeden → SeqTriple Nb J Q f)
    (hFree : InterferenceFree Nb J Q) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → Q f σ := by
  intro σ hletzte f hf
  have hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ↔ Q f nach) := by
    intro k g vor nach hkg hkv hkn
    by_cases heq : g = f
    · subst heq
      exact (hSeq g hf).2 k vor nach hkg hkv hkn
    · obtain ⟨hgm, _⟩ := J.hSchritt k g vor nach hkg hkv hkn
      exact hFree f hf k g vor nach hgm heq hkg hkv hkn
  have hall := kette_erhaelt J.welten J.schrittFaden J.hKette
    (Q f) ((hSeq f hf).1) hStep
  have hlast : J.welten[J.welten.length - 1]? = some σ := by
    rw [← List.getLast?_eq_getElem?]
    exact hletzte
  exact hall _ σ hlast

/-- (b): unfolding `StabilSchritt` shows the per-thread premise is `stabil`
    with extra application nodes. -/
example (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop)
    (fremd : D.Fn) (h : StabilSchritt (D := D) W G Q fremd)
    (hQ : HaengtAb W G Q) (σ σ' : World D)
    (hR : Rahmen (D.schreibt fremd) (D.gschreibt fremd) σ σ')
    (hd : Disjunkt W G (D.schreibt fremd) (D.gschreibt fremd)) :
    Q σ ↔ Q σ' :=
  h hQ σ σ' hR hd

/-
CUTS:
- (a) does not say `owickiGries_stabil` is false; it says on its ONLY path
  the left disjunct (disjointness/`stabil`) is never taken, so `hAb`, `hInv`,
  `hDeck`, `I` are all unused there (only `hSeq`+`hFree`+`hSchritt`-membership
  matter). Verified by the `audit_owickiGries_ohne_Ab` proof above, which
  drops `I`, `hInv`, `hDeck`, `hAb` entirely.
- `seqTriple_from_spec` / `stabil_from_spec` inherit this: folding
  `SpecTriple` into `SeqTriple` via `and_congr` is construction, and the only
  `hFremd` feed is the right disjunct again.
-/
#print axioms Gabbro.Grammatik.audit_owickiGries_ohne_Ab
#print axioms Gabbro.Grammatik.interferenceFree_gives_hFremd
