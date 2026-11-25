/-
  File:      core/Core/Speicher/Litmus/Rmw.lean
  Subject:   RMW ATOMICITY catalogue entry: two updates on one cell may not read the same write,
             so neither two `fetch_add` operations nor a pair of CAS operations can lose an
             increment. The allowed half exhibits a chained `fetch_add` and CAS.

  Source: Lahav, Vafeiadis, Kang, Hur, Dreyer, "Repairing Sequential Consistency in C/C++11"
  (PLDI 2017), §3.2 atomicity (`myrmw; eco` irreflexive and `myrmw ∩ (rb; mo) = ∅`) and §7
  (read-after-RMW elimination); the RCMC paper (POPL 2018) §3.2.3, which states that atomicity
  together with totality of `mo` makes `rf ; rmw` a partial function; Batty et al. (POPL 2011)
  for the C11 CAS/fetch-add fragment; the herd `rc11.cat` axiom `atomicity` and the LKMM test
  `Atomic-RMW-ops-are-atomic-WRT-atomic_set`.
  Modes: FORBIDDEN in every mode, `rlx`, `ra` and `sc` alike -- the two atomicity fields carry no
  mode premise; the allowed graph uses `.rlx`, the weakest atomic mode.
  Expected: FORBIDDEN (no consistent graph has two distinct updates reading one write); ALLOWED
  (a consistent and complete graph has the second update read the first one's increment).
-/
module

public import Core.Speicher.Trennung

@[expose] public section

namespace Gabbro.Core.Speicher

/-- **Atomicity of read-modify-writes is forbidden to break.** No consistent graph has two
    distinct updates `u₁`, `u₂` that read one and the same write `w`. Two `fetch_add` on one cell
    both reading the initial value would lose an increment; a pair of CAS with the same expected
    value would both succeed on the same old value. Feeds: `liest_vorher`, `atomar`, `mo_total`. -/
def RmwVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ ∃ w u₁ u₂ : E,
      G.rf w u₁ ∧ G.rf w u₂ ∧ G.istRmw u₁ ∧ G.istRmw u₂ ∧ u₁ ≠ u₂

theorem rmw_verboten_kat : RmwVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, w, u₁, u₂, h1, h2, hu1, hu2, hne⟩
  have sch : ∀ a, G.istRmw a → G.schreibt a := by
    intro a h
    unfold Graph.schreibt Graph.istRmw at *
    rw [h]
    exact trivial
  have o1 := hk.wf.rf_ort w u₁ h1
  have o2 := hk.wf.rf_ort w u₂ h2
  have ho : G.ort u₁ = G.ort u₂ := o1.symm.trans o2
  have m1 := hk.liest_vorher w u₁ h1 hu1
  have m2 := hk.liest_vorher w u₂ h2 hu2
  rcases hk.wf.mo_total u₁ u₂ (sch u₁ hu1) (sch u₂ hu2) ho hne with h | h
  · exact (hk.atomar w u₂ u₁ h2 hu2 m1) h
  · exact (hk.atomar w u₁ u₂ h1 hu1 m2) h

/-- The three events of the chained graph: the initial write, the fetch-and-add and the CAS. -/
inductive RmwLitEv where
  | w
  | fa
  | cas
  deriving DecidableEq, Repr

open RmwLitEv

/-- `w` writes `0`, the fetch-and-add reads `0` and writes `1`, the CAS reads `1` and writes `2`.
    Every access is relaxed; both updates are one event each, reading and writing. -/
def rmLab : RmwLitEv → Etikett Bool Nat
  | w => ⟨.schreiben, false, .rlx, 0, 0⟩
  | fa => ⟨.rmw, false, .rlx, 0, 1⟩
  | cas => ⟨.rmw, false, .rlx, 1, 2⟩

/-- No program order: the two updates are in different threads. -/
@[reducible] def rmPo (_a _b : RmwLitEv) : Prop := False

/-- Each update reads the write preceding it in modification order. -/
@[reducible] def rmRf (a b : RmwLitEv) : Prop := (a = w ∧ b = fa) ∨ (a = fa ∧ b = cas)

/-- Modification order is the chain `w < fa < cas`. -/
@[reducible] def rmMo (a b : RmwLitEv) : Prop :=
  (a = w ∧ (b = fa ∨ b = cas)) ∨ (a = fa ∧ b = cas)

def rmGraph : Graph RmwLitEv Bool Nat := ⟨rmLab, rmPo, rmRf, rmMo⟩

theorem rmWf : rmGraph.Wohlgeformt where
  po_trans := by
    intro _ _ _ h
    exact False.elim h
  po_irrefl := by
    intro _ h
    exact False.elim h
  rf_schreibt := by
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact trivial
  rf_liest := by
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact trivial
  rf_ort := by
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_wert := by
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_eindeutig := by
    intro a b c h1 h2
    revert h1 h2
    cases a <;> cases b <;> cases c <;> decide
  mo_schreibt := by
    rintro _ _ (⟨rfl, (rfl | rfl)⟩ | ⟨rfl, rfl⟩) <;> exact ⟨trivial, trivial⟩
  mo_ort := by
    rintro _ _ (⟨rfl, (rfl | rfl)⟩ | ⟨rfl, rfl⟩) <;> rfl
  mo_trans := by
    intro a b c
    show rmMo a b → rmMo b c → rmMo a c
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ rmMo a a
    cases a <;> decide
  mo_total := by
    intro a b _ _ _ hne
    show rmMo a b ∨ rmMo b a
    cases a <;> cases b <;> first | decide | exact absurd rfl hne

/-- No `sw` step exists: every mode is relaxed, so `Modus.stark` fails. -/
theorem rmHbSchrittFalsch (a b : RmwLitEv) : ¬ rmGraph.hbSchritt a b := by
  intro h
  rcases h with hpo | hsw
  · exact False.elim hpo
  · rcases hsw with ⟨_, hstark, _, _, _⟩
    cases a <;> simp only [Graph.modus, rmGraph, rmLab, Modus.stark] at hstark <;>
      exact False.elim hstark

theorem rmHbFalsch (a b : RmwLitEv) : ¬ rmGraph.hb a b := by
  intro h
  induction h with
  | single hs => exact rmHbSchrittFalsch _ _ hs
  | tail _ _ ih => exact ih

theorem rmPscFalsch (a b : RmwLitEv) : ¬ rmGraph.psc a b := by
  intro h
  obtain ⟨hsc, _⟩ := h
  cases a <;> simp only [Graph.sc, Graph.modus, rmGraph, rmLab, reduceCtorEq] at hsc

theorem rmKonsistent : rmGraph.Konsistent where
  wf := rmWf
  hb_irrefl := by
    intro a h
    exact rmHbFalsch a a h
  kohaerent := by
    intro a b h
    exact absurd h (rmHbFalsch a b)
  atomar := by
    intro w u w' hrf _ hmo
    revert hrf hmo
    cases w <;> cases u <;> cases w' <;> decide
  psc := by
    intro a h
    obtain ⟨c, hc⟩ := transGen_kopf h
    exact False.elim (rmPscFalsch a c hc)
  ohneLB := by
    refine azyklisch_von_rang (fun e : RmwLitEv => match e with | w => 0 | fa => 1 | cas => 2) ?_
    intro a b h
    rcases h with hpo | hrf
    · exact False.elim hpo
    · revert hrf
      cases a <;> cases b <;> decide
  liest_vorher := by
    intro w u hrf _
    revert hrf
    cases w <;> cases u <;> decide

/-- Both updates have a source: the graph is complete. -/
theorem rmVollstaendig : rmGraph.Vollstaendig := by
  intro a ha
  cases a with
  | w => exact (ha : False).elim
  | fa => exact ⟨w, Or.inl ⟨rfl, rfl⟩⟩
  | cas => exact ⟨fa, Or.inr ⟨rfl, rfl⟩⟩

/-- **Two chained updates are allowed.** A relaxed fetch-and-add reads the initial write and a
    relaxed CAS reads the fetch-and-add's write; no increment is lost. -/
def RmwErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ G.Vollstaendig ∧ ∃ w fa cas : E,
      G.rf w fa ∧ G.rf fa cas ∧ G.istRmw fa ∧ G.istRmw cas ∧ w ≠ fa ∧ fa ≠ cas

theorem rmw_erlaubt_kat : RmwErlaubtAussage := by
  refine ⟨RmwLitEv, Bool, Nat, rmGraph, rmKonsistent, rmVollstaendig, w, fa, cas,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · rfl
  · rfl
  · decide
  · decide

/-- **The RMW-atomicity catalogue entry.** -/
def RmwLitmusAussage : Prop := RmwVerbotenAussage ∧ RmwErlaubtAussage

theorem rmw_litmus : RmwLitmusAussage := ⟨rmw_verboten_kat, rmw_erlaubt_kat⟩

end Gabbro.Core.Speicher
