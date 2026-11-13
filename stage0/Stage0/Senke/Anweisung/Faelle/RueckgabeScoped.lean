/-
  The model's release of the scopes of a scoped return leaves every cell of the world: `World.gibt` changes only
  the trace (`World.gibt_foldl_speicher`), so the world in memory (`WeltAt_gibt_foldl`), the owed-invariant read
  phase (`owedWorld_gibt_slots`, `owedWorld_gibt_globs`, `owedFailure_gibt`) and the fault code of a normal return
  (`returnFault_gibt_foldl`) are those of the world before the release. The scoped returns themselves, with real
  releases at the return site, are `Sperre/Ticket/RueckLauf.lean`.
-/
module
public import Stage0.Senke.Anweisung
public import Stage0.Senke.Anweisung.Faelle.Kontext
public import Stage0.Senke.Anweisung.Faelle.Hilfen
public import Stage0.Senke.Rueckkehr.Normal
public import Stage0.Senke.Rueckkehr.Reason
public import Stage0.Senke.Ausdruck
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Return
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Ruf.RufLogik
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable [Kern]

variable {D : Deklaration} {L : Lay D}

section Freigabe

variable {P : Programm D} {f : D.Fn}

/-- Releasing scopes keeps every world cell: the fold is trace-only. -/
theorem WeltAt_gibt_foldl {m : Runner.Mem} {σ : World D} {Ls : List D.Lock}
    (h : WeltAt m L σ) : WeltAt m L (Ls.foldl World.gibt σ) := by
  obtain ⟨hs, hg⟩ := World.gibt_foldl_speicher σ Ls
  obtain ⟨hslots, hglobs, hwr⟩ := h
  refine ⟨fun t f k hk => ?_, fun g => ?_, hwr⟩
  · have hv := hslots t f k hk
    rwa [hs]
  · have hv := hglobs g
    rwa [hg]

/-- The owed-invariant read phase sees the same slots after a release fold. -/
theorem owedWorld_gibt_slots (postA postB : World D)
    (hps : postA.slots = postB.slots) :
    (owedWorld P f postA).slots = (owedWorld P f postB).slots := by
  simp only [owedWorld]
  rw [foldl_lese_slots, foldl_lese_slots]
  exact hps

/-- The owed-invariant read phase sees the same globals after a release fold. -/
theorem owedWorld_gibt_globs (postA postB : World D)
    (hpg : postA.globs = postB.globs) :
    (owedWorld P f postA).globs = (owedWorld P f postB).globs := by
  simp only [owedWorld]
  rw [foldl_lese_globs, foldl_lese_globs]
  exact hpg

/-- The reason-search outcome is unchanged by a release fold. -/
theorem owedFailure_gibt (wa wb : World D)
    (hws : wa.slots = wb.slots) (hwg : wa.globs = wb.globs) :
    owedFailure P f wa = owedFailure P f wb := by
  unfold owedFailure
  have hfind : ∀ is : List D.Inv,
      (is.find? fun i => schuldet f i && !wahr? (eval wa (P.invariante i) wa .nil)) =
      (is.find? fun i => schuldet f i && !wahr? (eval wb (P.invariante i) wb .nil)) := by
    intro is
    induction is with
    | nil => rfl
    | cons i is ih =>
      have hi : (schuldet f i && !wahr? (eval wa (P.invariante i) wa .nil)) =
          (schuldet f i && !wahr? (eval wb (P.invariante i) wb .nil)) := by
        rw [eval_spurfrei (P.invariante i) wa wb wa wb hws hwg hws hwg .nil]
      by_cases h : (schuldet f i && !wahr? (eval wa (P.invariante i) wa .nil)) = true
      · have h2 : (schuldet f i && !wahr? (eval wb (P.invariante i) wb .nil)) = true := by
          rw [← hi]; exact h
        rw [List.find?_cons_of_pos (p := fun j : D.Inv =>
              schuldet f j && !wahr? (eval wa (P.invariante j) wa .nil)) (a := i) (l := is) h,
            List.find?_cons_of_pos (p := fun j : D.Inv =>
              schuldet f j && !wahr? (eval wb (P.invariante j) wb .nil)) (a := i) (l := is) h2]
      · have h2 : ¬(schuldet f i && !wahr? (eval wb (P.invariante i) wb .nil)) = true := by
          intro hcon; apply h; rw [hi]; exact hcon
        rw [List.find?_cons_of_neg (p := fun j : D.Inv =>
              schuldet f j && !wahr? (eval wa (P.invariante j) wa .nil)) (a := i) (l := is) h,
            List.find?_cons_of_neg (p := fun j : D.Inv =>
              schuldet f j && !wahr? (eval wb (P.invariante j) wb .nil)) (a := i) (l := is) h2, ih]
  exact hfind D.invs

/-- The normal-return fault code is unchanged by a release fold. -/
theorem returnFault_lese_congr (σ0 : World D) (ρ : Env D (D.params f))
    (v : ErgVal D (D.erg f)) (postA postB : World D)
    (hps : postA.slots = postB.slots) (hpg : postA.globs = postB.globs) :
    (if wahr? (eval σ0 (P.ensures f) postA (ergEnv (D.erg f) v ρ)) = false then 102
      else if (owedFailure P f (owedWorld P f postA)).isSome then 103 else 0) =
    (if wahr? (eval σ0 (P.ensures f) postB (ergEnv (D.erg f) v ρ)) = false then 102
      else if (owedFailure P f (owedWorld P f postB)).isSome then 103 else 0) := by
  have hens : wahr? (eval σ0 (P.ensures f) postA (ergEnv (D.erg f) v ρ)) =
      wahr? (eval σ0 (P.ensures f) postB (ergEnv (D.erg f) v ρ)) :=
    congrArg wahr? (eval_spurfrei (P.ensures f) σ0 σ0 postA postB rfl rfl hps hpg _)
  have hws := owedWorld_gibt_slots (P := P) (f := f) postA postB hps
  have hwg := owedWorld_gibt_globs (P := P) (f := f) postA postB hpg
  have hf := owedFailure_gibt (P := P) (f := f) _ _ hws hwg
  rw [hens, hf]

/-- The normal-return fault code survives the scope release. -/
theorem returnFault_gibt_foldl (σ0 σ1 : World D) (ρ : Env D (D.params f))
    (v : ErgVal D (D.erg f)) (Ls : List D.Lock) :
    returnFault P f σ0 (Ls.foldl World.gibt σ1) ρ v =
      returnFault P f σ0 σ1 ρ v := by
  obtain ⟨hs, hg⟩ := World.gibt_foldl_speicher σ1 Ls
  have hps : ((Ls.foldl World.gibt σ1).lese (vertragVon D f).ende
      (P.ensures f).orte).slots =
      (σ1.lese (vertragVon D f).ende (P.ensures f).orte).slots := hs
  have hpg : ((Ls.foldl World.gibt σ1).lese (vertragVon D f).ende
      (P.ensures f).orte).globs =
      (σ1.lese (vertragVon D f).ende (P.ensures f).orte).globs := hg
  exact returnFault_lese_congr (P := P) (f := f) σ0 ρ v _ _ hps hpg

end Freigabe

end Gabbro.Stage0.Senke
