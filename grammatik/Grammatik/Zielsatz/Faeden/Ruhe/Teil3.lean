module

public import Grammatik.Zielsatz.Faeden.Ruhe.Teil1
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch.T3
import Grammatik.Bausteine.Kernzelle.ZulassungMitRuhe

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

section Transfer

variable [DecidableEq D.Fn] (P : Programm D) {S : SperrInv D} {fs ws : List D.Fn}

/-- A declared check as a check of `D.mitRuhe`: the same declaration, probe and
    gates under `some`, the same Duty (marks survive the idle root). -/
def CheckDecl.mitRuhe (c : CheckDecl D) : CheckDecl D.mitRuhe :=
  { name := c.name, claim := c.claim, misst := c.misst, gates := c.gates.map some, probe := some c.probe, duty := c.duty, boden := c.boden, sonde := c.sonde, testbau := c.testbau }

/-- Injectivity transport for gate lists: distinct gates stay distinct. -/
theorem nodup_map_some {gs : List D.Fn} (h : gs.Nodup) : (gs.map some).Nodup := by
  have hP : gs.Pairwise (· ≠ ·) := List.nodup_iff_pairwise_ne.mp h
  have hM : (gs.map some).Pairwise (· ≠ ·) :=
    hP.map some (fun a b hab he => hab (Option.some_inj.mp he))
  exact List.nodup_iff_pairwise_ne.mpr hM

/-- The exact expansion survives the idle root: signatures are shifted types
    over the same marks, gates and freshness. -/
theorem CheckExpansion.mitRuhe {c : CheckDecl D} (h : CheckExpansion P c) :
    CheckExpansion P.mitRuhe (CheckDecl.mitRuhe c) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1' : (D.signatur c.probe).erg = some .bool := h1
    show D.mitRuhe.erg (some c.probe) = _
    rw [show D.mitRuhe.erg (some c.probe) = ((D.signatur c.probe).erg).map tyR from rfl, h1']
    simp only [Option.map_some, tyR, Ty.mapNumbers]
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact h7 g0 hg0
  · intro hm
    have hp : (CheckDecl.mitRuhe c).probe = some c.probe := rfl
    rw [hp] at hm
    obtain ⟨g0, hg0, he⟩ := List.mem_map.mp hm
    exact h8 (Option.some_inj.mp he ▸ hg0)
  · exact nodup_map_some h9

/-- The call-graph closure survives the idle root: reach from `some` is reach
    from the function, and `none` is never reached from a probe. -/
theorem CheckRahmen.mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA : ∀ w, AbgK P fs (reachB P fs w)) {c : CheckDecl D} (h : CheckRahmen P fs c) :
    CheckRahmen P.mitRuhe (fsRuhe fs) (CheckDecl.mitRuhe c) := by
  intro f' hf' hne
  cases f' with
  | none =>
    change reachB P.mitRuhe (fsRuhe fs) (some c.probe) none = true at hf'
    rw [reachB_mitRuhe_nicht_ruhe P hA] at hf'
    cases hf'
  | some f =>
    change reachB P.mitRuhe (fsRuhe fs) (some c.probe) (some f) = true at hf'
    rw [reachB_mitRuhe P hvoll hA] at hf'
    have hne' : f ≠ c.probe := fun he => hne (congrArg some he)
    obtain ⟨hft, hfg, hfd⟩ := h f hf' hne'
    exact ⟨hft, hfg, hfd⟩

/-- The admission survives the idle root, check by check. -/
theorem CheckAdmission.mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA : ∀ w, AbgK P fs (reachB P fs w)) {checks : List (CheckDecl D)}
    (h : CheckAdmission P fs checks) :
    CheckAdmission P.mitRuhe (fsRuhe fs) (checks.map CheckDecl.mitRuhe) := by
  obtain ⟨hexp, hrah, hprobe, hgates, hnodup⟩ := h
  have e : ∀ l : List (CheckDecl D),
      (l.map CheckDecl.mitRuhe).map CheckDecl.name = l.map CheckDecl.name := by
    intro l
    induction l with
    | nil => rfl
    | cons c rest ih =>
      show CheckDecl.name (CheckDecl.mitRuhe c) :: (rest.map CheckDecl.mitRuhe).map CheckDecl.name = _
      rw [ih]
      rfl
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc g hg => ?_, ?_⟩
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    exact CheckExpansion.mitRuhe P (hexp c0 hc0)
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    exact CheckRahmen.mitRuhe P hvoll hA (hrah c0 hc0)
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    change some c0.probe ∈ none :: fs.map some
    exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨c0.probe, hprobe c0 hc0, rfl⟩))
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    change some g0 ∈ none :: fs.map some
    exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨g0, hgates c0 hc0 g0 hg0, rfl⟩))
  · rw [e]
    exact hnodup

/-- The same referenced foreign signatures retain all four admission facts. -/
theorem SchnittstellenOk.mitRuhe (h : SchnittstellenOk P fs) :
    SchnittstellenOk P.mitRuhe (fsRuhe fs) := by
  intro f' hf a ha
  cases f' with
  | none =>
      change Sum.inl a ∈ ([] : List (D.Ax ⊕ D.Reg)) at ha
      exact False.elim (List.not_mem_nil ha)
  | some f =>
      have hf0 : f ∈ fs := by
        change some f ∈ none :: fs.map some at hf
        rcases List.mem_cons.mp hf with hf | hf
        · cases hf
        · obtain ⟨g, hg, he⟩ := List.mem_map.mp hf
          exact Option.some.inj he ▸ hg
      rw [rumpf_mitRuhe_ants P f] at ha
      obtain ⟨hparams, herg, hgruende, hprod⟩ := h f hf0 a ha
      exact ⟨congrArg (List.map tyR) hparams, congrArg (Option.map tyR) herg,
        hgruende, hprod⟩

/-- **Transfer of the checker's facts to `P.mitRuhe`.** The declared checks ride
    along under `some` (probe and gates), with their admission transported. -/
theorem akzeptiertSpec_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) {A : List (Kernzelle.AccumulatorDecl D)} (hA : AkzeptiertSpec P S fs ws A) :
    AkzeptiertSpec P.mitRuhe S.mitRuhe (fsRuhe fs) (wsRuhe ws) (A.map Kernzelle.AccumulatorDecl.mitRuhe) where
  frag := frag_mitRuhe P hA.frag
  abg := abg_mitRuhe P hvoll hA.abg
  fuss := fussS_mitRuhe P hvoll hA.abg hA.fuss
  stufen := stufen_mitRuhe P hA.stufen
  sperrOrte := fun L c hc => (bewacht_mitRuhe (D := D) c L).mpr (hA.sperrOrte L c hc)
  wurzeln := fun w' hw' => by
    obtain ⟨w, hw, rfl⟩ := mem_wsRuhe.mp hw'
    exact hA.wurzeln w hw
  einzeln := einzelnPool_mitRuhe P hvoll hA.abg hA.einzeln
  renn := fun c hB hAt => schreibGetrennt_mitRuhe P hvoll hA.abg
    (hA.renn c (fun L hL => hB L ((bewacht_mitRuhe (D := D) c L).mpr hL)) hAt)
  antworten
    | none, _, hx => absurd hx List.not_mem_nil
    | some f, x, hx => (stelleOk_mitRuhe (D := D) x).mpr
        (hA.antworten f x (by rw [← rumpf_mitRuhe_ants P f]; exact hx))
  masken
    | none, hw, _, _ => Bool.noConfusion hw
    | some w, hw, f', hf' => by
        obtain ⟨f, rfl, hf⟩ := reach_mitRuhe_cases P hvoll hA.abg hf'
        rw [rumpf_mitRuhe_mE]
        exact hA.masken w hw f hf
  schnittstellen := SchnittstellenOk.mitRuhe P hA.schnittstellen
  reset := fun g elem len harr => by
    have hT : tyR (D.gtyp g) = .arr elem len := harr
    revert hT
    cases hτ : D.gtyp g with
    | arr elem' len' =>
      intro hT
      simp only [tyR, Ty.mapNumbers] at hT
      cases hT
      exact zeroAdmitting_tyR (hA.reset g _ _ hτ)
    | ptr cap =>
      rcases cap with ⟨space, rights, target⟩
      cases target
      intro hT
      simp only [tyR, Ty.mapNumbers, reduceCtorEq] at hT
    | _ => intro hT; simp only [tyR, Ty.mapNumbers, reduceCtorEq] at hT

  akku := Kernzelle.accumulatorAdmission_mitRuhe P hvoll hA.abg hA.akku

  pruef := by
    obtain ⟨checks, hChecks⟩ := hA.pruef
    exact ⟨checks.map CheckDecl.mitRuhe, CheckAdmission.mitRuhe P hvoll hA.abg hChecks⟩

/-- The fixture expansion survives the idle root. -/
theorem pruef_expansion_mitRuhe_zeuge :
    CheckExpansion pruefP.mitRuhe (CheckDecl.mitRuhe pruefC) :=
  CheckExpansion.mitRuhe pruefP pruef_expansion

end Transfer

end Gabbro.Grammatik
