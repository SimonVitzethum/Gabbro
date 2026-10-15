/-
  File:      Grammatik/X86/ComposeContractReturn.lean
  Subject:   Composition closing: contract-at-return closing (lane 832).

  Closes the return-contract producer/consumer interface over already-accepted
  modules only: the source return leg (`EnsAmRueck` at actual values,
  ContractSites/VertragOrtB), the checked entry leg (`eintrittOk`,
  EntryState), the loaded-image validator leg (`valX86`,
  ValidatorSkeleton) and the cost-summary leg (`kostenSummeOk`,
  CostSummary). The closing step is one checked `Bool`
  (`rueckSchlussOk`); an inferred (`QEnsuresB`) contract is never
  admitted. No new executor, no source/checker/Spec/goal/emitter change.
-/
import Grammatik.X86.ContractSites
import Grammatik.X86.EntryState
import Grammatik.X86.ValidatorSkeleton
import Grammatik.X86.CostSummary

namespace Gabbro.Grammatik.X86

/-- Closing step: the actual-result ensures bit at its place plus the three
    accepted target admission bits. A conjunction of checks only; execution
    evidence comes from the joint witness added next. -/
def rueckSchlussOk {D : Deklaration} (P : Programm D) (f : D.Fn)
    (sread sret : World D) (rho : Env D (D.params f)) (v : ErgVal D (D.erg f))
    (p : Profil) (bild : Bild) (bias : Nat) (art : EintrittArt)
    (z : EintrittZustand) (s : CostSummary) : Bool :=
  wahr? (eval sread (P.ensures f) sret (ergEnv (D.erg f) v rho)) &&
    (eintrittOk p bild bias art z && (valX86 p bild && kostenSummeOk s))

/-- COMPOSITION (generic over arbitrary admitted inputs): the source return
    contract at its actual values with the three accepted target admissions
    closes the step. Every premise is used by the rewrite below. -/
theorem ComposeContractReturn_verbindung {D : Deklaration} (P : Programm D)
    (f : D.Fn) (sread sret : World D) (rho : Env D (D.params f))
    (v : ErgVal D (D.erg f)) (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (s : CostSummary)
    (hEns : EnsAmRueck P f sread sret rho v)
    (hEintritt : eintrittOk p bild bias art z = true)
    (hVal : valX86 p bild = true)
    (hKosten : kostenSummeOk s = true) :
    rueckSchlussOk P f sread sret rho v p bild bias art z s = true := by
  unfold rueckSchlussOk
  have hE : wahr? (eval sread (P.ensures f) sret
      (ergEnv (D.erg f) v rho)) = true := hEns
  simp [hE, hEintritt, hVal, hKosten]

/-! ## Projections: the closing step carries every leg. -/

/-- A closed step carries the source return contract at its actual values. -/
theorem rueckSchluss_gibt_ens {D : Deklaration} (P : Programm D) (f : D.Fn)
    (sread sret : World D) (rho : Env D (D.params f)) (v : ErgVal D (D.erg f))
    (p : Profil) (bild : Bild) (bias : Nat) (art : EintrittArt)
    (z : EintrittZustand) (s : CostSummary)
    (h : rueckSchlussOk P f sread sret rho v p bild bias art z s = true) :
    EnsAmRueck P f sread sret rho v := by
  unfold rueckSchlussOk at h
  have h1 := (Bool.and_eq_true_iff.mp h).1
  exact h1

/-- A closed step carries the checked entry admission. -/
theorem rueckSchluss_gibt_eintritt {D : Deklaration} (P : Programm D)
    (f : D.Fn) (sread sret : World D) (rho : Env D (D.params f))
    (v : ErgVal D (D.erg f)) (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (s : CostSummary)
    (h : rueckSchlussOk P f sread sret rho v p bild bias art z s = true) :
    eintrittOk p bild bias art z = true := by
  unfold rueckSchlussOk at h
  have h1 := (Bool.and_eq_true_iff.mp h).2
  have h2 := (Bool.and_eq_true_iff.mp h1).1
  exact h2

/-- A closed step carries the loaded-image validator admission. -/
theorem rueckSchluss_gibt_val {D : Deklaration} (P : Programm D) (f : D.Fn)
    (sread sret : World D) (rho : Env D (D.params f)) (v : ErgVal D (D.erg f))
    (p : Profil) (bild : Bild) (bias : Nat) (art : EintrittArt)
    (z : EintrittZustand) (s : CostSummary)
    (h : rueckSchlussOk P f sread sret rho v p bild bias art z s = true) :
    valX86 p bild = true := by
  unfold rueckSchlussOk at h
  have h1 := (Bool.and_eq_true_iff.mp h).2
  have h2 := (Bool.and_eq_true_iff.mp h1).2
  have h3 := (Bool.and_eq_true_iff.mp h2).1
  exact h3

/-- A closed step carries the cost-summary admission. -/
theorem rueckSchluss_gibt_kosten {D : Deklaration} (P : Programm D) (f : D.Fn)
    (sread sret : World D) (rho : Env D (D.params f)) (v : ErgVal D (D.erg f))
    (p : Profil) (bild : Bild) (bias : Nat) (art : EintrittArt)
    (z : EintrittZustand) (s : CostSummary)
    (h : rueckSchlussOk P f sread sret rho v p bild bias art z s = true) :
    kostenSummeOk s = true := by
  unfold rueckSchlussOk at h
  have h1 := (Bool.and_eq_true_iff.mp h).2
  have h2 := (Bool.and_eq_true_iff.mp h1).2
  have h3 := (Bool.and_eq_true_iff.mp h2).2
  exact h3

/-! ## Generic refusals: one failing leg poisons the closing step. -/

/-- Without the actual-result ensures bit the step never closes. -/
theorem rueckSchluss_verweigert_ohne_ens {D : Deklaration} (P : Programm D)
    (f : D.Fn) (sread sret : World D) (rho : Env D (D.params f))
    (v : ErgVal D (D.erg f)) (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (s : CostSummary)
    (h : wahr? (eval sread (P.ensures f) sret
      (ergEnv (D.erg f) v rho)) = false) :
    rueckSchlussOk P f sread sret rho v p bild bias art z s = false := by
  unfold rueckSchlussOk
  simp [h]

/-- Without the checked entry admission the step never closes. -/
theorem rueckSchluss_verweigert_ohne_eintritt {D : Deklaration}
    (P : Programm D) (f : D.Fn) (sread sret : World D)
    (rho : Env D (D.params f)) (v : ErgVal D (D.erg f)) (p : Profil)
    (bild : Bild) (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (s : CostSummary)
    (h : eintrittOk p bild bias art z = false) :
    rueckSchlussOk P f sread sret rho v p bild bias art z s = false := by
  unfold rueckSchlussOk
  simp [h]

/-- Without the loaded-image validator admission the step never closes. -/
theorem rueckSchluss_verweigert_ohne_val {D : Deklaration} (P : Programm D)
    (f : D.Fn) (sread sret : World D) (rho : Env D (D.params f))
    (v : ErgVal D (D.erg f)) (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (s : CostSummary)
    (h : valX86 p bild = false) :
    rueckSchlussOk P f sread sret rho v p bild bias art z s = false := by
  unfold rueckSchlussOk
  simp [h]

/-- Without the cost-summary admission the step never closes. -/
theorem rueckSchluss_verweigert_ohne_kosten {D : Deklaration} (P : Programm D)
    (f : D.Fn) (sread sret : World D) (rho : Env D (D.params f))
    (v : ErgVal D (D.erg f)) (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (s : CostSummary)
    (h : kostenSummeOk s = false) :
    rueckSchlussOk P f sread sret rho v p bild bias art z s = false := by
  unfold rueckSchlussOk
  simp [h]

/-! ## Concrete legs: the witness image admits the hosted entry. -/

/-- The minimal validator image admits the hosted entry state. -/
theorem eintritt_valZeuge_hosted_ok :
    eintrittOk .p48 valZeuge 0 .hostedMain zeugenEintrittHosted = true := by
  decide

/-! ## Planted refusals: each concrete failing leg poisons the close. -/

/-- The refuting result admits no close: `0 = 2 + 1` is false at its place. -/
theorem schluss_verweigert_falsches_ergebnis :
    rueckSchlussOk miniContrP fTrue miniWelt miniWelt miniRho miniV0
      .p48 valZeuge 0 .hostedMain zeugenEintrittHosted blattSummary
      = false := by
  have hfalse : wahr? (eval miniWelt (miniContrP.ensures fTrue) miniWelt
      (ergEnv (miniContrD.erg fTrue) miniV0 miniRho)) = false := rfl
  exact rueckSchluss_verweigert_ohne_ens miniContrP fTrue miniWelt miniWelt
    miniRho miniV0 .p48 valZeuge 0 .hostedMain zeugenEintrittHosted
    blattSummary hfalse

/-- An entry touching XMM without a save admits no close. -/
theorem schluss_verweigert_xmm_ohne_sicherung :
    rueckSchlussOk miniContrP fTrue miniWelt miniWelt miniRho miniV
      .p48 zeugenBild 0 .hostedMain zeugenEintrittXmmOhneSave blattSummary
      = false := by
  exact rueckSchluss_verweigert_ohne_eintritt miniContrP fTrue miniWelt
    miniWelt miniRho miniV .p48 zeugenBild 0 .hostedMain
    zeugenEintrittXmmOhneSave blattSummary zeugenXmm_verweigert

/-- A mutated opcode byte admits no close: decode coverage refuses. -/
theorem schluss_verweigert_mutiertes_byte :
    rueckSchlussOk miniContrP fTrue miniWelt miniWelt miniRho miniV
      .p48 { valZeuge with datei := [natByte 0] } 0 .hostedMain
      zeugenEintrittHosted blattSummary = false := by
  exact rueckSchluss_verweigert_ohne_val miniContrP fTrue miniWelt miniWelt
    miniRho miniV .p48 { valZeuge with datei := [natByte 0] } 0 .hostedMain
    zeugenEintrittHosted blattSummary valZeuge_mutiert_verweigert

/-- An unbounded retry site behind a constant bound admits no summary. -/
def laxeSummary : CostSummary := { blattSummary with retryBound := none }

/-- The unbounded summary is refused by the admission Bool. -/
theorem laxeSummary_verweigert : kostenSummeOk laxeSummary = false := by
  decide

/-- An unbounded retry summary admits no close. -/
theorem schluss_verweigert_unbegrenzte_wiederholung :
    rueckSchlussOk miniContrP fTrue miniWelt miniWelt miniRho miniV
      .p48 valZeuge 0 .hostedMain zeugenEintrittHosted laxeSummary
      = false := by
  exact rueckSchluss_verweigert_ohne_kosten miniContrP fTrue miniWelt
    miniWelt miniRho miniV .p48 valZeuge 0 .hostedMain zeugenEintrittHosted
    laxeSummary laxeSummary_verweigert

/-! ## No inference: the close admits the place, never the quantified guess. -/

/-- PLACE HOLDS, QUANTIFIED FAILS, through the closing step: the return
    contract closes at its actual values while the inferred `QEnsuresB`
    on the same contract is false. An inferred ensures is never admitted. -/
theorem rueckSchluss_ohne_qensures :
    rueckSchlussOk miniContrP fTrue miniWelt miniWelt miniRho miniV
      .p48 valZeuge 0 .hostedMain zeugenEintrittHosted blattSummary = true ∧
    ¬ QEnsuresB miniContrP fTrue miniWelt :=
  ⟨ComposeContractReturn_verbindung miniContrP fTrue miniWelt miniWelt
    miniRho miniV .p48 valZeuge 0 .hostedMain zeugenEintrittHosted
    blattSummary mini_ens_am_ort eintritt_valZeuge_hosted_ok
    valZeuge_akzeptiert blattSummary_ok,
   mini_qensures_falsch⟩

/-! ## Joint witness: every premise jointly on a table-writing run. -/

/-- JOINT WITNESS: every premise of `ComposeContractReturn_verbindung`
    holds jointly -- the real `setze` return contract at its actual values
    (with the `0 -> 5` memory change on a table `setze` writes), the three
    accepted target legs on one image, the closed step itself -- together
    with a reached machine run and a byte-level memory-changing write.
    Non-degenerate: `setze` writes its table, the run is reached, and both
    the source slot and a target byte observably change. -/
theorem ComposeContractReturn_verbindung_zeuge :
    ∃ (sread σ1 sret sinv σ' : World eD) (v : ErgVal eD (eD.erg eSetze))
      (M : RufMaschineG eD),
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      (eD.signatur eSetze).schreibt () = true ∧
      ((((eSp.welt []).lese [] []).slots () 0 ()).n = 0 ∧
        (sret.slots () 0 ()).n = 5) ∧
      EnsAmRueck eP eSetze sread sret .nil v ∧
      execEnd (V := vertragVon eD eSetze) eO 0 (rufAt eP eO 0 0)
        (eP.rumpf eSetze) sread .nil = EndAusgang.zurueck σ1 v ∧
      sinv = (eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte) sret ∧
      rufAt eP eO 0 1 eSetze ((eSp.welt []).lese [] []) .nil =
        RufAusgang.ok σ' v ∧
      eintrittOk .p48 valZeuge 0 .hostedMain zeugenEintrittHosted = true ∧
      valX86 .p48 valZeuge = true ∧
      kostenSummeOk blattSummary = true ∧
      rueckSchlussOk eP eSetze sread sret .nil v .p48 valZeuge 0
        .hostedMain zeugenEintrittHosted blattSummary = true ∧
      ∃ (m m' : Speicher) (a : Adresse) (w : Wort),
        w ≠ 0 ∧ write64 m a w = some m' ∧ read64 m' a = some w ∧
          m.bytes a ≠ m'.bytes a := by
  obtain ⟨sread, σ1, sret, sinv, σ', v, _, _, hbody, _, hsinv0, _, hok,
      hens1, hschr, hslots, _⟩ := rufAt_ok_gibt_ens_zeuge
  obtain ⟨M, hr, _⟩ := vertragStandort_lauf_zeuge
  have hEns : EnsAmRueck eP eSetze sread sret .nil v := hens1
  have hSchluss := ComposeContractReturn_verbindung eP eSetze sread sret
    .nil v .p48 valZeuge 0 .hostedMain zeugenEintrittHosted blattSummary
    hEns eintritt_valZeuge_hosted_ok valZeuge_akzeptiert blattSummary_ok
  obtain ⟨_, m, m', a, w, hne, hwr, hrd, hchg⟩ := eintritt_zeuge
  exact ⟨sread, σ1, sret, sinv, σ', v, M, hr, hschr, hslots, hEns, hbody,
    hsinv0, hok, eintritt_valZeuge_hosted_ok, valZeuge_akzeptiert,
    blattSummary_ok, hSchluss, m, m', a, w, hne, hwr, hrd, hchg⟩

/- CUTS:
   - Per-access x86-TSO refinement and full source-to-final-byte closure
     stay OPEN (decoder/bridge lanes own them); this file only closes
     the admitted return-contract interface over already-accepted legs.
   - `InlinePflicht.hp`/`hr` (caller footprint, lock floor) stay where
     ContractSites leaves them; the closing step carries the admitted
     bits, it does not discharge caller-side obligations.
   - Indirect calls (`callInd`, `bindCallInd`) have no site form here;
     the source leg covers direct calls through `rufAt`, as in
     ContractSites.
   - Budget simulation (`budgetSimulationOffen`, CostSummary) stays OPEN;
     the cost leg is the admitted `kostenSummeOk` Bool, never a derived
     stop claim.
   - Guard discipline is the single-probe check of EntryState, decode
     coverage the skeleton check of ValidatorSkeleton; wider sweeps stay
     with their owning lanes.
   - The `FernVertrag` inadmissible shape is reused from ContractSites,
     not restated here; its force as "quantifying away is false" comes
     from `rueckSchluss_ohne_qensures` on the inhabited mini contract.
-/

#print axioms ComposeContractReturn_verbindung
#print axioms ComposeContractReturn_verbindung_zeuge
#print axioms rueckSchluss_gibt_ens
#print axioms rueckSchluss_gibt_eintritt
#print axioms rueckSchluss_gibt_val
#print axioms rueckSchluss_gibt_kosten
#print axioms rueckSchluss_verweigert_ohne_ens
#print axioms rueckSchluss_verweigert_ohne_eintritt
#print axioms rueckSchluss_verweigert_ohne_val
#print axioms rueckSchluss_verweigert_ohne_kosten
#print axioms eintritt_valZeuge_hosted_ok
#print axioms schluss_verweigert_falsches_ergebnis
#print axioms schluss_verweigert_xmm_ohne_sicherung
#print axioms schluss_verweigert_mutiertes_byte
#print axioms laxeSummary_verweigert
#print axioms schluss_verweigert_unbegrenzte_wiederholung
#print axioms rueckSchluss_ohne_qensures

end Gabbro.Grammatik.X86
