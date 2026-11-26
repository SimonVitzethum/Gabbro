/-
  File:      core/Core/Ast/Semantik/Runtime/Unterbrechung/Beweise.lean
  Subject:   Proofs for the MK-20 statements: the kernel facts, the flow instances and, for every
             statement, the joint satisfiability of its scenario (`_erfuellbar`) and a model element
             that violates it or its informativeness witness (`_nichtTrivial`). The two open duties
             (`SendeLiefertAussage`, `ZaehlerUmlaufAussage`) have witnesses on both sides but no
             proof; their decomposition is in the designer's report.
-/
module

public import Core.Ast.Semantik.Runtime.Unterbrechung.Aussagen
public import Core.Ast.Semantik.Runtime.Regeln
public import Core.Beobachtung.Fluss.Beschriftung.Sprung
public import Core.Beobachtung.Fluss.Beschriftung.Leck

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Beobachtung

/-- A frame-only step leaves the machine fields the delivery decision reads. -/
private theorem ideal_nach_gleich (b : Befehl) (h : b.Privat) (c : Kontext) (s u : Zustand)
    (w : PUnit.{1}) (plans : List Plan) (step : b.ideal c s w plans u) :
    plans = [b.plan (s.lokal c) 0] ∧ u.kerne = s.kerne ∧ u.status = s.status ∧
      u.geliefert = s.geliefert ∧ u.epoche = s.epoche := by
  obtain ⟨hplan, hu⟩ := (b.ideal_privat h c s w plans u).1 step
  refine ⟨hplan, ?_, ?_, ?_, ?_⟩ <;> rw [hu] <;> rfl

/-- **Masking acts at the boundary** (proof of `MaskeSimAussage`). -/
theorem maskeSim : MaskeSimAussage := by
  intro b c s u w plans h step run t k id irq d nmi ausstehend nimmt ruht
  have priv : b.Privat := by
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  obtain ⟨_, hkerne, hstatus, hgeliefert, hepoche⟩ := ideal_nach_gleich b priv c s u w plans step
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hle, hid, hmem, hgel, hausw⟩ := ausstehend
    refine ⟨by rw [hepoche]; exact hle, hid, hmem, by rw [hgeliefert]; exact hgel, hausw⟩
  · rw [hkerne]
    exact nimmt
  · rw [hstatus]
    exact ruht

/-- **The threshold filters** (proof of `PrioritaetFilterAussage`). -/
theorem prioritaetFilter : PrioritaetFilterAussage := by
  intro m v p hlt
  have hdec : decide (p < m.minimum) = true := decide_eq_true_eq.mpr hlt
  simp only [unterbrechungen, hdec, Bool.or_true, ite_true]

/-- **The routed line enters its handler** (proof of `LeiteWirktAussage`). -/
theorem leiteWirkt : LeiteWirktAussage := by
  intro s run t k id leitung prioritaet d nmi _ _ _ _
  refine ⟨Zustandseintritt s k id d nmi, rfl, ?_, ?_⟩
  · simp only [Zustandseintritt, Function.update_self]
  · simp only [Zustandseintritt, Function.update_self, KernZustand.unterbrechen]

/-- The cleared core of a witness: no mask, no threshold, no NMI. -/
private def witnessKern (base : KernZustand Nat) : KernZustand Nat :=
  { base with maske := fun _ => false, untergrenze := 0, nmiAktiv := false }

/-- A witness state: the cleared core `k` and the resting handler context `d`. -/
private def witnessZustand (k : Kern) (d : Kontext) : Zustand :=
  { Leerzustand with
    kerne := Function.update Leerzustand.kerne k (witnessKern (Leerzustand.kerne k))
    status := Function.update Leerzustand.status d .ruht
    geliefert := [] }

/-- A witness offer: a raise at cut `0`, its selection at cut `1`, silence elsewhere. -/
private def witnessAngebot (kern : Nat) (irq : Unterbrechung) : Nat → Gelegenheit
  | 0 => ⟨none, fun c => decide (c = kern), [.erhoben kern irq], fun _ => false, false, false, 0⟩
  | 1 => ⟨none, fun c => decide (c = kern), [.zustellen kern (0, 0) irq], fun _ => false,
    false, false, 1⟩
  | _ + 2 => ⟨none, fun c => decide (c = kern), [], fun _ => false, false, false, 0⟩

/-- A witness run over the reference policy. -/
private def witnessLauf (kern : Nat) (irq : Unterbrechung) : HwLauf :=
  ⟨witnessAngebot kern irq,
    (Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer)).politik⟩

/-- A silent run: raises without any selection. -/
private def stummLauf : HwLauf :=
  ⟨fun _ => ⟨none, fun _ => false, [.erhoben 0 (.maskierbar 0 0)], fun _ => false, false,
    false, 0⟩,
    (Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer)).politik⟩

/-- The silent run never selects: its only signal is a raise. -/
private theorem stumm_keine_auswahl (t' : Nat) (id : Nat × Nat) :
    (stummLauf.angebot t').interruptAuswahl ≠ some (0, id, (.maskierbar 0 0)) := by
  intro h
  have hnone : (stummLauf.angebot t').interruptAuswahl = none := rfl
  rw [hnone] at h
  cases h

/-- The reference run raises nothing. -/
private theorem referenz_stumm (t' i : Nat) (kern : Nat) (irq : Unterbrechung) :
    ((Katalog.Umgebung.referenzLauf Plattform.x86_64.katalog 1
      (fun _ _ => AussenSicht.leer)).angebot t').interrupts[i]? ≠ some (.erhoben kern irq) := by
  intro h
  have hempty : ((Katalog.Umgebung.referenzLauf Plattform.x86_64.katalog 1
    (fun _ _ => AussenSicht.leer)).angebot t').interrupts = [] := rfl
  rw [hempty, List.getElem?_nil] at h
  cases h

/-- **A debug hit is offered** (proof of `DebugTrefferAussage`). -/
theorem debugTreffer : DebugTrefferAussage := by
  intro k h irq kern hkern support
  let signale : Nat → List InterruptSignal
    | 0 => [.erhoben kern irq]
    | 1 => [.zustellen kern (0, 0) irq]
    | _ + 2 => []
  let hw : HwLauf :=
    ⟨fun t => ⟨none, fun c => decide (c = kern), signale t, fun _ => false, false, false, t⟩,
      h.politik⟩
  refine ⟨hw, ⟨rfl, fun t => ⟨?_, ?_, ?_, ?_, ?_⟩⟩, rfl, rfl⟩
  · intro _ impossible
    cases impossible
  · intro c offered
    change decide (c = kern) = true at offered
    exact (decide_eq_true_eq.mp offered).symm ▸ hkern
  · cases t with
    | zero =>
      intro signal mem
      cases List.mem_singleton.mp mem
      exact ⟨hkern, support⟩
    | succ t =>
      cases t with
      | zero =>
        intro signal mem
        cases List.mem_singleton.mp mem
        exact ⟨hkern, support, (decide_eq_true_eq.mpr rfl), rfl, ⟨Nat.zero_le _, rfl⟩, rfl,
          fun _ => rfl⟩
      | succ _ =>
        intro signal mem
        exact (List.not_mem_nil mem).elim
  · intro _ impossible
    exact (Bool.false_ne_true impossible).elim
  · intro impossible
    exact (impossible.elim Bool.false_ne_true Bool.false_ne_true).elim

/-- **The backtrace grows at a call** (proof of `RueckblickAussage`). -/
theorem rueckblickWaechst : RueckblickAussage := by
  intro r name args bind
  unfold Rahmen.ruf Rahmen.rueckblick
  simp only [Id.run]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

/-- An interrupt-control step only advances the program counter, like `springe` with
    distance one: public equality is kept when the labels at `pc + 1` are at
    least as secret as at `pc`. -/
theorem unterbrechungSicht (β : Beschriftung) (pc : Nat) (b : Befehl)
    (hschritt : ∀ r live, b.auswerten r live = { r with pc := r.pc + 1 })
    (hT : ∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true)
    (hL : ∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) :
    b.SichtErhaltendBei β pc := by
  intro r₁ r₂ live hpc h
  subst hpc
  have pcEq : r₂.pc = r₁.pc := (sicht_pc h).symm
  simp only [hschritt, pcEq]
  exact sicht_pcWechsel hT hL h

theorem maskiereSicht (β : Beschriftung) (pc : Nat) (vektor : Nat) (aus : Bool)
    (hT : ∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true)
    (hL : ∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) :
    (Befehl.maskiere vektor aus).SichtErhaltendBei β pc :=
  unterbrechungSicht β pc _ (fun _ _ => rfl) hT hL

theorem prioritaetSicht (β : Beschriftung) (pc : Nat) (grenze : Nat)
    (hT : ∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true)
    (hL : ∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) :
    (Befehl.prioritaet grenze).SichtErhaltendBei β pc :=
  unterbrechungSicht β pc _ (fun _ _ => rfl) hT hL

theorem sendeUnterbrechungSicht (β : Beschriftung) (pc : Nat) (vektor kern : Nat)
    (hT : ∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true)
    (hL : ∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) :
    (Befehl.sendeUnterbrechung vektor kern).SichtErhaltendBei β pc :=
  unterbrechungSicht β pc _ (fun _ _ => rfl) hT hL

theorem leiteLeitungSicht (β : Beschriftung) (pc : Nat) (leitung kern prioritaet : Nat)
    (hT : ∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true)
    (hL : ∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) :
    (Befehl.leiteLeitung leitung kern prioritaet).SichtErhaltendBei β pc :=
  unterbrechungSicht β pc _ (fun _ _ => rfl) hT hL

/-- The label rule of `maskiere` is sound (proof of `MaskeFlussAussage`). -/
theorem maskeFluss : MaskeFlussAussage :=
  fun β pc vektor aus hT hL => maskiereSicht β pc vektor aus hT hL

/-- The label rule of `prioritaet` is sound (proof of `PrioritaetFlussAussage`). -/
theorem prioritaetFluss : PrioritaetFlussAussage :=
  fun β pc grenze hT hL => prioritaetSicht β pc grenze hT hL

/-- The label rule of `sendeUnterbrechung` is sound (proof of `SendeFlussAussage`). -/
theorem sendeFluss : SendeFlussAussage :=
  fun β pc vektor kern hT hL => sendeUnterbrechungSicht β pc vektor kern hT hL

/-- The label rule of `leiteLeitung` is sound (proof of `LeiteFlussAussage`). -/
theorem leiteFluss : LeiteFlussAussage :=
  fun β pc leitung kern prioritaet hT hL => leiteLeitungSicht β pc leitung kern prioritaet hT hL

/-! ### Satisfiability: the model represents every scenario -/

/-- The premises of `MaskeSimAussage` hold jointly: a mask step exists. -/
theorem maskeSim_erfuellbar :
    ∃ (b : Befehl) (c : Kontext) (s : Zustand) (w : PUnit.{1}) (plans : List Plan) (u : Zustand),
      (b.klasse = .maskiere ∨ b.klasse = .prioritaet) ∧ b.ideal c s w plans u := by
  obtain ⟨plans, u, step⟩ := (Befehl.maskiere 0 true).form.ideal_total eintritt Leerzustand ()
  exact ⟨.maskiere 0 true, eintritt, Leerzustand, (), plans, u, Or.inl rfl, step⟩

/-- `MaskeSimAussage` is informative: some steps do change the delivery state. Delivery itself
    records the consumed offer, so the frame-level stability the statement proves is a real
    restriction, not vacuity. -/
theorem maskeSim_nichtTrivial :
    ∃ (s : Zustand) (k : Kern) (id : Nat × Nat) (c : Kontext) (nmi : Bool),
      (Zustandseintritt s k id c nmi).geliefert ≠ s.geliefert := by
  refine ⟨Leerzustand, 0, (0, 0), eintritt, false, ?_⟩
  show (Leerzustand.geliefert ++ [(0, 0)]) ≠ Leerzustand.geliefert
  intro h
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

/-- The premises of `PrioritaetFilterAussage` hold jointly. -/
theorem prioritaetFilter_erfuellbar : ∃ (m : Maske) (v p : Nat), p < m.minimum :=
  ⟨⟨false, 1, false, false⟩, 0, 0, by decide⟩

/-- `PrioritaetFilterAussage` is informative: an unfiltered line is delivered. -/
theorem prioritaetFilter_nichtTrivial :
    ∃ (m : Maske) (v p : Nat), unterbrechungen m (.maskierbar v p) = .handler :=
  ⟨⟨false, 0, false, false⟩, 0, 0, by decide⟩

/-- The premises of `SendeLiefertAussage` hold jointly: a raise exists. -/
theorem sendeLiefert_erfuellbar :
    ∃ (run : HwLauf) (t vektor kern i : Nat),
      (run.angebot t).interrupts[i]? = some (.erhoben kern (.maskierbar vektor 0)) :=
  ⟨stummLauf, 0, 0, 0, 0, rfl⟩

/-- The model represents the lost send: a raise that is never selected. Only the checker (with
    the selection-fairness row) excludes it. -/
theorem sendeLiefert_nichtTrivial :
    ∃ (run : HwLauf) (t vektor kern i : Nat),
      (run.angebot t).interrupts[i]? = some (.erhoben kern (.maskierbar vektor 0)) ∧
      ∀ (t' : Nat) (id : Nat × Nat),
        (run.angebot t').interruptAuswahl ≠ some (kern, id, (.maskierbar vektor 0)) :=
  ⟨stummLauf, 0, 0, 0, 0, rfl, fun t' id => stumm_keine_auswahl t' id⟩

/-- The premises of `LeiteWirktAussage` hold jointly: a selection on an enabled core. -/
theorem leiteWirkt_erfuellbar :
    ∃ (s : Zustand) (run : HwLauf) (t : Nat) (k : Kern) (id : Nat × Nat)
      (leitung prioritaet : Nat) (d : Kontext),
      (run.angebot t).interruptAuswahl = some (k, id, (.maskierbar leitung prioritaet)) ∧
      UnterbrechungAusstehend s run t k id (.maskierbar leitung prioritaet) ∧
      NimmtUnterbrechung (s.kerne k) k (Nat.pair id.1 id.2) (.maskierbar leitung prioritaet)
        d false ∧
      s.status d = .ruht := by
  refine ⟨witnessZustand 0 (.handler 0 0 (Nat.pair 0 0)), witnessLauf 0 (.maskierbar 0 0), 1, 0,
    (0, 0), 0, 0, (.handler 0 0 (Nat.pair 0 0)), rfl,
    ⟨Nat.zero_le _, Nat.zero_le _, rfl,
      by show (0, 0) ∉ ([] : List (Nat × Nat)); exact fun h => List.not_mem_nil h, rfl⟩,
    ?_, rfl⟩
  apply NimmtUnterbrechung.handler_bei
  · exact ⟨rfl, rfl⟩
  · exact Nat.le_refl _

/-- The model represents the refused entry: a masked line is never taken. -/
theorem leiteWirkt_nichtTrivial :
    ∃ (z : KernZustand Nat) (v k idx : Nat) (c : Kontext),
      z.maske v = true ∧ ¬ NimmtUnterbrechung z k idx (.maskierbar v 0) c false := by
  refine ⟨{ (Leerzustand.kerne 0) with maske := fun _ => true }, 0, 0, 0,
    (.handler 0 0 (Nat.pair 0 0)), rfl, ?_⟩
  intro nimmt
  cases nimmt
  rename_i m _
  exact KernZustand.maskiert_nicht _ rfl m

/-- The premises of `DebugTrefferAussage` hold jointly on x86-64. -/
theorem debugTreffer_erfuellbar :
    ∃ (k : Katalog) (h : Katalog.Umgebung) (irq : Unterbrechung) (kern : Nat),
      kern < h.kernzahl ∧ h.ziel.unterstuetzt irq := by
  refine ⟨Plattform.x86_64.katalog,
    Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer),
    .maskierbar 0 0, 0, by decide, ?_⟩
  show (Plattform.x86_64.ziel.unterstuetzt (.maskierbar 0 0))
  simp only [ZielDaten.unterstuetzt, Plattform.ziel]
  decide

/-- The model represents the missed debug hit: a raise that is never selected. -/
theorem debugTreffer_nichtTrivial :
    ∃ (hw : HwLauf) (kern : Nat) (irq : Unterbrechung),
      (hw.angebot 0).interrupts[0]? = some (.erhoben kern irq) ∧
      ∀ (t' : Nat) (id : Nat × Nat),
        (hw.angebot t').interruptAuswahl ≠ some (kern, id, irq) :=
  ⟨stummLauf, 0, (.maskierbar 0 0), rfl, fun t' id => stumm_keine_auswahl t' id⟩

/-- The premises of `ZaehlerUmlaufAussage` hold jointly: the reference run counts. -/
theorem zaehlerUmlauf_erfuellbar :
    ∃ (h : Katalog.Umgebung) (run : HwLauf) (t kern umlauf : Nat), (run.angebot t).cycles = umlauf := by
  refine ⟨Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer),
    Katalog.Umgebung.referenzLauf Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer), 7, 0, 7, rfl⟩

/-- The model represents the silent counter: cycles pass without any raise. -/
theorem zaehlerUmlauf_nichtTrivial :
    ∃ (h : Katalog.Umgebung) (run : HwLauf) (t kern umlauf : Nat),
      (run.angebot t).cycles = umlauf ∧
      ∀ (t' : Nat) (irq : Unterbrechung) (i : Nat),
        t ≤ t' → (run.angebot t').interrupts[i]? ≠ some (.erhoben kern irq) := by
  refine ⟨Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer),
    Katalog.Umgebung.referenzLauf Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer), 7, 0, 7, rfl,
    fun t' irq i _ => referenz_stumm t' i 0 irq⟩

/-- The premises of `RueckblickAussage` hold jointly: a frame with a backtrace. -/
theorem rueckblick_erfuellbar : ∃ r : Rahmen, r.rueckblick ≠ [] :=
  ⟨{ Rahmen.start [] with fortsetzungen :=
    [⟨0, fun _ => none, [], fun _ => none, fun _ => none, none, none, none⟩] },
    List.cons_ne_nil _ _⟩

/-- The backtrace can be empty on a stopped frame: emptiness means no saved frame, not no error. -/
theorem rueckblick_nichtTrivial : ∃ r : Rahmen, r.rueckblick = [] ∧ r.stopp.isSome = true :=
  ⟨(Rahmen.start []).halt .fertig, rfl, rfl⟩

/-- A secret label after a public one breaks the fall-through premise. -/
private def geheimNachher : Beschriftung :=
  { temp := fun pc s => if pc = 0 ∧ s = 0 then geheim else ∅ }

/-- The flow premises hold jointly under the all-public declaration. -/
private theorem flussVoraussetzungen :
    (∀ s, oeffentlich ((.alleOeffentlich : Beschriftung).temp (0 + 1) s) = true →
      oeffentlich ((.alleOeffentlich : Beschriftung).temp 0 s) = true) ∧
    (∀ i, oeffentlich ((.alleOeffentlich : Beschriftung).lokal (0 + 1) i) = true →
      oeffentlich ((.alleOeffentlich : Beschriftung).lokal 0 i) = true) :=
  ⟨fun s _ => oeffentlich_leer, fun i _ => oeffentlich_leer⟩

/-- The flow premises fail jointly under a secret label: only the checker excludes it. -/
private theorem flussVoraussetzungen_verletzt :
    ¬ (∀ s, oeffentlich (geheimNachher.temp (0 + 1) s) = true →
      oeffentlich (geheimNachher.temp 0 s) = true) := by
  intro h
  have htmp : geheimNachher.temp 1 0 = ∅ := rfl
  have hpub : oeffentlich (geheimNachher.temp 1 0) = true := by
    rw [htmp]
    exact oeffentlich_leer
  have hsec := h 0 hpub
  have hgleich : geheimNachher.temp 0 0 = geheim := rfl
  rw [hgleich, geheim_verborgen] at hsec
  cases hsec

/-- The premises of `MaskeFlussAussage` hold jointly. -/
theorem maskeFluss_erfuellbar :
    ∃ (β : Beschriftung) (pc vektor : Nat) (aus : Bool),
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, 0, true, flussVoraussetzungen⟩

/-- The model represents the secret fall-through the rule refuses. -/
theorem maskeFluss_nichtTrivial :
    ∃ (β : Beschriftung) (pc : Nat),
      ¬ (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) :=
  ⟨geheimNachher, 0, flussVoraussetzungen_verletzt⟩

/-- The premises of `PrioritaetFlussAussage` hold jointly. -/
theorem prioritaetFluss_erfuellbar :
    ∃ (β : Beschriftung) (pc grenze : Nat),
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, 0, flussVoraussetzungen⟩

/-- The model represents the secret fall-through the rule refuses. -/
theorem prioritaetFluss_nichtTrivial :
    ∃ (β : Beschriftung) (pc : Nat),
      ¬ (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) :=
  ⟨geheimNachher, 0, flussVoraussetzungen_verletzt⟩

/-- The premises of `SendeFlussAussage` hold jointly. -/
theorem sendeFluss_erfuellbar :
    ∃ (β : Beschriftung) (pc vektor kern : Nat),
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, 0, 0, flussVoraussetzungen⟩

/-- The model represents the secret fall-through the rule refuses. -/
theorem sendeFluss_nichtTrivial :
    ∃ (β : Beschriftung) (pc : Nat),
      ¬ (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) :=
  ⟨geheimNachher, 0, flussVoraussetzungen_verletzt⟩

/-- The premises of `LeiteFlussAussage` hold jointly. -/
theorem leiteFluss_erfuellbar :
    ∃ (β : Beschriftung) (pc leitung kern prioritaet : Nat),
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, 0, 0, 0, flussVoraussetzungen⟩

/-- The model represents the secret fall-through the rule refuses. -/
theorem leiteFluss_nichtTrivial :
    ∃ (β : Beschriftung) (pc : Nat),
      ¬ (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) :=
  ⟨geheimNachher, 0, flussVoraussetzungen_verletzt⟩

end Gabbro.Core.Ast.Semantik
