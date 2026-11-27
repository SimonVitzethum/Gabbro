/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Hebung/Teilbuendel.lean
  Subject:   Causal draw-prefix replay through the ordinary exchange arrival.

  The register-valued `ZiehungsAntwort` of the old replay encoding is excluded at every
  admission point (KatalogAnkunft): a marked exchange cannot commit a register result.
  The draw therefore enters through `zufallsAnkunft`, whose band-indexed catalogue policy
  installs an exchange body in one object and lets the machine admit the resulting ordinary
  answer step. This module keeps the generic causal recursion of the lift, replaces the
  excluded register premise by that manufactured exchange step, and proves conservation of
  the consumed draw count. The full bundle is not claimed closed.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Hebung.ZiehungsMass
public import Core.Beobachtung.Wahrscheinlichkeit.Hebung.KatalogAnkunft
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Maschine
open Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]

/-- The bundle without the scheduler-following and draw-stamping fields. -/
structure Teilbuendel (B : Zufallsbindung) (S : Scheduler)
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) where
  mu : MeasureTheory.Measure Band
  replay : Band → Maschine.Lauf E
  istWMass : MeasureTheory.IsProbabilityMeasure mu
  massErhalt : ∀ Z : Zylinder B.quelle, (Z.pfad.map Prod.fst).Nodup →
    mu {band : Band | ∀ p ∈ Z.pfad, band B.quelle.id p.1 % B.quelle.anz = p.2.val} =
      ZylinderGewicht B.quelle Z
  replayZulaessig : ∀ band, Maschine.Laeufe E h (replay band)
  replayKausal : KausalReplay replay

/-- The partial bundle exists: the measure comes from `ZiehungsMass`, the replay is a
    single run admitted by the hardware and start, and causality is trivial for a
    constant replay. -/
noncomputable def teilbuendel_erfuellbar (B : Zufallsbindung) (S : Scheduler)
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) (hardware : Hardware E.katalog h)
    (start : ∃ s : AussenStart, E.ZulStart h s) : Teilbuendel B S E h := by
  let s := Classical.choose start
  have zul := Classical.choose_spec start
  let rest := lauf_ab_start E hardware zul
  let ρ := Classical.choose rest
  have zulaessig := (Classical.choose_spec rest).1
  let mass := massBuendel_erfuellbar B
  exact
    { mu := mass.mu
      replay := fun _ => ρ
      istWMass := mass.istWMass
      massErhalt := mass.massErhalt
      replayZulaessig := fun _ => zulaessig
      replayKausal := fun _ _ _ _ _ _ => ⟨rfl, rfl⟩ }

/-- Finite causal agreement: the states at every cut `m ≤ n` and the traces at every
    step `t < n`. This is the induction invariant behind `KausalReplay`. -/
def StimmenBis (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ₁ ρ₂ : Maschine.Lauf E) (n : Nat) : Prop :=
  (∀ m, m ≤ n → ρ₁.zeit.zustand m = ρ₂.zeit.zustand m) ∧
    ∀ t, t < n → ρ₁.zeit.spur t = ρ₂.zeit.spur t

/-- What one replay step produces: the traced choice and the state it reaches. Its
    admissibility is deliberately not part of this data. -/
abbrev SchrittAusgabe (Wahl Ort Wert : Type) (S : Type) :=
  Option (SchrittWahl Wahl × SchrittSpur Ort Wert) × S

/-- A draw step at cut `t`: the band index `k` selects a body through the fixed catalogue
    policy `code`, the marked exchange answer carries that body, and the machine admits
    the resulting ordinary answer step. This replaces the excluded register premise: the
    reply is the `exchanged` result manufactured by `zufallsAnkunft`, never a `register`. -/
def IstZufallsAnkunftSchritt (B : Zufallsbindung)
    (code : Fin B.quelle.anz → List UInt8) (band : Band)
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (t k : Nat) (s : Option (Zustand L Ort Wert Raum Lok Grund))
    (aus : SchrittAusgabe Wahl Ort Wert (Option (Zustand L Ort Wert Raum Lok Grund))) : Prop :=
  ∃ a : AntwortEreignis, ∃ spur : SchrittSpur Ort Wert,
    ∃ s₀ s₀' : Zustand L Ort Wert Raum Lok Grund,
      s = some s₀ ∧
      aus = (some (.antwort a, spur), some s₀') ∧
      Zufallsfrage B a.question ∧
      ∃ (origin : Herkunft) (footprint : List Herkunft) (body : List UInt8),
        a.reply = ⟨origin, footprint, .ok (.exchanged B.kennung body)⟩ ∧
        body = code (Ziehung B.quelle band k) ∧
        ∃ run : HwLauf,
          AntwortSchritt E.einrichtung E.katalog run t a s₀ spur s₀'

/-- Equal raw draws give equal typed drawings. -/
theorem ziehungWertGleich (B : Zufallsbindung) (b₁ b₂ : Band) (k : Nat)
    (h : b₁ B.quelle.id k = b₂ B.quelle.id k) :
    Ziehung B.quelle b₁ k = Ziehung B.quelle b₂ k := by
  apply Fin.ext
  change b₁ B.quelle.id k % B.quelle.anz = b₂ B.quelle.id k % B.quelle.anz
  rw [h]

/-- The marked random answers produced at one cut of a run. -/
def antwortenBei (B : Zufallsbindung)
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ : Maschine.Lauf E) (t : Nat) : List AntwortEreignis :=
  match ρ.zeit.spur t with
  | none => []
  | some (_, spur) =>
      spur.aussen.filterMap fun e => match e with
        | .antwort a => if istZufallsfrage B a.question then some a else none
        | _ => none

/-- The consumed draw count of a prefix, accumulated cut by cut. -/
def ziehungenBis (B : Zufallsbindung)
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ : Maschine.Lauf E) : Nat → Nat
  | 0 => 0
  | t + 1 => ziehungenBis B ρ t + (antwortenBei B ρ t).length

/-- A manufactured marked arrival contributes exactly one consumed draw. -/
theorem antwortenBei_anzahl (B : Zufallsbindung)
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ : Maschine.Lauf E) (t : Nat) (a : AntwortEreignis) (spur : SchrittSpur Ort Wert)
    (hfrag : Zufallsfrage B a.question)
    (hspur : ρ.zeit.spur t = some (.antwort a, spur))
    (haussen : spur.aussen = [Ereignis.antwort a]) :
    (antwortenBei B ρ t).length = 1 := by
  have hfrag' : istZufallsfrage B a.question = true := hfrag
  simp only [antwortenBei, hspur, haussen, List.filterMap_cons, List.filterMap_nil,
    hfrag', ↓reduceIte, List.length_cons, List.length_nil]

/-- Conservation: a manufactured draw step consumes one draw, no more and no less. -/
theorem ziehungenBis_draw (B : Zufallsbindung)
    (code : Fin B.quelle.anz → List UInt8) (band : Band)
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (F : Option (Zustand L Ort Wert Raum Lok Grund) → Nat →
      SchrittAusgabe Wahl Ort Wert (Option (Zustand L Ort Wert Raum Lok Grund)))
    (ρ : Maschine.Lauf E) (t k : Nat)
    (h : IstZufallsAnkunftSchritt B code band E t k (ρ.zeit.zustand t)
      (F (ρ.zeit.zustand t) (Ziehung B.quelle band k).val))
    (hF : (ρ.zeit.spur t, ρ.zeit.zustand (t + 1)) =
      F (ρ.zeit.zustand t) (Ziehung B.quelle band k).val) :
    ziehungenBis B ρ (t + 1) = ziehungenBis B ρ t + 1 := by
  rcases h with ⟨a, spur, s₀, s₀', hs, haus, hfrag, origin, footprint, body, reply, hbody, run, schritt⟩
  have heq := hF.trans haus
  have hspur : ρ.zeit.spur t = some (.antwort a, spur) := congrArg Prod.fst heq
  have haussen : spur.aussen = [.antwort a] := schritt.2.1
  simp only [ziehungenBis]
  rw [antwortenBei_anzahl B ρ t a spur hfrag hspur haussen]

/-- Conservation: an idle cut consumes no draw. -/
theorem ziehungenBis_wartet (B : Zufallsbindung)
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ : Maschine.Lauf E) (t : Nat) (h : ρ.zeit.spur t = none) :
    ziehungenBis B ρ (t + 1) = ziehungenBis B ρ t := by
  simp only [ziehungenBis, antwortenBei, h, List.length_nil, Nat.add_zero]

/-- Conservation: a cut with no marked random answer consumes no draw. -/
theorem ziehungenBis_keineAntwort (B : Zufallsbindung)
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (ρ : Maschine.Lauf E) (t : Nat) (h : antwortenBei B ρ t = []) :
    ziehungenBis B ρ (t + 1) = ziehungenBis B ρ t := by
  simp only [ziehungenBis, h, List.length_nil, Nat.add_zero]

/-- The causal prefix step at a manufactured draw: equal bands at the consumed draw and
    the one recursion `F` give agreement one cut further. -/
theorem zufallsPraefixSchritt
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (code : Fin B.quelle.anz → List UInt8) (n k : Nat)
    (F : Option (Zustand L Ort Wert Raum Lok Grund) → Nat →
      SchrittAusgabe Wahl Ort Wert (Option (Zustand L Ort Wert Raum Lok Grund)))
    (ρ₁ ρ₂ : Maschine.Lauf E) (b₁ b₂ : Band)
    (hprev : StimmenBis E ρ₁ ρ₂ n)
    (hband : b₁ B.quelle.id k = b₂ B.quelle.id k)
    (h₁ : IstZufallsAnkunftSchritt B code b₁ E n k (ρ₁.zeit.zustand n)
      (F (ρ₁.zeit.zustand n) (Ziehung B.quelle b₁ k).val))
    (h₂ : IstZufallsAnkunftSchritt B code b₂ E n k (ρ₂.zeit.zustand n)
      (F (ρ₂.zeit.zustand n) (Ziehung B.quelle b₂ k).val))
    (hF₁ : (ρ₁.zeit.spur n, ρ₁.zeit.zustand (n + 1)) =
      F (ρ₁.zeit.zustand n) (Ziehung B.quelle b₁ k).val)
    (hF₂ : (ρ₂.zeit.spur n, ρ₂.zeit.zustand (n + 1)) =
      F (ρ₂.zeit.zustand n) (Ziehung B.quelle b₂ k).val) :
    StimmenBis E ρ₁ ρ₂ (n + 1) := by
  have hdraw := ziehungWertGleich B b₁ b₂ k hband
  have hzustand : ρ₁.zeit.zustand n = ρ₂.zeit.zustand n := hprev.1 n (Nat.le_refl n)
  have haus : (ρ₁.zeit.spur n, ρ₁.zeit.zustand (n + 1)) =
      (ρ₂.zeit.spur n, ρ₂.zeit.zustand (n + 1)) := by
    rw [hF₁, hF₂, hzustand, hdraw]
  constructor
  · intro m hm
    rcases lt_or_eq_of_le hm with hlt | rfl
    · exact hprev.1 m (Nat.le_of_lt_succ hlt)
    · exact congrArg Prod.snd haus
  · intro t ht
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ ht) with hlt | rfl
    · exact hprev.2 t hlt
    · exact congrArg Prod.fst haus

/-- Prefix agreement also holds across an idle cut: a pause leaves the state unchanged
    and both traces are `none`, so the band plays no role at all. -/
theorem wartetPraefixSchritt
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ₁ ρ₂ : Maschine.Lauf E) (n : Nat)
    (hprev : StimmenBis E ρ₁ ρ₂ n)
    (h₁ : ρ₁.zeit.spur n = none) (h₂ : ρ₂.zeit.spur n = none) :
    StimmenBis E ρ₁ ρ₂ (n + 1) := by
  have w₁ := ρ₁.zeit.wartet h₁
  have w₂ := ρ₂.zeit.wartet h₂
  have hzustand : ρ₁.zeit.zustand (n + 1) = ρ₂.zeit.zustand (n + 1) := by
    rw [w₁.1, w₂.1]
    exact hprev.1 n (Nat.le_refl n)
  constructor
  · intro m hm
    rcases lt_or_eq_of_le hm with hlt | rfl
    · exact hprev.1 m (Nat.le_of_lt_succ hlt)
    · exact hzustand
  · intro t ht
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ ht) with hlt | rfl
    · exact hprev.2 t hlt
    · rw [h₁, h₂]

/-- Prefix agreement for an arbitrary idle or non-draw step: the step is produced by a
    draw-free function `G` of the current state alone, so equal states give equal steps. -/
theorem drawFreierPraefixSchritt
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (G : Option (Zustand L Ort Wert Raum Lok Grund) →
      SchrittAusgabe Wahl Ort Wert (Option (Zustand L Ort Wert Raum Lok Grund)))
    (ρ₁ ρ₂ : Maschine.Lauf E) (n : Nat)
    (hprev : StimmenBis E ρ₁ ρ₂ n)
    (hG₁ : (ρ₁.zeit.spur n, ρ₁.zeit.zustand (n + 1)) = G (ρ₁.zeit.zustand n))
    (hG₂ : (ρ₂.zeit.spur n, ρ₂.zeit.zustand (n + 1)) = G (ρ₂.zeit.zustand n)) :
    StimmenBis E ρ₁ ρ₂ (n + 1) := by
  have hzustand : ρ₁.zeit.zustand n = ρ₂.zeit.zustand n := hprev.1 n (Nat.le_refl n)
  have haus : (ρ₁.zeit.spur n, ρ₁.zeit.zustand (n + 1)) =
      (ρ₂.zeit.spur n, ρ₂.zeit.zustand (n + 1)) := by
    rw [hG₁, hG₂, hzustand]
  constructor
  · intro m hm
    rcases lt_or_eq_of_le hm with hlt | rfl
    · exact hprev.1 m (Nat.le_of_lt_succ hlt)
    · exact congrArg Prod.snd haus
  · intro t ht
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ ht) with hlt | rfl
    · exact hprev.2 t hlt
    · exact congrArg Prod.fst haus

/-- Composing the step over all cuts: a replay whose draw cuts are driven by the one
    recursion `F` and whose other cuts are driven by the draw-free `G` is causal. The
    catalogue side still has to show each draw cut is admitted; this is the recursion
    half only. `KausalReplay` is used unchanged. -/
theorem kausalReplay_ausPraefixSchritt
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (code : Fin B.quelle.anz → List UInt8)
    (k : Nat → Nat) (hkn : ∀ n, k n ≤ n)
    (F : Option (Zustand L Ort Wert Raum Lok Grund) → Nat →
      SchrittAusgabe Wahl Ort Wert (Option (Zustand L Ort Wert Raum Lok Grund)))
    (G : Option (Zustand L Ort Wert Raum Lok Grund) →
      SchrittAusgabe Wahl Ort Wert (Option (Zustand L Ort Wert Raum Lok Grund)))
    (ZiehungsCut : Nat → Option (Zustand L Ort Wert Raum Lok Grund) → Prop)
    (replay : Band → Maschine.Lauf E)
    (hinit : ∀ b₁ b₂ : Band, (replay b₁).zeit.zustand 0 = (replay b₂).zeit.zustand 0)
    (hfolgt : ∀ (b : Band) (t : Nat),
      (ZiehungsCut t ((replay b).zeit.zustand t) →
        IstZufallsAnkunftSchritt B code b E t (k t) ((replay b).zeit.zustand t)
          (F ((replay b).zeit.zustand t) (Ziehung B.quelle b (k t)).val) ∧
        ((replay b).zeit.spur t, (replay b).zeit.zustand (t + 1)) =
          F ((replay b).zeit.zustand t) (Ziehung B.quelle b (k t)).val) ∧
      (¬ ZiehungsCut t ((replay b).zeit.zustand t) →
        ((replay b).zeit.spur t, (replay b).zeit.zustand (t + 1)) =
          G ((replay b).zeit.zustand t))) :
    KausalReplay replay := by
  intro b₁ b₂ t hband t' ht'
  have bis : ∀ n, n ≤ t → StimmenBis E (replay b₁) (replay b₂) n := by
    intro n hn
    induction n with
    | zero =>
        exact ⟨fun m hm => by have : m = 0 := Nat.eq_zero_of_le_zero hm; subst m; exact hinit b₁ b₂,
          fun t h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
        have prev := ih (Nat.le_trans (Nat.le_succ n) hn)
        have hnlt : n < t := Nat.lt_of_succ_le hn
        have hbband : b₁ B.quelle.id (k n) = b₂ B.quelle.id (k n) :=
          hband B.quelle.id (k n) (Nat.lt_of_le_of_lt (hkn n) hnlt)
        have hzustand : (replay b₁).zeit.zustand n = (replay b₂).zeit.zustand n :=
          prev.1 n (Nat.le_refl n)
        by_cases hcut : ZiehungsCut n ((replay b₁).zeit.zustand n)
        · have hcut₂ : ZiehungsCut n ((replay b₂).zeit.zustand n) := by
            rwa [← hzustand]
          have hd₁ := (hfolgt b₁ n).1 hcut
          have hd₂ := (hfolgt b₂ n).1 hcut₂
          exact zufallsPraefixSchritt E B code n (k n) F (replay b₁) (replay b₂) b₁ b₂
            prev hbband hd₁.1 hd₂.1 hd₁.2 hd₂.2
        · have hcut₂ : ¬ ZiehungsCut n ((replay b₂).zeit.zustand n) := by
            intro hc
            exact hcut (by rwa [hzustand])
          have hf₁ := (hfolgt b₁ n).2 hcut
          have hf₂ := (hfolgt b₂ n).2 hcut₂
          exact drawFreierPraefixSchritt E G (replay b₁) (replay b₂) n prev hf₁ hf₂
  have bt := bis t (Nat.le_refl t)
  exact ⟨bt.1 t' (Nat.le_of_lt ht'), bt.2 t' ht'⟩

/-- A concrete, valid, non-idle draw prefix: on the x86-64 platform a pending marked
    exchange is installed and `zufallsAnkunft` manufactures an admitted `ImplSchritt`
    carrying the band-indexed body. The step is exhibited, never projected from an
    assumed answer. -/
theorem zufallsAnkunftSchritt_erfuellbar
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (hkatalog : E.katalog = Plattform.x86_64.katalog)
    (basis : Zustand L Ort Wert Raum Lok Grund) :
  ∃ (s : Zustand L Ort Wert Raum Lok Grund) (q : FrageEreignis) (band : Band)
    (a : AntwortEreignis) (spur : SchrittSpur Ort Wert)
    (s' : Zustand L Ort Wert Raum Lok Grund) (run : HwLauf),
      q ∈ s.fragen ∧
      let B : Zufallsbindung := ⟨muenzQuelle, .cProcess, []⟩
      let code : Fin B.quelle.anz → List UInt8 := fun v => if v.val = 0 then [] else [1]
      IstZufallsAnkunftSchritt B code band E 1 0 (some s)
        (some (SchrittWahl.antwort (Wahl := Wahl) a, spur), some s') ∧
      (some (SchrittWahl.antwort (Wahl := Wahl) a, spur) :
        Option (SchrittWahl Wahl × SchrittSpur Ort Wert)) ≠ none ∧
      ImplSchritt E.einrichtung E.system E.katalog run 1 s
        (SchrittWahl.antwort (Wahl := Wahl) a, spur) s' := by
  let B : Zufallsbindung := ⟨muenzQuelle, .cProcess, []⟩
  let code : Fin B.quelle.anz → List UInt8 := fun v => if v.val = 0 then [] else [1]
  let obj : Objekt := ⟨.cProcess, 1⟩
  let handle : Handle := ⟨0, ⟨obj, 0⟩, [.invoke]⟩
  let q : FrageEreignis := ⟨0, 0, 0, ⟨.cProcess, handle, [], .exchange []⟩⟩
  let s := (Zustand.start (L := L) basis.lokal basis.status basis.kerne basis.rechte
    basis.initial basis.persistenz).frage q
  let snapshot : AussenSicht := { AussenSicht.leer with
    objects := Function.update AussenSicht.leer.objects obj ⟨0, true, true, [], fun _ => 0⟩
    channels := fun ep i => if ep = .cProcess ∧ i = 0 then some handle else none }
  let k := Plattform.x86_64.katalog
  let h := Umgebung.referenz k 1 (fun _ _ => snapshot)
  let run := Umgebung.referenzLauf k 1 (fun _ _ => snapshot)
  let fair : FairLaeufe k h run :=
    Umgebung.referenz_fair k 1 _ (Plattform.katalog_wohlgeformt _) (Nat.zero_lt_succ 0)
  have zeile : ZufallszeileZugelassen k B := by
    change Zeile.zufall 0 ∈ Plattform.x86_64.zeilen
    decide
  have marker : Zufallsfrage B q.question := rfl
  have pending : q ∈ s.fragen := List.mem_cons_self
  have delivery : (run.angebot 1).delivery q.question.endpoint = true := by
    change decide (Zeile.endpoint .cProcess ∈ Plattform.x86_64.zeilen) = true
    decide
  have valid : q.question.zugriffe.all (snapshot.gueltig .cProcess) = true := by
    simp only [q, Frage.zugriffe, List.all_cons, AussenOperation.required, snapshot,
      AussenSicht.gueltig, handle, obj, AussenSicht.herkunft, Function.update_self,
      ↓reduceIte, and_self, BEq.rfl, List.mem_singleton, decide_true, Bool.and_self, List.all_nil]
  have ready : (snapshot.objects obj).ready = true := by
    simp only [snapshot, Function.update_self]
  let band : Band := fun _ _ => 0
  let body := code (Ziehung B.quelle band (0 : Fin 2))
  let h' := austauschUmgebung k h 1 q.question.objekt body
  let run' : HwLauf := { run with politik := h'.politik }
  obtain ⟨a, spur, s', _, _, _, zu, schritt, reply⟩ :=
    zufallsAnkunft fair.hardware fair.konform ⟨zeile, zufallGesetz_nationaleMuenze _⟩
      q marker pending (Nat.le_refl _) (Nat.zero_le _)
      (fun _ mem => (List.not_mem_nil mem).elim) delivery rfl valid ready
      Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig code band (0 : Fin 2)
  have schritt' : AntwortSchritt E.einrichtung E.katalog run' 1 a s spur s' := by
    simpa [hkatalog, run', h', body, k] using schritt
  have crashFrei : (run'.angebot 1).crash = false := by
    simp only [run', run, Umgebung.referenzLauf]
  refine ⟨s, q, band, a, spur, s', run', pending, ?_, ?_, ?_⟩
  · dsimp only
    use a, spur, s, s'
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rw [← zu.2.2.2]
      exact marker
    · have hresult : a.reply.result =
          .ok (.exchanged B.kennung (code (Ziehung B.quelle band 0))) := by
        rw [reply]
        rfl
      cases hrep : a.reply with
      | mk origin footprint result =>
        rw [hrep] at hresult
        change result = .ok (.exchanged B.kennung (code (Ziehung B.quelle band 0))) at hresult
        refine ⟨origin, footprint, code (Ziehung B.quelle band 0), ?_, ?_, ?_⟩
        · rw [hresult]
        · rfl
        · exact ⟨run', schritt'⟩
  · simp
  · exact ImplSchritt.antwort crashFrei schritt'

end Gabbro.Core.Beobachtung
