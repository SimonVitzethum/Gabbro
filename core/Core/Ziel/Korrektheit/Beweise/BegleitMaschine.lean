/-
  File:      core/Core/Ziel/Korrektheit/Beweise/BegleitMaschine.lean
  Subject:   COMPANION LEMMAS for the pinned statements of `Core/Ziel/Korrektheit/Maschine.lean`
              (implementation machine and ideal machine `I`, M4): for every `…Aussage` an
              `X.erfuellbar` (the premises hold jointly) and an `X.nichtTrivial` (the statement is
              sharp: a weaker form fails, or a refused object violates it). No statement is changed.
              The loader witnesses reuse `fragment_geladen` for the empty unit on x86-64; the rule
              witnesses reuse `trivialesSystem` (vacuous determinacy) and `gebenSystem` (one rule
              with two plans, on both projections).
-/
module

public import Core.Ziel.Korrektheit.Maschine
public import Core.Ziel.Korrektheit.Beweise.ProtokollLauf
public import Core.Ziel.Korrektheit.Beweise.ProtokollAbschluss
public import Core.Speicher.Graphmaschine
public import Core.Annahme.Annahme
public import Core.Beobachtung.Fluss.Fragment
public import Core.Katalog.Erfuellbar
public import Core.Katalog.Start
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Katalog
open Maschine

/-- The empty source unit: no declarations. Its fragment is total, so the loader witnesses below
    never inspect source forms. -/
def trivialUnit : Ast.Unit := ⟨[], Ast.UnitBody.done⟩

/-- The empty source unit elaborates to frame-only code. -/
theorem trivialUnit_rein : (Ast.Semantik.fragment Ast.Category.unit trivialUnit).Rein := by
  intro b present
  have code : (Ast.Semantik.fragment Ast.Category.unit trivialUnit).code =
      [Ast.Semantik.Befehl.starte Ast.Semantik.mainName, Ast.Semantik.Befehl.ende] := rfl
  rw [code] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl


/-- The loader succeeds for the empty unit on x86-64, with hardware, a fair history, an admissible
    start and a loaded state satisfying the protocol invariants. Feeds: `katalog_nichtLeer`,
    `zulStart_erfuellbar`, `fragment_geladen`, `protokoll_start_gut`. The image proof follows the
    `bild.gueltig` argument for the fixed loader image. -/
theorem trivial_start_bereit :
    ∃ (H : Umgebung) (s : AussenStart) (hw : HwLauf),
      (einheitVon Plattform.x86_64 trivialUnit).ZulStart H s ∧
      Hardware (einheitVon Plattform.x86_64 trivialUnit).katalog H ∧
      FairLaeufe (einheitVon Plattform.x86_64 trivialUnit).katalog H hw ∧
      ∃ z, (einheitVon Plattform.x86_64 trivialUnit).laden s (H.lade (einheitVon Plattform.x86_64 trivialUnit).bild) = some z ∧
        ProtokollGut z := by
  let P := Plattform.x86_64
  let p := Ast.Semantik.fragment Ast.Category.unit trivialUnit
  let E := einheitVon P trivialUnit
  obtain ⟨H, hw, hwhw, fair⟩ :=
    katalog_nichtLeer E.katalog (Plattform.katalog_wohlgeformt P)
  have image : E.bild.gueltig E.katalog.plattform.ziel := by
    refine ⟨List.Mem.head _, ?_, ?_⟩
    · intro a v h
      change (if a = 0 then some 0 else none) = some v at h
      split at h
      · rename_i atZero
        subst a
        exact Nat.pow_pos (Nat.zero_lt_succ _)
      · cases h
    · intro a mem
      obtain rfl := List.mem_singleton.mp mem
      exact ⟨0, rfl⟩
  obtain ⟨s, zul⟩ := zulStart_erfuellbar hwhw image
  have geladen : E.laden s (H.lade E.bild) = some (I.start E s).2 :=
    Beobachtung.fragment_geladen p P hwhw zul
  exact ⟨H, s, hw, zul, hwhw, fair, _, geladen, protokoll_start_gut P trivialUnit H s _ geladen⟩

/-- The premises of step preservation hold jointly: the all-`Unit` start state satisfies the
    protocol invariants. Feeds: `Speicher.Zustand.leer_konsistent`,
    `Speicher.Zustand.leer_vollstaendig`. Proof sketch: the start state carries the empty graph
    (consistent and complete), consumes nothing and holds free locks. -/
theorem ProtokollSchrittErhaeltAussage.erfuellbar :
    ∃ (L Ort Wert Raum Lok Grund : Type) (s : Zustand L Ort Wert Raum Lok Grund),
      ProtokollGut s := by
  let s : Zustand Unit Unit Unit Unit Unit Unit :=
    Zustand.start (fun _ => ()) (fun _ => .ruht)
      (fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩)
      ⟨fun _ => false, fun _ => 0⟩ (fun _ => ()) (PersistZustand.leer fun _ => 0)
  refine ⟨Unit, Unit, Unit, Unit, Unit, Unit, s, ⟨?_, ?_, ?_⟩⟩
  · exact ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩
  · intro c
    exact Nat.zero_le _
  · intro l
    exact ⟨List.nodup_nil, fun c hc => nomatch hc⟩

/-- The ticket guard is essential: an unguarded second ticket for a queued context breaks the
    duplicate-freedom of the queue. Feeds: `SperrZustand.anstellen`. -/
theorem ProtokollSchrittErhaeltAussage.nichtTrivial :
    ∃ (c : Kontext) (z : SperrZustand),
      z.schlange.Nodup ∧ ¬ (z.anstellen c).schlange.Nodup := by
  refine ⟨.faden 0, ⟨none, [.faden 0]⟩, List.nodup_singleton _, ?_⟩
  intro h
  exact (List.nodup_cons.mp h).1 (List.mem_singleton.mpr rfl)

/-- The premises of the loaded-start statement hold jointly: the empty unit loads on x86-64. -/
theorem ProtokollStartGutAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit) (H : Umgebung) (s : AussenStart)
      (z : Zustand Nat Ast.Semantik.Zelle Int Nat Ast.Semantik.Rahmen PUnit),
      (einheitVon P t).laden s (H.lade (einheitVon P t).bild) = some z ∧ ProtokollGut z := by
  obtain ⟨H, s, hw, zul, hwhw, fair, z, geladen, gut⟩ := trivial_start_bereit
  exact ⟨_, _, H, s, z, geladen, gut⟩

/-- The loader premise is load-bearing: with an environment that observes no image data, the load
    of the same unit fails. -/
theorem ProtokollStartGutAussage.nichtTrivial :
    ∃ (P : Plattform) (t : Ast.Unit) (H : Umgebung) (s : AussenStart),
      (einheitVon P t).laden s (H.lade (einheitVon P t).bild) = none := by
  let P := Plattform.x86_64
  let p := Ast.Semantik.fragment Ast.Category.unit trivialUnit
  let E := einheitVon P trivialUnit
  let H : Umgebung :=
    { Umgebung.referenz E.katalog 1 (fun _ _ => AussenSicht.leer) with
      lade := fun _ => ⟨fun _ => none, fun _ => none⟩ }
  let s : AussenStart := ⟨0, fun _ => none, [], fun _ => none, AussenSicht.leer⟩
  refine ⟨P, trivialUnit, H, s, ?_⟩
  show Ast.Semantik.laden p.eingang p.eintritte p.speicher P s (H.lade E.bild) = none
  have hcond : ¬ ((H.lade E.bild).starts 0 = some 0 ∧ (H.lade E.bild).bytes 0 = some 0) := by
    rintro ⟨h1, _⟩
    exact nomatch h1
  unfold Ast.Semantik.laden
  rw [if_neg hcond]

/-- The premises of the implementation-run statement hold jointly: a fair run of the empty unit
    has a loaded cut satisfying the invariants. Feeds: `fairer_lauf`, `protokoll_gut_im_lauf`. -/
theorem ProtokollGutImLaufAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit) (H : Umgebung) (ρ : Lauf (einheitVon P t)) (n : Nat)
      (z : Zustand Nat Ast.Semantik.Zelle Int Nat Ast.Semantik.Rahmen PUnit),
      Laeufe (einheitVon P t) H ρ ∧ ρ.zeit.zustand n = some z ∧ ProtokollGut z := by
  obtain ⟨H, s, hw, zul, hwhw, fair, z, geladen, gut⟩ := trivial_start_bereit
  obtain ⟨ρ, run, startEq, _⟩ := fairer_lauf _ zul fair
  refine ⟨_, _, H, ρ, 0, z, run, ?_, gut⟩
  rw [run.2.2.2, startEq]
  exact geladen

/-- The cut premise is load-bearing: runs can have empty cuts. The trivial unit never loads, so
    every cut of its admitted runs is empty. Feeds: `lauf_ab_start`. -/
theorem ProtokollGutImLaufAussage.nichtTrivial :
    ∃ (H : Umgebung) (ρ : Lauf Annahme.trivialeEinheit) (n : Nat),
      Laeufe Annahme.trivialeEinheit H ρ ∧ ρ.zeit.zustand n = none := by
  obtain ⟨H, _, hwhw, _⟩ := katalog_nichtLeer Annahme.trivialeEinheit.katalog
    (Plattform.katalog_wohlgeformt .x86_64)
  have image : Annahme.trivialeEinheit.bild.gueltig
      Annahme.trivialeEinheit.katalog.plattform.ziel := by
    exact ⟨List.Mem.head _, (fun _ _ h => nomatch h), fun _ h => (List.not_mem_nil h).elim⟩
  obtain ⟨s, zul⟩ := zulStart_erfuellbar hwhw image
  obtain ⟨ρ, run, _⟩ := lauf_ab_start Annahme.trivialeEinheit hwhw zul
  exact ⟨H, ρ, 0, run, by rw [run.2.2.2]; rfl⟩

/-- The premises of the ideal-run statement hold jointly: a fair ideal run of the empty unit
    satisfies the invariants at every cut. Feeds: `I.lauf_mit_hw`,
    `ideal_protokoll_gut_im_lauf`. -/
theorem IdealProtokollGutImLaufAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit) (η : I.Lauf (einheitVon P t)) (n : Nat),
      I.Laeufe (einheitVon P t) η ∧
      ProtokollGut (η.zeit.zustand n) := by
  obtain ⟨H, s, hw, zul, hwhw, fair, z, geladen, gut⟩ := trivial_start_bereit
  obtain ⟨η, ideal, _, _⟩ := I.lauf_mit_hw _ hwhw zul fair.konform
  exact ⟨_, _, η, 0, ideal, ideal_protokoll_gut_im_lauf _ _ _ ideal 0⟩

/-- The run premise is a real restriction: not every time evolution is an ideal run. Starting the
    clock from a state with a live context instead of the canonical start state breaks the initial
    cut. Feeds: `Zeitlauf.existiert`. -/
theorem IdealProtokollGutImLaufAussage.nichtTrivial :
    ∃ (E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit) (η : I.Lauf E),
      ¬ I.Laeufe E η := by
  let E := Annahme.trivialeEinheit
  let s : AussenStart := ⟨0, fun _ => none, [], fun _ => none, AussenSicht.leer⟩
  let H := Umgebung.referenz E.katalog 1 (fun _ _ => AussenSicht.leer)
  let hw := Umgebung.referenzLauf E.katalog 1 (fun _ _ => AussenSicht.leer)
  let bad : Zustand Unit Unit Unit Unit Unit Unit :=
    { (I.start E s).2 with status := fun _ => .laeuft }
  obtain ⟨zeit, init⟩ := Zeitlauf.existiert
    (I.Schritt E.einrichtung E.system E.katalog hw) bad
  have pause : ∀ t (z : Zustand Unit Unit Unit Unit Unit Unit),
      KeinSchritt (I.Schritt E.einrichtung E.system E.katalog hw) t z →
      ¬ AbsturzAngeboten E.katalog hw t :=
    fun t z stuck offer => stuck _ _ (.absturz (absturz_schritt_erfuellbar _ _ offer z))
  refine ⟨E, ⟨s, H, hw, zeit.erlaubePausen pause, fun _ => none⟩, ?_⟩
  intro h
  have h0 := h.2.2.2.1
  change zeit.zustand 0 = (I.start E s).2 at h0
  rw [init] at h0
  have hst := congrArg
    (fun z : Zustand Unit Unit Unit Unit Unit Unit => z.status (.faden 0)) h0
  rw [show bad.status (.faden 0) = Status.laeuft from rfl] at hst
  rw [show (I.start E s).2.status (.faden 0) = Status.ruht from rfl] at hst
  cases hst

/-- The determinacy premise holds jointly: the trivial system has no step, so its rule is
    vacuously determinate. Feeds: `Annahme.trivialesSystem`. -/
theorem ImplBestimmtAussage.erfuellbar :
    ∃ (L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type)
      (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
      (Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι),
      (∀ i c s w plans plans' u u', (Sy.regel i).impl c s w plans u →
        (Sy.regel i).impl c s w plans' u' → plans = plans' ∧ u = u') := by
  refine ⟨Unit, Unit, Unit, Unit, Unit, Unit, Unit, Unit, Unit,
    Annahme.trivialeEinheit.einrichtung, Annahme.trivialesSystem, ?_⟩
  intro i c s w plans plans' u u' h1 h2
  exact False.elim h1

/-- The rule premise is load-bearing: the release-witness rule relates one input to two plans
    (hand the lock over, or stutter), so determinacy fails for it. Feeds: `Annahme.gebenSystem`. -/
theorem ImplBestimmtAussage.nichtTrivial :
    ∃ (L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type)
      (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
      (Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι)
      (i : ι) (c : Kontext) (s : Zustand L Ort Wert Raum Lok Grund) (w : Wahl)
      (plans plans' : List (SchrittPlan L Ort Wert Bedingung))
      (u u' : Zustand L Ort Wert Raum Lok Grund),
      (Sy.regel i).impl c s w plans u ∧ (Sy.regel i).impl c s w plans' u' ∧
        ¬ (plans = plans' ∧ u = u') := by
  refine ⟨Unit, Unit, Unit, Unit, Unit, Unit, Unit, Unit, Unit, Annahme.gebenEinrichtung,
    Annahme.gebenSystem, (), Annahme.gibtHalter, Annahme.gebenZustand, (), [Annahme.gebenPlan],
    [Annahme.stutterPlanG], Annahme.gebenZustand, Annahme.gebenZustand, ?_, ?_, ?_⟩
  · exact Or.inl ⟨_, .besitzer _ _, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · rintro ⟨h1, -⟩
    have hakt : (.sperre () .geben : Aktion Unit Unit) = .intern :=
      congrArg SchrittPlan.aktion (List.cons.inj h1).1
    cases hakt

/-- The ideal machine is determinate and progressive for every elaborated unit, witnessed by the
    empty unit on x86-64. Feeds: `ideal_akzeptierte_einheit`. -/
theorem IdealAkzeptierteEinheitAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit),
      I.Bestimmt (einheitVon P t).einrichtung (einheitVon P t).system ∧
      I.Fortschritt (einheitVon P t).einrichtung (einheitVon P t).system :=
  ⟨Plattform.x86_64, trivialUnit, ideal_akzeptierte_einheit_rein _ trivialUnit trivialUnit_rein⟩

/-- Determinacy is a real restriction on the ideal side too: the same release-witness rule is
    nondeterministic through its ideal projection. Feeds: `Annahme.gebenSystem`. -/
theorem IdealAkzeptierteEinheitAussage.nichtTrivial :
    ∃ (L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type)
      (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung)
      (Sy : MaschinenSystem L Ort Wert Raum Lok Grund Bedingung Wahl ι)
      (i : ι) (c : Kontext) (s : Zustand L Ort Wert Raum Lok Grund) (w : Wahl)
      (plans plans' : List (SchrittPlan L Ort Wert Bedingung))
      (u u' : Zustand L Ort Wert Raum Lok Grund),
      (Sy.regel i).ideal c s w plans u ∧ (Sy.regel i).ideal c s w plans' u' ∧
        ¬ (plans = plans' ∧ u = u') := by
  refine ⟨Unit, Unit, Unit, Unit, Unit, Unit, Unit, Unit, Unit, Annahme.gebenEinrichtung,
    Annahme.gebenSystem, (), Annahme.gibtHalter, Annahme.gebenZustand, (), [Annahme.gebenPlan],
    [Annahme.stutterPlanG], Annahme.gebenZustand, Annahme.gebenZustand, ?_, ?_, ?_⟩
  · exact Or.inl ⟨_, .besitzer _ _, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · rintro ⟨h1, -⟩
    have hakt : (.sperre () .geben : Aktion Unit Unit) = .intern :=
      congrArg SchrittPlan.aktion (List.cons.inj h1).1
    cases hakt

end Gabbro.Core.Ziel.Korrektheit
