/-
  File:      Core/Beobachtung/SchrankenBeweise/DurchlaufEinheit.lean
  Subject:   PER-PASS COST MARKS (MK-12a follow-up): the start duty and the protocol duty of the
             units and their loaders. The start duty holds for every unit because every mark
             window is empty at cut zero; the protocol duty holds once protocol transitions
             keep the mark stand, but the unrestricted protocol duty is false for a loader whose
             recovery data opens a mark with an already elapsed window. The missing premise is
             named exactly; nothing is weakened.
-/
module

public import Core.Beobachtung.SchrankenBeweise.Durchlauf

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Annahme
open Annahme.Hosted

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- Counting a last unmarked tick does not change an interval count. -/
private theorem zaehle_still {markiert : Nat → Bool} {anfang k : Nat}
    (still : markiert (anfang + k) = false) :
    I.zaehle markiert anfang (k + 1) = I.zaehle markiert anfang k := by
  simp only [I.zaehle, still, Bool.false_eq_true, if_false, Nat.add_zero]

/-- A tick that is no context step of `c` adds nothing to the context cost of `c`. -/
private theorem kontextkosten_fremd {ρ : Lauf E} {c : Kontext} {a k t : Nat}
    (eq : a + k = t)
    (fremd : ∀ d w spur, ρ.zeit.spur t = some (.kontext d w, spur) → d ≠ c) :
    Kontextkosten ρ c a (k + 1) = Kontextkosten ρ c a k := by
  have tick : ∀ d w spur, ρ.zeit.spur (a + k) = some (.kontext d w, spur) → d ≠ c := by
    intro d w spur h
    rw [eq] at h
    exact fremd d w spur h
  have still : (fun t => match ρ.zeit.spur t with
      | some (.kontext d _, _) => decide (c = d)
      | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
      (a + k) = false := by
    change (match ρ.zeit.spur (a + k) with
      | some (.kontext d _, _) => decide (c = d)
      | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
      = false
    cases hsp : ρ.zeit.spur (a + k) with
    | none => rfl
    | some label =>
      rcases label with ⟨w, spur⟩
      cases w with
      | antwort _ | interrupt _ | absturz => rfl
      | kontext d _ =>
        show decide (c = d) = false
        exact decide_eq_false (Ne.symm (tick d _ _ hsp))
  simp only [Kontextkosten]
  rw [zaehle_still still]

/-- The start duty of every unit. At cut zero the only candidate is the loader's state; every
    mark read from its local stand has an empty cost window (`0 - m.2 = 0`), so the ceiling is
    met whether the stand is empty or carries marks. Loader data therefore need no extra premise
    for the start leg. -/
theorem durchlaufStart : DurchlaufStartPflicht E := by
  intro h ρ lauf t' s hle sEq c m hmem
  have ht0 : t' = 0 := by omega
  subst t'
  have e0 : 0 - m.2 = 0 := by omega
  rw [e0]
  simp only [Kontextkosten, I.zaehle]
  intro n _
  exact Nat.zero_le n

/-- The missing premise of the protocol duty: a protocol transition never introduces an open
    mark whose window already contains executed ticks. Every mark of the successor's stand was
    already open before the tick, or opens after it. Answers and interrupts satisfy this
    definitionally (they leave the local state untouched); a crash only satisfies it when the
    recovery entry's loader data carries no such back-dated mark. -/
def ProtokollMarkenErhaltend (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop :=
  ∀ {h : Umgebung} {ρ : Lauf E} {t : Nat} {w : SchrittWahl Wahl} {spur : SchrittSpur Ort Wert}
    {vor nach : Zustand L Ort Wert Raum Lok Grund},
    Laeufe E h ρ →
    ρ.zeit.zustand t = some vor → ρ.zeit.spur t = some (w, spur) → ProtokollB8Wahl w →
    ρ.zeit.zustand (t + 1) = some nach →
    ∀ c m, m ∈ E.schranken.durchlaufstand (nach.lokal c) →
      m ∈ E.schranken.durchlaufstand (vor.lokal c) ∨ t < m.2

/-- The protocol duty under that premise. Older cuts carry over by the premise; a new cut's
    inherited mark keeps its cost because the protocol tick is foreign to every context. A mark
    opening after the tick has an empty window. -/
theorem durchlaufProtokoll (marken : ProtokollMarkenErhaltend E) : DurchlaufProtokollPflicht E := by
  intro h ρ lauf t w spur vor nach hyp vorEq spurEq wahl nachEq t' s hle sEq c m hmem
  by_cases hle' : t' ≤ t
  · exact hyp t' s hle' sEq c m hmem
  · have et : t' = t + 1 := by omega
    subst t'
    by_cases hm2 : t < m.2
    · have e0 : t + 1 - m.2 = 0 := by omega
      rw [e0]
      simp only [Kontextkosten, I.zaehle]
      intro n _
      exact Nat.zero_le n
    · have hmemOder := marken lauf vorEq spurEq wahl sEq c m hmem
      have hvor : m ∈ E.schranken.durchlaufstand (vor.lokal c) := by
        cases hmemOder with
        | inl hm => exact hm
        | inr hlt => exact (hm2 hlt).elim
      have boundVor := hyp t vor (Nat.le_refl t) vorEq c m hvor
      have fremd : ∀ d w' spur', ρ.zeit.spur t = some (.kontext d w', spur') → d ≠ c := by
        intro d w' spur' hsp
        have pairEq : (w, spur) = (.kontext d w', spur') := Option.some.inj (spurEq.symm.trans hsp)
        have wEq : w = .kontext d w' := congrArg Prod.fst pairEq
        cases w with
        | kontext _ _ => exact False.elim wahl
        | antwort _ | interrupt _ | absturz => cases wEq
      have ewin : t + 1 - m.2 = (t - m.2) + 1 := by omega
      rw [ewin]
      have eadd : m.2 + (t - m.2) = t := by omega
      rw [kontextkosten_fremd eadd fremd]
      exact boundVor

private def griff2 : Handle := { griff with channel := 1 }

private theorem griff_ungleich : griff ≠ griff2 := by
  intro h
  have hc := congrArg Handle.channel h
  simp only [griff, griff2] at hc
  omega

private def einrichtungGegen : Einrichtung Unit Unit Unit Unit (Option Handle) Unit Unit :=
  { einrichtung with
    wiederanlauf := { einrichtung.wiederanlauf with daten := fun _ => daten (some griff2) } }

private def markenGegen (l : Option Handle) : List (Nat × Nat) :=
  if l = some griff2 then [(0, 0)] else []

private def gegenEinheit : Modell :=
  { einheit with
    einrichtung := einrichtungGegen
    schranken := { Schrankendaten.leer with
      durchlauf := fun b => if b = 0 then some 0 else none
      durchlaufstand := markenGegen } }

private theorem gegen_persistence : gegenEinheit.katalog.enthaelt .persistence := by
  change .persistence ∈ (ZielZeilen ++ .persistence :: _ : List Zeile)
  exact List.mem_append.mpr (Or.inr (List.Mem.head _))

private def gegenBasis : Gelegenheit := ⟨none, fun _ => false, [], fun _ => false, false, false, 0⟩

private def gegenHw : HwLauf :=
  { politik := (umgebung []).politik
    angebot := fun t =>
      if t = 0 then { gegenBasis with core := some 0, cycles := t }
      else if t = 1 then { gegenBasis with crash := true, cycles := t }
      else gegenBasis }

private theorem gegenHw_0 : gegenHw.angebot 0 = { gegenBasis with core := some 0 } := by
  dsimp only [gegenHw]
  rw [if_pos rfl]
  rfl

private theorem gegenHw_1 : gegenHw.angebot 1 = { gegenBasis with crash := true, cycles := 1 } := by
  dsimp only [gegenHw]
  rw [if_neg (by omega : (1 : Nat) ≠ 0), if_pos rfl]

private theorem gegenHw_ander {i : Nat} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    gegenHw.angebot i = gegenBasis := by
  dsimp only [gegenHw]
  rw [if_neg h0, if_neg h1]

private theorem gegenHw_konform : gegenHw.konform gegenEinheit.katalog (umgebung []) := by
  constructor
  · rfl
  · intro i
    by_cases h0 : i = 0
    · subst i
      rw [gegenHw_0]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        change some 0 = some c at hc
        cases Option.some.inj hc
        exact Nat.zero_lt_succ 0
      · intro c hc
        cases hc
      · intro sig mem
        cases mem
      · intro e he
        cases he
      · intro hm
        cases hm with
        | inl medium => cases medium
        | inr crash => cases crash
    · by_cases h1 : i = 1
      · subst i
        rw [gegenHw_1]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro c hc
          cases hc
        · intro c hc
          cases hc
        · intro sig mem
          cases mem
        · intro e he
          cases he
        · intro hm
          exact gegen_persistence
      · rw [gegenHw_ander h0 h1]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro c hc
          cases hc
        · intro c hc
          cases hc
        · intro sig mem
          cases mem
        · intro e he
          cases he
        · intro hm
          cases hm with
          | inl medium => cases medium
          | inr crash => cases crash

private theorem stand_start_leer (s : AussenStart) (zul : einheit.ZulStart (umgebung []) s)
    (c : Kontext) : gegenEinheit.schranken.durchlaufstand ((startZustand s).lokal c) = [] := by
  change markenGegen ((startDaten s).lokal c) = []
  have granted : s.outside.channels .hosted 0 = some griff := by
    rw [zul.2.2.2.2.2.2.2]
    rfl
  change markenGegen (s.outside.channels .hosted 0) = []
  rw [granted]
  simp only [markenGegen]
  rw [if_neg (by
    intro eq
    exact griff_ungleich (Option.some.inj eq))]

private theorem stand_binde_leer (s : AussenStart) (c : Kontext) :
    gegenEinheit.schranken.durchlaufstand ((binde (startZustand s)).lokal c) = [] := by
  change markenGegen ((binde (startZustand s)).lokal c) = []
  change markenGegen (none : Option Handle) = []
  simp only [markenGegen]
  rw [if_neg (by intro h; cases h)]

private def zustand2Gegen (s : AussenStart) : Zustand :=
  (binde (startZustand s)).wiederanlauf gegenEinheit.einrichtung.wiederanlauf 1
    (nachAbsturz (binde (startZustand s)).persistenz)

private theorem gegen_konkreter_lauf (s : AussenStart) (zul : einheit.ZulStart (umgebung []) s) :
    ∃ ρ : Lauf gegenEinheit,
      Laeufe gegenEinheit (umgebung []) ρ ∧
      ρ.zeit.zustand 0 = some (startZustand s) ∧
      ρ.zeit.zustand 1 = some (binde (startZustand s)) ∧
      ρ.zeit.zustand 2 = some (zustand2Gegen s) ∧
      ρ.zeit.spur 0 = some (.kontext kontext (), ⟨[], []⟩) ∧
      ρ.zeit.spur 1 = some (.absturz, absturzSpur) := by
  obtain ⟨g, g', grant, issue, reply⟩ := protokoll_erfuellbar s []
  let z0 := startZustand s
  let z1 := binde z0
  let z2 := zustand2Gegen s
  let offer : AbsturzAngeboten gegenEinheit.katalog gegenHw 1 :=
    ⟨gegen_persistence, by rw [gegenHw_1]⟩
  have step0 : Lauffolge gegenEinheit gegenHw 0 (some z0) (.kontext kontext (), ⟨[], []⟩) (some z1) := by
    apply Lauffolge.schritt
    apply ImplSchritt.kontext
    · rw [gegenHw_0]
      rfl
    · exact ⟨0, rfl, rfl, rfl⟩
    · change einheit.system.ImplSchritt kontext z0 () [bindePlan] z1
      exact form_binden zul
    · refine ⟨?_, ?_, [], ?_, ?_, ?_, ?_⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · intro l mem
        exact (List.not_mem_nil mem).elim
      · exact z1
      · exact FuehrtAus.intern
      · exact Speicherfolge.nil _
      · rfl
  have step1 : Lauffolge gegenEinheit gegenHw 1 (some z1) (.absturz, absturzSpur) (some z2) := by
    apply Lauffolge.schritt
    apply ImplSchritt.absturz
    exact absturz_schritt_erfuellbar _ _ offer _
  have still : ∀ u, KeinSchritt (Lauffolge gegenEinheit gegenHw) (u + 2) (some z2) := by
    intro u ev next step
    cases step with
    | schritt impl =>
      cases impl with
      | kontext _ ready _ _ =>
        obtain ⟨k, gelegen, _, _⟩ := ready
        change (gegenHw.angebot (u + 2)).core = some k at gelegen
        rw [gegenHw_ander (by omega : u + 2 ≠ 0) (by omega : u + 2 ≠ 1)] at gelegen
        cases gelegen
      | antwort _ replyStep =>
        have erl := replyStep.1.2.1
        simp only [AntwortEreignis.erlaubt] at erl
        rw [replyStep.1.1] at erl
        rw [gegenHw_ander (by omega : u + 2 ≠ 0) (by omega : u + 2 ≠ 1)] at erl
        exact Bool.false_ne_true erl.1
      | interrupt _ enters =>
        obtain ⟨k, irq, c, nmi, offerInt, rest⟩ := enters
        rw [gegenHw_ander (by omega : u + 2 ≠ 0) (by omega : u + 2 ≠ 1)] at offerInt
        cases offerInt
      | absturz crash =>
        have noCrash : (gegenHw.angebot (u + 2)).crash = false := by
          rw [gegenHw_ander (by omega : u + 2 ≠ 0) (by omega : u + 2 ≠ 1)]
          rfl
        exact Bool.false_ne_true (noCrash.symm.trans crash.1.2)
  let zeit : Zeitlauf (Lauffolge gegenEinheit gegenHw) :=
    { zustand
        | 0 => z0
        | 1 => z1
        | _ + 2 => z2
      spur
        | 0 => some (.kontext kontext (), ⟨[], []⟩)
        | 1 => some (.absturz, absturzSpur)
        | _ + 2 => none
      takt
        | 0 => .schritt rfl step0
        | 1 => .schritt rfl step1
        | u + 2 => .wartet rfl rfl (still u) }
  let ρ : Lauf gegenEinheit := ⟨s, gegenHw, zeit⟩
  refine ⟨ρ, ?_, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨erlaubt [], gegenHw_konform, zul, rfl⟩

private theorem gegen_widerspruch (duty : DurchlaufProtokollPflicht gegenEinheit) : False := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, lauf, cut0, cut1, cut2, spur0, spur1⟩ := gegen_konkreter_lauf s zul
  let z0 := startZustand s
  let z1 := binde z0
  let z2 := zustand2Gegen s
  have hyp1 : DurchlaufPrefix gegenEinheit ρ 1 := by
    intro t' s' hle' sEq' c m hmem
    have faelle : t' = 0 ∨ t' = 1 := by omega
    rcases faelle with rfl | rfl
    · have eqs : s' = z0 := Option.some.inj (sEq'.symm.trans cut0)
      subst s'
      rw [stand_start_leer s zul c] at hmem
      exact (List.not_mem_nil hmem).elim
    · have eqs : s' = z1 := Option.some.inj (sEq'.symm.trans cut1)
      subst s'
      rw [stand_binde_leer s c] at hmem
      exact (List.not_mem_nil hmem).elim
  have prefix2 : DurchlaufPrefix gegenEinheit ρ (1 + 1) :=
    duty lauf 1 .absturz absturzSpur z1 (some z2) hyp1 cut1 spur1 trivial cut2
  have hmem : (0, 0) ∈ gegenEinheit.schranken.durchlaufstand (z2.lokal kontext) := by
    change (0, 0) ∈ markenGegen (some griff2)
    simp only [markenGegen, if_pos rfl]
    exact List.mem_cons_self
  have bound := prefix2 2 z2 (by omega) cut2 kontext (0, 0) hmem
  have f0 : (match ρ.zeit.spur 0 with
      | some (.kontext d _, _) => decide (kontext = d)
      | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false) = true := by
    rw [spur0]
    rfl
  have f1 : (match ρ.zeit.spur 1 with
      | some (.kontext d _, _) => decide (kontext = d)
      | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false) = false := by
    rw [spur1]
  have cost : Kontextkosten ρ kontext 0 2 = 1 := by
    simp only [Kontextkosten, I.zaehle, Nat.zero_add]
    rw [spur0, spur1]
    simp only [decide_eq_true_eq, Bool.false_eq_true, if_true, if_false,
      Nat.add_zero, Nat.zero_add]
  have bound' : 1 ≤ 0 := by
    have b := bound 0 rfl
    simpa only [Nat.sub_zero, cost] using b
  omega

/-- The unrestricted protocol duty is false: a loader whose recovery data opens a back-dated
    mark breaks the bound at the crash cut. The missing premise is `ProtokollMarkenErhaltend`. -/
theorem durchlaufProtokoll_allgemein_falsch :
    ¬ (∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
      (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form), DurchlaufProtokollPflicht E) := by
  intro all
  exact gegen_widerspruch (all Unit Unit Unit Unit (Option Handle) Unit Unit Unit Unit gegenEinheit)

/-- **Per-pass duties of units and loaders, in one pinned statement** (MK-12a follow-up): the
    start duty holds for every unit; the protocol duty holds under the mark-stand premise; and
    the unrestricted protocol duty is false. The last conjunct records the finding that the
    premise cannot be dropped. -/
def DurchlaufEinheitAussage : Prop :=
  (∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form),
    DurchlaufStartPflicht E) ∧
  (∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form),
    ProtokollMarkenErhaltend E → DurchlaufProtokollPflicht E) ∧
  ¬ (∀ (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form),
    DurchlaufProtokollPflicht E)

theorem durchlaufEinheit : DurchlaufEinheitAussage := by
  refine ⟨?_, ?_, ?_⟩
  · intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E
    exact durchlaufStart
  · intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E marken
    exact durchlaufProtokoll marken
  · exact durchlaufProtokoll_allgemein_falsch

/-- Joint satisfiability: the hosted unit with its concrete run has no open marks, so both
    duties hold and the mark-stand premise is vacuous. -/
theorem durchlaufEinheit_erfuellbar :
    ∃ (E : Modell) (h : Umgebung) (ρ : Lauf E),
      Laeufe E h ρ ∧ DurchlaufStartPflicht E ∧ DurchlaufProtokollPflicht E := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, g, g', lauf, _, _, _, _, _, _, _, _, _, _⟩ := konkreter_lauf zul []
  refine ⟨einheit, umgebung [], ρ, lauf, durchlaufStart, ?_⟩
  apply durchlaufProtokoll
  intro h' ρ' t w spur vor nach lauf' vorEq spurEq wahl nachEq c m hmem
  have leer : einheit.schranken.durchlaufstand (nach.lokal c) = [] := rfl
  rw [leer] at hmem
  exact (List.not_mem_nil hmem).elim

/-- The premise is not vacuous and the refutation is real: an admitted run of the counter-unit
    fails its protocol duty at the crash cut. -/
theorem durchlaufEinheit_nichtTrivial :
    ∃ (E : Modell) (h : Umgebung) (ρ : Lauf E),
      Laeufe E h ρ ∧ ¬ DurchlaufProtokollPflicht E := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, lauf, _, _, _, _, _⟩ := gegen_konkreter_lauf s zul
  refine ⟨gegenEinheit, umgebung [], ρ, lauf, ?_⟩
  exact gegen_widerspruch

end Gabbro.Core.Beobachtung
