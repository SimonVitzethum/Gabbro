module

public import Core.Ziel.Korrektheit.Waechter.WaechterAbstrakt
public import Core.Ziel.Korrektheit.NichtAkzeptierteEinheit
public import Core.Linken.Abgeschottet

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core Gabbro.Core.Ast Gabbro.Core.Ast.Semantik Gabbro.Core.Maschine
open Gabbro.Core.Annahme Gabbro.Core.Katalog

private def eingangCode : List Befehl :=
  [.lesen 2 0, .setzePasszahl 2 0, .literal 0 0, .literal 1 0, .teilen 0]

private def eingangFragment (scope : Scope) : Fragment :=
  ⟨eingangCode, .leer, scope, fun _ => none, .leer, []⟩

private abbrev leererEingang := eingangFragment []
private abbrev belegterEingang := eingangFragment [⟨indexName, .int 0 0, false, true⟩]

/-- Without an incoming integer, setting the pass count halts before the division. -/
private def LeererEingangsrahmen (r : Semantik.Rahmen) : Prop :=
  r.pc ≤ 1 ∧ r.lokale = [] ∧ r.temp 2 = none

private theorem eingangKopf {r : Semantik.Rahmen} {b : Befehl}
    (bound : r.pc ≤ 1) (lookup : eingangCode[r.pc]? = some b) :
    (r.pc = 0 ∧ b = .lesen 2 0) ∨ (r.pc = 1 ∧ b = .setzePasszahl 2 0) := by
  by_cases zero : r.pc = 0
  · rw [zero] at lookup
    exact .inl ⟨zero, (Option.some.inj lookup).symm⟩
  · have one : r.pc = 1 := by omega
    rw [one] at lookup
    exact .inr ⟨one, (Option.some.inj lookup).symm⟩

private theorem leererEingang_halt :
    WaechterHalten (leererEingang.einheit .x86_64) := by
  refine ⟨?_, ?_, Linken.fragment_sperrhalter_halten _ _⟩
  · intro ρ run cut op args use
    obtain ⟨c, b, head, guard⟩ : ∃ c b, kopf eingangCode (ρ.zeit.zustand cut.val) c = some b ∧
        b.guard ((ρ.zeit.zustand cut.val).lokal c) = some ⟨op, args⟩ := use
    have invariant := privatRahmen_lauf leererEingang .x86_64 LeererEingangsrahmen
      ?_ ?_ ρ run cut.val c
    · rcases eingangKopf invariant.1 (Gabbro.Core.Ast.Semantik.kopf_code head) with ⟨_, rfl⟩ | ⟨_, rfl⟩
      all_goals cases guard
    · intro k platform regions d
      refine ⟨?_, rfl, rfl⟩
      change (if d = eintritt then 0 else (none : Option Nat).getD 0) ≤ 1
      split <;> exact Nat.zero_le _
    · intro instr r live lookup _ before
      rcases eingangKopf before.1 lookup with ⟨zero, rfl⟩ | ⟨one, rfl⟩
      · refine ⟨Or.inl rfl, ?_⟩
        simp only [LeererEingangsrahmen, Befehl.auswerten, Rahmen.schreibe,
          before.2.1, Function.update_self, List.getElem?_nil, Option.join, zero]
        exact ⟨Nat.le_refl _, trivial, rfl⟩
      · refine ⟨Or.inl rfl, ?_⟩
        have empty : r.zahl 2 = none := by
          simp only [Rahmen.zahl, before.2.2, Option.bind_none]
        simp only [Befehl.auswerten, empty, LeererEingangsrahmen, Rahmen.halt]
        exact before
  · intro ρ run cut
    exact fun ⟨C, closed⟩ =>
      Linken.fragment_geschlossen_wartend_leer leererEingang .x86_64 _ C closed

private def eingangZustand (start : AussenStart) (t : Nat) : Semantik.Zustand :=
  (eingangCode.take t).foldl (fun s b => b.nach eintritt s)
    (I.start (belegterEingang.einheit .x86_64) start).2

private theorem belegterEingang_guardVersagt :
    ¬ WaechterHalten (belegterEingang.einheit .x86_64) := by
  intro holds
  let E := belegterEingang.einheit .x86_64
  obtain ⟨ambient, _, hardware, _⟩ :=
    katalog_nichtLeer E.katalog (Plattform.katalog_wohlgeformt .x86_64)
  have image : E.bild.gueltig E.katalog.plattform.ziel :=
    Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨start, legal⟩ := zulStart_erfuellbar hardware image
  obtain ⟨k, assigned⟩ := legal.2.2.1 0 (Nat.zero_lt_succ _)
  let hw := txtHw ambient k
  have conform : hw.konform E.katalog ambient :=
    txt_konformHw ambient start legal k assigned
  obtain ⟨time, init⟩ := Zeitlauf.existiert
    (I.Schritt E.einrichtung E.system E.katalog hw) (I.start E start).2
  have pause (t s) (_ : KeinSchritt (I.Schritt E.einrichtung E.system E.katalog hw) t s) :
      ¬ AbsturzAngeboten E.katalog hw t :=
    fun offer => Bool.false_ne_true offer.2
  let ρ : I.Lauf E := ⟨start, ambient, hw, time.erlaubePausen pause, fun _ => none⟩
  have run : I.Laeufe E ρ :=
    ⟨hardware, conform, legal, init, time.erlaubePausen_maximal pause _ (fun _ => rfl),
      fun _ _ h => nomatch h⟩
  let Agrees (t : Nat) :=
    let s := eingangZustand start t
    (ρ.zeit.zustand t).lokal = s.lokal ∧ (ρ.zeit.zustand t).status = s.status ∧
    (ρ.zeit.zustand t).kerne = s.kerne ∧ (ρ.zeit.zustand t).fragen = [] ∧
    Zustand.regionLive (ρ.zeit.zustand t) = Zustand.regionLive s
  have base : Agrees 0 := by
    dsimp only [Agrees]
    rw [run.2.2.2.1]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have advance (t : Nat) (b : Befehl) (agree : Agrees t)
      (head : kopf eingangCode (eingangZustand start t) eintritt = some b)
      (internal : b.klasse = .lokal)
      (status : (eingangZustand start t).status = (I.start E start).2.status)
      (cores : (eingangZustand start t).kerne = (I.start E start).2.kerne)
      (noRequests : (eingangZustand start t).fragen = [])
      (next : eingangZustand start (t + 1) = b.nach eintritt (eingangZustand start t)) :
      (∃ ev, ρ.zeit.spur t = some ev) ∧ Agrees (t + 1) := by
    obtain ⟨localEq, statusEq, coresEq, requestsEq, regionsEq⟩ := agree
    have ready : KannSchreiten ρ.hw t eintritt (eingangZustand start t) := by
      refine ⟨k, rfl, ?_, ?_⟩
      · rw [cores]
        exact txt_dispatch start k assigned
      · rw [status]
        rfl
    have asleep : ∀ d, d ≠ eintritt → (eingangZustand start t).status d = .ruht := by
      intro d other
      rw [status]
      exact txt_status_other start d other
    have forced := fragmentForceStep belegterEingang .x86_64 ρ run t k b (eingangZustand start t)
      rfl rfl rfl (fun _ => rfl) rfl rfl localEq statusEq coresEq
      (requestsEq.trans noRequests.symm) regionsEq head (.inl internal) ready asleep noRequests
    simpa only [Agrees, next] using forced
  have s1 := (advance 0 (.lesen 2 0) base rfl rfl rfl rfl rfl rfl).2
  have s2 := (advance 1 (.setzePasszahl 2 0) s1 rfl rfl rfl rfl rfl rfl).2
  have s3 := (advance 2 (.literal 0 0) s2 rfl rfl rfl rfl rfl rfl).2
  obtain ⟨⟨ev, step⟩, s4⟩ := advance 3 (.literal 1 0) s3 rfl rfl rfl rfl rfl rfl
  let cut : I.Schnitt E ρ := ⟨4, .inr ⟨3, ev, rfl, step⟩⟩
  have head : kopf eingangCode (ρ.zeit.zustand 4) eintritt = some (.teilen 0) := by
    rw [kopf_kontextgleich (congrFun s4.2.1 eintritt) (congrFun s4.1 eintritt)]
    rfl
  have demand : (Befehl.teilen 0).guard ((ρ.zeit.zustand 4).lokal eintritt) =
      some ⟨.division, (0, 0)⟩ := by
    rw [congrFun s4.1 eintritt]
    rfl
  have impossible := holds.1 ρ run cut .division (0, 0) ⟨eintritt, .teilen 0, head, demand⟩
  exact impossible rfl

/-- The existing fragment accepts the same instruction sequence for two entrance scopes with
    opposite guard validity. A verdict that depends on code alone cannot decide both. -/
theorem waechterCode_keinEntscheider (verdict : List Befehl → Bool)
    (sound : ∀ (p : Fragment) (platform : Plattform),
      verdict p.code = true → WaechterHalten (p.einheit platform)) :
    ¬ (∀ (p : Fragment) (platform : Plattform),
      waechterFragmentCode p.code = true → WaechterHalten (p.einheit platform) →
        verdict p.code = true) := by
  intro complete
  have checked : verdict eingangCode = true :=
    complete leererEingang .x86_64 rfl leererEingang_halt
  exact belegterEingang_guardVersagt (sound belegterEingang .x86_64 checked)

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
