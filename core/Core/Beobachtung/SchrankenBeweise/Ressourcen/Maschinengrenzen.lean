module

public import Core.Beobachtung.SchrankenBeweise.Ressourcen.Stapelgrenze
public import Core.Beobachtung.SchrankenBeweise.Ressourcen.Startbuchung
import Core.Beobachtung.Fluss.Fragment
import Core.Sicherheit.Laufkonstruktion

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Befehl Rahmen Schrittform Zelle)

/-- The bounded machine uses the existing class rules with a bounded frame transfer, charges
    the actual initial grants at load, and explicitly clears volatile continuations at restart.
    Its implementation-side loader has an exact byte charge. The ideal start connection requires
    a shared initial booking, since the current `I.start` always creates an empty one. -/
def einheitMitRessourcenschutz (P : Plattform) (u : UnitMitSchranken) : Ast.Semantik.Einheit :=
  let E := einheitMitSchranken P u
  let w := E.einrichtung.wiederanlauf
  { E with
    system := { E.system with
      regel := fun b => (b.form.mitStapelgrenze E.schranken.stapel).regel }
    einrichtung := { E.einrichtung with
      wiederanlauf := { w with
        verwerfen := fun r => { w.verwerfen r with fortsetzungen := [] } } }
    laden := fun a p => (ladeStartbuchung P u a p).toOption }

private theorem ressourcenschutz_laden {P : Plattform} {u : UnitMitSchranken}
    {a : AussenStart} {p : Ladung} {s : Ast.Semantik.Zustand}
    (geladen : (einheitMitRessourcenschutz P u).laden a p = some s) :
    ladeStartbuchung P u a p = .ok s := by
  change (ladeStartbuchung P u a p).toOption = some s at geladen
  cases h : ladeStartbuchung P u a p with
  | error e =>
    rw [h] at geladen
    cases geladen
  | ok s' =>
    rw [h] at geladen
    have hs : s' = s := Option.some.inj geladen
    subst s'
    first | exact h | rfl

/-- The implementation loader publishes no start state after a named full-region refusal. -/
theorem ressourcenschutz_regionVoll (P : Plattform) (u : UnitMitSchranken) (a : AussenStart)
    (p : Ladung) {n : Nat} {s : Ast.Semantik.Zustand}
    (bild : (einheitMitSchranken P u).laden a p = some s)
    (grenze : u.deklaration.speicher = some n) (voll : n < handoffByteFootprint a.regions) :
    (einheitMitRessourcenschutz P u).laden a p = none := by
  change (ladeStartbuchung P u a p).toOption = none
  simp only [ladeStartbuchung_regionVoll P u a p bild grenze voll, Except.toOption]

/-- The load cut of a concrete run carries the complete canonical charge of the grants. -/
theorem ressourcenschutz_start_bytes (P : Plattform) (u : UnitMitSchranken)
    {h : Umgebung} {ρ : Lauf (einheitMitRessourcenschutz P u)} (lauf : Laeufe _ h ρ)
    {s : Ast.Semantik.Zustand} (schnitt : ρ.zeit.zustand 0 = some s) :
    (LebendeZellen s).encard = handoffByteFootprint ρ.start.regions := by
  have geladen : (einheitMitRessourcenschutz P u).laden ρ.start
      (h.lade (einheitMitRessourcenschutz P u).bild) = some s := lauf.2.2.2.symm.trans schnitt
  obtain ⟨_, _, _, count, _⟩ := ladeStartbuchung_erfolg P u ρ.start _ (ressourcenschutz_laden geladen)
  exact count

theorem ressourcenschutz_start (P : Plattform) (u : UnitMitSchranken) :
    ressourcenStartAussage (einheitMitRessourcenschutz P u) := by
  apply ressourcenStart_unterLade
  intro a p s geladen
  obtain ⟨roh, bild, lokal, count, passt⟩ :=
    ladeStartbuchung_erfolg P u a p (ressourcenschutz_laden geladen)
  refine ⟨?_, ?_⟩
  · intro c n grenze
    change u.deklaration.stapel = some n at grenze
    change (s.lokal c).fortsetzungen.length ≤ n
    rw [lokal]
    exact (bindungLadeSchranken P u a p bild).1 c n grenze
  · intro n grenze
    change u.deklaration.speicher = some n at grenze
    rw [count]
    exact ENat.natCast_le_natCast.mpr (passt n grenze)

theorem ressourcenschutz_regel (P : Plattform) (u : UnitMitSchranken) (b : Befehl) :
    ressourcenRegelAussage (einheitMitRessourcenschutz P u) b := by
  intro h ρ lauf t c w spur vor nach vorEq kopf spurEq nachEq step stapelVor speicherVor
  cases step with
  | kontext _ _ regel aus =>
    obtain ⟨i, kopfI, regelI⟩ := regel
    have gleich : i = b := Option.some.inj (kopfI.symm.trans kopf)
    subst i
    let E := einheitMitRessourcenschutz P u
    let F := b.form.mitStapelgrenze E.schranken.stapel
    have rule : F.ideal c vor w [_] _ := regelI
    exact ⟨Ast.Semantik.klassenSchrankenStapel E F
      (Schrittform.mitStapelgrenze_stapel E b.form) (fun _ => rfl) c vor nach w _ spur rule aus stapelVor,
      Ast.Semantik.klassenSchrankenSpeicher E F c vor nach w _ spur rule aus speicherVor⟩

/-- The same checked transfer supplies the per-form ideal checker row. -/
theorem ressourcenschutz_regelSchranken (P : Plattform) (u : UnitMitSchranken) (b : Befehl) :
    Annahme.RegelSchranken (einheitMitRessourcenschutz P u) b := by
  let E := einheitMitRessourcenschutz P u
  let F := b.form.mitStapelgrenze E.schranken.stapel
  exact Ast.Semantik.klassenSchranken F.klasse Befehl E b F rfl
    ⟨rfl, rfl, rfl⟩ (Schrittform.mitStapelgrenze_stapel E b.form) (fun _ => rfl)

/-- Crash recovery discards the continuation stack and uses the existing empty restart
    booking. Replies and interrupts preserve both resources through the shared protocol. -/
theorem ressourcenschutz_protokoll (P : Plattform) (u : UnitMitSchranken) :
    ressourcenProtokollAussage (einheitMitRessourcenschutz P u) := by
  apply ressourcenProtokoll_unterWiederanlauf
  intro t s p c
  refine ⟨fun _ _ => Nat.zero_le _, ?_⟩
  intro z hz
  have hlt := hz.2
  change z.2 < 0 at hlt
  exact Nat.not_lt_zero _ hlt

theorem ressourcenschutz (P : Plattform) (u : UnitMitSchranken) :
    RessourcenPflichten (einheitMitRessourcenschutz P u) :=
  ⟨ressourcenschutz_start P u, ressourcenschutz_regel P u, ressourcenschutz_protokoll P u⟩

/-- An implementation run with a positive booked grant cannot match the current ideal start.
    The protocol relation fixes both liveness and the complete booking extent. -/
theorem ressourcenschutz_start_bezug_unmoeglich (P : Plattform) (u : UnitMitSchranken)
    {h : Umgebung} {ρ : Lauf (einheitMitRessourcenschutz P u)} (lauf : Laeufe _ h ρ)
    {s : Ast.Semantik.Zustand} (schnitt : ρ.zeit.zustand 0 = some s)
    (bytes : 0 < handoffByteFootprint ρ.start.regions) :
    ¬ I.ProtokollBezug s (I.start (einheitMitRessourcenschutz P u) ρ.start).2 := by
  intro bezug
  let ideal := (I.start (einheitMitRessourcenschutz P u) ρ.start).2
  have eq : { s with lokal := ideal.lokal } = ideal := bezug
  have extent : s.buchung.umfang = ideal.buchung.umfang :=
    congrArg (fun z => z.buchung.umfang) eq
  have empty : LebendeZellen s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z mem
    have hlt := mem.2
    rw [extent] at hlt
    change z.2 < 0 at hlt
    exact Nat.not_lt_zero _ hlt
  have count := ressourcenschutz_start_bytes P u lauf schnitt
  rw [empty, Set.encard_empty] at count
  have zero : 0 = handoffByteFootprint ρ.start.regions := congrArg ENat.toNat count
  exact (Nat.ne_of_lt bytes) zero

/-- Both finite ceilings hold on a run that loads a positive grant. This run also exercises
    the initial-state mismatch with the current ideal machine. -/
theorem ressourcenschutz_erfuellbar (baum : Ast.Unit) :
    let u : UnitMitSchranken := ⟨baum, { stapel := some 1, speicher := some 1 }⟩
    let E := einheitMitRessourcenschutz .x86_64 u
    ∃ (h : Umgebung) (ρ : Lauf E) (s : Ast.Semantik.Zustand),
      Laeufe E h ρ ∧ ρ.zeit.zustand 0 = some s ∧ (LebendeZellen s).encard = 1 ∧
      (∀ t, RessourcenPrefix E ρ t) ∧ ¬ I.ProtokollBezug s (I.start E ρ.start).2 := by
  intro u E
  let h := Sicherheit.Laufkonstruktion.umgebung Sicherheit.Laufkonstruktion.leer
  have hardware : Hardware E.katalog h := Sicherheit.Laufkonstruktion.erlaubt _
  have imageOk : E.bild.gueltig E.katalog.plattform.ziel := Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨empty, image, core, assigned, fits, _, _, _, outside⟩ := zulStart_erfuellbar hardware imageOk
  let a : AussenStart := { empty with regions := [⟨0, 1⟩], inputBytes := fun _ => none }
  have startOk : E.ZulStart h a := by
    refine ⟨image, core, assigned, fits, List.pairwise_singleton _ _, ?_,
      (fun _ _ impossible => nomatch impossible), outside⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨Nat.zero_lt_one, ?_, ?_⟩
    · change 1 ≤ 2 ^ (52 : Nat)
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · intro endpoint device selected mmio
      cases endpoint <;> cases selected
      · cases mmio
      · exact Or.inl (by change 1 ≤ 0x10000000; omega)
  have roh := fragment_geladen (Ast.Semantik.programm baum) .x86_64 hardware startOk
  obtain ⟨ρ, lauf, startEq⟩ := lauf_ab_start E hardware startOk
  let s0 := (I.start ((Ast.Semantik.programm baum).einheit .x86_64) a).2
  let s : Ast.Semantik.Zustand := { s0 with buchung := handoffBooking 1 a.regions s0.buchung }
  have cap : u.deklaration.speicher = some 1 := rfl
  have charge : handoffByteFootprint a.regions = 1 := rfl
  have preloaded : (einheitMitSchranken .x86_64 u).laden a
      (h.lade (einheitMitSchranken .x86_64 u).bild) = some s0 := roh
  have geladen : E.laden a (h.lade E.bild) = some s := by
    change (ladeStartbuchung .x86_64 u a
      (h.lade (einheitMitSchranken .x86_64 u).bild)).toOption = some s
    simp only [ladeStartbuchung, preloaded, cap, charge, Option.any,
      decide_eq_false (Nat.lt_irrefl 1), Bool.false_eq_true, if_false, Except.toOption, s]
  have schnitt : ρ.zeit.zustand 0 = some s := lauf.2.2.2.trans (startEq.symm ▸ geladen)
  have bytes : 0 < handoffByteFootprint ρ.start.regions := by
    rw [startEq, charge] <;> exact Nat.zero_lt_one
  have count := ressourcenschutz_start_bytes .x86_64 u lauf schnitt
  rw [startEq, charge] at count
  exact ⟨h, ρ, s, lauf, schnitt, count, b9_b21_aus_pflichten (ressourcenschutz .x86_64 u) lauf,
    ressourcenschutz_start_bezug_unmoeglich .x86_64 u lauf schnitt bytes⟩

end Gabbro.Core.Beobachtung
