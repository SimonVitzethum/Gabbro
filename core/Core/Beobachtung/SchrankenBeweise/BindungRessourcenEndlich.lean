/-
  File:      core/Core/Beobachtung/SchrankenBeweise/BindungRessourcenEndlich.lean
  Subject:   THE RESOURCE PROTOCOL DUTY OF BOUND UNITS (M9, MK-12). The bare
              `ressourcenProtokollAussage` is false: a crash can install recovery
              data outside the declared bounds. Its missing premise is the
              recovery start-data discipline (`ressourcenProtokoll_unterWiederanlauf`).
              For bound units the premise holds unconditionally: the elaborated
              restart data is the loader start data with the identity clearing,
              so the cleared entry has depth zero and the durable booking is
              empty. This closes the protocol resource family of
              `SchrankenbindungOffenAussage` over bound units. The per-form
              family still needs the class footprints, and the checker row the
              simulation match; both stay open findings.
-/
module

public import Core.Beobachtung.SchrankenBeweise.RessourcenEinheit
public import Core.Beobachtung.SchrankenBeweise.Bindung
public import Core.Beobachtung.SchrankenBeweise.BindungRessourcen
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Schranken
public import Core.Ziel.Korrektheit.Pruefer
import Core.Ziel.Korrektheit.Beweise.BegleitVerfeinerung
import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The elaborated restart data clears nothing: entry data keeps its frame. -/
theorem einrichtung_verwerfen_id (scope : Scope) (eintritte : Kontext → Option Nat)
    (plan : Speicherplan) (r : Rahmen) :
    (einrichtung scope eintritte plan).wiederanlauf.verwerfen r = r :=
  rfl

/-- The elaborated restart entry starts with an empty continuation stack. -/
theorem einrichtung_daten_tiefe (scope : Scope) (eintritte : Kontext → Option Nat)
    (plan : Speicherplan) (m : Nat → UInt8) (c : Kontext) :
    (((einrichtung scope eintritte plan).wiederanlauf.daten m).lokal c).fortsetzungen.length =
      0 :=
  rfl

/-- The booking after a crash reset is empty, whatever the pre-state and the
    installed rights are: the reset builds a start state, whose booking
    defaults to empty. -/
theorem wiederanlauf_umfang_leer {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    {w : Wiederanlauf Zelle Int Nat Rahmen PUnit} {t : Nat} {p : PersistZustand}
    {r : Rechte} {i : Nat} :
    ({ s.wiederanlauf w t p with rechte := r } : Zustand Nat Zelle Int Nat Rahmen PUnit).buchung.umfang
        i =
      [] :=
  rfl

/-- The resource protocol duty of every bound unit: answers and interrupts keep
    both bounds by the generic preservation facts, and the crash case meets the
    recovery start-data discipline because the cleared entry has depth zero
    and books nothing. -/
theorem bindungRessourcenProtokoll_endlich (P : Katalog.Plattform)
    (u : UnitMitSchranken) :
    ressourcenProtokollAussage (einheitMitSchranken P u) := by
  apply ressourcenProtokoll_unterWiederanlauf
  intro t s p c
  have hverw : ∀ r : Rahmen,
      (einheitMitSchranken P u).einrichtung.wiederanlauf.verwerfen r = r :=
    fun r => einrichtung_verwerfen_id _ _ _ r
  have htiefe : ∀ (m : Nat → UInt8) (d : Kontext),
      (((einheitMitSchranken P u).einrichtung.wiederanlauf.daten m).lokal d).fortsetzungen.length =
        0 :=
    fun m d => einrichtung_daten_tiefe _ _ _ m d
  refine ⟨?_, ?_⟩
  · rw [einheitMitSchranken_tiefe, hverw _, htiefe _ _]
    exact fun _ _ => Nat.zero_le _
  · intro z hz
    simp only [LebendeZellen, Set.mem_setOf_eq] at hz
    obtain ⟨_, hlen⟩ := hz
    have humfang : ({ s.wiederanlauf (einheitMitSchranken P u).einrichtung.wiederanlauf t p
      with rechte :=
        ((einheitMitSchranken P u).einrichtung.wiederanlauf.daten p.dauerhaft).rechte } :
      Zustand Nat Zelle Int Nat Rahmen PUnit).buchung.umfang z.1 = [] :=
      wiederanlauf_umfang_leer
    rw [humfang, List.length_nil] at hlen
    exact Nat.not_lt_zero _ hlen


/-- A concrete context step preserves the memory ceiling by the selected class's form relation
    and its completed action. With the stack ceiling open this closes the instruction duty. -/
theorem bindungRessourcenRegel_ohneStapel (P : Plattform) (u : UnitMitSchranken)
    (offen : u.deklaration.stapel = none) (b : Befehl) :
    ressourcenRegelAussage (einheitMitSchranken P u) b := by
  intro h ρ lauf t c w spur vor nach vorEq kopf spurEq nachEq step stapelVor speicherVor
  cases step with
  | kontext _ _ regel aus =>
    obtain ⟨i, kopfI, regelI⟩ := regel
    have gleich : i = b := Option.some.inj (kopfI.symm.trans kopf)
    subst i
    refine ⟨?_, klassenSchrankenSpeicher (einheitMitSchranken P u) b.form
      c vor nach w _ spur regelI aus speicherVor⟩
    intro d n hn
    rw [einheitMitSchranken_stapel, offen] at hn
    cases hn

open Gabbro.Core.Ziel.Korrektheit

/-- The public source elaborator installs an open memory ceiling for every tree.
    The finite ceiling comes from the adjacent declaration in `UnitMitSchranken`. -/
theorem einheitVon_speicher_offen (P : Plattform) (t : Ast.Unit) :
    (einheitVon P t).schranken.speicher = none := rfl

/-- A finite side declaration bounds the live allocation cells of the original source run.
    Both elaborations share the execution and load relations. -/
theorem bindungSpeicher_quelllauf (P : Plattform) (u : UnitMitSchranken)
    (offen : u.deklaration.stapel = none)
    {n : Nat} (grenze : u.deklaration.speicher = some n)
    {H : Umgebung} {ρ : Lauf (einheitVon P u.baum)}
    (lauf : Laeufe (einheitVon P u.baum) H ρ) :
    ∀ t s, ρ.zeit.zustand t = some s → (LebendeZellen s).encard ≤ n := by
  let E := einheitMitSchranken P u
  have folge {hw t vor spur nach} :
      Lauffolge (einheitVon P u.baum) hw t vor spur nach ↔ Lauffolge E hw t vor spur nach := by
    constructor <;> intro schritt <;> cases schritt with
    | schritt step => exact .schritt step
  let gebunden : Lauf E := ⟨ρ.start, ρ.hw, ⟨ρ.zeit.zustand, ρ.zeit.spur, fun t => by
    cases ρ.zeit.takt t with
    | schritt label step => exact .schritt label (folge.mp step)
    | wartet label gleich ruhe =>
      exact .wartet label gleich (fun spur nach step => ruhe spur nach (folge.mpr step))⟩⟩
  have gebundenerLauf : Laeufe E H gebunden := ⟨lauf.1, lauf.2.1, lauf.2.2.1, lauf.2.2.2⟩
  have pflichten : RessourcenPflichten E :=
    ⟨bindungRessourcenStart P u, bindungRessourcenRegel_ohneStapel P u offen,
      bindungRessourcenProtokoll_endlich P u⟩
  intro t s schnitt
  exact (b9_b21_aus_pflichten pflichten gebundenerLauf t s schnitt).2 n grenze

/-- The zero ceiling, acceptance of the source tree, and an admitted run with a successful
    load hold jointly. -/
theorem bindungSpeicher_quelllauf_erfuellbar :
    ∃ (P : Plattform) (u : UnitMitSchranken) (H : Umgebung)
      (ρ : Lauf (einheitVon P u.baum)),
      u.deklaration.stapel = none ∧ u.deklaration.speicher = some 0 ∧
      Annahme.Akzeptiert (einheitVon P u.baum) ∧ Laeufe (einheitVon P u.baum) H ρ ∧
      (∃ s, ρ.zeit.zustand 0 = some s) ∧
      ∀ t s, ρ.zeit.zustand t = some s → (LebendeZellen s).encard ≤ 0 := by
  obtain ⟨P, t, H, ρ, akzeptiert, lauf⟩ := VerfeinerungAkzeptiertAussage.erfuellbar
  let u : UnitMitSchranken := ⟨t, { speicher := some 0 }⟩
  have geladen := fragment_geladen (fragment .unit t) P lauf.1 lauf.2.2.1
  exact ⟨P, u, H, ρ, rfl, rfl, akzeptiert, lauf, ⟨_, lauf.2.2.2.trans geladen⟩,
    bindungSpeicher_quelllauf P u rfl rfl lauf⟩

/-- The loader of the source elaboration books no cell: its loaded state has an empty live
    set, independently of any declared ceiling. This is the exact point where the source
    path fails to carry an occupied booking. -/
theorem bindungLadeLeer_quell (P : Plattform) (u : UnitMitSchranken)
    (a : AussenStart) (p : Ladung) {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    (geladen : (einheitVon P u.baum).laden a p = some s) :
    LebendeZellen s = ∅ := by
  change (laden (programm u.baum).eingang (programm u.baum).eintritte
    (programm u.baum).speicher P a p) = some s at geladen
  unfold laden at geladen
  by_cases ok : p.starts 0 = some 0 ∧ p.bytes 0 = some 0
  · rw [if_pos ok] at geladen
    let d := startdaten (programm u.baum).eingang (programm u.baum).eintritte
      (a.assignment 0) P a.regions
    let s0 : Zustand Nat Zelle Int Nat Rahmen PUnit := Zustand.start d.lokal d.status
      d.kerne d.rechte
        (einrichtung (programm u.baum).eingang (programm u.baum).eintritte
          (programm u.baum).speicher).initial (.leer (startmedium a))
    have hs : s = s0 := by
      dsimp only [s0]
      exact (Option.some.inj geladen).symm
    subst s
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z mem
    change s0.rechte.lebt z.1 = true ∧ z.2 < (s0.buchung.umfang z.1).length at mem
    have hleer : s0.buchung.umfang z.1 = [] := rfl
    rw [hleer] at mem
    simp only [List.length_nil] at mem
    exact Nat.not_lt_zero _ mem.2
  · rw [if_neg ok] at geladen
    cases geladen

/-- The precise missing connection: the admitted source run's load cut books no cell, so the
    source elaboration cannot exhibit a positive living-cell count there. The positive booked
    case lives on the checked low-level path (`b21_belegte_buchung_erfuellbar`), which the
    source load does not reach. -/
theorem bindungSpeicher_quell_lade_leer (P : Plattform) (u : UnitMitSchranken)
    {H : Umgebung} {ρ : Lauf (einheitVon P u.baum)}
    (lauf : Laeufe (einheitVon P u.baum) H ρ)
    {s : Zustand Nat Zelle Int Nat Rahmen PUnit} (schnitt : ρ.zeit.zustand 0 = some s) :
    LebendeZellen s = ∅ := by
  have geladen : (einheitVon P u.baum).laden ρ.start (H.lade (einheitVon P u.baum).bild) = some s :=
    lauf.2.2.2.symm.trans schnitt
  exact bindungLadeLeer_quell P u ρ.start (H.lade (einheitVon P u.baum).bild) geladen

end Gabbro.Core.Beobachtung
