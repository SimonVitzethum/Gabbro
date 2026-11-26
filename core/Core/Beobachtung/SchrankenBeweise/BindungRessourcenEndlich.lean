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
import Core.Ziel.Korrektheit.Beweise.BegleitMaschine

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
  let gebunden : Lauf E := ⟨ρ.start, ρ.hw, ρ.zeit⟩
  have gebundenerLauf : Laeufe E H gebunden := lauf
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
  let P := Plattform.x86_64
  let u : UnitMitSchranken := ⟨trivialUnit, { speicher := some 0 }⟩
  have akzeptiert : Annahme.Akzeptiert (einheitVon P u.baum) := by
    unfold einheitVon elaborieren
    apply Fragment.akzeptiert_ohne_bedarf
    · rfl
    · intro b present
      change b ∈ ([Befehl.starte mainName, Befehl.ende] : List Befehl) at present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
    · intro b present frame
      change b ∈ ([Befehl.starte mainName, Befehl.ende] : List Befehl) at present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> rfl
  obtain ⟨H, start, hw, zul, _, fair, z, geladen, _⟩ := trivial_start_bereit
  obtain ⟨ρ, lauf, startEq, _⟩ := fairer_lauf (einheitVon P u.baum) zul fair
  refine ⟨P, u, H, ρ, rfl, rfl, akzeptiert, lauf, ⟨z, ?_⟩,
    bindungSpeicher_quelllauf P u rfl rfl lauf⟩
  rw [lauf.2.2.2, startEq]
  exact geladen

end Gabbro.Core.Beobachtung
