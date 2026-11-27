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

private theorem quellladen_startzustand (P : Plattform) (u : UnitMitSchranken)
    (a : AussenStart) (p : Ladung) {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    (geladen : (einheitVon P u.baum).laden a p = some s) :
    let d := startdaten (programm u.baum).eingang (programm u.baum).eintritte
      (a.assignment 0) P a.regions
    s = Zustand.start d.lokal d.status d.kerne d.rechte
      (einrichtung (programm u.baum).eingang (programm u.baum).eintritte
        (programm u.baum).speicher).initial (.leer (startmedium a)) := by
  change (laden (programm u.baum).eingang (programm u.baum).eintritte
    (programm u.baum).speicher P a p) = some s at geladen
  unfold laden at geladen
  split at geladen
  · exact (Option.some.inj geladen).symm
  · cases geladen

/-- A source load starts with an empty ledger. -/
theorem laden_buchung_umfang_leer (P : Plattform) (u : UnitMitSchranken)
    (a : AussenStart) (p : Ladung) {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    (geladen : (einheitVon P u.baum).laden a p = some s) :
    s.buchung.umfang = fun _ => [] :=
  congrArg (fun z => z.buchung.umfang) (quellladen_startzustand P u a p geladen)

/-- A successfully loaded ordinary source unit has no live booked cells. -/
theorem bindungLadeLeer_quell (P : Plattform) (u : UnitMitSchranken)
    (a : AussenStart) (p : Ladung) {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    (geladen : (einheitVon P u.baum).laden a p = some s) :
    LebendeZellen s = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z mem
  have hlt : z.2 < (s.buchung.umfang z.1).length := mem.2
  rw [laden_buchung_umfang_leer P u a p geladen] at hlt
  exact Nat.not_lt_zero _ hlt

/-- The precise missing connection: the admitted source run's load cut books no cell, so the
    source elaboration cannot exhibit a positive living-cell count there. The positive booked
    case lives on the hosted machine model (`b21_belegte_buchung_erfuellbar`), which the
    source load does not reach. -/
theorem bindungSpeicher_quell_lade_leer (P : Plattform) (u : UnitMitSchranken)
    {H : Umgebung} {ρ : Lauf (einheitVon P u.baum)}
    (lauf : Laeufe (einheitVon P u.baum) H ρ)
    {s : Zustand Nat Zelle Int Nat Rahmen PUnit} (schnitt : ρ.zeit.zustand 0 = some s) :
    LebendeZellen s = ∅ := by
  have geladen : (einheitVon P u.baum).laden ρ.start (H.lade (einheitVon P u.baum).bild) = some s :=
    lauf.2.2.2.symm.trans schnitt
  exact bindungLadeLeer_quell P u ρ.start (H.lade (einheitVon P u.baum).bild) geladen

/- BLOCKER OF THE DIRECT LOADER CONNECTION. The boundary admits regions (`AussenStart.regions`,
   checked by `ZulStart`: pairwise disjoint, valid extents) and `startdaten` turns their number
   into `rechte.lebt i = decide (i < regions.length)`. `Rahmen.bindeRegion` reads that live flag
   and the extent, but only writes a value into the frame; it never touches the ledger. The
   loader builds the state with `Zustand.start`, whose `buchung` defaults to `Buchung.leer`.
   So a granted region slot is live as a right and absent from `buchung.umfang`. The missing
   operation is an addition to the existing booking; `bucheZellen` below supplies it generically. -/

/-- The checked data of an actually loaded existing region: slot `i` lives (the loader read it
    from `regions.length`) but the ledger still books nothing for it. This is the precise point
    at which the region's checked specification fails to reach the bounded ledger. -/
theorem geladeneRegion_lebt_leer (P : Plattform) (u : UnitMitSchranken)
    (a : AussenStart) (p : Ladung) {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    (geladen : (einheitVon P u.baum).laden a p = some s)
    (i : Nat) (hi : i < a.regions.length) :
    s.rechte.lebt i = true ∧ s.buchung.umfang i = [] := by
  refine ⟨?_, congrFun (laden_buchung_umfang_leer P u a p geladen) i⟩
  rw [quellladen_startzustand P u a p geladen]
  exact decide_eq_true hi

/- GENERIC LEDGER CONNECTION. All statements below quantify over an arbitrary state, object and
   list of new cells; none runs a program. A live object is exactly what a checked loaded region
   supplies (`geladeneRegion_lebt_leer`). Adding cells to its existing booking is the operation
   the loader omits, and these lemmas are the reusable foundation for attaching it later. -/

variable {L Ort Wert Raum Lok Grund : Type}

/-- The booking after adding `neu` cells to object `o`; every other object keeps its extent. -/
def bucheZellen (s : Zustand L Ort Wert Raum Lok Grund) (o : Nat) (neu : List Ort) :
    Zustand L Ort Wert Raum Lok Grund :=
  { s with buchung := { s.buchung with
      umfang := fun i => if i = o then s.buchung.umfang i ++ neu else s.buchung.umfang i } }

/-- The cells newly contributed by `bucheZellen`: object `o`, offsets just past its old extent. -/
def frischeZellen (s : Zustand L Ort Wert Raum Lok Grund) (o : Nat) (neu : List Ort) :
    Set (Nat × Nat) :=
  { z | z.1 = o ∧ (s.buchung.umfang o).length ≤ z.2 ∧
        z.2 < (s.buchung.umfang o).length + neu.length }

/-- Booking a live object's new cells adds exactly those cells to the live set. -/
theorem lebendeZellen_buche (s : Zustand L Ort Wert Raum Lok Grund) (o : Nat) (neu : List Ort)
    (hleb : s.rechte.lebt o = true) :
    LebendeZellen (bucheZellen s o neu) = LebendeZellen s ∪ frischeZellen s o neu := by
  ext z
  rcases z with ⟨i, j⟩
  simp only [LebendeZellen, bucheZellen, frischeZellen, Set.mem_union, Set.mem_setOf_eq]
  by_cases hio : i = o
  · subst i
    simp only [↓reduceIte, List.length_append]
    constructor
    · rintro ⟨_, hj⟩
      by_cases hjold : j < (s.buchung.umfang o).length
      · exact Or.inl ⟨hleb, hjold⟩
      · exact Or.inr ⟨trivial, Nat.le_of_not_gt hjold, hj⟩
    · intro h
      refine ⟨hleb, ?_⟩
      rcases h with ⟨_, hjold⟩ | ⟨_, _, hjneu⟩
      · exact Nat.lt_of_lt_of_le hjold (Nat.le_add_right _ _)
      · exact hjneu
  · simp only [hio, if_false, false_and, or_false]

/-- The new cells are disjoint from every old live cell: old cells of the same object end before
    the appended range, and cells of other objects have a different object number. -/
theorem frischeZellen_disjoint (s : Zustand L Ort Wert Raum Lok Grund) (o : Nat) (neu : List Ort) :
    Disjoint (LebendeZellen s) (frischeZellen s o neu) := by
  rw [Set.disjoint_left]
  intro z hzalt hzneu
  simp only [LebendeZellen, frischeZellen, Set.mem_setOf_eq] at hzalt hzneu
  rcases hzneu with ⟨hzo, hm, _⟩
  have hlt : z.2 < (s.buchung.umfang o).length := by
    simpa [hzo] using hzalt.2
  exact (not_lt_of_ge hm) hlt

/-- The appended range has exactly `neu.length` cells. -/
theorem frischeZellen_encard (s : Zustand L Ort Wert Raum Lok Grund) (o : Nat) (neu : List Ort) :
    (frischeZellen s o neu).encard = neu.length := by
  have hrange : frischeZellen s o neu =
      Set.range (fun k : Fin neu.length => (o, (s.buchung.umfang o).length + k.val)) := by
    ext z
    rcases z with ⟨i, j⟩
    constructor
    · rintro ⟨hzo, hmj, hj⟩
      simp only [Prod.fst, Prod.snd] at hzo hmj hj
      subst i
      have hlt : j - (s.buchung.umfang o).length < neu.length := by omega
      have heq : (s.buchung.umfang o).length + (j - (s.buchung.umfang o).length) = j := by omega
      refine ⟨⟨j - (s.buchung.umfang o).length, hlt⟩, ?_⟩
      simp only [Fin.val_mk]
      exact Prod.ext rfl heq
    · rintro ⟨k, hk⟩
      rw [← hk]
      simp only [frischeZellen, Set.mem_setOf_eq, Prod.fst, Prod.snd]
      refine ⟨trivial, ?_, ?_⟩ <;> omega
  rw [hrange]
  have hinj : Function.Injective
      (fun k : Fin neu.length => (o, (s.buchung.umfang o).length + k.val)) := by
    intro a b h
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Prod.snd h)
  rw [hinj.encard_range]
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]

/-- Exact growth: the ledger's live-cell count rises by exactly the number of booked cells. -/
theorem lebendeZellen_buche_encard (s : Zustand L Ort Wert Raum Lok Grund) (o : Nat)
    (neu : List Ort) (hleb : s.rechte.lebt o = true) :
    (LebendeZellen (bucheZellen s o neu)).encard = (LebendeZellen s).encard + neu.length := by
  rw [lebendeZellen_buche s o neu hleb]
  rw [Set.encard_union_eq (frischeZellen_disjoint s o neu)]
  rw [frischeZellen_encard s o neu]

/-- The ledger stays within the old ceiling extended by the newly booked cells. -/
theorem lebendeZellen_buche_encard_le (s : Zustand L Ort Wert Raum Lok Grund) (o : Nat)
    (neu : List Ort) (hleb : s.rechte.lebt o = true) (grenze : Nat)
    (vor : (LebendeZellen s).encard ≤ grenze) :
    (LebendeZellen (bucheZellen s o neu)).encard ≤ grenze + neu.length := by
  rw [lebendeZellen_buche_encard s o neu hleb]
  simpa using (add_le_add_right vor (neu.length : ℕ∞))

/-- The generic connection for a checked live object: disjoint new cells, exact live-set union,
    exact count growth, an extended finite ceiling, and unchanged extents of other objects. -/
theorem region_ledger_anschluss (s : Zustand L Ort Wert Raum Lok Grund) (o : Nat) (neu : List Ort)
    (hleb : s.rechte.lebt o = true) (grenze : Nat)
    (vor : (LebendeZellen s).encard ≤ grenze) :
    LebendeZellen (bucheZellen s o neu) = LebendeZellen s ∪ frischeZellen s o neu ∧
    Disjoint (LebendeZellen s) (frischeZellen s o neu) ∧
    (LebendeZellen (bucheZellen s o neu)).encard =
      (LebendeZellen s).encard + neu.length ∧
    (LebendeZellen (bucheZellen s o neu)).encard ≤ grenze + neu.length ∧
    (∀ i, i ≠ o → (bucheZellen s o neu).buchung.umfang i = s.buchung.umfang i) := by
  refine ⟨lebendeZellen_buche s o neu hleb, frischeZellen_disjoint s o neu,
    lebendeZellen_buche_encard s o neu hleb,
    lebendeZellen_buche_encard_le s o neu hleb grenze vor, ?_⟩
  intro i hi
  simp only [bucheZellen, if_neg hi]

/-- The connection specialized to an actually loaded region: the checked slot supplies `hleb`
    via `geladeneRegion_lebt_leer`, so the generic bounded-ledger result applies at load. -/
theorem geladeneRegion_ledger_anschluss (P : Plattform) (u : UnitMitSchranken)
    (a : AussenStart) (p : Ladung) {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    (geladen : (einheitVon P u.baum).laden a p = some s)
    (i : Nat) (hi : i < a.regions.length) (neu : List Zelle) (grenze : Nat)
    (vor : (LebendeZellen s).encard ≤ grenze) :
    LebendeZellen (bucheZellen s i neu) = LebendeZellen s ∪ frischeZellen s i neu ∧
    Disjoint (LebendeZellen s) (frischeZellen s i neu) ∧
    (LebendeZellen (bucheZellen s i neu)).encard =
      (LebendeZellen s).encard + neu.length ∧
    (LebendeZellen (bucheZellen s i neu)).encard ≤ grenze + neu.length := by
  rcases region_ledger_anschluss s i neu
      (geladeneRegion_lebt_leer P u a p geladen i hi).1 grenze vor with
    ⟨h1, h2, h3, h4, _⟩
  exact ⟨h1, h2, h3, h4⟩

/-- Complete logical cells in a physical handoff, for an explicitly supplied
    storage width in bytes. A trailing partial cell is unusable. -/
def handoffCells (bytes : Nat) (regions : List Strecke) (slot : Nat) : List Zelle :=
  match regions[slot]? with
  | none => []
  | some extent => (List.range ((extent.bis - extent.von) / bytes)).map (.region slot)

/-- The same extent projection consumed by the access and live-cell rules.
    Boot metadata and all authority fields are kept by the caller. -/
def handoffBooking (bytes : Nat) (regions : List Strecke) (booking : Sicherheit.Buchung Zelle) :
    Sicherheit.Buchung Zelle :=
  { booking with umfang := handoffCells bytes regions }

theorem handoffBooking_nil (bytes : Nat) :
    handoffBooking bytes [] Sicherheit.Buchung.leer = Sicherheit.Buchung.leer := rfl

/-- At a granted slot, the ledger lookup is exactly the source cell of that
    slot and logical offset, provided the complete cell fits in the grant. -/
theorem handoffBooking_lookup (bytes : Nat) (regions : List Strecke)
    (booking : Sicherheit.Buchung Zelle) {slot offset : Nat} {extent : Strecke}
    (grant : regions[slot]? = some extent) :
    ((handoffBooking bytes regions booking).umfang slot)[offset]? =
      some (.region slot offset) ↔ offset < (extent.bis - extent.von) / bytes := by
  change (handoffCells bytes regions slot)[offset]? = _ ↔ _
  rw [handoffCells, grant]
  constructor
  · intro h
    have bound := (List.getElem?_eq_some_iff.mp h).1
    simpa only [List.length_map, List.length_range] using bound
  · intro h
    simp only [List.getElem?_map, List.getElem?_range h, Option.map_some]

/-- The ledger's logical offset denotes a complete physical subextent of the
    grant. The positive layout width and the grant's actual endpoints determine
    that subextent. -/
theorem handoffBooking_inside {bytes : Nat} (positive : 0 < bytes) {regions : List Strecke}
    {booking : Sicherheit.Buchung Zelle} {slot offset : Nat} {extent : Strecke}
    (grant : regions[slot]? = some extent)
    (booked : ((handoffBooking bytes regions booking).umfang slot)[offset]? =
      some (.region slot offset)) :
    extent.enthaelt ⟨extent.von + offset * bytes, extent.von + (offset + 1) * bytes⟩ := by
  have fits := (handoffBooking_lookup bytes regions booking grant).mp booked
  have last : (offset + 1) * bytes ≤ extent.bis - extent.von :=
    (Nat.le_div_iff_mul_le positive).mp (Nat.succ_le_of_lt fits)
  have growth : offset * bytes < (offset + 1) * bytes := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have extentPositive : extent.von < extent.bis := by
    have : bytes ≤ (offset + 1) * bytes := by rw [Nat.add_mul, Nat.one_mul]; omega
    omega
  change extent.von ≤ extent.von + offset * bytes ∧
    extent.von + offset * bytes < extent.von + (offset + 1) * bytes ∧
    extent.von + (offset + 1) * bytes ≤ extent.bis
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left growth _, by omega⟩

/-- Distinct slots in the admitted handoff assign disjoint physical storage
    to the logical cells recorded in the ledger. -/
theorem handoffBooking_disjoint {bytes : Nat} (positive : 0 < bytes)
    {regions : List Strecke} (disjoint : regions.Pairwise Strecke.getrennt)
    {booking : Sicherheit.Buchung Zelle} {i j u v : Nat} {left right : Strecke}
    (distinct : i ≠ j) (leftGrant : regions[i]? = some left)
    (rightGrant : regions[j]? = some right)
    (leftCell : ((handoffBooking bytes regions booking).umfang i)[u]? = some (.region i u))
    (rightCell : ((handoffBooking bytes regions booking).umfang j)[v]? = some (.region j v)) :
    Strecke.getrennt ⟨left.von + u * bytes, left.von + (u + 1) * bytes⟩
      ⟨right.von + v * bytes, right.von + (v + 1) * bytes⟩ := by
  obtain ⟨hi, hleft⟩ := List.getElem?_eq_some_iff.mp leftGrant
  obtain ⟨hj, hright⟩ := List.getElem?_eq_some_iff.mp rightGrant
  have grants : left.getrennt right := by
    rw [← hleft, ← hright]
    by_cases before : i < j
    · exact disjoint.rel_getElem_of_lt hi hj before
    · exact Strecke.getrennt_symm (disjoint.rel_getElem_of_lt hj hi (by omega))
  obtain ⟨beginL, _, endL⟩ := handoffBooking_inside positive leftGrant leftCell
  obtain ⟨beginR, _, endR⟩ := handoffBooking_inside positive rightGrant rightCell
  exact grants.elim
    (fun h => Or.inl (endL.trans (h.trans beginR)))
    (fun h => Or.inr (endR.trans (h.trans beginL)))

/-- An installed single grant at the live boot slot contributes exactly its
    complete cells to B21. A grant at least one cell wide gives a positive count. -/
theorem handoffBooking_single_encard {L Wert Raum Lok Grund : Type}
    (s : Zustand L Zelle Wert Raum Lok Grund) (bytes : Nat) (extent : Strecke)
    (live : s.rechte.lebt 0 = true) :
    (LebendeZellen { s with buchung := handoffBooking bytes [extent] s.buchung }).encard =
      ((extent.bis - extent.von) / bytes : Nat) := by
  let count := (extent.bis - extent.von) / bytes
  let index : Fin count → Nat × Nat := fun i => (0, i.val)
  have range : LebendeZellen { s with buchung := handoffBooking bytes [extent] s.buchung } =
      Set.range index := by
    ext ⟨slot, offset⟩
    cases slot with
    | zero =>
      change (s.rechte.lebt 0 = true ∧ offset < ((List.range count).map (.region 0)).length) ↔ _
      simp only [live, true_and, List.length_map, List.length_range]
      exact ⟨fun h => ⟨⟨offset, h⟩, rfl⟩, by
        rintro ⟨i, hi⟩
        exact (congrArg Prod.snd hi) ▸ i.isLt⟩
    | succ slot =>
      change (s.rechte.lebt (slot + 1) = true ∧ offset < ([] : List Zelle).length) ↔ _
      refine ⟨fun h => (Nat.not_lt_zero _ h.2).elim, ?_⟩
      rintro ⟨i, hi⟩
      exact (Nat.noConfusion (congrArg Prod.fst hi) : False).elim
  have injective : Function.Injective index := fun _ _ h => Fin.ext (congrArg Prod.snd h)
  rw [range, injective.encard_range, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

end Gabbro.Core.Beobachtung
