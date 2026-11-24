module

public import Core.Sicherheit.KatalogSchritt

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
variable {vor nach : Zustand L Ort Wert Raum Lok Grund} {spur : SchrittSpur Ort Wert}

/-- Obligations at the unit's non-form boundaries. An arbitrary loader needs a safe start
    specification. Declared predicates may observe catalogue, interrupt or recovery state and
    therefore must be proved at those updates as well as at the execution of forms. -/
structure GrenzenSicher (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form) : Prop where
  laden : ∀ H start s, Hardware E.maschine.katalog H → E.maschine.ZulStart H start →
    E.maschine.laden start (H.lade E.maschine.bild) = some s →
    s.graph.ev = [] ∧ s.buchung.wirkungen = [] ∧ s.fragen = [] ∧ InvariantenAmSchnitt E s
  antwort : ∀ hw t a vor spur nach,
    AntwortSchritt E.maschine.einrichtung E.maschine.katalog hw t a vor spur nach →
    InvariantenAmSchnitt E vor → InvariantenAmSchnitt E nach
  interrupt : ∀ hw t id vor spur nach,
    UnterbrechungsSchritt E.maschine.einrichtung hw t id vor spur nach →
    InvariantenAmSchnitt E vor → InvariantenAmSchnitt E nach
  wiederanlauf : ∀ hw t vor spur nach,
    AbsturzSchritt E.maschine.einrichtung.persistenzRegion E.maschine.einrichtung.wiederanlauf
      E.maschine.katalog hw t vor spur nach →
    InvariantenAmSchnitt E vor → InvariantenAmSchnitt E nach

/-- Each question in a recorded state was issued strictly before the cut of that state. -/
def FragenVor (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∀ q ∈ s.fragen, q.cut < t

omit [DecidableEq L] in
theorem fragen_leer {s : Zustand L Ort Wert Raum Lok Grund} (leer : s.fragen = []) :
    FragenVor 0 s ∧ OffeneFragenBefugt s := by
  constructor <;> intro q member <;> rw [leer] at member <;> cases member

private theorem aktion_fragen_vor {t c zwischen a ls es}
    (aktion : FuehrtAus E.maschine.einrichtung t c vor zwischen a ls es nach)
    (rahmen : Zustandsrahmen vor zwischen) (alt : FragenVor t vor) : FragenVor (t + 1) nach := by
  cases aktion with
  | frage q =>
    intro a member
    change a ∈ zwischen.fragen ++ [vor.stelleFrage t c q] at member
    rw [rahmen.fragen, List.mem_append, List.mem_singleton] at member
    rcases member with frueher | jetzt
    · exact Nat.lt_succ_of_lt (alt _ frueher)
    · cases jetzt
      exact Nat.lt_succ_self _
  | intern | warte _ | sperre _ _ | verbrauche _ | rueckkehr _ _ =>
    intro a member
    exact Nat.lt_succ_of_lt (alt _ (rahmen.fragen ▸ member))

theorem kontext_fragen_vor {t c zwischen plan} (h :
    FuehrtSchrittAus E.maschine.einrichtung t c vor zwischen plan spur nach)
    (alt : FragenVor t vor) : FragenVor (t + 1) nach := by
  obtain ⟨rahmen, _, _, v, aktion, _, zustand⟩ := h
  rw [zustand]
  exact aktion_fragen_vor (E := E) (nach := v) aktion rahmen alt

omit [DecidableEq L] in
theorem angebot_befugt {k hw t a} (angebot : vor.AntwortAngeboten k hw t a)
    (offen : OffeneFragenBefugt vor) :
    (∃ c, c.nummer = a.context ∧ EigeneGriffe vor c a.question) ∧
    RegisterErlaubt vor a.context a.question := by
  obtain ⟨q, member, epoche, _, context, instanceId, question⟩ := angebot.2.2.2.1
  have rechte := offen q member epoche (fun e mem => instanceId.symm ▸ angebot.2.2.2.2 e mem)
  rwa [context, question] at rechte

private theorem katalog_ohne_speicherwirkung
    {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
    {hw t ev} (aussen : spur.aussen = [ev]) (keinCrash : ev ≠ .persistenz .crash)
    (folge : Speicherfolge vor.initial .aussen vor.graph [aussenEtikett e ev] spur.speicher nach.graph)
    (buchung : nach.buchung = vor.buchung) (rechte : nach.rechte = vor.rechte) :
    ZugriffGebucht vor nach spur ∧
      (RennenImGraph vor.graph → RennenImGraph nach.graph) ∧
      NeueWirkungen vor nach spur [] ∧ FreigabenGueltig vor nach hw t spur [] := by
  obtain ⟨eintrag, rennen⟩ := katalog_speicher rfl folge
  have keinAbsturz : ¬ Absturz spur := by
    intro member
    change Ereignis.persistenz .crash ∈ spur.aussen at member
    rw [aussen] at member
    exact keinCrash (List.mem_singleton.mp member).symm
  refine ⟨?_, rennen, wirkungsloser_schritt keinAbsturz buchung rechte⟩
  intro i actor label archiv nichtAussen
  rw [eintrag] at archiv
  have member := List.mem_of_getElem? archiv
  cases List.mem_singleton.mp member
  exact (nichtAussen rfl).elim

theorem antwort_sicher {H ρ t a}
    (grenzen : GrenzenSicher E) (hardware : Hardware E.maschine.katalog H)
    (politik : ρ.hw.politik = H.politik)
    (schritt : AntwortSchritt E.maschine.einrichtung E.maschine.katalog ρ.hw t a vor spur nach)
    (alt : FragenVor t vor) (offen : OffeneFragenBefugt vor) :
    SchrittSicherheit E H ρ t vor nach spur ∧ FragenVor (t + 1) nach ∧ OffeneFragenBefugt nach := by
  have invariant := grenzen.antwort _ _ _ _ _ _ schritt
  obtain ⟨angebot, aussen, speicher, ziel⟩ := schritt
  have buchung : nach.buchung = vor.buchung := ziel ▸ rfl
  have rechte : nach.rechte = vor.rechte := ziel ▸ rfl
  obtain ⟨zugriff, rennen, wirkungen, freigaben⟩ :=
    katalog_ohne_speicherwirkung (hw := ρ.hw) (t := t) aussen (fun h => nomatch h) speicher buchung rechte
  have erlaubt := angebot_befugt angebot offen
  have aktuell {H' : Umgebung} (hw : Hardware E.maschine.katalog H')
      (gleich : H'.politik.antwort t vor.verlauf a.question = .antwort a.reply)
      (erfolg : a.reply.result.isOk = true) :
      Aussen.GueltigBeiCommit E.maschine.katalog.plattform (H'.politik.sicht t vor.verlauf) a.question := by
    rw [hw.antwort _ _ _ angebot.2.2.1] at gleich
    exact Aussen.atomar_gueltig gleich erfolg
  refine ⟨⟨⟨zugriff, [], wirkungen, freigaben⟩, invariant,
    fun _ => kein_sperrwechsel (ziel ▸ rfl), rennen, ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, [], wirkungen, fun _ mem => (List.not_mem_nil mem).elim⟩
    intro ev mem
    rw [aussen] at mem
    have eq := List.mem_singleton.mp mem
    constructor
    · intro q frage
      cases eq.symm.trans frage
    · intro other commit
      cases Ereignis.antwort.inj (eq.symm.trans commit.1)
      exact erlaubt.2
  · refine ⟨?_, [], wirkungen, fun _ mem => (List.not_mem_nil mem).elim⟩
    intro ev mem other commit
    rw [aussen] at mem
    cases List.mem_singleton.mp mem
    cases Ereignis.antwort.inj commit.1
    have antwort := angebot.2.1.2
    rw [angebot.1, politik] at antwort
    exact ⟨erlaubt.1, aktuell hardware antwort commit.2,
      fun _ historie gleich => aktuell historie.1 gleich commit.2⟩
  · rw [ziel]
    exact fun q member => Nat.lt_succ_of_lt (alt q member)
  · rw [ziel]
    intro q member epoche unbenutzt
    exact offen q member epoche (fun a' mem => unbenutzt a' (List.mem_append_left _ mem))

theorem interrupt_sicher {H ρ t id}
    (grenzen : GrenzenSicher E)
    (schritt : UnterbrechungsSchritt E.maschine.einrichtung ρ.hw t id vor spur nach)
    (alt : FragenVor t vor) (offen : OffeneFragenBefugt vor) :
    SchrittSicherheit E H ρ t vor nach spur ∧ FragenVor (t + 1) nach ∧ OffeneFragenBefugt nach := by
  have invariant := grenzen.interrupt _ _ _ _ _ _ schritt
  obtain ⟨_, _, _, _, _, _, _, _, aussen, speicher, ziel⟩ := schritt
  have buchung : nach.buchung = vor.buchung := ziel ▸ rfl
  have rechte : nach.rechte = vor.rechte := ziel ▸ rfl
  obtain ⟨zugriff, rennen, wirkungen, freigaben⟩ :=
    katalog_ohne_speicherwirkung (hw := ρ.hw) (t := t) aussen (fun h => nomatch h) speicher buchung rechte
  refine ⟨⟨⟨zugriff, [], wirkungen, freigaben⟩, invariant,
    fun _ => kein_sperrwechsel (ziel ▸ rfl), rennen, ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, [], wirkungen, fun _ mem => (List.not_mem_nil mem).elim⟩
    intro ev mem
    rw [aussen] at mem
    have eq := List.mem_singleton.mp mem
    constructor
    · intro q frage
      cases eq.symm.trans frage
    · intro a commit
      cases eq.symm.trans commit.1
  · refine ⟨?_, [], wirkungen, fun _ mem => (List.not_mem_nil mem).elim⟩
    intro ev mem other commit
    rw [aussen] at mem
    cases (List.mem_singleton.mp mem).symm.trans commit.1
  · rw [ziel]
    exact fun q member => Nat.lt_succ_of_lt (alt q member)
  · rw [ziel]
    exact offen

theorem absturz_sicher {H ρ t}
    (grenzen : GrenzenSicher E)
    (schritt : AbsturzSchritt E.maschine.einrichtung.persistenzRegion E.maschine.einrichtung.wiederanlauf
      E.maschine.katalog ρ.hw t vor spur nach) (alt : FragenVor t vor) :
    SchrittSicherheit E H ρ t vor nach spur ∧ FragenVor (t + 1) nach ∧ OffeneFragenBefugt nach := by
  obtain ⟨label, ziel⟩ := schritt.genau
  have crash : Absturz spur := label ▸ List.mem_cons_self
  have wirkungen : NeueWirkungen vor nach spur [] := Or.inl ⟨crash, ziel ▸ rfl, rfl⟩
  refine ⟨⟨⟨?_, [], wirkungen, List.nodup_nil, fun _ _ mem => (List.not_mem_nil mem).elim,
    fun kein => (kein crash).elim⟩, grenzen.wiederanlauf _ _ _ _ _ schritt,
    fun kein => (kein crash).elim, fun _ => rennen_bei_leeren_ereignissen (ziel ▸ rfl),
    ?_, ?_⟩, ?_, ?_⟩
  · rw [label]
    intro i actor zugriff mem _
    cases mem
  · refine ⟨?_, [], wirkungen, fun _ mem => (List.not_mem_nil mem).elim⟩
    rw [label]
    intro ev mem
    have eq := List.mem_singleton.mp mem
    constructor
    · intro q frage
      cases eq.symm.trans frage
    · intro a commit
      cases eq.symm.trans commit.1
  · refine ⟨?_, [], wirkungen, fun _ mem => (List.not_mem_nil mem).elim⟩
    rw [label]
    intro ev mem a commit
    cases (List.mem_singleton.mp mem).symm.trans commit.1
  · rw [ziel]
    exact fun q mem => Nat.lt_succ_of_lt (alt q mem)
  · rw [ziel]
    intro q mem epoche _
    exact (Nat.not_le_of_lt (Nat.lt_succ_of_lt (alt q mem)) epoche).elim

end Gabbro.Core.Sicherheit
