module

public import Core.Annahme.Hosted

@[expose] public section

namespace Gabbro.Core.Annahme.Hosted

open Katalog Maschine

def lebend (bytes : List UInt8) : AussenSicht :=
  ⟨fun _ => ⟨0, true, true, bytes, fun _ => 0⟩,
    fun e i => if e = .hosted ∧ i = 0 then some griff else none, fun _ _ => none⟩

/-- The handle is granted at boot. The object is unavailable when the request is issued,
    and the catalogue independently checks the snapshot where the answer commits. -/
def sicht (bytes : List UInt8) (t : Nat) (_ : AussenVerlauf) : AussenSicht :=
  if t = 1 then .leer else lebend (if t = 0 then [] else bytes)

def umgebung (bytes : List UInt8) : Umgebung := Umgebung.referenz einheit.katalog 1 (sicht bytes)
def hardware (bytes : List UInt8) : HwLauf := Umgebung.referenzLauf einheit.katalog 1 (sicht bytes)

theorem erlaubt (bytes : List UInt8) : Hardware einheit.katalog (umgebung bytes) :=
  Umgebung.referenz_hardware _ _ _ (Plattform.katalog_wohlgeformt _) (Nat.zero_lt_succ _)

theorem konform (bytes : List UInt8) : (hardware bytes).konform einheit.katalog (umgebung bytes) :=
  (Umgebung.referenz_fair _ _ _ (Plattform.katalog_wohlgeformt _) (Nat.zero_lt_succ _)).konform

theorem gleicher_start {s : AussenStart} (zul : einheit.ZulStart (umgebung []) s) (bytes : List UInt8) :
    einheit.ZulStart (umgebung bytes) s := zul

def ausgabe (bytes : List UInt8) : Antwort := ⟨griff.origin, [griff.origin], .ok (.data bytes)⟩

def gestellt (s : AussenStart) : FrageEreignis := (binde (startZustand s)).stelleFrage 1 kontext frage

def angekommen (s : AussenStart) (bytes : List UInt8) : AntwortEreignis :=
  let e := gestellt s
  ⟨2, e.context, e.questionInstance, e.question, ausgabe bytes⟩

def frageSpur (s : AussenStart) : Spur :=
  ⟨[(.kontext kontext, aussenEtikett einrichtung (.frage (gestellt s)))], [.frage (gestellt s)]⟩

def antwortSpur (s : AussenStart) (bytes : List UInt8) : Spur :=
  ⟨[(.aussen, aussenEtikett einrichtung (.antwort (angekommen s bytes)))], [.antwort (angekommen s bytes)]⟩

theorem issue_ungueltig (history : AussenVerlauf) (bytes : List UInt8) :
    ¬ Aussen.GueltigBeiCommit einheit.katalog.plattform (sicht bytes 1 history) frage := by
  intro valid
  let z : Zugriff := ⟨griff, .read⟩
  have mem : z ∈ frage.zugriffe := List.mem_cons_self
  cases valid with
  | frisch all =>
    have ja := List.all_eq_true.mp all z mem
    have nein := Aussen.tot_gueltig_falsch AussenSicht.leer frage.endpoint z (fun _ => rfl)
    exact Bool.false_ne_true (nein.symm.trans ja)
  | stabil all => exact Aussen.hosted_nicht_stabil _ _ rfl (all z mem)

theorem antwort_atomar (history : AussenVerlauf) (bytes : List UInt8) :
    atomar einheit.katalog.plattform (sicht bytes 2 history) frage = .antwort (ausgabe bytes) := rfl

private theorem rahmen_binde (s : Zustand) : Zustandsrahmen s (binde s) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem rahmen_warte (s : Zustand) : Zustandsrahmen s (warte s) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem binde_regel {s : AussenStart} (zul : einheit.ZulStart (umgebung []) s) :
    regel kontext (startZustand s) () [bindePlan] (binde (startZustand s)) := by
  refine ⟨rfl, Or.inl ⟨rfl, ?_, rfl⟩⟩
  change s.outside.channels .hosted 0 = some griff
  rw [zul.2.2.2.2.2.2.2]
  rfl

private theorem binde_aus (s : AussenStart) :
    FuehrtSchrittAus einrichtung 0 kontext (startZustand s) (binde (startZustand s))
      bindePlan ⟨[], []⟩ (binde (startZustand s)) :=
  ⟨rahmen_binde _, fun _ mem => (List.not_mem_nil mem).elim, [], _, .intern, .nil _, rfl⟩

private theorem frage_aus (s : AussenStart) :
    ∃ g, FuehrtSchrittAus einrichtung 1 kontext (binde (startZustand s)) (warte (binde (startZustand s)))
      fragePlan (frageSpur s) { (warte (binde (startZustand s))).frage (gestellt s) with graph := g } := by
  obtain ⟨g, step⟩ := Speicher.Zustand.schritt_ohne_lesen
    Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig (SpeicherAkteur.kontext kontext)
    (aussenEtikett einrichtung (.frage (gestellt s))) id
  exact ⟨g, rahmen_warte _, fun _ mem => (List.not_mem_nil mem).elim, [], _, .frage frage,
    .cons (.ohne (Or.inl rfl)) step (.nil _), rfl⟩

private theorem antwort_aus (s : AussenStart) (bytes : List UInt8) {g : SpeicherGraph Unit Unit}
    (gut : g.graph.Konsistent ∧ g.graph.Vollstaendig) :
    let z := { (warte (binde (startZustand s))).frage (gestellt s) with graph := g }
    ∃ g', AntwortSchritt einrichtung einheit.katalog (hardware bytes) 2 (angekommen s bytes)
      z (antwortSpur s bytes) { z.antwort (angekommen s bytes) with graph := g' } := by
  intro z
  obtain ⟨g', step⟩ := Speicher.Zustand.schritt_ohne_lesen gut.1 gut.2
    (SpeicherAkteur.aussen : SpeicherAkteur Unit)
    (aussenEtikett einrichtung (.antwort (angekommen s bytes))) id
  have offered : z.AntwortAngeboten einheit.katalog (hardware bytes) 2 (angekommen s bytes) := by
    refine ⟨rfl, ⟨decide_eq_true ausgewaehlt, ?_⟩, ausgewaehlt,
      ⟨gestellt s, List.mem_cons_self, Nat.zero_le _, Nat.le_succ _, rfl, rfl, rfl⟩,
      fun _ mem => (List.not_mem_nil mem).elim⟩
    exact antwort_atomar z.verlauf bytes
  exact ⟨g', offered, rfl, .cons (.ohne (Or.inl rfl)) step (.nil _), rfl⟩

private theorem antwortfertig {s : AussenStart} {bytes : List UInt8} {g : SpeicherGraph Unit Unit}
    {t : Nat} {a : AntwortEreignis}
    (angebot : ({ ((warte (binde (startZustand s))).frage (gestellt s)).antwort (angekommen s bytes)
      with graph := g } : Zustand).AntwortAngeboten einheit.katalog (hardware bytes) t a) : False := by
  obtain ⟨ev, mem, _, _, _, instanz, _⟩ := angebot.2.2.2.1
  cases List.mem_singleton.mp mem
  exact angebot.2.2.2.2 (angekommen s bytes) List.mem_cons_self instanz

def fragend (s : AussenStart) (g : SpeicherGraph Unit Unit) : Zustand :=
  { (warte (binde (startZustand s))).frage (gestellt s) with graph := g }

def fertig (s : AussenStart) (bytes : List UInt8) (g g' : SpeicherGraph Unit Unit) : Zustand :=
  { (fragend s g).antwort (angekommen s bytes) with graph := g' }

private theorem beendet {s : AussenStart} {bytes : List UInt8} {g g'}
    {t c} (bereit : KannSchreiten (hardware bytes) t c (fertig s bytes g g')) : False := by
  obtain ⟨_, _, _, h⟩ := bereit
  change Status.ruht = Status.laeuft at h
  cases h

private theorem kein_interrupt {s : AussenStart} {bytes : List UInt8} {g g'}
    {t id spur nach}
    (step : UnterbrechungsSchritt einrichtung (hardware bytes) t id (fertig s bytes g g') spur nach) : False := by
  obtain ⟨_, _, _, _, _, angeboten, _⟩ := step
  have eq := angeboten.2.2.1
  change ([] : List InterruptSignal)[id.2]? = some _ at eq
  rw [List.getElem?_nil] at eq
  cases eq

private theorem kein_absturz {s : AussenStart} {bytes : List UInt8} {g g'}
    {t spur nach}
    (step : AbsturzSchritt einrichtung.persistenzRegion einrichtung.wiederanlauf einheit.katalog
      (hardware bytes) t (fertig s bytes g g') spur nach) : False := by
  have eq := step.1.2
  cases eq

private theorem ideal_still {s : AussenStart} {bytes : List UInt8} {g g'} (t : Nat) :
    KeinSchritt (I.Schritt einrichtung einheit.system einheit.katalog (hardware bytes)) t (fertig s bytes g g') := by
  intro _ _ step
  cases step with
  | kontext _ ready _ _ => exact beendet ready
  | antwort _ reply => exact antwortfertig reply.1
  | interrupt _ enters => exact kein_interrupt enters
  | absturz crash => exact kein_absturz crash

private theorem konkret_still {s : AussenStart} {bytes : List UInt8} {g g'} (t : Nat) :
    KeinSchritt (Lauffolge einheit (hardware bytes)) t (some (fertig s bytes g g')) := by
  intro _ _ step
  cases step with
  | schritt transition =>
    cases transition with
    | kontext _ ready _ _ => exact beendet ready
    | antwort _ reply => exact antwortfertig reply.1
    | interrupt _ enters => exact kein_interrupt enters
    | absturz crash => exact kein_absturz crash

def dreiTakte {S Ev : Type} {schritt : Nat → S → Ev → S → Prop}
    {s₀ s₁ s₂ s₃ : S} {e₀ e₁ e₂ : Ev}
    (h₀ : schritt 0 s₀ e₀ s₁) (h₁ : schritt 1 s₁ e₁ s₂) (h₂ : schritt 2 s₂ e₂ s₃)
    (ende : ∀ t, KeinSchritt schritt (t + 3) s₃) : Zeitlauf schritt where
  zustand
    | 0 => s₀
    | 1 => s₁
    | 2 => s₂
    | _ + 3 => s₃
  spur
    | 0 => some e₀
    | 1 => some e₁
    | 2 => some e₂
    | _ + 3 => none
  takt
    | 0 => .schritt rfl h₀
    | 1 => .schritt rfl h₁
    | 2 => .schritt rfl h₂
    | t + 3 => .wartet rfl rfl (ende t)

theorem protokoll_erfuellbar (s : AussenStart) (bytes : List UInt8) :
    ∃ g g',
      FuehrtSchrittAus einrichtung 0 kontext (startZustand s) (binde (startZustand s))
        bindePlan ⟨[], []⟩ (binde (startZustand s)) ∧
      FuehrtSchrittAus einrichtung 1 kontext (binde (startZustand s)) (warte (binde (startZustand s)))
        fragePlan (frageSpur s) (fragend s g) ∧
      AntwortSchritt einrichtung einheit.katalog (hardware bytes) 2 (angekommen s bytes)
        (fragend s g) (antwortSpur s bytes) (fertig s bytes g g') := by
  obtain ⟨g, aus⟩ := frage_aus s
  have gut := (aus.viele einrichtung).gut Speicher.Zustand.leer_konsistent Speicher.Zustand.leer_vollstaendig
  obtain ⟨g', reply⟩ := antwort_aus s bytes gut
  exact ⟨g, g', binde_aus s, aus, reply⟩

theorem form_binden {s : AussenStart} (zul : einheit.ZulStart (umgebung []) s) :
    einheit.system.ISchritt kontext (startZustand s) () [bindePlan] (binde (startZustand s)) :=
  ⟨(), rfl, binde_regel zul⟩

theorem form_fragen (s : AussenStart) :
    einheit.system.ISchritt kontext (binde (startZustand s)) () [fragePlan] (warte (binde (startZustand s))) :=
  ⟨(), rfl, rfl, Or.inr ⟨rfl, eigene_frage _, rfl⟩⟩

theorem ruhe_erlaubt (bytes : List UInt8) (t : Nat) :
    ¬ AbsturzAngeboten einheit.katalog (hardware bytes) t := fun h => Bool.false_ne_true h.2

/-- A concrete run shares the same issuing and answer steps as the ideal run. Its finite
    prefix is followed by genuine idle ticks. -/
theorem konkreter_lauf {s : AussenStart} (zul : einheit.ZulStart (umgebung []) s) (bytes : List UInt8) :
    ∃ (ρ : Lauf einheit) (g g' : SpeicherGraph Unit Unit),
      Laeufe einheit (umgebung bytes) ρ ∧ ρ.start = s ∧ ρ.hw = hardware bytes ∧
      ρ.zeit.zustand 0 = some (startZustand s) ∧ ρ.zeit.zustand 1 = some (binde (startZustand s)) ∧
      ρ.zeit.zustand 2 = some (fragend s g) ∧ ρ.zeit.zustand 3 = some (fertig s bytes g g') ∧
      ρ.zeit.spur 0 = some (.kontext kontext (), ⟨[], []⟩) ∧
      ρ.zeit.spur 1 = some (.kontext kontext (), frageSpur s) ∧
      ρ.zeit.spur 2 = some (.antwort (angekommen s bytes), antwortSpur s bytes) ∧
      ∀ t, ρ.zeit.spur (t + 3) = none := by
  obtain ⟨g, g', grant, issue, reply⟩ := protokoll_erfuellbar s bytes
  let h₀ : Lauffolge einheit (hardware bytes) 0 (some (startZustand s))
      (.kontext kontext (), ⟨[], []⟩) (some (binde (startZustand s))) :=
    .schritt (.kontext rfl ⟨0, rfl, rfl, rfl⟩ (form_binden zul) grant)
  let h₁ : Lauffolge einheit (hardware bytes) 1 (some (binde (startZustand s)))
      (.kontext kontext (), frageSpur s) (some (fragend s g)) :=
    .schritt (.kontext rfl ⟨0, rfl, rfl, rfl⟩ (form_fragen s) issue)
  let h₂ : Lauffolge einheit (hardware bytes) 2 (some (fragend s g))
      (.antwort (angekommen s bytes), antwortSpur s bytes) (some (fertig s bytes g g')) :=
    .schritt (.antwort rfl reply)
  let ρ : Lauf einheit := ⟨s, hardware bytes, dreiTakte h₀ h₁ h₂ (fun t => konkret_still (t + 3))⟩
  exact ⟨ρ, g, g', ⟨erlaubt bytes, konform bytes, gleicher_start zul bytes, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

end Gabbro.Core.Annahme.Hosted
