/-
  File:      core/Core/Ast/Semantik/Runtime/ZugriffSicher/RennenLauf.lean
  Subject:   THE RUN-LEVEL RACE INVARIANT OF A SOURCE UNIT (the missing second leg of
              `ZugriffSicherAussage`). A run of a source unit appends memory events only at the entry
              context: its `eintritte` names no handler, so every other context's boot frame carries no
              arrival regions, and an access without a region is refused before it records an event.
              Therefore all executed accesses of every prefix have the one actor `.kontext eintritt`,
              and program order orders every conflicting pair (`rennenAusEinemKontext`). No statement
              is changed.
-/
module

public import Core.Ast.Semantik.Runtime.ZugriffSicher.RennenBein
public import Core.Ast.Semantik.Runtime.ZugriffSicher.Grenzen
public import Core.Ast.Semantik.Runtime.Mehrkontext.Start
public import Core.Sicherheit.KatalogSchritt
public import Core.Ast.Semantik.Runtime.UnitInvarianten
public import Core.Ast.Semantik.Runtime.Klasse.Ankunft
public import Core.Ast.Semantik.Runtime.Faden.Erhalt
public import Core.Ast.Semantik.Runtime.ZugriffSicher.Grenzen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Sicherheit
open Gabbro.Core.Sicherheit (Konflikt AusgefuehrterZugriff RennenImGraph)
open Gabbro.Core.Speicher (Zustand)

/-- A context without arrival regions holds no handle, so it is authorised for no cell. -/
theorem keineBefugnisOhneAnkunft {s : Zustand} {c : Kontext}
    (leer : (s.lokal c).arrivalRegions = []) :
    ∀ (z : Zelle) (recht : Speicherrecht), ¬ s.befugt c z recht := by
  intro z recht bef
  obtain ⟨g, off, griff, _, _, _, _, _⟩ := bef
  have gn : s.griff c z = none := by
    cases z with
    | region slot offset =>
      simp only [Zustand.griff, leer, List.length_nil, Nat.not_lt_zero, if_false]
    | sperre lock => rfl
    | aussen => rfl
  rw [gn] at griff
  cases griff

/-- The authority of every access form but the fence is the cell authority of its operand. -/
theorem zugriffBefugtBrauchtAnkunft (z : Zugriffsform)
    (hz : ∀ m, z ≠ .zaun m) {s : Zustand} {c : Kontext}
    (leer : (s.lokal c).arrivalRegions = []) :
    ¬ (Befehl.zugriff z).form.klasse.befugt ((Befehl.zugriff z).form.operand (s.lokal c)) s c := by
  cases z with
  | zaun m => exact False.elim (hz m rfl)
  | lade ziel region index typ mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.lade ziel region index typ mode) (s.lokal c)).ort) .lesen)
  | erwarte ziel region index erwartet typ mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.erwarte ziel region index erwartet typ mode) (s.lokal c)).ort) .lesen)
  | speichere region index quelle mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.speichere region index quelle mode) (s.lokal c)).ort) .schreiben)
  | veroeffentliche region index quelle mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.veroeffentliche region index quelle mode) (s.lokal c)).ort) .schreiben)
  | tausche ziel region index quelle typ mode =>
    intro bef
    have hn := keineBefugnisOhneAnkunft (s := s) (c := c) leer
      ((Zugriffsform.operand (Zugriffsform.tausche ziel region index quelle typ mode) (s.lokal c)).ort) .lesen
    exact hn (by
      simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
        Wirkungsklasse.befugt] using bef.1)
  | vergleicheTausche ziel region index erwartet neu typ mode =>
    intro bef
    have hn := keineBefugnisOhneAnkunft (s := s) (c := c) leer
      ((Zugriffsform.operand (Zugriffsform.vergleicheTausche ziel region index erwartet neu typ mode) (s.lokal c)).ort) .lesen
    exact hn (by
      simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
        Wirkungsklasse.befugt] using bef.1)
  | holeUndAddiere ziel region index betrag typ mode =>
    intro bef
    have hn := keineBefugnisOhneAnkunft (s := s) (c := c) leer
      ((Zugriffsform.operand (Zugriffsform.holeUndAddiere ziel region index betrag typ mode) (s.lokal c)).ort) .lesen
    exact hn (by
      simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
        Wirkungsklasse.befugt] using bef.1)

/-- A step of a class-good instruction at a context with no arrival regions plans the
    private step: a frame-only form is private by its class; a fence plans nothing; every other
    access form is refused because it holds no handle. -/
theorem quellSchrittPlanPrivat (p : Fragment) (f : Befehl) (hgut : f.Klassengut)
    {c : Kontext} {s : Zustand} (leer : (s.lokal c).arrivalRegions = [])
    {w : PUnit} {plan : Plan} {u : Zustand}
    (impl : ((system p.code).regel f).impl c s w [plan] u) :
    plan = Semantik.plan := by
  change f.impl c s w [plan] u at impl
  rcases hgut with hpriv | ⟨z, rfl⟩
  · exact (List.cons.inj (((Befehl.impl_privat f hpriv c s w [plan] u).1 impl).1)).1
  · have step := (Zugriffsform.ideal_iff z c s w [plan] u).1 impl
    rcases step with ⟨_, eq, _⟩ | ⟨bef, v, _, eq, _⟩
    · exact (List.cons.inj eq).1
    · by_cases hz : ∃ m, z = .zaun m
      · rcases hz with ⟨m, rfl⟩
        have hp : plan = (Befehl.zugriff (Zugriffsform.zaun m)).form.plan (s.lokal c) v :=
          (List.cons.inj eq).1
        simpa [Befehl.form, Befehl.klasse, Zugriffsform.klasse, Schrittform.plan, Wirkungsklasse.plan] using hp
      · have hf : ∀ m, z ≠ .zaun m := by
          intro m hzaun
          exact hz ⟨m, hzaun⟩
        exact False.elim ((zugriffBefugtBrauchtAnkunft z hf leer) bef)



/-- A class-good step leaves every context's arrival regions unchanged. -/
theorem quellImplArrivalGleich (p : Fragment) (f : Befehl) (hgut : f.Klassengut)
    {c : Kontext} {s : Zustand} {w : PUnit} {plan : Plan} {u : Zustand}
    (impl : ((system p.code).regel f).impl c s w [plan] u) :
    ∀ d, (u.lokal d).arrivalRegions = (s.lokal d).arrivalRegions := by
  change f.impl c s w [plan] u at impl
  intro d
  rcases hgut with hpriv | ⟨z, rfl⟩
  · have hu : u = Befehl.nach f c s := ((Befehl.impl_privat f hpriv c s w [plan] u).1 impl).2
    subst u
    by_cases hdc : d = c
    · subst d
      simp only [Befehl.nach, Zustand.lokal, Function.update_self]
      exact ankunftUnveraendert f (s.lokal c) s.regionLive
    · simp only [Befehl.nach, Zustand.lokal, Function.update_of_ne hdc]
  · have step := (Zugriffsform.ideal_iff z c s w [plan] u).1 impl
    rcases step with ⟨_, _, hu⟩ | ⟨_, v, _, _, hu⟩
    · subst u
      by_cases hdc : d = c
      · subst d
        simp only [Schrittform.verweigert, Zustand.lokal, Function.update_self, Rahmen.halt]
      · simp only [Schrittform.verweigert, Zustand.lokal, Function.update_of_ne hdc]
    · subst u
      by_cases hdc : d = c
      · subst d
        simp only [Schrittform.zugriffNach, Schrittform.nach, Zustand.lokal, Function.update_self]
        exact Zugriffsform.uebertrag_arrival z (s.lokal c) v
      · simp only [Schrittform.zugriffNach, Schrittform.nach, Zustand.lokal, Function.update_of_ne hdc]

/-- A `Speicherfolge` with no labels appends no event. -/
theorem speicherfolgeLeer {Ort Wert} {anfang : Ort → Wert} {f : SpeicherAkteur Ort}
    {g g' : SpeicherGraph Ort Wert} {es} (h : Speicherfolge anfang f g [] es g') :
    es = [] ∧ g' = g := by
  cases h with
  | nil g => exact ⟨rfl, rfl⟩

/-- A class-good step at a context with no arrival regions appends no memory event at all. -/
theorem quellSchrittGraphGleich (p : Fragment) (platform : Plattform) (f : Befehl) (hgut : f.Klassengut)
    {t : Nat} {c : Kontext} {s u : Zustand} {w : PUnit} {plan : Plan}
    {spur : SchrittSpur Zelle Int} {s' : Zustand}
    (leer : (s.lokal c).arrivalRegions = [])
    (impl : ((system p.code).regel f).impl c s w [plan] u)
    (aus : FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s') :
    s'.graph.ev = s.graph.ev := by
  have planEq := quellSchrittPlanPrivat p f hgut leer impl
  have still : plan.aktion.Still := Befehl.impl_aktion_still f (w := w) (c := c) (s := s) (p := plan) (u := u) impl
  obtain ⟨_, _, _, _, aktion, folge, _⟩ := aus
  have hstill := FuehrtAus.still_erhaelt aktion still
  have hlabels : sperren ++ plan.lesen ++
      schreibEreignisse plan.fuss plan.schreibt plan.modus plan.wert ++
      spur.aussen.map (aussenEtikett (p.einheit platform).einrichtung) = [] := by
    simp [planEq, hstill.1, hstill.2.1, Semantik.plan, schreibEreignisse]
  have folgeLeer : Speicherfolge s.initial (.kontext c) s.graph [] spur.speicher s'.graph := by
    simpa [hlabels] using folge
  obtain ⟨_, gEq⟩ := speicherfolgeLeer folgeLeer
  rw [gEq]

/-- Every event a `Speicherfolge` appends is a step of its actor or a lazily materialised
    initial write. -/
theorem initialisierungAkteen {Ort Wert} {anfang : Ort → Wert} {l : Speicher.Etikett Ort Wert}
    {g g' : SpeicherGraph Ort Wert} {init} (h : Initialisierung anfang l g init g') :
    ∀ x ∈ init, ∃ ort, x.1 = SpeicherAkteur.initial ort := by
  cases h with
  | ohne _ => intro x hx; cases hx
  | erste _ _ _ =>
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact ⟨l.ort, rfl⟩

theorem speicherfolgeAkteen {Ort Wert} {anfang : Ort → Wert} {f : SpeicherAkteur Ort}
    {g g' : SpeicherGraph Ort Wert} {ls es}
    (h : Speicherfolge anfang f g ls es g') :
    ∀ x ∈ es, x.1 = f ∨ ∃ ort, x.1 = SpeicherAkteur.initial ort := by
  induction h with
  | nil g => intro x hx; cases hx
  | @cons g g0 g1 g2 l ls init esTail vor hs nach ih =>
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hxInit | hxTail
    · exact Or.inr (initialisierungAkteen vor x hxInit)
    · rw [List.mem_cons] at hxTail
      rcases hxTail with xeq | hxRest
      · left
        subst x
        rfl
      · exact ih x hxRest

/-- A single outside label appends only its own event and an optional initial write. -/
theorem speicherfolgeEinzel {Ort Wert} {anfang : Ort → Wert} {f : SpeicherAkteur Ort}
    {g g' : SpeicherGraph Ort Wert} {l : Speicher.Etikett Ort Wert} {es}
    (h : Speicherfolge anfang f g [l] es g') :
    ∀ x ∈ es, (∃ ort, x.1 = SpeicherAkteur.initial ort) ∨ x = (f, l) := by
  cases h with
  | cons g0 g1 g2 l ls init esTail vor hs nach =>
    cases nach
    intro x hx
    change x ∈ init ++ [(f, l)] at hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Or.inl (initialisierungAkteen vor x hx)
    · exact Or.inr rfl

/-- **One actor in the event list**: every memory access recorded in the graph was appended by
    the entry context. This is the list form of the premise of `rennenAusEinemKontext`. -/
def EinAkt {Ort Wert : Type} (g : SpeicherGraph Ort Wert) (c : Kontext) : Prop :=
  ∀ x ∈ g.ev, (x.lab.art.liest ∨ x.lab.art.schreibt) →
    (∀ ort, x.kontext ≠ SpeicherAkteur.initial ort) → x.kontext = .kontext c

theorem einAktIndex {Ort Wert : Type} {g : SpeicherGraph Ort Wert} {c : Kontext}
    (h : EinAkt g c) :
    ∀ i (hi : i < g.ev.length), AusgefuehrterZugriff g ⟨i, hi⟩ →
      (g.ev[i]'hi).kontext = .kontext c := by
  intro i hi zg
  unfold AusgefuehrterZugriff at zg
  exact h (g.ev[i]'hi) (List.getElem_mem _) zg.1 (by
    intro ort eq
    rw [eq] at zg
    exact zg.2)

theorem einAktRennen {g : SpeicherGraph Zelle Int} (h : Gabbro.Core.Speicher.Zustand.Erreichbar g)
    (ein : EinAkt g eintritt) : RennenImGraph g :=
  rennenAusEinemKontext h (einAktIndex ein)

/-- A catalogue event adds no executed access, so it keeps the one-actor property. -/
theorem einAktBeiAussen {Ort Wert} {initial : Ort → Wert} {vor nach : SpeicherGraph Ort Wert}
    {label : Speicher.Etikett Ort Wert} {spur : SpeicherSpur Ort Wert}
    (istAussen : label.art = .aussen)
    (folge : Speicherfolge initial (.aussen : SpeicherAkteur Ort) vor [label] spur nach)
    (vorEin : EinAkt vor eintritt) : EinAkt nach eintritt := by
  have evEq := folge.viele.ev
  intro x hx memLab nichtInitial
  rw [evEq] at hx
  rcases List.mem_append.mp hx with hxAlt | hxNeu
  · exact vorEin x hxAlt memLab nichtInitial
  · rcases List.mem_map.mp hxNeu with ⟨pair, hpair, rfl⟩
    rcases speicherfolgeEinzel folge pair hpair with ⟨ort, hinit⟩ | heq
    · exact False.elim (nichtInitial ort hinit)
    · have artAus : pair.2.art = .aussen := by rw [heq, istAussen]
      rw [artAus] at memLab
      simp only [Speicher.Art.liest, Speicher.Art.schreibt] at memLab
      exact False.elim memLab

/-- A class-good step keeps the one-actor property: either its context has no arrival regions
    and the graph is unchanged, or it is the entry context and every new access is booked there. -/
theorem einAktBeiKontext (p : Fragment) (platform : Plattform) (f : Befehl) (hgut : f.Klassengut)
    {t : Nat} {c : Kontext} {s u : Zustand} {w : PUnit} {plan : Plan}
    {spur : SchrittSpur Zelle Int} {s' : Zustand}
    (impl : ((system p.code).regel f).impl c s w [plan] u)
    (aus : FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s')
    (vorEin : EinAkt s.graph eintritt)
    (vorAnk : ∀ d, d ≠ eintritt → (s.lokal d).arrivalRegions = []) :
    EinAkt s'.graph eintritt := by
  by_cases leer : (s.lokal c).arrivalRegions = []
  · have graphEq := quellSchrittGraphGleich p platform f hgut leer impl aus
    intro x hx memLab nichtInitial
    rw [graphEq] at hx
    exact vorEin x hx memLab nichtInitial
  · have hcein : c = eintritt := by
      by_contra hne
      exact leer (vorAnk c hne)
    subst c
    obtain ⟨_, _, _, _, _, folge, _⟩ := aus
    have evEq := folge.viele.ev
    intro x hx memLab nichtInitial
    rw [evEq] at hx
    rcases List.mem_append.mp hx with hxAlt | hxNeu
    · exact vorEin x hxAlt memLab nichtInitial
    · rcases List.mem_map.mp hxNeu with ⟨pair, hpair, rfl⟩
      rcases speicherfolgeAkteen folge pair hpair with hf | ⟨ort, hinit⟩
      · simpa [hf]
      · exact False.elim (nichtInitial ort hinit)

/-- The arrival regions of a non-entry context stay empty across a class-good step. -/
theorem einAktAnkunft (p : Fragment) (platform : Plattform) (f : Befehl) (hgut : f.Klassengut)
    {t : Nat} {c : Kontext} {s u : Zustand} {w : PUnit} {plan : Plan}
    {spur : SchrittSpur Zelle Int} {s' : Zustand}
    (impl : ((system p.code).regel f).impl c s w [plan] u)
    (aus : FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s')
    (vorAnk : ∀ d, d ≠ eintritt → (s.lokal d).arrivalRegions = []) :
    ∀ d, d ≠ eintritt → (s'.lokal d).arrivalRegions = [] := by
  obtain ⟨_, _, _, _, aktion, _, zustand⟩ := aus
  have still : plan.aktion.Still := Befehl.impl_aktion_still f (w := w) (c := c) (s := s) (p := plan) (u := u) impl
  have hstill := FuehrtAus.still_erhaelt aktion still
  intro d hd
  rw [zustand, hstill.2.2.1]
  have hu := quellImplArrivalGleich p f hgut impl d
  rw [hu]
  exact vorAnk d hd

/-- The run invariant of a source unit: reachable graph, one actor, and no arrival regions
    outside the entry context. -/
def QuellSchnitt (p : Fragment) (platform : Plattform) (s : Zustand) : Prop :=
  Gabbro.Core.Speicher.Zustand.Erreichbar s.graph ∧ EinAkt s.graph eintritt ∧
    ∀ c, c ≠ eintritt → (s.lokal c).arrivalRegions = []

/-- The loader of a source unit starts at the empty graph and grants arrival regions only to
    the entry context. -/
theorem quellStartSchnitt (p : Fragment) (platform : Plattform) (H : Katalog.Umgebung) (start : AussenStart)
    {s : Zustand}
    (h : (p.einheit platform).laden start (H.lade (p.einheit platform).bild) = some s) :
    QuellSchnitt p platform s := by
  simp only [Fragment.einheit, Ast.Semantik.laden] at h
  split at h
  · cases h
    refine ⟨?_, ?_, ?_⟩
    · change Gabbro.Core.Speicher.Zustand.Erreichbar Gabbro.Core.Speicher.Zustand.leer
      exact Gabbro.Core.Speicher.Zustand.Erreichbar.start
    · intro x hx
      change x ∈ ([] : List (Speicher.Ereignis (SpeicherAkteur Zelle) Zelle Int)) at hx
      cases hx
    · intro c hc
      simp only [Zustand.start, startdaten, if_neg hc]
  · cases h

/-- A context step of a class-good fragment preserves the run invariant. -/
theorem quellKontextSchnitt (p : Fragment) (platform : Plattform) (klassenrein : p.KlassenRein)
    {t : Nat} {c : Kontext} {vor u : Zustand} {plan : Plan} {w : PUnit}
    {spur : SchrittSpur Zelle Int} {nach : Zustand}
    (f : Befehl) (head : (system p.code).kopf vor c = some f)
    (impl : ((system p.code).regel f).impl c vor w [plan] u)
    (aus : FuehrtSchrittAus (p.einheit platform).einrichtung t c vor u plan spur nach)
    (vorher : QuellSchnitt p platform vor) :
    QuellSchnitt p platform nach := by
  have hgut := klassenrein f (kopf_mem head)
  refine ⟨(FuehrtSchrittAus.viele (p.einheit platform).einrichtung aus).erreichbar vorher.1, ?_, ?_⟩
  · exact einAktBeiKontext p platform f hgut impl aus vorher.2.1 vorher.2.2
  · exact einAktAnkunft p platform f hgut impl aus vorher.2.2

/-- **The race invariant of every cut of a run of a source unit.** -/
theorem quellLaufRennen (p : Fragment) (platform : Plattform) (klassenrein : p.KlassenRein)
    (H : Katalog.Umgebung) (ρ : Sicherheit.Lauf (p.sicherheitsEinheit platform))
    (lauf : Laeufe (p.einheit platform) H ρ) :
    ∀ t s, ρ.zeit.zustand t = some s → RennenImGraph s.graph := by
  have schnitte (t : Nat) : ∀ s, ρ.zeit.zustand t = some s → QuellSchnitt p platform s := by
    induction t with
    | zero =>
      intro s anfang
      exact quellStartSchnitt p platform H ρ.start
        (lauf.2.2.2.symm.trans anfang)
    | succ t ih =>
      intro s nachher
      cases ρ.zeit.takt t with
      | wartet _label gleich _pause =>
        exact ih s (gleich.symm.trans nachher)
      | schritt _label step =>
        rw [nachher] at step
        cases vorher : ρ.zeit.zustand t with
        | none =>
          rw [vorher] at step
          cases step
        | some vor =>
          rw [vorher] at step
          cases step with
          | schritt h =>
            cases h with
            | kontext _ _ regel aus =>
              obtain ⟨f, head, impl⟩ := regel
              exact quellKontextSchnitt p platform klassenrein f head impl aus (ih vor vorher)
            | antwort _ h =>
              have erreichbar := (AntwortSchritt.viele (p.einheit platform).einrichtung h).erreichbar (ih vor vorher).1
              have aexists : ∃ a : AntwortEreignis, spur.aussen = [.antwort a] := by
                simpa using h.2.1
              obtain ⟨a, _⟩ := aexists
              have folge := h.2.2.1
              have ziel := h.2.2.2
              refine ⟨erreichbar, ?_, ?_⟩
              · exact einAktBeiAussen (label := aussenEtikett (p.einheit platform).einrichtung (.antwort a)) rfl folge (ih vor vorher).2.1
              · intro d hd
                rw [ziel]
                exact (ih vor vorher).2.2 d hd
            | interrupt _ h =>
              have erreichbar := (UnterbrechungsSchritt.viele (p.einheit platform).einrichtung h).erreichbar (ih vor vorher).1
              obtain ⟨k0, irq, _, _, _, _, _, _, _, folge, ziel⟩ := h
              refine ⟨erreichbar, ?_, ?_⟩
              · exact einAktBeiAussen (label := aussenEtikett (p.einheit platform).einrichtung (.interrupt k0 irq .handler)) rfl folge (ih vor vorher).2.1
              · intro d hd
                rw [ziel]
                exact (ih vor vorher).2.2 d hd
            | absturz h =>
              obtain ⟨_, _, pers, crash, rfl⟩ := h
              refine ⟨?_, ?_, ?_⟩
              · change Gabbro.Core.Speicher.Zustand.Erreichbar Gabbro.Core.Speicher.Zustand.leer
                exact Gabbro.Core.Speicher.Zustand.Erreichbar.start
              · intro x hx
                change x ∈ ([] : List (Speicher.Ereignis (SpeicherAkteur Zelle) Zelle Int)) at hx
                cases hx
              · intro d hd
                simp [Zustand.wiederanlauf, Zustand.start, Fragment.sicherheitsEinheit,
                  Fragment.einheit, einrichtung, startdaten, hd]
  intro t s anfang
  exact einAktRennen (schnitte t s anfang).1 (schnitte t s anfang).2.1

/-- **The pinned safety statement of a source unit with an access instruction.** The checker
    verdict supplies the loader, restart and per-command premises; the class legs, the invariant
    leg and the one-context run race close the four safety legs. -/
theorem zugriffSicherBeweis : ZugriffSicherAussage := by
  intro p platform ps quell zugriff tab ok H ρ lauf
  let E := p.sicherheitsEinheit platform
  have grenzen : GrenzenSicher E := fragmentGrenzen platform tab
    (pruefeEinheit_start p ps ok) (pruefeEinheit_neustart p ps ok)
  have okAll : ∀ b ∈ p.code, pruefeBefehlErhalt ps b = true := by
    intro b hmem
    exact pruefeEinheit_befehl p ps b hmem ok
  have regeln : ∀ f, RegelPflichtenOhneRennen E f :=
    fragmentRegelPflichtenOhneRennen p platform ps zugriff.1 tab okAll
  have rennen : ∀ t s, ρ.zeit.zustand t = some s → RennenImGraph s.graph :=
    quellLaufRennen p platform zugriff.1 H ρ lauf
  exact sicherheit_aus_regeln_ohne_rennen grenzen regeln H ρ rennen lauf

end Gabbro.Core.Ast.Semantik
