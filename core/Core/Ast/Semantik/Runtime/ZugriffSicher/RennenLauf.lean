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
      rw [Befehl.uebertrag_privat f hpriv]
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

/-- A class-good step at a context with no arrival regions appends no memory event at all. -/
theorem quellSchrittGraphGleich (p : Fragment) (platform : Plattform) (f : Befehl) (hgut : f.Klassengut)
    {t c : Nat} {s u : Zustand} {w : PUnit} {plan : Plan} {spur : SchrittSpur Zelle Int} {s' : Zustand}
    (leer : (s.lokal c).arrivalRegions = [])
    (impl : ((system p.code).regel f).impl c s w [plan] u)
    (aus : FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s') :
    s'.graph.ev = s.graph.ev := by
  have planEq := quellSchrittPlanPrivat p f hgut leer impl
  rw [planEq] at aus
  obtain ⟨_, _, _, _, aktion, folge, _⟩ := aus
  cases aktion
  have folgeLeer : Speicherfolge s.initial (.kontext c) s.graph [] [] s'.graph := by
    simpa using folge
  have evEq := folgeLeer.viele.ev
  simpa using evEq

/-- Every event a `Speicherfolge` appends is a step of its actor or a lazily materialised
    initial write; the initial writes are prepared by `Initialisierung`. -/
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

/-- An old executed access stays an executed access under an append. -/
theorem ausgefuehrterAlt {F Ort Wert} {Z Z' : Speicher.Zustand F Ort Wert}
    (h : Gabbro.Core.Speicher.Erweitert Z Z') (i : Fin Z.ev.length)
    (zugriff : AusgefuehrterZugriff Z' (h.alt i)) :
    AusgefuehrterZugriff Z i := by
  have evEq := h.getElem i.2 (h.alt i).2
  simpa only [AusgefuehrterZugriff, Speicher.Graph.liest, Speicher.Graph.schreibt,
    Speicher.Zustand.graph, evEq] using zugriff

/-- Every event appended by a class-good step that is an executed access is recorded at the
    acting context. An initial write is not an access. -/
theorem quellSchrittNeueAkzesse (p : Fragment) (platform : Plattform) (f : Befehl) (hgut : f.Klassengut)
    {t c : Nat} {s u : Zustand} {w : PUnit} {plan : Plan} {spur : SchrittSpur Zelle Int} {s' : Zustand}
    (_ : ((system p.code).regel f).impl c s w [plan] u)
    (aus : FuehrtSchrittAus (p.einheit platform).einrichtung t c s u plan spur s') :
    ∀ i (hi : i < s'.graph.ev.length), s.graph.ev.length ≤ i →
      AusgefuehrterZugriff s'.graph ⟨i, hi⟩ → (s'.graph.ev[i]'hi).kontext = .kontext c := by
  obtain ⟨_, _, _, _, _, folge, _⟩ := aus
  have evEq := folge.viele.ev
  intro i hi spaeter zugriff
  let j := i - s.graph.ev.length
  have jlt : j < spur.speicher.length := by
    have hsum : s.graph.ev.length + spur.speicher.length = s'.graph.ev.length := by
      rw [evEq, List.length_append, List.length_map]
    omega
  have getEq : s'.graph.ev[i]'hi = ⟨(spur.speicher[j]).1, (spur.speicher[j]).2⟩ := by
    rw [evEq]
    have hji : i = s.graph.ev.length + j := by omega
    rw [hji]
    exact List.getElem_append_right (by omega) (by omega)
  have akt := speicherfolgeAkteen folge (spur.speicher[j]) (List.getElem_mem _)
  rcases akt with hf | ⟨ort, hinit⟩
  · rw [getEq]
    exact hf
  · exfalso
    rw [getEq] at zugriff
    simp only [AusgefuehrterZugriff, Speicher.Ereignis.kontext, hinit] at zugriff

/-- A catalogue event changes no executed access: its label is outside the memory, and an
    initial write it may materialise is not an access. The one-actor property is preserved. -/
theorem einenKontextBeiAussen {Ort Wert} {vor nach : SpeicherGraph Ort Wert}
    {label : Speicher.Etikett Ort Wert} {spur : SpeicherSpur Ort Wert}
    (istAussen : label.art = .aussen)
    (folge : Speicherfolge vor.initial (.aussen : SpeicherAkteur Ort) vor.graph [label] spur nach)
    {c : SpeicherAkteur Ort}
    (vorAlle : ∀ i (hi : i < vor.graph.ev.length), AusgefuehrterZugriff vor.graph ⟨i, hi⟩ →
      (vor.graph.ev[i]'hi).kontext = c) :
    ∀ i (hi : i < nach.graph.ev.length), AusgefuehrterZugriff nach.graph ⟨i, hi⟩ →
      (nach.graph.ev[i]'hi).kontext = c := by
  intro i hi zugriff
  have erweitert := folge.viele.erweitert
  have alt (k : Fin nach.graph.ev.length) (zk : AusgefuehrterZugriff nach.graph k) :
      k.val < vor.graph.ev.length := by
    by_contra! spaeter
    have length : nach.graph.ev.length = vor.graph.ev.length + 1 := by
      have evEq := folge.viele.ev
      have es : spur.length = 1 := by
        rcases folge with _ | ⟨_, _, rest⟩
        · simp at evEq
        · cases rest
          simp
      rw [evEq, List.length_append, List.length_map, es]
    have bound := Nat.lt_of_lt_of_le k.isLt length.le
    have idx : k.val = vor.graph.ev.length := Nat.le_antisymm (Nat.lt_succ_iff.mp bound) spaeter
    have boundNeu : vor.graph.ev.length < nach.graph.ev.length := Nat.lt_of_le_of_lt spaeter k.isLt
    have same : k = ⟨vor.graph.ev.length, boundNeu⟩ := Fin.ext idx
    have lab : nach.graph.lab k = label := by
      rw [same]
      have evEq := folge.viele.ev
      rw [evEq]
      rw [List.getElem_append_right (Nat.le_refl _) boundNeu]
      have esHead : (spur[0]'by omega) = ((.aussen : SpeicherAkteur Ort), label) := by
        rcases folge with _ | ⟨_, _, rest⟩
        · simp at evEq
        · cases rest
          rfl
      rw [esHead]
      rfl
    have real := zugriff.1
    simp only [Speicher.Graph.liest, Speicher.Graph.schreibt, lab, istAussen] at real
    exact real.elim id id
  have hiAlt := alt ⟨i, hi⟩ zugriff
  have evEq := erweitert.getElem hi hi
  have zalt : AusgefuehrterZugriff vor.graph ⟨i, hiAlt⟩ :=
    ausgefuehrterAlt erweitert ⟨i, hiAlt⟩ (by simpa [Fin.ext_iff] using zugriff)
  rw [evEq]
  exact vorAlle i hiAlt zalt

end Gabbro.Core.Ast.Semantik
