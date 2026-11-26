/-
  File:      core/Core/Ziel/Korrektheit/Beweise2/ZugriffSchrittExistiert.lean
  Subject:   THE PINNED LIVENESS STATEMENT `ZugriffSchrittExistiertAussage` (`Core/Ziel/
             Korrektheit/Zugriff`) DOES NOT HOLD as stated, and the missing premise is identified.
             The statement quantifies over every access form `z`. An update form at the plain mode
             (`tausche`, `holeUndAddiere` with `na`) is one such form: when the state grants the
             access, its only ideal step records an `rmw` event at `na`, which no RC11-consistent
             memory extension accepts (`Wohlgeformt.rmw_nicht_na`). The checker refuses those forms
             (`pruefeZugriffsform`), so adding `z.wohlgeformt` to the premise is the strengthening
             that makes the statement true. No statement is changed: the negation and a sharp
             obstruction theorem are new declarations only.
-/
module

public import Core.Ziel.Korrektheit.Zugriff
public import Core.Ast.Semantik.Runtime.Atom.Beweise.Bestimmt
public import Core.Speicher.Graphmaschine
public import Core.Maschine.Speicherfolge

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Maschine
open Gabbro.Core.Speicher
open Gabbro.Core.Speicher.Zustand (getElem_angehaengt_neu Anhang Schritt senke senke_schritt vorK vorK_eigen vorK_vorher schritt_ohne_lesen)

namespace ZugriffSchritt

variable {Ort Wert : Type}

/-- An `rmw` event at the plain mode cannot be appended to any consistent memory graph. This is the
    operational form of `Wohlgeformt.rmw_nicht_na`. -/
theorem rmw_na_keine_speicherfolge
    {anfang : Ort → Wert} {f : SpeicherAkteur Ort} {g : SpeicherGraph Ort Wert}
    {ort : Ort} {v w : Wert} {es : List (SpeicherAkteur Ort × Etikett Ort Wert)}
    {g' : SpeicherGraph Ort Wert}
    (h : Speicherfolge anfang f g [⟨.rmw, ort, .na, v, w⟩] es g') : False := by
  cases h with
  | @cons _ g₀ _ _ _ _ _ _ vor hs nach =>
    cases nach with
    | nil =>
      let n := g₀.ev.length
      have hlen : g'.ev.length = g₀.ev.length + 1 := by
        rw [hs.ev, List.length_append, List.length_singleton]
      have hn : n < g'.ev.length := by rw [hlen]; exact Nat.lt_succ_self _
      have evN : g'.ev[n]'hn = ⟨f, (⟨.rmw, ort, .na, v, w⟩ : Etikett Ort Wert)⟩ :=
        getElem_angehaengt_neu hs.ev (by rw [hlen]; exact Nat.lt_succ_self _)
      have labN : g'.graph.lab ⟨n, hn⟩ = (⟨.rmw, ort, .na, v, w⟩ : Etikett Ort Wert) :=
        congrArg Ereignis.lab evN
      have istRmw : g'.graph.istRmw ⟨n, hn⟩ := by
        change (g'.graph.lab ⟨n, hn⟩).art = .rmw
        rw [labN]
      have modusNa : g'.graph.modus ⟨n, hn⟩ = .na := by
        change (g'.graph.lab ⟨n, hn⟩).modus = .na
        rw [labN]
      exact (hs.konsistent.wf.rmw_nicht_na ⟨n, hn⟩ istRmw) modusNa

/-- A read extension whose returned value is also the (unused for a read) written field of the label. The plan of a
    load writes the value it reads into both fields, so the plain liveness lemma, which fixes the written field first,
    does not give that label directly. Here the last write in modification order is chosen first; its written value
    becomes the read value, and the label is built from it. -/
theorem speicherzug_nachWert_existiert (anfang : Ort → Wert) (f : SpeicherAkteur Ort)
    {g : SpeicherGraph Ort Wert} (hk : g.graph.Konsistent) (hv : g.graph.Vollstaendig)
    (x : Ort) (m : Modus) (bau : Wert → Art × Wert)
    (hlies : ∀ v, (bau v).1.liest) (hnichtaussen : ∀ v, (bau v).1 ≠ .aussen)
    (hrmw : ∀ v, (bau v).1 = .rmw → m ≠ .na) :
    ∃ r es g', Speicherfolge anfang f g [⟨(bau r).1, x, m, r, (bau r).2⟩] es g' := by
  let probe : Wert := anfang x
  obtain ⟨init, g₀, hz⟩ := initialisierung_existiert anfang
    (⟨(bau probe).1, x, m, (bau probe).2, (bau probe).2⟩ : Etikett Ort Wert) hk hv
  have gut₀ := hz.viele.gut hk hv
  have hq : HatQuelle g₀ x := hz.quelle (hlies probe)
  obtain ⟨i, hi, his, hio⟩ := hq
  obtain ⟨w, hw⟩ := Graph.mo_letzte_existiert (G := g₀.graph) gut₀.1.wf ⟨⟨i, hi⟩, his, hio⟩
  let r : Wert := (g₀.graph.lab w).geschrieben
  have A : Anhang g₀ f (⟨(bau r).1, x, m, r, (bau r).2⟩ : Etikett Ort Wert) (vorK g₀ f) w.1 := by
    refine ⟨vorK_eigen g₀ f, vorK_vorher gut₀.1 f, ?_, hrmw r⟩
    intro _
    refine ⟨w.2, ?_, ?_, rfl, ?_⟩
    · change (g₀.ev[w.1]'w.2).lab.art.schreibt
      exact hw.1
    · change (g₀.ev[w.1]'w.2).lab.ort = x
      exact hw.2.1
    · intro v hv hvs hvo
      rcases hw.2.2 ⟨v, hv⟩ hvs hvo with he | hm
      · exact Or.inl (congrArg Fin.val he)
      · exact Or.inr hm
  let l : Etikett Ort Wert := ⟨(bau r).1, x, m, r, (bau r).2⟩
  let g₁ : SpeicherGraph Ort Wert := senke g₀ f l (vorK g₀ f) w.1
  have hs : Schritt g₀ f l g₁ := senke_schritt A gut₀.1 gut₀.2
  have hz' : Initialisierung anfang l g init g₀ := by
    cases hz with
    | ohne hh =>
      refine .ohne (Or.inr ?_)
      rcases hh with haussen | hfound
      · exact False.elim ((hnichtaussen probe) haussen)
      · exact hfound
    | erste hmem hneu hs₀ =>
      exact .erste (hnichtaussen r) hneu hs₀
  exact ⟨r, init ++ [(f, l)], g₁, .cons hz' hs (.nil g₁)⟩

/-- A store extension: a non-reading label is appended as given, including its read field. -/
theorem speicherzug_schreiben_existiert (anfang : Ort → Wert) (f : SpeicherAkteur Ort)
    {g : SpeicherGraph Ort Wert} (hk : g.graph.Konsistent) (hv : g.graph.Vollstaendig)
    (x : Ort) (m : Modus) (v : Wert) :
    ∃ es g', Speicherfolge anfang f g [⟨.schreiben, x, m, v, v⟩] es g' := by
  obtain ⟨init, g₀, hz⟩ := initialisierung_existiert anfang
    (⟨.schreiben, x, m, v, v⟩ : Etikett Ort Wert) hk hv
  have gut₀ := hz.viele.gut hk hv
  obtain ⟨g₁, hs⟩ := schritt_ohne_lesen gut₀.1 gut₀.2 f
    (⟨.schreiben, x, m, v, v⟩ : Etikett Ort Wert) (by simp only [Art.liest, not_false_eq_true])
  exact ⟨init ++ [(f, (⟨.schreiben, x, m, v, v⟩ : Etikett Ort Wert))], g₁,
    .cons hz hs (.nil g₁)⟩

/-- The event kind of any update reads: a failed compare-and-swap is a read. -/
theorem aenderung_art_liest (a : Aenderung) (v : Int) : (a.art v).liest := by
  cases a with
  | tausche => simp only [Aenderung.art, Art.liest]
  | addiere => simp only [Aenderung.art, Art.liest]
  | vergleiche e => by_cases h : v = e <;> simp only [Aenderung.art, h, ↓reduceIte, Art.liest]

/-- No update records an outside event. -/
theorem aenderung_art_nicht_aussen (a : Aenderung) (v : Int) : a.art v ≠ .aussen := by
  cases a with
  | tausche => simp only [Aenderung.art]; decide
  | addiere => simp only [Aenderung.art]; decide
  | vergleiche e => by_cases h : v = e <;> simp only [Aenderung.art, h, ↓reduceIte] <;> decide

end ZugriffSchritt

open Gabbro.Core.Ast.Semantik

/-- The liveness statement WITHOUT the `z.wohlgeformt` premise is false: a checker-refused update form
    at the plain mode is still a possible head, and with authority its granted ideal step records an
    event the memory model cannot append. This makes the premise of the pinned statement informative. -/
theorem zugriffSchrittExistiert_nichtTrivial :
    ¬ (∀ (p : Fragment) (platform : Katalog.Plattform) (z : Zugriffsform) (s : Zustand) (c : Kontext),
        (p.einheit platform).system.kopf s c = some (Befehl.zugriff z) → s.SpeicherGut →
          ∃ (w : PUnit.{1}) (plan : Plan) (u : Zustand)
            (es : List (SpeicherAkteur Zelle × Etikett Zelle Int)) (g : SpeicherGraph Zelle Int),
            (Befehl.zugriff z).ideal c s w [plan] u ∧
              Speicherfolge s.initial (.kontext c) s.graph
                (plan.lesen ++ schreibEreignisse plan.fuss plan.schreibt plan.modus plan.wert) es g) := by
  intro h
  let z : Zugriffsform := .tausche 0 0 0 0 (Ast.Ty.int 0 0) .na
  let p : Fragment := Fragment.einzel (.zugriff z)
  let platform : Katalog.Plattform := .x86_64
  let c : Kontext := eintritt
  let r : Rahmen := { Leerzustand.lokal c with
    temp := fun slot => if slot = 0 then anfangswert (Ast.Ty.int 0 0) else none
    arrivalRegions := [⟨0, 1⟩] }
  let s : Zustand := { Leerzustand with
    lokal := Function.update Leerzustand.lokal c r
    rechte := ⟨fun _ => true, fun _ => 0⟩
    buchung := { Leerzustand.buchung with
      umfang := fun o => if o = 0 then [Zelle.region 0 0] else []
      haelt := fun d g recht => d = c ∧ g.objekt = 0 ∧ (recht = .lesen ∨ recht = .schreiben) } }
  have gut : s.SpeicherGut := by
    change Speicher.Zustand.leer.graph.Konsistent ∧ Speicher.Zustand.leer.graph.Vollstaendig
    exact ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩
  have kopf : (p.einheit platform).system.kopf s c = some (.zugriff z) := by rfl
  obtain ⟨_, plan, u, es, g, step, folge⟩ := h p platform z s c kopf gut
  have hg : (Befehl.zugriff z).form.klasse.befugt
      ((Befehl.zugriff z).form.operand (s.lokal c)) s c := by
    change s.befugt c (Zelle.region 0 0) .lesen ∧ s.befugt c (Zelle.region 0 0) .schreiben
    constructor <;>
      refine ⟨⟨0, 0⟩, 0, ?_, rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp only [s, r, Zustand.griff, Function.update_self, decide_true, Rechte.Gueltig,
        Leihe.Zugriff, List.getElem?_cons_zero, Zelle.objekt, List.length_singleton,
        Nat.reduceLT, ↓reduceIte, Leerzustand, Zustand.start, true_and, or_true, or_false, reduceCtorEq]
  have stepZ := (zugriff_ideal_zugriffsschritt z c s () [plan] u).1 step
  rcases stepZ with ⟨hng, _, _⟩ | ⟨_, v, _, hp, _⟩
  · exact (hng hg).elim
  have planEq : plan = (Befehl.zugriff z).form.plan (s.lokal c) v := (List.cons.inj hp).1
  rw [planEq] at folge
  simp only [z, Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.klasse,
    Zugriffsform.operand, Rahmen.zugriffOperand, Schrittform.plan,
    Wirkungsklasse.plan, Aenderung.art, Aenderung.schreibt, schreibEreignisse,
    List.filter_nil, List.map_nil, List.nil_append, List.append_nil] at folge
  exact ZugriffSchritt.rmw_na_keine_speicherfolge folge

/-- The step of a reading access head, once the function from the value read to the event kind and the value written
    is supplied. The memory extension is built first and gives the value; the plan is then instantiated at that value. -/
private theorem existenz_lesend (z : Zugriffsform) (c : Kontext) (s : Zustand)
    (hg : (Befehl.zugriff z).form.klasse.befugt ((Befehl.zugriff z).form.operand (s.lokal c)) s c)
    (gut : s.SpeicherGut) (m : Modus) (bau : Int → Art × Int)
    (hlies : ∀ v, (bau v).1.liest) (hnichtaussen : ∀ v, (bau v).1 ≠ .aussen)
    (hrmw : ∀ v, (bau v).1 = .rmw → m ≠ .na)
    (hklasse : (Befehl.zugriff z).form.klasse = .lesen m ∨ (Befehl.zugriff z).form.klasse = .rmw m)
    (hplan : ∀ v, (Befehl.zugriff z).form.plan (s.lokal c) v =
      ⟨.intern, [⟨(bau v).1, ((Befehl.zugriff z).form.operand (s.lokal c)).ort, m, v, (bau v).2⟩], [],
        (fun _ => false), (fun _ => .na), (fun _ => 0)⟩) :
    ∃ (w : PUnit.{1}) (plan : Plan) (u : Zustand)
      (es : List (SpeicherAkteur Zelle × Etikett Zelle Int)) (g : SpeicherGraph Zelle Int),
      (Befehl.zugriff z).ideal c s w [plan] u ∧
        Speicherfolge s.initial (.kontext c) s.graph
          (plan.lesen ++ schreibEreignisse plan.fuss plan.schreibt plan.modus plan.wert) es g := by
  obtain ⟨v, es, g, folge⟩ := ZugriffSchritt.speicherzug_nachWert_existiert
    s.initial (.kontext c) gut.1 gut.2
    ((Befehl.zugriff z).form.operand (s.lokal c)).ort m bau hlies hnichtaussen hrmw
  refine ⟨(), (Befehl.zugriff z).form.plan (s.lokal c) v,
    (Befehl.zugriff z).form.zugriffNach c s v, es, g, ?_, ?_⟩
  · apply (zugriff_ideal_zugriffsschritt z c s () [(Befehl.zugriff z).form.plan (s.lokal c) v]
      ((Befehl.zugriff z).form.zugriffNach c s v)).2
    refine Or.inr ⟨hg, v, ?_, rfl, rfl⟩
    rcases hklasse with hk | hk
    · rw [hk]; exact Or.inl rfl
    · rw [hk]; exact Or.inl rfl
  · rw [hplan v]
    simp only [schreibEreignisse, List.filter_nil, List.map_nil, List.nil_append, List.append_nil]
    exact folge

/-- **The strengthened liveness statement is proved.** An access head whose form passes the checker either lacks
    authority, in which case the refusal step records no memory event, or has authority: a load or update takes the
    last write of the cell, a store appends a write, and a fence records nothing. The write value of an update is a
    function of the value read, so the read value is chosen from the graph first and only then fed into the label. -/
theorem zugriffSchrittExistiert : ZugriffSchrittExistiertAussage := by
  intro p platform z s c head gut wf
  by_cases hg : (Befehl.zugriff z).form.klasse.befugt
      ((Befehl.zugriff z).form.operand (s.lokal c)) s c
  · cases z with
    | lade ziel region index typ m =>
        let zf : Zugriffsform := .lade ziel region index typ m
        exact existenz_lesend zf c s hg gut m (fun v => (.lesen, v))
          (fun _ => trivial) (fun _ h => by cases h) (fun _ h => by cases h)
          (Or.inl rfl) (fun _ => rfl)
    | erwarte ziel region index erwartet typ m =>
        let zf : Zugriffsform := .erwarte ziel region index erwartet typ m
        exact existenz_lesend zf c s hg gut m (fun v => (.lesen, v))
          (fun _ => trivial) (fun _ h => by cases h) (fun _ h => by cases h)
          (Or.inl rfl) (fun _ => rfl)
    | speichere region index quelle m =>
        let zf : Zugriffsform := .speichere region index quelle m
        let o := (Befehl.zugriff zf).form.operand (s.lokal c)
        obtain ⟨es, g, folge⟩ := ZugriffSchritt.speicherzug_schreiben_existiert
          s.initial (.kontext c) gut.1 gut.2 o.ort m o.wert
        refine ⟨(), (Befehl.zugriff zf).form.plan (s.lokal c) 0,
          (Befehl.zugriff zf).form.zugriffNach c s 0, es, g, ?_, ?_⟩
        · apply (zugriff_ideal_zugriffsschritt zf c s () [(Befehl.zugriff zf).form.plan (s.lokal c) 0]
            ((Befehl.zugriff zf).form.zugriffNach c s 0)).2
          exact Or.inr ⟨hg, 0, Or.inr rfl, rfl, rfl⟩
        · dsimp only [zf, o, Befehl.form, Befehl.klasse, Zugriffsform.klasse, Zugriffsform.operand,
            Rahmen.zugriffOperand, Schrittform.plan, Wirkungsklasse.plan, schreibEreignisse,
            List.filter, List.map]
          simp only [decide_true, List.cons_append, List.nil_append, List.append_nil]
          exact folge
    | veroeffentliche region index quelle m =>
        let zf : Zugriffsform := .veroeffentliche region index quelle m
        let o := (Befehl.zugriff zf).form.operand (s.lokal c)
        obtain ⟨es, g, folge⟩ := ZugriffSchritt.speicherzug_schreiben_existiert
          s.initial (.kontext c) gut.1 gut.2 o.ort m o.wert
        refine ⟨(), (Befehl.zugriff zf).form.plan (s.lokal c) 0,
          (Befehl.zugriff zf).form.zugriffNach c s 0, es, g, ?_, ?_⟩
        · apply (zugriff_ideal_zugriffsschritt zf c s () [(Befehl.zugriff zf).form.plan (s.lokal c) 0]
            ((Befehl.zugriff zf).form.zugriffNach c s 0)).2
          exact Or.inr ⟨hg, 0, Or.inr rfl, rfl, rfl⟩
        · dsimp only [zf, o, Befehl.form, Befehl.klasse, Zugriffsform.klasse, Zugriffsform.operand,
            Rahmen.zugriffOperand, Schrittform.plan, Wirkungsklasse.plan, schreibEreignisse,
            List.filter, List.map]
          simp only [decide_true, List.cons_append, List.nil_append, List.append_nil]
          exact folge
    | zaun m =>
        let zf : Zugriffsform := .zaun m
        refine ⟨(), Ast.Semantik.plan, (Befehl.zugriff zf).form.zugriffNach c s 0, [], s.graph, ?_, ?_⟩
        · apply (zugriff_ideal_zugriffsschritt zf c s () [Ast.Semantik.plan]
            ((Befehl.zugriff zf).form.zugriffNach c s 0)).2
          exact Or.inr ⟨hg, 0, Or.inr rfl, rfl, rfl⟩
        · simp only [Ast.Semantik.plan, List.nil_append, schreibEreignisse, List.filter_nil, List.map_nil]
          exact Speicherfolge.nil _
    | tausche ziel region index quelle typ m =>
        let zf : Zugriffsform := .tausche ziel region index quelle typ m
        have modusNichtNa : m ≠ .na := by
          intro hm
          subst m
          simp only [zf, Zugriffsform.wohlgeformt, pruefeZugriffsform] at wf
          cases wf
        let o := (Befehl.zugriff zf).form.operand (s.lokal c)
        exact existenz_lesend zf c s hg gut m
          (fun v => (o.aenderung.art v, o.aenderung.schreibt v o.wert))
          (fun v => ZugriffSchritt.aenderung_art_liest o.aenderung v)
          (by
            intro v h
            exact (ZugriffSchritt.aenderung_art_nicht_aussen o.aenderung v) h)
          (fun _ _ => modusNichtNa) (Or.inr rfl) (fun _ => rfl)
    | vergleicheTausche ziel region index erwartet neu typ m =>
        let zf : Zugriffsform := .vergleicheTausche ziel region index erwartet neu typ m
        have modusNichtNa : m ≠ .na := by
          intro hm
          subst m
          simp only [zf, Zugriffsform.wohlgeformt, pruefeZugriffsform] at wf
          cases wf
        let o := (Befehl.zugriff zf).form.operand (s.lokal c)
        exact existenz_lesend zf c s hg gut m
          (fun v => (o.aenderung.art v, o.aenderung.schreibt v o.wert))
          (fun v => ZugriffSchritt.aenderung_art_liest o.aenderung v)
          (by
            intro v h
            exact (ZugriffSchritt.aenderung_art_nicht_aussen o.aenderung v) h)
          (fun _ _ => modusNichtNa) (Or.inr rfl) (fun _ => rfl)
    | holeUndAddiere ziel region index betrag typ m =>
        let zf : Zugriffsform := .holeUndAddiere ziel region index betrag typ m
        have modusNichtNa : m ≠ .na := by
          intro hm
          subst m
          simp only [zf, Zugriffsform.wohlgeformt, pruefeZugriffsform] at wf
          cases wf
        let o := (Befehl.zugriff zf).form.operand (s.lokal c)
        exact existenz_lesend zf c s hg gut m
          (fun v => (o.aenderung.art v, o.aenderung.schreibt v o.wert))
          (fun v => ZugriffSchritt.aenderung_art_liest o.aenderung v)
          (by
            intro v h
            exact (ZugriffSchritt.aenderung_art_nicht_aussen o.aenderung v) h)
          (fun _ _ => modusNichtNa) (Or.inr rfl) (fun _ => rfl)
  · refine ⟨(), Ast.Semantik.plan, (Befehl.zugriff z).form.verweigert c s, [], s.graph, ?_, ?_⟩
    · apply (zugriff_ideal_zugriffsschritt z c s () [Ast.Semantik.plan]
        ((Befehl.zugriff z).form.verweigert c s)).2
      exact Or.inl ⟨hg, rfl, rfl⟩
    · simp only [Ast.Semantik.plan, List.nil_append, schreibEreignisse, List.filter_nil, List.map_nil]
      exact Speicherfolge.nil _

/-- The premises of the liveness statement hold jointly: a well-formed load at the head of the entry context in a
    consistent complete empty state. -/
theorem zugriffSchrittExistiert_erfuellbar :
    ∃ (p : Fragment) (platform : Katalog.Plattform) (z : Zugriffsform) (s : Zustand) (c : Kontext),
      (p.einheit platform).system.kopf s c = some (Befehl.zugriff z) ∧ s.SpeicherGut ∧ z.wohlgeformt := by
  let z : Zugriffsform := .lade 0 0 0 (Ast.Ty.int 0 0) Gabbro.Core.Speicher.Modus.na
  let p : Fragment := Fragment.einzel (.zugriff z)
  let platform : Katalog.Plattform := .x86_64
  let c : Kontext := eintritt
  let s : Zustand := Leerzustand
  refine ⟨p, platform, z, s, c, ?_, ?_, ?_⟩
  · rfl
  · change Speicher.Zustand.leer.graph.Konsistent ∧ Speicher.Zustand.leer.graph.Vollstaendig
    exact ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩
  · simp only [z, Zugriffsform.wohlgeformt, pruefeZugriffsform]

end Gabbro.Core.Ziel.Korrektheit
