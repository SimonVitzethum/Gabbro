/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/Speicherfolge.lean
  Subject:   THE MEMORY LEG OF THE CLASS SAFETY DUTY (MK-03, PERFECT-MODEL §3.6). The pinned statement
             `KlassenSpeicherbeinAussage` is proved for the three classes that record a memory event
             (`lesen`, `schreiben`, `rmw`). The index lemma identifies the access inside a one-label
             `Speicherfolge`; the guard supplies `Zustand.befugt`, which books the access at that index.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Ast.Semantik.Runtime.Klasse.Sicherheit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Speicher (Etikett Modus)
open Gabbro.Core.Sicherheit (Speicherzugriff Adresse Absturz NeueWirkungen FreigabenGueltig ZugriffGebucht Wirkung)

open Classical in
/-- **The access of a one-label `Speicherfolge` sits at `zugriffsereignis`.** Unfolding
    `Speicherfolge.cons` once for the single label `l` appends one lazily materialised initial write
    (`Initialisierung`, split on `HatQuelle g l.ort`) immediately before the access `(f, l)`:
    `es = init ++ [(f, l)]`. The exact form of `init` follows from the definition: in the `ohne` case
    `init = []` and, since `l.art ≠ .aussen`, `HatQuelle g l.ort`; in the `erste` case
    `init = [(.initial l.ort, ⟨.schreiben, l.ort, l.modus, anfang l.ort, anfang l.ort⟩)]` and
    `¬ HatQuelle g l.ort`. Hence `init.length = if HatQuelle g l.ort then 0 else 1` and the access is
    at index `init.length` of `es`, i.e. at absolute event index `g.ev.length + init.length`; this equals
    `g.ev.length + (if HatQuelle g l.ort then 0 else 1)`, the value of `Zustand.zugriffsereignis` at
    the pre-state graph `g` for `z = l.ort`. -/
theorem speicherfolge_zugriffsindex {anfang : Zelle → Int} {f : SpeicherAkteur Zelle}
    {g g' : SpeicherGraph Zelle Int} {l : Etikett Zelle Int}
    {es : List (SpeicherAkteur Zelle × Etikett Zelle Int)}
    (h : Speicherfolge anfang f g [l] es g') (hneq : l.art ≠ .aussen) :
    ∃ init : List (SpeicherAkteur Zelle × Etikett Zelle Int),
      es = init ++ [(f, l)] ∧
        (init = [] ∧ HatQuelle g l.ort ∨
          init = [(.initial l.ort, ⟨.schreiben, l.ort, l.modus, anfang l.ort, anfang l.ort⟩)] ∧
            ¬ HatQuelle g l.ort) ∧
      init.length = (if HatQuelle g l.ort then 0 else 1) ∧
      es[init.length]? = some (f, l) := by
  cases h with
  | cons vor hs nach =>
    cases nach with
    | nil =>
      cases vor with
      | ohne hh =>
        have hq : HatQuelle g l.ort := by
          rcases hh with hout | hq
          · exact False.elim (hneq hout)
          · exact hq
        refine ⟨[], ?_, ?_, ?_, ?_⟩
        · simp only [List.nil_append]
        · exact Or.inl ⟨rfl, hq⟩
        · simp only [List.length_nil, hq, ite_true]
        · simp only [List.nil_append, List.length_nil, List.getElem?_cons_zero]
      | erste mem neu hsinit =>
        refine ⟨[(.initial l.ort, ⟨.schreiben, l.ort, l.modus, anfang l.ort, anfang l.ort⟩)], ?_, ?_, ?_, ?_⟩
        · simp only [List.singleton_append]
        · exact Or.inr ⟨rfl, neu⟩
        · simp only [List.length_singleton, neu, ite_false]
        · simp only [List.singleton_append, List.length_singleton, List.getElem?_cons_succ,
            List.getElem?_cons_zero]

/-- An internal protocol action records no lock events, no outside events and leaves the intermediate
    state unchanged. -/
theorem fuehrtAus_intern_nil {t : Nat} {s u : Zustand}
    {sperren : List (Etikett Zelle Int)} {aussen : List Katalog.Ereignis}
    {v : Zustand} (c : Kontext)
    (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit)
    (h : FuehrtAus e t c s u .intern sperren aussen v) :
    sperren = [] ∧ aussen = [] ∧ v = u := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- An empty label list records no event and leaves the graph unchanged. -/
theorem speicherfolge_leer {Ort Wert : Type} {anfang : Ort → Wert} {f : SpeicherAkteur Ort}
    {g : SpeicherGraph Ort Wert} {es : List (SpeicherAkteur Ort × Etikett Ort Wert)}
    {g' : SpeicherGraph Ort Wert} (h : Speicherfolge anfang f g [] es g') :
    es = [] ∧ g' = g := by
  cases h
  exact ⟨rfl, rfl⟩

open Classical in
/-- The concrete address of an authorised access satisfies `Speicherzugriff`. The ledger picks an
    address through `Zustand.adresse`; the handle it names equals the one the guard holds, because
    `Zustand.griff` is a function. A fence label never reaches this lemma (the fence class plans
    the private plan): it is neither a read nor a write. -/
theorem adresse_speicherzugriff {s : Zustand} {c : Kontext} {z : Zelle} {l : Etikett Zelle Int}
    (hneq : l.art ≠ .aussen) (hzaun : l.art ≠ .zaun) (hz : z = l.ort)
    (hBles : l.art.liest → s.befugt c z .lesen)
    (hBschr : l.art.schreibt → s.befugt c z .schreiben) :
    ∃ a : Adresse, s.adresse c z = some a ∧ Speicherzugriff s c l a := by
  have hbef : s.befugt c z .lesen ∨ s.befugt c z .schreiben := by
    cases hla : l.art with
    | lesen => exact Or.inl (hBles (by simp only [hla, Speicher.Art.liest]))
    | schreiben => exact Or.inr (hBschr (by simp only [hla, Speicher.Art.schreibt]))
    | rmw => exact Or.inl (hBles (by simp only [hla, Speicher.Art.liest]))
    | aussen => exact False.elim (hneq hla)
    | zaun => exact False.elim (hzaun hla)
  rcases hbef with hb | hb
  · obtain ⟨g, off, hg, hgo, hgu, hzug, humf, hhaelt⟩ := hb
    have hex : ∃ a : Adresse, s.griff c z = some a.griff ∧
        (s.buchung.umfang a.griff.objekt)[a.offset]? = some z := ⟨⟨g, off⟩, hg, humf⟩
    rw [Zustand.adresse, dif_pos hex]
    let a := Classical.choose hex
    have hs := Classical.choose_spec hex
    refine ⟨a, rfl, ?_⟩
    have hag : a.griff = g := Option.some.inj (hs.1.symm.trans hg)
    refine ⟨by rw [hag]; exact hgu, ?_, ?_, ?_⟩
    · rw [hs.2, hz]
    · intro hl
      obtain ⟨g', off', hg', _, _, _, _, hh'⟩ := hBles hl
      have hag' : a.griff = g' := Option.some.inj (hs.1.symm.trans hg')
      rw [hag']
      exact hh'
    · intro hl
      obtain ⟨g', off', hg', _, _, _, _, hh'⟩ := hBschr hl
      have hag' : a.griff = g' := Option.some.inj (hs.1.symm.trans hg')
      rw [hag']
      exact hh'
  · obtain ⟨g, off, hg, hgo, hgu, hzug, humf, hhaelt⟩ := hb
    have hex : ∃ a : Adresse, s.griff c z = some a.griff ∧
        (s.buchung.umfang a.griff.objekt)[a.offset]? = some z := ⟨⟨g, off⟩, hg, humf⟩
    rw [Zustand.adresse, dif_pos hex]
    let a := Classical.choose hex
    have hs := Classical.choose_spec hex
    refine ⟨a, rfl, ?_⟩
    have hag : a.griff = g := Option.some.inj (hs.1.symm.trans hg)
    refine ⟨by rw [hag]; exact hgu, ?_, ?_, ?_⟩
    · rw [hs.2, hz]
    · intro hl
      obtain ⟨g', off', hg', _, _, _, _, hh'⟩ := hBles hl
      have hag' : a.griff = g' := Option.some.inj (hs.1.symm.trans hg')
      rw [hag']
      exact hh'
    · intro hl
      obtain ⟨g', off', hg', _, _, _, _, hh'⟩ := hBschr hl
      have hag' : a.griff = g' := Option.some.inj (hs.1.symm.trans hg')
      rw [hag']
      exact hh'

/-- A step whose memory trace is the single access `(f, l)` by `f = .kontext c` books that access at
    `zugriffsereignis`: the ledger entry written by `Schrittform.buchungNach` is `vor.adresse c l.ort`,
    and `Zustand.befugt` makes it a `Speicherzugriff`. The synthetic initial write, when present, is
    justified by the access in the same trace. -/
theorem eineZugriffGebucht (vor nach : Zustand) (c : Kontext) (l : Etikett Zelle Int)
    (hneq : l.art ≠ .aussen) (f : SpeicherAkteur Zelle) (hf : f = .kontext c)
    (hfolge : Speicherfolge vor.initial f vor.graph [l] spur.speicher nach.graph)
    (hbuch : nach.buchung.adresse (vor.zugriffsereignis l.ort) = vor.adresse c l.ort)
    (hgebucht : ∃ a : Adresse, vor.adresse c l.ort = some a ∧ Speicherzugriff vor c l a) :
    ZugriffGebucht vor nach spur := by
  subst f
  intro i actor l' hspur hlneq'
  obtain ⟨init, hes, hinit, hlen, hidx⟩ := speicherfolge_zugriffsindex hfolge hneq
  rw [hes] at hspur
  rcases hinit with hinit | hinit
  · rcases hinit with ⟨rfl, hq⟩
    simp only [List.nil_append] at hspur
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at hspur
      cases hspur
      have hidxeq : vor.graph.ev.length + 0 = vor.zugriffsereignis l.ort := by
        simp only [Zustand.zugriffsereignis, hq, ite_true, Nat.add_zero]
      rw [hidxeq]
      obtain ⟨a, hadr, hzug⟩ := hgebucht
      exact ⟨a, by rw [hbuch, hadr], hzug⟩
    | succ i =>
      simp only [List.getElem?_cons_succ, List.getElem?_nil] at hspur
      cases hspur
  · rcases hinit with ⟨rfl, hneu⟩
    simp only [List.singleton_append] at hspur
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at hspur
      cases hspur
      refine ⟨rfl, ?_⟩
      refine ⟨c, l, ?_, hneq, rfl⟩
      rw [hes]
      exact List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)
    | succ i =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at hspur
        cases hspur
        have hidxeq : vor.graph.ev.length + 1 = vor.zugriffsereignis l.ort := by
          simp only [Zustand.zugriffsereignis, hneu, ite_false]
        rw [hidxeq]
        obtain ⟨a, hadr, hzug⟩ := hgebucht
        exact ⟨a, by rw [hbuch, hadr], hzug⟩
      | succ i =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_nil] at hspur
        cases hspur

/-- A step that changes neither the ledger effects nor the authority state releases nothing. -/
theorem keineWirkungen (vor nach : Zustand) (spur : SchrittSpur Zelle Int)
    (hkeinAbsturz : ¬ Absturz spur) (hwirk : nach.buchung.wirkungen = vor.buchung.wirkungen) :
    NeueWirkungen vor nach spur [] := by
  refine Or.inr ⟨hkeinAbsturz, ?_⟩
  rw [hwirk, List.append_nil]

theorem keineFreigaben (vor nach : Zustand) (hw : HwLauf) (t : Nat) (spur : SchrittSpur Zelle Int)
    (hrechte : nach.rechte = vor.rechte) (hkeinAbsturz : ¬ Absturz spur) :
    FreigabenGueltig vor nach hw t spur [] := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Wirkung.freigabeObjekt, List.filterMap_nil, List.nodup_nil]
  · intro c g h
    simp only [List.not_mem_nil] at h
  · intro _ o hleb hstirbt
    rw [hrechte] at hstirbt
    rw [hleb] at hstirbt
    cases hstirbt

/-- The safety leg of a refused access: the memory trace is empty and only the local frame changes. -/
theorem verweigertBein (vor nach : Zustand) (hw : HwLauf) (t : Nat) (spur : SchrittSpur Zelle Int)
    (F : Schrittform) (c : Kontext)
    (hfolge : Speicherfolge vor.initial (.kontext c) vor.graph [] spur.speicher nach.graph)
    (hnach : nach = { F.verweigert c vor with graph := nach.graph })
    (haussen : spur.aussen = []) :
    ZugriffGebucht vor nach spur ∧ ∃ neu, NeueWirkungen vor nach spur neu ∧ FreigabenGueltig vor nach hw t spur neu := by
  obtain ⟨hes, hg⟩ := speicherfolge_leer hfolge
  have hkeinAbsturz : ¬ Absturz spur := by
    rw [Absturz, haussen]
    simp only [List.not_mem_nil, not_false_eq_true]
  refine ⟨?_, ?_⟩
  · intro i actor l' hspur hlneq'
    rw [hes] at hspur
    simp only [List.getElem?_nil] at hspur
    cases hspur
  · refine ⟨[], ?_, ?_⟩
    · exact keineWirkungen vor nach spur hkeinAbsturz (by rw [hnach]; rfl)
    · exact keineFreigaben vor nach hw t spur (by rw [hnach]; rfl) hkeinAbsturz

/-- **The memory leg, for the three classes that record a memory event.** The guard supplies the
    authority; `Speicherfolge` places the one access at `zugriffsereignis` (with at most one initial
    write), so `ZugriffGebucht` holds. The step books one address and releases nothing, hence
    `neu = []`, `NeueWirkungen` is the unchanged ledger and `FreigabenGueltig` is empty. -/
theorem klassenSpeicherbein_zugriff (k : Wirkungsklasse) (m : Modus)
    (hk : k = .lesen m ∨ k = .schreiben m ∨ k = .rmw m) : KlassenSpeicherbeinAussage k := by
  intro hber ι E f F hFk emb hw t c w vor zwischen nach plan spur kopf impl_step aus
  rw [emb.regel] at impl_step
  rcases aus with ⟨hrahmen, hlies, sperren, vfa, hfa, folge, hnach⟩
  rcases hk with rfl | rfl | rfl
  · simp only [Schrittform.regel, Schrittform.impl, Schrittform.ideal] at impl_step
    rw [hFk] at impl_step
    simp only [Schrittform.zugriffsschritt, Wirkungsklasse.befugt, hFk] at impl_step
    rcases impl_step with href | haut
    · obtain ⟨hnichtBef, hplanL, hzwischen⟩ := href
      have hplan : plan = Semantik.plan := (List.cons.inj hplanL).1
      subst zwischen
      have hplanakt : plan.aktion = .intern := by rw [hplan]; rfl
      rw [hplanakt] at hfa
      obtain ⟨hsperren, haussen, hvfa⟩ := fuehrtAus_intern_nil c E.maschine.einrichtung hfa
      rw [hsperren, haussen] at folge
      rw [hvfa] at hnach
      simp only [hplan, Semantik.plan, List.nil_append, schreibEreignisse] at folge
      exact verweigertBein vor nach hw t spur F c folge hnach haussen
    · obtain ⟨hBef, v, hv, hplanL, hzwischen⟩ := haut
      have hplan : plan = F.plan (vor.lokal c) v := (List.cons.inj hplanL).1
      have hplanakt : plan.aktion = .intern := by
        rw [hplan, Schrittform.plan, hFk]
        rfl
      rw [hplanakt] at hfa
      obtain ⟨hsperren, haussen, hvfa⟩ := fuehrtAus_intern_nil c E.maschine.einrichtung hfa
      rw [hsperren, haussen] at folge
      rw [hvfa] at hnach
      rw [hzwischen] at hnach
      simp only [hplan, Schrittform.plan, hFk, Wirkungsklasse.plan, List.nil_append,
        schreibEreignisse, List.filter, List.map] at folge
      let l : Etikett Zelle Int := ⟨.lesen, (F.operand (vor.lokal c)).ort, m, v, v⟩
      have hbuch : nach.buchung.adresse (vor.zugriffsereignis l.ort) = vor.adresse c l.ort := by
        rw [hnach]
        simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        rw [hFk]
        simp only [l, dif_pos rfl, if_true]
      have hgebucht : ∃ a : Adresse, vor.adresse c l.ort = some a ∧ Speicherzugriff vor c l a := by
        exact adresse_speicherzugriff (c := c) (z := (F.operand (vor.lokal c)).ort) (l := l)
          (by simp only [l]; decide) (by simp only [l]; decide) (by simp only [l]) (fun _ => hBef)
          (fun h => by cases h)
      have hwirk : nach.buchung.wirkungen = vor.buchung.wirkungen := by
        rw [hnach]
        simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        rw [hFk]
      have hkeinAbsturz : ¬ Absturz spur := by
        rw [Absturz, haussen]
        simp only [List.not_mem_nil, not_false_eq_true]
      refine ⟨eineZugriffGebucht vor nach c l (by simp only [l]; decide) (.kontext c) rfl folge hbuch hgebucht, ?_⟩
      refine ⟨[], ?_, ?_⟩
      · exact keineWirkungen vor nach spur hkeinAbsturz hwirk
      · exact keineFreigaben vor nach hw t spur (by rw [hnach]; rfl) hkeinAbsturz
  · simp only [Schrittform.regel, Schrittform.impl, Schrittform.ideal] at impl_step
    rw [hFk] at impl_step
    simp only [Schrittform.zugriffsschritt, Wirkungsklasse.befugt, hFk] at impl_step
    rcases impl_step with href | haut
    · obtain ⟨hnichtBef, hplanL, hzwischen⟩ := href
      have hplan : plan = Semantik.plan := (List.cons.inj hplanL).1
      subst zwischen
      have hplanakt : plan.aktion = .intern := by rw [hplan]; rfl
      rw [hplanakt] at hfa
      obtain ⟨hsperren, haussen, hvfa⟩ := fuehrtAus_intern_nil c E.maschine.einrichtung hfa
      rw [hsperren, haussen] at folge
      rw [hvfa] at hnach
      simp only [hplan, Semantik.plan, List.nil_append, schreibEreignisse] at folge
      exact verweigertBein vor nach hw t spur F c folge hnach haussen
    · obtain ⟨hBef, v, hv, hplanL, hzwischen⟩ := haut
      have hplan : plan = F.plan (vor.lokal c) v := (List.cons.inj hplanL).1
      have hplanakt : plan.aktion = .intern := by
        rw [hplan, Schrittform.plan, hFk]
        rfl
      rw [hplanakt] at hfa
      obtain ⟨hsperren, haussen, hvfa⟩ := fuehrtAus_intern_nil c E.maschine.einrichtung hfa
      rw [hsperren, haussen] at folge
      rw [hvfa] at hnach
      rw [hzwischen] at hnach
      simp only [hplan, Schrittform.plan, hFk, Wirkungsklasse.plan, List.nil_append,
        schreibEreignisse] at folge
      have hfilter : List.filter (fun x => decide (x = (F.operand (vor.lokal c)).ort))
          [(F.operand (vor.lokal c)).ort] = [(F.operand (vor.lokal c)).ort] := by
        simp only [List.filter]
        rfl
      rw [hfilter] at folge
      simp only [List.map, List.cons_append, List.append_nil] at folge
      let l : Etikett Zelle Int := ⟨.schreiben, (F.operand (vor.lokal c)).ort, m,
        (F.operand (vor.lokal c)).wert, (F.operand (vor.lokal c)).wert⟩
      have hbuch : nach.buchung.adresse (vor.zugriffsereignis l.ort) = vor.adresse c l.ort := by
        rw [hnach]
        simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        rw [hFk]
        simp only [l, dif_pos rfl, if_true]
      have hgebucht : ∃ a : Adresse, vor.adresse c l.ort = some a ∧ Speicherzugriff vor c l a := by
        exact adresse_speicherzugriff (c := c) (z := (F.operand (vor.lokal c)).ort) (l := l)
          (by simp only [l]; decide) (by simp only [l]; decide) (by simp only [l]) (fun h => by cases h)
          (fun _ => hBef)
      have hwirk : nach.buchung.wirkungen = vor.buchung.wirkungen := by
        rw [hnach]
        simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        rw [hFk]
      have hkeinAbsturz : ¬ Absturz spur := by
        rw [Absturz, haussen]
        simp only [List.not_mem_nil, not_false_eq_true]
      refine ⟨eineZugriffGebucht vor nach c l (by simp only [l]; decide) (.kontext c) rfl folge hbuch hgebucht, ?_⟩
      refine ⟨[], ?_, ?_⟩
      · exact keineWirkungen vor nach spur hkeinAbsturz hwirk
      · exact keineFreigaben vor nach hw t spur (by rw [hnach]; rfl) hkeinAbsturz
  · simp only [Schrittform.regel, Schrittform.impl, Schrittform.ideal] at impl_step
    rw [hFk] at impl_step
    simp only [Schrittform.zugriffsschritt, Wirkungsklasse.befugt, hFk] at impl_step
    rcases impl_step with href | haut
    · obtain ⟨hnichtBef, hplanL, hzwischen⟩ := href
      have hplan : plan = Semantik.plan := (List.cons.inj hplanL).1
      subst zwischen
      have hplanakt : plan.aktion = .intern := by rw [hplan]; rfl
      rw [hplanakt] at hfa
      obtain ⟨hsperren, haussen, hvfa⟩ := fuehrtAus_intern_nil c E.maschine.einrichtung hfa
      rw [hsperren, haussen] at folge
      rw [hvfa] at hnach
      simp only [hplan, Semantik.plan, List.nil_append, schreibEreignisse] at folge
      exact verweigertBein vor nach hw t spur F c folge hnach haussen
    · obtain ⟨hBef, v, hv, hplanL, hzwischen⟩ := haut
      have hplan : plan = F.plan (vor.lokal c) v := (List.cons.inj hplanL).1
      have hplanakt : plan.aktion = .intern := by
        rw [hplan, Schrittform.plan, hFk]
        rfl
      rw [hplanakt] at hfa
      obtain ⟨hsperren, haussen, hvfa⟩ := fuehrtAus_intern_nil c E.maschine.einrichtung hfa
      rw [hsperren, haussen] at folge
      rw [hvfa] at hnach
      rw [hzwischen] at hnach
      simp only [hplan, Schrittform.plan, hFk, Wirkungsklasse.plan, List.nil_append,
        schreibEreignisse, List.filter, List.map] at folge
      let l : Etikett Zelle Int := ⟨(F.operand (vor.lokal c)).aenderung.art v, (F.operand (vor.lokal c)).ort, m, v,
        (F.operand (vor.lokal c)).aenderung.schreibt v (F.operand (vor.lokal c)).wert⟩
      have hbuch : nach.buchung.adresse (vor.zugriffsereignis l.ort) = vor.adresse c l.ort := by
        rw [hnach]
        simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        rw [hFk]
        simp only [l, dif_pos rfl, if_true]
      have hgebucht : ∃ a : Adresse, vor.adresse c l.ort = some a ∧ Speicherzugriff vor c l a := by
        exact adresse_speicherzugriff (c := c) (z := (F.operand (vor.lokal c)).ort) (l := l)
          (Aenderung.art_ne_aussen _ _) (Aenderung.art_ne_zaun _ _) (by simp only [l]) (fun _ => hBef.1)
          (fun _ => hBef.2)
      have hwirk : nach.buchung.wirkungen = vor.buchung.wirkungen := by
        rw [hnach]
        simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
        rw [hFk]
      have hkeinAbsturz : ¬ Absturz spur := by
        rw [Absturz, haussen]
        simp only [List.not_mem_nil, not_false_eq_true]
      refine ⟨eineZugriffGebucht vor nach c l (Aenderung.art_ne_aussen _ _) (.kontext c) rfl folge hbuch hgebucht, ?_⟩
      refine ⟨[], ?_, ?_⟩
      · exact keineWirkungen vor nach spur hkeinAbsturz hwirk
      · exact keineFreigaben vor nach hw t spur (by rw [hnach]; rfl) hkeinAbsturz

end Gabbro.Core.Ast.Semantik
