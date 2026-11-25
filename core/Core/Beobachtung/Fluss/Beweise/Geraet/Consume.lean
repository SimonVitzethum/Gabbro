module

public import Core.Beobachtung.Fluss.Beweise.Geraet.Hilfe
public import Core.Beobachtung.Fluss.Beweise.Geraet.Issue
public import Core.Beobachtung.Fluss.Beweise.GeraetIssueKontext

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast
open Gabbro.Core.Ast.LowLevel (entryContext)
open Classical

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- The frame installed by a device consume step: pending cleared, the register
    result recorded and the phase advanced on a confirmed write. -/
def geraete_consume_rahmen (s : State) (c : Kontext) (binding : Binding k)
    (access : RegisterAccess) (answer : AntwortEreignis) (target : Option GeraetePhase) : Frame :=
  { s.lokal c with
    pending := none
    last := some (access.result answer.reply)
    phases := match access.result answer.reply, target with
      | .written, some phase => Function.update (s.lokal c).phases binding.object (some phase)
      | _, _ => (s.lokal c).phases }

/-- A consume tick consumes the first unconsumed answer: the ledgers stay, the
    consumption counter advances and the entry frame clears. -/
theorem geraete_consume_tick {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase}
    {t : Nat} {c : Kontext} {s : State} {w : PUnit} {plan : Plan}
    {spur : SchrittSpur Nat UInt8} {s' : State} {u : State} {answer : AntwortEreignis}
    (aus : FuehrtSchrittAus (d.unit locals).einrichtung t c s u plan spur s')
    (hplans : [plan] = [{ internal with aktion := .verbrauche answer }])
    (hu : u = setFrame s c (geraete_consume_rahmen s c binding access answer target))
    (owned : Befugt binding required access s c)
    (pending : (s.lokal c).pending = some (binding.question access))
    (ready : s.naechsteAntwort c = some answer)
    (sameQuestion : answer.question = binding.question access) :
    spur.aussen = [] ∧
      s'.fragen = s.fragen ∧ s'.verlauf = s.verlauf ∧ s'.antworten = s.antworten ∧
      s'.verbraucht = Function.update s.verbraucht c (s.verbraucht c + 1) ∧
      s'.verworfen = s.verworfen ∧ s'.buchung = s.buchung ∧
      s'.epoche = s.epoche ∧ s'.geliefert = s.geliefert ∧
      s'.kerne = s.kerne ∧ s'.status = s.status ∧
      s'.lokal = Function.update s.lokal c (geraete_consume_rahmen s c binding access answer target) ∧
      (s'.lokal c).pending = none ∧
      s'.initial = s.initial ∧ s'.rechte = s.rechte ∧ s'.leihen = s.leihen ∧
      s'.persistenz = s.persistenz := by
  have hplan : plan = { internal with aktion := .verbrauche answer } :=
    (List.cons.inj hplans).1
  subst hplan
  cases spur with
  | mk speicher aussen =>
    obtain ⟨rahmen, auth, sperren, v, fuehrtAus, speicherfolge, nEqState⟩ := aus
    have hsfragen : s'.fragen = v.fragen := by rw [nEqState]
    have hsverlauf : s'.verlauf = v.verlauf := by rw [nEqState]
    have hsantworten : s'.antworten = v.antworten := by rw [nEqState]
    have hsverbraucht : s'.verbraucht = v.verbraucht := by rw [nEqState]
    have hsverworfen : s'.verworfen = v.verworfen := by rw [nEqState]
    have hsbuchung : s'.buchung = v.buchung := by rw [nEqState]
    have hsepoche : s'.epoche = v.epoche := by rw [nEqState]
    have hsgeliefert : s'.geliefert = v.geliefert := by rw [nEqState]
    have hskerne : s'.kerne = v.kerne := by rw [nEqState]
    have hsstatus : s'.status = v.status := by rw [nEqState]
    have hslokal : s'.lokal = v.lokal := by rw [nEqState]
    have hsinitial : s'.initial = v.initial := by rw [nEqState]
    have hsrechte : s'.rechte = v.rechte := by rw [nEqState]
    have hsleihen : s'.leihen = v.leihen := by rw [nEqState]
    have hspersistenz : s'.persistenz = v.persistenz := by rw [nEqState]
    have huvfragen : u.fragen = s.fragen := by rw [hu]; rfl
    have huvverlauf : u.verlauf = s.verlauf := by rw [hu]; rfl
    have huvantworten : u.antworten = s.antworten := by rw [hu]; rfl
    have huvverbraucht : u.verbraucht = s.verbraucht := by rw [hu]; rfl
    have huvverworfen : u.verworfen = s.verworfen := by rw [hu]; rfl
    have huvbuchung : u.buchung = s.buchung := by rw [hu]; rfl
    have huvepoche : u.epoche = s.epoche := by rw [hu]; rfl
    have huvgeliefert : u.geliefert = s.geliefert := by rw [hu]; rfl
    have huvkerne : u.kerne = s.kerne := by rw [hu]; rfl
    have huvstatus : u.status = s.status := by rw [hu]; rfl
    have huvinitial : u.initial = s.initial := by rw [hu]; rfl
    have huvrechte : u.rechte = s.rechte := by rw [hu]; rfl
    have huvleihen : u.leihen = s.leihen := by rw [hu]; rfl
    have huvpersistenz : u.persistenz = s.persistenz := by rw [hu]; rfl
    cases fuehrtAus with
    | verbrauche ready' =>
      have e1 : s'.lokal = u.lokal := by
        rw [hslokal]
        rfl
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [hsfragen, huvfragen, Zustand.verbrauche]
      · simp only [hsverlauf, huvverlauf, Zustand.verbrauche]
      · simp only [hsantworten, huvantworten, Zustand.verbrauche]
      · simp only [hsverbraucht, huvverbraucht, Zustand.verbrauche]
      · simp only [hsverworfen, huvverworfen, Zustand.verbrauche]
      · simp only [hsbuchung, huvbuchung, Zustand.verbrauche]
      · simp only [hsepoche, huvepoche, Zustand.verbrauche]
      · simp only [hsgeliefert, huvgeliefert, Zustand.verbrauche]
      · simp only [hskerne, huvkerne, Zustand.verbrauche]
      · simp only [hsstatus, huvstatus, Zustand.verbrauche]
      · simp only [hslokal, hu, Zustand.verbrauche, setFrame, geraete_consume_rahmen]
      · simp only [hslokal, hu, Zustand.verbrauche, setFrame, geraete_consume_rahmen,
          Function.update_self]
      · simp only [hsinitial, huvinitial, Zustand.verbrauche]
      · simp only [hsrechte, huvrechte, Zustand.verbrauche]
      · simp only [hsleihen, huvleihen, Zustand.verbrauche]
      · simp only [hspersistenz, huvpersistenz, Zustand.verbrauche]

/-- A consume tick is silent: no memory label, no outside event, no commit and no
    new end is recorded. -/
theorem geraete_consume_beob_tick {ρ : Lauf (d.unit locals)} {predictor : Praediktor}
    {t : Nat} {binding : Binding k} {access : RegisterAccess} {required : GeraetePhase}
    {target : Option GeraetePhase} {c : Kontext} {s s' : State} {w : PUnit}
    {spur : SchrittSpur Nat UInt8}
    (tick : ρ.zeit.spur t = some ((.kontext c w), spur))
    (atS : ρ.zeit.zustand t = some s) (atN : ρ.zeit.zustand (t + 1) = some s')
    {u : State} {plan : Plan} {answer : AntwortEreignis}
    (aus : FuehrtSchrittAus (d.unit locals).einrichtung t c s u plan spur s')
    (hplans : [plan] = [{ internal with aktion := .verbrauche answer }])
    (hu : u = setFrame s c (geraete_consume_rahmen s c binding access answer target))
    (hkopf : (d.unit locals).system.kopf s c = some ())
    (hbuch : s.buchung = s'.buchung)
    (hstatus : s'.status = s.status) :
    schrittBeob ρ predictor t = [] := by
  subst hu
  have hplan : plan = { internal with aktion := .verbrauche answer } :=
    (List.cons.inj hplans).1
  subst hplan
  cases spur with
  | mk speicher aussen =>
    obtain ⟨rahmen, auth, sperren, v, fuehrtAus, speicherfolge, nEqState⟩ := aus
    cases fuehrtAus with
    | verbrauche ready' =>
      simp only [internal, schreibEreignisse, List.filter_nil, List.map_nil,
        List.nil_append, List.append_nil] at speicherfolge
      have hmem : ∀ l ∈ ([] : List (Speicher.Etikett Nat UInt8)), l.art = .aussen := by
        intro l hl
        cases hl
      have hspeicher := geraete_speicher_still (k := k) (scope := scope) (locals := locals)
        (d := d) speicherfolge hmem
      have hkontext : kontextBeob ρ predictor t c s s'
          ⟨speicher, ([] : List Ereignis)⟩ = [] :=
        geraete_kontext_beob_still (ρ := ρ) (predictor := predictor) (t := t)
          (spur := ⟨speicher, ([] : List Ereignis)⟩) hbuch hkopf
      have hende : ¬ ∃ ctx, (neuBeendet s s' (d.unit locals).etiketten ctx).isSome = true := by
        rintro ⟨ctx, hd⟩
        have hnone : neuBeendet s s' (d.unit locals).etiketten ctx = none := by
          simp only [neuBeendet, hstatus]
          cases hst : s.status ctx <;> rfl
        rw [hnone] at hd
        cases hd
      rw [schrittBeob, tick, atS, atN]
      simp only [hspeicher, hkontext, hende, if_false,
        List.filterMap_nil, List.flatMap_nil, List.nil_append, List.append_nil]

/-- A ready answer rules out the unbalanced ledger shape: with a pending question
    the consumption index would already cover every arrived answer. -/
theorem geraete_consume_ausgeglichen {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase}
    {c : Kontext} {s : State} {answer : AntwortEreignis}
    (inv : GeraeteInvariantAussage binding s)
    (owned : Befugt binding required access s c)
    (pending : (s.lokal c).pending = some (binding.question access))
    (ready : s.naechsteAntwort c = some answer) :
    s.fragen.length = s.antworten.length ∧ s.verbraucht entryContext + 1 = s.antworten.length ∧
      ∀ q ∈ s.fragen, s.epoche ≤ q.cut → ∃ a ∈ s.antworten, a.zu q := by
  have hA := geraete_issue_pre inv owned
  obtain ⟨hothers, hqctx, hactx, hfwd, hrange, hpre, hpost⟩ := inv
  obtain ⟨hverw, hepoche, hidle, hbusy⟩ := hpre hA
  have hentry : c = entryContext := geraete_issue_kontext (target := target) hA owned
  have hne : (s.lokal entryContext).pending ≠ none := by
    rw [← hentry, pending]
    exact Option.some_ne_none _
  cases hbusy hne with
  | inl hbb => exact hbb
  | inr hub =>
    obtain ⟨hnm', hverb', hex⟩ := hub
    have hang : s.angekommen entryContext = s.antworten := by
      simp only [Zustand.angekommen]
      induction h : s.antworten with
      | nil => rfl
      | cons a as ih =>
        have hmem : a ∈ a :: as := List.mem_cons.mpr (Or.inl rfl)
        have hac : a.context = entryContext.nummer := hactx a (h.symm ▸ hmem)
        have hpos : ((fun e => e.context == entryContext.nummer) a) = true := by
          simp only [hac, beq_self_eq_true]
        rw [List.filter_cons_of_pos hpos, ih]
    have hidx : s.verworfen entryContext + s.verbraucht entryContext = s.antworten.length := by
      rw [hverw entryContext, Nat.zero_add, hverb']
    have hnone : s.naechsteAntwort entryContext = none := by
      simp only [Zustand.naechsteAntwort, hang, hidx, List.getElem?_eq_none (Nat.le_refl _)]
    rw [← hentry] at hnone
    rw [ready] at hnone
    cases hnone

/-- A consume step preserves the device invariant: the answered ledger stays
    matched while the entry pending slot clears. -/
theorem geraete_consume_erhaelt_invariante {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase}
    {c : Kontext} {s : State} {answer : AntwortEreignis}
    (inv : GeraeteInvariantAussage binding s)
    (owned : Befugt binding required access s c)
    (pending : (s.lokal c).pending = some (binding.question access))
    (ready : s.naechsteAntwort c = some answer)
    (sameQuestion : answer.question = binding.question access) :
    GeraeteInvariantAussage binding
      ((setFrame s c (geraete_consume_rahmen s c binding access answer target)).verbrauche c) := by
  have hA := geraete_issue_pre inv owned
  obtain ⟨hothers, hqctx, hactx, hfwd, hrange, hpre, hpost⟩ := inv
  obtain ⟨hverw, hepoche, hidle, hbusy⟩ := hpre hA
  have hentry : c = entryContext := geraete_issue_kontext (target := target) hA owned
  have hbb := geraete_consume_ausgeglichen (target := target) inv owned pending ready
  obtain ⟨hnm, hverb, halle⟩ := hbb
  set u := (setFrame s c (geraete_consume_rahmen s c binding access answer target)).verbrauche c with hu
  have hufragen : u.fragen = s.fragen := rfl
  have huantworten : u.antworten = s.antworten := rfl
  have huverlauf : u.verlauf = s.verlauf := rfl
  have hubuchung : u.buchung = s.buchung := rfl
  have huepoche : u.epoche = s.epoche := rfl
  have huverworfen : u.verworfen = s.verworfen := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    have hne : c' ≠ c := by rw [hentry]; exact hc'
    refine ⟨?_, ?_, ?_⟩
    · have h1 : (u.lokal c').pending =
          ((setFrame s c (geraete_consume_rahmen s c binding access answer target)).lokal c').pending := rfl
      simp only [h1, setFrame, geraete_consume_rahmen, Function.update_of_ne hne]
      exact (hothers c' hc').1
    · have h2 : u.verbraucht c' = s.verbraucht c' := by
        simp only [hu, Zustand.verbrauche, setFrame, geraete_consume_rahmen,
          Function.update_of_ne hne]
      rw [h2]
      exact (hothers c' hc').2.1
    · have h3 : u.verworfen c' = s.verworfen c' := by rfl
      rw [h3]
      exact (hothers c' hc').2.2
  · intro q hq
    rw [hufragen] at hq
    exact hqctx q hq
  · intro a ha
    rw [huantworten] at ha
    exact hactx a ha
  · rw [hufragen, huantworten]
    exact hfwd
  · rw [hufragen, hrange]
  · intro hpre'
    have hA' : s.buchung.geraet = (startBuchung binding.object binding.handle).geraet := hA
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c'
      have hv : u.verworfen c' = s.verworfen c' := by rfl
      rw [hv]
      exact hverw c'
    · have he : u.epoche = s.epoche := rfl
      rw [he]
      exact hepoche
    · intro hnone
      refine ⟨?_, ?_, ?_⟩
      · rw [hufragen, huantworten]
        exact hnm
      · have hv1 : u.verbraucht entryContext = s.verbraucht c + 1 := by
          rw [← hentry]
          simp only [hu, Zustand.verbrauche, setFrame, geraete_consume_rahmen,
            Function.update_self]
        have hverb' : s.verbraucht c + 1 = s.antworten.length := by
          rw [hentry]
          exact hverb
        rw [hv1, hverb', huantworten]
      · intro q hq hcut
        rw [hufragen] at hq
        obtain ⟨a, ham, hzu⟩ := halle q hq hcut
        exact ⟨a, huantworten.symm ▸ ham, hzu⟩
    · intro hne
      have hsome : (u.lokal entryContext).pending = none := by
        rw [← hentry]
        simp only [hu, Zustand.verbrauche, setFrame, geraete_consume_rahmen,
          Function.update_self]
      exact absurd hsome hne
  · intro hbne
    exact absurd hA hbne

/-- A ready answer rules out arrivals: every question is already matched, so no
    offered answer is both matching and fresh. -/
theorem geraete_consume_schliesst_ankunft_aus {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase}
    {c : Kontext} {s : State} {answer : AntwortEreignis}
    (inv : GeraeteInvariantAussage binding s)
    (owned : Befugt binding required access s c)
    (pending : (s.lokal c).pending = some (binding.question access))
    (ready : s.naechsteAntwort c = some answer) :
    ¬ ∃ a hw t, s.AntwortAngeboten (d.unit locals).katalog hw t a := by
  have hbb := geraete_consume_ausgeglichen (target := target) inv owned pending ready
  obtain ⟨hnm, hverb, halle⟩ := hbb
  rintro ⟨a, hw, t, offered⟩
  obtain ⟨hcut, herlaubt, henthaelt, hfrage, hfrisch⟩ := offered
  obtain ⟨q, hqmem, hqcut, hzu⟩ := hfrage
  obtain ⟨a', hamem, hzu'⟩ := halle q hqmem hqcut
  exact hfrisch a' hamem (hzu'.2.2.1.symm.trans hzu.2.2.1)

end Gabbro.Core.Beobachtung
