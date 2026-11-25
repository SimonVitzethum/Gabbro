module

public import Core.Beobachtung.Fluss.Beweise.Geraet.Hilfe
public import Core.Beobachtung.Fluss.Beweise.GeraetIssueKontext

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast
open Classical

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/-- From device authority the pre-state satisfies the pre-crash invariant branch. -/
theorem geraete_issue_pre {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {c : Kontext} {s : State}
    (inv : GeraeteInvariantAussage binding s)
    (owned : Befugt binding required access s c) :
    s.buchung.geraet = (startBuchung binding.object binding.handle).geraet := by
  obtain ⟨hothers, hqctx, hactx, hfwd, hrange, hpre, hpost⟩ := inv
  by_contra hB
  have hnone := (hpost hB).1
  have hobj : s.buchung.geraet binding.object = none := congrFun hnone binding.object
  simp only [Binding.object] at hobj
  rw [owned.1] at hobj
  cases hobj

/-- A device issue tick appends the fresh question to the pending ledger and the
    outside history; every other ledger, the booking and the machine fields stay. -/
theorem geraete_issue_tick {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase}
    {t : Nat} {c : Kontext} {s : State} {w : PUnit} {plan : Plan}
    {spur : SchrittSpur Nat UInt8} {s' : State} {u : State}
    (aus : FuehrtSchrittAus (d.unit locals).einrichtung t c s u plan spur s')
    (hplans : [plan] = [{ internal with aktion := .frage (binding.question access) }])
    (hu : u = setFrame s c { s.lokal c with pending := some (binding.question access) })
    (owned : Befugt binding required access s c)
    (idle : (s.lokal c).pending = none) :
    let e := s.stelleFrage t c (binding.question access)
    spur.aussen = [.frage e] ∧
      s'.fragen = s.fragen ++ [e] ∧
      s'.verlauf = s.verlauf ++ [(e.cut, .frage e.question)] ∧
      s'.antworten = s.antworten ∧ s'.verbraucht = s.verbraucht ∧
      s'.verworfen = s.verworfen ∧ s'.buchung = s.buchung ∧
      s'.epoche = s.epoche ∧ s'.geliefert = s.geliefert ∧
      s'.kerne = s.kerne ∧ s'.status = s.status ∧
      s'.lokal = Function.update s.lokal c { s.lokal c with pending := some (binding.question access) } ∧
      (s'.lokal c).pending = some (binding.question access) ∧
      s'.initial = s.initial ∧ s'.rechte = s.rechte ∧ s'.leihen = s.leihen ∧
      s'.persistenz = s.persistenz ∧
      e.questionInstance = s.fragen.length ∧ e.context = c.nummer ∧ e.cut = t ∧
      e.question = binding.question access := by
  subst hu
  have hplan : plan = { internal with aktion := .frage (binding.question access) } :=
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
    cases fuehrtAus with
    | frage q =>
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
      · simp only [hsfragen, Zustand.frage, setFrame]
      · simp only [hsverlauf, Zustand.frage, setFrame]
      · simp only [hsantworten, Zustand.frage, setFrame]
      · simp only [hsverbraucht, Zustand.frage, setFrame]
      · simp only [hsverworfen, Zustand.frage, setFrame]
      · simp only [hsbuchung, Zustand.frage, setFrame]
      · simp only [hsepoche, Zustand.frage, setFrame]
      · simp only [hsgeliefert, Zustand.frage, setFrame]
      · simp only [hskerne, Zustand.frage, setFrame]
      · simp only [hsstatus, Zustand.frage, setFrame]
      · simp only [hslokal, Zustand.frage, setFrame]
      · simp only [hslokal, Zustand.frage, setFrame, Function.update_self]
      · simp only [hsinitial, Zustand.frage, setFrame]
      · simp only [hsrechte, Zustand.frage, setFrame]
      · simp only [hsleihen, Zustand.frage, setFrame]
      · simp only [hspersistenz, Zustand.frage, setFrame]

/-- A device issue tick publishes exactly the fresh low question event. -/
theorem geraete_issue_beob_tick {ρ : Lauf (d.unit locals)} {predictor : Praediktor}
    {t : Nat} {binding : Binding k} {c : Kontext} {s s' : State} {w : PUnit}
    {spur : SchrittSpur Nat UInt8}
    (tick : ρ.zeit.spur t = some ((.kontext c w), spur))
    (atS : ρ.zeit.zustand t = some s) (atN : ρ.zeit.zustand (t + 1) = some s')
    {u : State} {plan : Plan}
    (aus : FuehrtSchrittAus (d.unit locals).einrichtung t c s u plan spur s')
    (hplans : [plan] = [{ internal with aktion := .frage (binding.question access) }])
    (hu : u = setFrame s c { s.lokal c with pending := some (binding.question access) })
    (hkopf : (d.unit locals).system.kopf s c = some ())
    (hbuch : s.buchung = s'.buchung)
    (hstatus : s'.status = s.status) :
    schrittBeob ρ predictor t =
      [.frage c.nummer s.fragen.length (binding.question access)] := by
  subst hu
  have hplan : plan = { internal with aktion := .frage (binding.question access) } :=
    (List.cons.inj hplans).1
  subst hplan
  cases spur with
  | mk speicher aussen =>
    obtain ⟨rahmen, auth, sperren, v, fuehrtAus, speicherfolge, nEqState⟩ := aus
    cases fuehrtAus with
    | frage q =>
      simp only [internal, schreibEreignisse, List.filter_nil, List.map_nil,
        List.nil_append, List.append_nil, List.map_cons] at speicherfolge
      have hmem : ∀ l ∈ [aussenEtikett (d.unit locals).einrichtung
          (.frage (s.stelleFrage t c (binding.question access)))], l.art = .aussen := by
        intro l hl
        cases List.mem_singleton.mp hl
        rfl
      have hspeicher := geraete_speicher_still speicherfolge hmem
      have haussenBeob : aussen.flatMap (aussenBeob (d.unit locals)) =
          [.frage c.nummer s.fragen.length (binding.question access)] := by
        have hleer : (d.unit locals).etiketten = .leer := geraete_etiketten_leer d
        have hfrage := geraete_issue_beob (E := d.unit locals) hleer
          (s.stelleFrage t c (binding.question access))
        simp only [hfrage, List.flatMap_cons, List.flatMap_nil]
      have hkontext := geraete_kontext_beob_still (ρ := ρ) hbuch hkopf
      have hende : ¬ ∃ d, (neuBeendet s s' (d.unit locals).etiketten d).isSome = true := by
        rintro ⟨d, hd⟩
        have hnone : neuBeendet s s' (d.unit locals).etiketten d = none := by
          simp only [neuBeendet, hstatus]
          cases hst : s.status d <;> rfl
        rw [hnone] at hd
        cases hd
      rw [schrittBeob, tick, atS, atN]
      simp only [hspeicher, haussenBeob, hkontext, hende, if_false,
        List.nil_append, List.append_nil]

/-- An issue step preserves the device invariant: the fresh question extends the
    ordered ledger, the entry pending slot fills, and all answers stay matched. -/
theorem geraete_issue_erhaelt_invariante {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase}
    {c : Kontext} {s : State} {t : Nat}
    (inv : GeraeteInvariantAussage binding s)
    (owned : Befugt binding required access s c)
    (idle : (s.lokal c).pending = none) :
    GeraeteInvariantAussage binding
      ((setFrame s c { s.lokal c with pending := some (binding.question access) }).frage
        (s.stelleFrage t c (binding.question access))) := by
  have hA := geraete_issue_pre inv owned
  obtain ⟨hothers, hqctx, hactx, hfwd, hrange, hpre, hpost⟩ := inv
  obtain ⟨hverw, hepoche, hidle, hbusy⟩ := hpre hA
  have hentry : c = entryContext := geraete_issue_kontext hA owned
  have hbal := hidle idle
  obtain ⟨hnm, hverb, halle⟩ := hbal
  set e := s.stelleFrage t c (binding.question access) with he
  have hfrage_eq : ((setFrame s c { s.lokal c with pending := some (binding.question access) }).frage e).fragen =
      s.fragen ++ [e] := rfl
  have hnant_eq : ((setFrame s c { s.lokal c with pending := some (binding.question access) }).frage e).antworten =
      s.antworten := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    have hne : c' ≠ c := by rw [hentry]; exact hc'
    simp only [Zustand.frage, setFrame, Function.update_of_ne hne]
    exact hothers c' hc'
  · intro q hq
    simp only [hfrage_eq, List.mem_append] at hq
    cases hq with
    | inl hmem => exact hqctx q hmem
    | inr hsingle =>
      cases List.mem_singleton.mp hsingle
      simp only [he, Zustand.stelleFrage, hentry]
  · intro a ha
    simp only [hnant_eq] at ha
    exact hactx a ha
  · have htake : (s.fragen ++ [e]).take s.antworten.length = s.fragen.take s.antworten.length := by
      have hllen : ((s.fragen ++ [e]).take s.antworten.length).length =
          (s.fragen.take s.antworten.length).length := by
        simp only [List.length_take, List.length_append, List.length_singleton, hnm]
        omega
      apply List.ext_getElem hllen
      intro i h1 h2
      have hi1 : i < (s.fragen ++ [e]).length := by
        simp only [List.length_take] at h1
        simp only [List.length_append, List.length_singleton]
        omega
      have hi2 : i < s.fragen.length := by
        simp only [List.length_take] at h2
        simp only [hnm] at h2
        omega
      simp only [List.getElem_take]
      exact List.getElem_append_left hi2
    simp only [hfrage_eq, hnant_eq, htake]
    exact hfwd
  · simp only [hfrage_eq, List.map_append, List.map_singleton, he, Zustand.stelleFrage,
      hrange, List.range_succ, hnm]
  · intro hpre
    have hsbuch : ((setFrame s c { s.lokal c with pending := some (binding.question access) }).frage
        (s.stelleFrage t c (binding.question access))).buchung = s.buchung := rfl
    have hA' : s.buchung.geraet = (startBuchung binding.object binding.handle).geraet := hA
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c'
      have hv : ((((setFrame s c { s.lokal c with pending := some (binding.question access) }).frage
          (s.stelleFrage t c (binding.question access)))).verworfen) c' = s.verworfen c' := rfl
      rw [hv]
      exact hverw c'
    · have he : (((setFrame s c { s.lokal c with pending := some (binding.question access) }).frage
        (s.stelleFrage t c (binding.question access)))).epoche = s.epoche := rfl
      rw [he]
      exact hepoche
    · intro hnone
      have hsome : (((setFrame s c { s.lokal c with pending := some (binding.question access) }).frage
          (s.stelleFrage t c (binding.question access))).lokal entryContext).pending =
          some (binding.question access) := by
        rw [← hentry]
        simp only [Zustand.frage, setFrame, Function.update_self]
      rw [hsome] at hnone
      cases hnone
    · intro _
      refine Or.inr ⟨?_, ?_, ?_⟩
      · simp only [hfrage_eq, hnant_eq, List.length_append, List.length_singleton, hnm]
      · have hv : ((((setFrame s c { s.lokal c with pending := some (binding.question access) }).frage
          (s.stelleFrage t c (binding.question access)))).verbraucht) entryContext =
          s.verbraucht entryContext := rfl
        rw [hv, hverb, hnant_eq]
      · refine ⟨e, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)), ?_, ?_⟩
        · have hep : (((setFrame s c { s.lokal c with pending := some (binding.question access) }).frage
            (s.stelleFrage t c (binding.question access)))).epoche = s.epoche := rfl
          have hecut : e.cut = t := by rw [he]; rfl
          rw [hep, hepoche, hecut]
          exact Nat.zero_le t
        · intro a ha hzu
          rw [hnant_eq] at ha
          have hainst : a.questionInstance ∈ List.map
              (fun a : AntwortEreignis => a.questionInstance) s.antworten :=
            List.mem_map_of_mem _ ha
          have htakeq : s.fragen.take s.antworten.length = s.fragen := by
            rw [← hnm]
            exact List.take_all_of_le (Nat.le_refl _)
          have htakeq_map : List.map (fun q : FrageEreignis => q.questionInstance)
              (s.fragen.take s.antworten.length) =
              List.range (s.fragen.take s.antworten.length).length := by
            rw [htakeq, hrange]
          have hrange' := geraete_antwort_inst_range hfwd htakeq_map
          rw [hrange'] at hainst
          have hlt := List.mem_range.mp hainst
          have heinst : e.questionInstance = s.fragen.length := by rw [he]; rfl
          have hazu : a.questionInstance = e.questionInstance := hzu.2.2.1.symm
          omega
  · intro hbne
    exact absurd hA hbne

/-- An issue-enabled state admits no arrival: the balanced ledger answers every
    question, so no offered answer is both matching and fresh. -/
theorem geraete_issue_schliesst_ankunft_aus {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {c : Kontext} {s : State}
    (inv : GeraeteInvariantAussage binding s)
    (owned : Befugt binding required access s c)
    (idle : (s.lokal c).pending = none) :
    ¬ ∃ a hw t, s.AntwortAngeboten (d.unit locals).katalog hw t a := by
  have hA := geraete_issue_pre inv owned
  obtain ⟨hothers, hqctx, hactx, hfwd, hrange, hpre, hpost⟩ := inv
  obtain ⟨hverw, hepoche, hidle, hbusy⟩ := hpre hA
  obtain ⟨hnm, hverb, halle⟩ := hidle idle
  rintro ⟨a, hw, t, offered⟩
  obtain ⟨hcut, herlaubt, henthaelt, hfrage, hfrisch⟩ := offered
  obtain ⟨q, hqmem, hqcut, hzu⟩ := hfrage
  obtain ⟨a', hamem, hzu'⟩ := halle q hqmem hqcut
  exact hfrisch a' hamem (hzu.2.2.1.trans hzu'.2.2.1.symm)

end Gabbro.Core.Beobachtung
