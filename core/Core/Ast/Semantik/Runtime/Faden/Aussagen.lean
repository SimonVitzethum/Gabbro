/-
  File:      core/Core/Ast/Semantik/Runtime/Faden/Aussagen.lean
  Subject:   THE STATEMENTS OF THE THREAD LIFECYCLE (MK-07), pinned under ONE statement `FadenAussagen`:
             * `StarteBestimmtAussage`: a start picks the thread with the next number, which rests, runs it and moves
               the counter on; two starts from the same state agree. PROVED (`starteBestimmt`).
             * `FadenAutoritaetAussage`: authority moves with a start and comes back with a join, it is never copied:
               after a hand-over the new thread holds what the starter held on the handed-over handles and the starter
               holds none of it; nothing else changes; exclusive authority keeps one holder. PROVED
               (`fadenAutoritaet`), at the ledger and at the class step.
             * `VerbindeErgebnisAussage`: a join delivers the outcome of the ended thread to the joiner's frame and takes
               back what the ended thread held. PROVED (`verbindeErgebnis`).
             * `WechsleAussage`: a switch or a core start makes the core run the context switched to, which ran on no
               core, so no context runs on two cores. PROVED (`wechsle`).
             * `KindStartetBeiAnkunftAussage`: a resting thread never steps, and a started thread begins at the entry
               frame of its body with an empty stack. PROVED (`kindStartetBeiAnkunft`).
             * `FadenHbAussage`: a release publication before the start and an acquire observation by the child order
               everything the starter did before the start before everything the child does after its observation; the
               same for the end and the join. PROVED (`fadenHb`) from the synchronises-with edge of the pair.
             * `FadenBestimmtAussage`: the step of a lifecycle instruction is determinate. PROVED (`fadenBestimmt`).
             Each has a satisfiability lemma (`…_erfuellbar`: the premises hold jointly) and a non-triviality lemma
             (`…_nichtTrivial`: the model REPRESENTS the error, and only the rule or the checker excludes it): a
             counter a form resets, a start of a thread that does not rest, authority copied instead of moved, a join of
             a thread that has not ended, a switch to a context already on a core, a start and an observation with a
             flag mode too weak to synchronise, a rule that lets the refusal and the run both happen.
             The open duties of the lifecycle instructions are pinned under `FadenBefehlAussage` for the registry entry
             of `Befehl.faden`: composability (`FadenKomponierbarAussage`) and the progress of a join under hardware
             fairness (`VerbindeFortschrittAussage`).
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Gesamt
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Faden
public import Core.Ast.Semantik.Runtime.Faden.Autoritaet
public import Core.Ast.Semantik.Runtime.Faden.Erhalt
public import Core.Speicher.Atom.NutzlastSchwach
public import Core.Verfeinerung.Fortschritt

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Sicherheit (Buchung Speicherrecht)

/-! ### The start is exact -/

/-- **A start is exact and determinate.** The machine starts the thread with the next number, which rests (a running
    or ended thread is never started again), runs it afterwards, moves the counter on by one and changes no other status;
    two starts from the same state agree. -/
def StarteBestimmtAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung : Type) [DecidableEq L]
    (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung) (t : Nat) (c : Kontext)
    (s u v v' : Maschine.Zustand L Ort Wert Raum Lok Grund)
    (sperren sperren' : List (Speicher.Etikett Ort Wert)) (ereignisse ereignisse' : List Ereignis),
    FuehrtAus e t c s u .starte sperren ereignisse v →
      s.status (.faden s.naechsterFaden) = .ruht ∧ v.status (.faden s.naechsterFaden) = .laeuft ∧
        v.naechsterFaden = s.naechsterFaden + 1 ∧
        (∀ d : Kontext, d ≠ .faden s.naechsterFaden → v.status d = u.status d) ∧
        (FuehrtAus e t c s u .starte sperren' ereignisse' v' → v = v')

/-- **A start is exact and determinate** (the proof of `StarteBestimmtAussage`). -/
theorem starteBestimmt : StarteBestimmtAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung _ e t c s u v v' sperren sperren' ereignisse ereignisse' h
  obtain ⟨ruht, laeuft, zaehler, andere⟩ := h.starte_genau
  exact ⟨ruht, laeuft, zaehler, andere, fun h' => (h.bestimmt h').2.2⟩

/-- The empty unit's start state: the entry thread runs, every other thread rests, the next number is `1`. -/
theorem leerzustand_faden_ruht : Leerzustand.status (Kontext.faden 1) = .ruht := by
  have ne : Kontext.faden 1 ≠ eintritt := fun h => Nat.one_ne_zero (Kontext.faden.inj h)
  change (if Kontext.faden 1 = eintritt then (Status.laeuft : Status Int PUnit) else Status.ruht) = Status.ruht
  rw [if_neg ne]

/-- The empty unit's start state counts from `1`. -/
theorem leerzustand_naechsterFaden : Leerzustand.naechsterFaden = 1 := rfl

/-- **The premises of the start statement hold jointly**: in the start state of the empty unit the thread `1` rests
    and the machine starts it. -/
theorem starteBestimmt_erfuellbar :
    ∃ (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit) (t : Nat) (c : Kontext) (v : Zustand),
      FuehrtAus e t c Leerzustand Leerzustand .starte [] [] v :=
  ⟨einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher, 0, eintritt, _,
    .starte leerzustand_faden_ruht⟩

/-- **The start statement is not trivial**: the model represents a start of a thread that does not rest, and a form
    that resets the thread counter; the machine has no step for either. A thread that runs is not started again, and
    the counter is the machine's, so no number is used twice. -/
theorem starteBestimmt_nichtTrivial :
    ∃ (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit) (t : Nat) (c : Kontext) (s : Zustand),
      (∀ (u v : Zustand) sperren ereignisse, ¬ FuehrtAus e t c s u .starte sperren ereignisse v) ∧
        (∃ u : Zustand, u.naechsterFaden ≠ s.naechsterFaden ∧
          ∀ (t' : Nat) (c' : Kontext) (plan : Plan) (spur : SchrittSpur Zelle Int) (s' : Zustand),
            ¬ FuehrtSchrittAus e t' c' s u plan spur s') := by
  refine ⟨einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher, 0, eintritt,
    { Leerzustand with status := fun _ => .laeuft }, ?_, ?_⟩
  · intro u v sperren ereignisse h
    cases h with
    | starte ruht => cases ruht
  · refine ⟨{ Leerzustand with naechsterFaden := 0 }, ?_, ?_⟩
    · intro h
      exact Nat.zero_ne_one h
    · intro t' c' plan spur s' h
      exact Nat.zero_ne_one h.1.naechsterFaden

/-! ### Authority moves, it is never copied -/

/-- **Authority is present exactly once after a start, and comes back with a join.** At the ledger: a hand-over gives
    the new holder what the starter held on the handed-over handles and leaves the starter none of it, changes no other
    holder and no other handle, and keeps exclusive authority with one holder; a take-back does the same for a join. At the
    class step: the step of the class `starte` keeps exclusive authority with one holder. -/
def FadenAutoritaetAussage : Prop :=
  (∀ (Ort : Type) (b : Buchung Ort) (von an : Kontext) (gs : List Griff), von ≠ an → b.Eindeutig →
    (∀ g ∈ gs, ∀ r, b.haelt von g r → b.uebergeben von an gs an g r ∧ ¬ b.uebergeben von an gs von g r) ∧
    (∀ d, d ≠ von → d ≠ an → ∀ g r, b.uebergeben von an gs d g r ↔ b.haelt d g r) ∧
    (∀ g, g ∉ gs → ∀ d r, b.uebergeben von an gs d g r ↔ b.haelt d g r) ∧
    Buchung.Eindeutig { b with haelt := b.uebergeben von an gs }) ∧
  (∀ (Ort : Type) (b : Buchung Ort) (kind an : Kontext), kind ≠ an → b.Eindeutig →
    (∀ g r, b.haelt kind g r → b.zurueckgegeben kind an an g r ∧ ¬ b.zurueckgegeben kind an kind g r) ∧
    Buchung.Eindeutig { b with haelt := b.zurueckgegeben kind an }) ∧
  (∀ (F : Schrittform), F.klasse = .starte → ∀ (c : Kontext) (s u : Zustand) (w : PUnit) (p : Plan),
    s.buchung.Eindeutig → F.ideal c s w [p] u → u.buchung.Eindeutig)

/-- **Authority moves, it is never copied** (the proof of `FadenAutoritaetAussage`). -/
theorem fadenAutoritaet : FadenAutoritaetAussage := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ort b von an gs hne h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg r hr
      exact ⟨Buchung.uebergeben_an b von an gs hg r hr, Buchung.uebergeben_von b gs hne hg r⟩
    · intro d hv ha g r
      exact Buchung.uebergeben_andere b gs hv ha g r
    · intro g hg d r
      exact Buchung.uebergeben_ausser b von an hg d r
    · intro d d' g r hr hd hd'
      exact Buchung.uebergeben_eindeutig b von an gs h d d' g r hr hd hd'
  · intro Ort b kind an hne h
    refine ⟨?_, ?_⟩
    · intro g r hr
      exact Buchung.zurueckgegeben_zurueck b hne g r hr
    · intro d d' g r hr hd hd'
      exact Buchung.zurueckgegeben_eindeutig b kind an h d d' g r hr hd hd'
  · intro F hk c s u w p eins step
    obtain ⟨k, o, t⟩ := F
    change k = .starte at hk
    subst hk
    have lz : (⟨.starte, o, t⟩ : Schrittform).Lebenszyklus := Or.inl rfl
    rcases Schrittform.lebenszyklus_zustand lz step with hu | hu
    · subst u
      exact eins
    · subst u
      intro d d' g r hr hd hd'
      exact Buchung.uebergeben_eindeutig s.buchung c (Kontext.faden s.naechsterFaden) _ eins d d' g r hr hd hd'

/-- **The premises of the authority statement hold jointly**: a ledger with one holder of a handle, a hand-over of that
    handle to another context. -/
theorem fadenAutoritaet_erfuellbar :
    ∃ (b : Buchung Zelle) (von an : Kontext) (gs : List Griff), von ≠ an ∧ b.Eindeutig ∧
      ∃ g ∈ gs, ∃ r, b.haelt von g r := by
  refine ⟨{ Buchung.leer with haelt := fun d _ r => d = Kontext.faden 0 ∧ r = Speicherrecht.schreiben },
    Kontext.faden 0, Kontext.faden 1, [⟨0, 0⟩], ?_, ?_, ⟨0, 0⟩, List.mem_singleton_self _,
    Speicherrecht.schreiben, ⟨rfl, rfl⟩⟩
  · intro h
    exact Nat.zero_ne_one (Kontext.faden.inj h)
  · intro d d' g r _ hd hd'
    exact hd.1.trans hd'.1.symm

/-- **The authority statement is not trivial**: the model represents authority that is COPIED to the new thread, so that
    two contexts hold the right to write one handle. The hand-over (`Buchung.uebergeben`) keeps it with one holder, the
    copy does not. -/
theorem fadenAutoritaet_nichtTrivial :
    ∃ (b : Buchung Zelle) (von an : Kontext) (gs : List Griff), von ≠ an ∧ b.Eindeutig ∧
      ¬ Buchung.Eindeutig { b with haelt := b.kopiert von an gs } := by
  refine ⟨{ Buchung.leer with haelt := fun d _ r => d = Kontext.faden 0 ∧ r = Speicherrecht.schreiben },
    Kontext.faden 0, Kontext.faden 1, [⟨0, 0⟩], ?_, ?_, ?_⟩
  · intro h
    exact Nat.zero_ne_one (Kontext.faden.inj h)
  · intro d d' g r _ hd hd'
    exact hd.1.trans hd'.1.symm
  · intro h
    have same := h (Kontext.faden 0) (Kontext.faden 1) ⟨0, 0⟩ Speicherrecht.schreiben (Or.inl rfl)
      (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, List.mem_singleton_self _, rfl, rfl⟩)
    exact Nat.zero_ne_one (Kontext.faden.inj same)

/-! ### A join delivers the outcome -/

/-- **The state of a join of an ended thread** (a lemma of the proof below): the joiner's frame is the transfer of its
    instruction at the outcome, and the holdings are taken back. -/
theorem Schrittform.faedenNach_verbinde_wert (F : Schrittform) (hk : F.klasse = .verbinde) (c : Kontext)
    (s : Zustand) (n : Nat) (v : Int) (hn : (F.operand (s.lokal c)).faden.kind = n)
    (hs : s.status (.faden n) = .beendet (.wert v)) :
    F.faedenNach c s =
      { s with
        lokal := Function.update s.lokal c (F.uebertrag (s.lokal c) s.regionLive v),
        buchung := { s.buchung with haelt := s.buchung.zurueckgegeben (.faden n) c } } := by
  unfold Schrittform.faedenNach
  try dsimp only
  rw [hk]
  simp only [hn, hs]

/-- **A join delivers the outcome and takes the authority back.** When the thread a join names has ended with the
    outcome `v`, the step of the class `verbinde` (with its operands in order) leaves the joiner's frame at the transfer
    of its instruction for `v`, gives the joiner what the ended thread still held, and leaves the ended thread none of
    it. -/
def VerbindeErgebnisAussage : Prop :=
  ∀ (F : Schrittform), F.klasse = .verbinde → ∀ (c : Kontext) (s u : Zustand) (w : PUnit) (p : Plan) (n : Nat) (v : Int),
    F.ideal c s w [p] u → F.klasse.befugt (F.operand (s.lokal c)) s c →
      (F.operand (s.lokal c)).faden.kind = n → s.status (.faden n) = .beendet (.wert v) → Kontext.faden n ≠ c →
        u.lokal c = F.uebertrag (s.lokal c) s.regionLive v ∧
          ∀ g r, s.buchung.haelt (.faden n) g r → u.buchung.haelt c g r ∧ ¬ u.buchung.haelt (.faden n) g r

/-- **A join delivers the outcome and takes the authority back** (the proof of `VerbindeErgebnisAussage`). -/
theorem verbindeErgebnis : VerbindeErgebnisAussage := by
  intro F hk c s u w p n v step bef hn hs hne
  have uEq : u = F.faedenNach c s := by
    obtain ⟨k, o, t⟩ := F
    change k = .verbinde at hk
    subst hk
    rcases step with ⟨nb, _, _⟩ | ⟨_, _, hu⟩
    · exact absurd bef nb
    · exact hu
  rw [uEq, Schrittform.faedenNach_verbinde_wert F hk c s n v hn hs]
  refine ⟨?_, fun g r h => Buchung.zurueckgegeben_zurueck s.buchung hne g r h⟩
  change Function.update s.lokal c (F.uebertrag (s.lokal c) s.regionLive v) c = _
  rw [Function.update_self]

/-- **The premises of the join statement hold jointly**: a form of the class `verbinde` whose operands are in order,
    a state in which the thread it names has ended with an outcome. -/
theorem verbindeErgebnis_erfuellbar :
    ∃ (F : Schrittform) (c : Kontext) (s u : Zustand) (p : Plan) (n : Nat) (v : Int),
      F.klasse = .verbinde ∧ F.ideal c s () [p] u ∧ F.klasse.befugt (F.operand (s.lokal c)) s c ∧
        (F.operand (s.lokal c)).faden.kind = n ∧ s.status (.faden n) = .beendet (.wert v) ∧
        Kontext.faden n ≠ c := by
  let F : Schrittform := ⟨.verbinde, fun _ => { Operand.keiner with faden := { Fadenoperand.keiner with kind := 1 } },
    fun r _ _ => r⟩
  let s : Zustand := { Leerzustand with status := fun d => if d = Kontext.faden 1 then .beendet (.wert 7) else .ruht }
  refine ⟨F, eintritt, s, F.faedenNach eintritt s, F.plan (s.lokal eintritt) 0, 1, 7, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · change (if Kontext.faden 1 = Kontext.faden 1 then Status.beendet (.wert 7) else .ruht) = _
    rw [if_pos rfl]
  · intro h
    exact Nat.one_ne_zero (Kontext.faden.inj h)

/-- **The join statement is not trivial**: the model represents a join of a thread that has not ended, and the
    machine has no step for it, so a join never delivers an outcome that does not exist. -/
theorem verbindeErgebnis_nichtTrivial :
    ∃ (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit) (t : Nat) (c : Kontext) (s : Zustand) (kind : Kontext),
      s.status kind = .laeuft ∧
        ∀ (u v : Zustand) sperren ereignisse, ¬ FuehrtAus e t c s u (.verbinde kind) sperren ereignisse v := by
  refine ⟨einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher, 0, eintritt,
    { Leerzustand with status := fun _ => .laeuft }, Kontext.faden 1, rfl, ?_⟩
  intro u v sperren ereignisse h
  cases h with
  | verbinde fertig => cases fertig

/-! ### A switch and a core start -/

/-- **A switch or a core start makes the core run the context switched to.** The context ran on no core and is not
    the acting one; no other core changes; and so no context runs on two cores. -/
def WechsleAussage : Prop :=
  ∀ (L Ort Wert Raum Lok Grund Bedingung : Type) [DecidableEq L]
    (e : Einrichtung L Ort Wert Raum Lok Grund Bedingung) (t : Nat) (c : Kontext)
    (s u v : Maschine.Zustand L Ort Wert Raum Lok Grund) (kern : Kern) (kind : Kontext)
    (sperren : List (Speicher.Etikett Ort Wert)) (ereignisse : List Ereignis),
    FuehrtAus e t c s u (.wechsle kern kind) sperren ereignisse v → u.kerne = s.kerne →
      s.EinKern →
        (v.kerne kern).laeuft = some kind ∧ v.EinKern ∧ (∀ k, k ≠ kern → v.kerne k = s.kerne k) ∧ kind ≠ c ∧
          s.status kind = .laeuft

/-- **A switch or a core start makes the core run the context switched to** (the proof of `WechsleAussage`). -/
theorem wechselKern : WechsleAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung _ e t c s u v kern kind sperren ereignisse h rahmen eins
  obtain ⟨_, laeuft, _, anders, hkern, andere⟩ := h.wechsle_genau
  exact ⟨hkern, h.wechsle_erhaelt_einkern rahmen eins, fun k hk => (andere k hk).trans (congrFun rahmen k),
    anders, laeuft⟩

/-- **The premises of the switch statement hold jointly**: a state in which every core is idle and every context runs,
    a switch of an idle core to a context. -/
theorem wechselKern_erfuellbar :
    ∃ (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit) (t : Nat) (c : Kontext) (s v : Zustand) (kern : Kern)
      (kind : Kontext) (sperren : List (Speicher.Etikett Zelle Int)) (ereignisse : List Ereignis),
      FuehrtAus e t c s s (.wechsle kern kind) sperren ereignisse v ∧ s.EinKern := by
  let s : Zustand := { Leerzustand with
    status := fun _ => .laeuft, kerne := fun k => { Leerzustand.kerne k with laeuft := none } }
  refine ⟨einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher, 0, eintritt, s, _, 0,
    Kontext.faden 1, [], [], .wechsle (Or.inr rfl) rfl (fun k h => by cases h)
      (fun h => Nat.one_ne_zero (Kontext.faden.inj h)), ?_⟩
  intro k k' d hk
  cases hk

/-- **The switch statement is not trivial**: the model represents a switch to a context that already runs on a core, and
    the machine has no step for it, so no context ever runs on two cores. -/
theorem wechselKern_nichtTrivial :
    ∃ (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit) (t : Nat) (c : Kontext) (s : Zustand) (kern : Kern)
      (kind : Kontext), s.status kind = .laeuft ∧ (∃ k, (s.kerne k).laeuft = some kind) ∧
        ∀ (u v : Zustand) sperren ereignisse, ¬ FuehrtAus e t c s u (.wechsle kern kind) sperren ereignisse v := by
  let s : Zustand := { Leerzustand with
    status := fun _ => .laeuft,
    kerne := fun k => { Leerzustand.kerne k with laeuft := some (Kontext.faden 1) } }
  refine ⟨einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher, 0, eintritt, s, 0,
    Kontext.faden 1, rfl, ⟨0, rfl⟩, ?_⟩
  intro u v sperren ereignisse h
  obtain ⟨_, _, nirgends, _, _, _⟩ := h.wechsle_genau
  exact nirgends 0 rfl

/-! ### A thread starts at its entry -/

/-- The first frame of a started thread sits at the entry position its instruction names (a lemma of the proofs below). -/
theorem Schrittform.faedenNach_starte_pc (F : Schrittform) (hk : F.klasse = .starte) (c : Kontext) (s : Zustand) :
    ((F.faedenNach c s).lokal (.faden s.naechsterFaden)).pc = (F.operand (s.lokal c)).faden.anfang.pc := by
  obtain ⟨k, o, t⟩ := F
  change k = .starte at hk
  subst hk
  unfold Schrittform.faedenNach
  try dsimp only
  rw [Function.update_self]

/-- **A resting thread never steps, and a started thread begins at its entry.** The machine schedules a context only
    when it runs, so a thread that has not been started has no step; the step of the class `starte` gives the new thread
    the entry frame of its body with an empty continuation stack. -/
def KindStartetBeiAnkunftAussage : Prop :=
  (∀ (L Ort Wert Raum Lok Grund : Type) (run : HwLauf) (t : Nat) (c : Kontext)
      (s : Maschine.Zustand L Ort Wert Raum Lok Grund), s.status c = .ruht → ¬ KannSchreiten run t c s) ∧
    ∀ (F : Schrittform), F.klasse = .starte → ∀ (c : Kontext) (s u : Zustand) (w : PUnit) (p : Plan),
      F.ideal c s w [p] u → F.klasse.befugt (F.operand (s.lokal c)) s c →
        u.lokal (.faden s.naechsterFaden) = { (F.operand (s.lokal c)).faden.anfang with fortsetzungen := [] }

/-- **A resting thread never steps, and a started thread begins at its entry** (the proof of
    `KindStartetBeiAnkunftAussage`). -/
theorem kindStartetBeiAnkunft : KindStartetBeiAnkunftAussage := by
  refine ⟨?_, ?_⟩
  · intro L Ort Wert Raum Lok Grund run t c s ruht h
    obtain ⟨_, _, _, laeuft⟩ := h
    rw [ruht] at laeuft
    cases laeuft
  · intro F hk c s u w p step bef
    obtain ⟨k, o, t⟩ := F
    change k = .starte at hk
    subst hk
    rcases step with ⟨nb, _, _⟩ | ⟨_, _, hu⟩
    · exact absurd bef nb
    · rw [hu]
      change Function.update (Function.update s.lokal c _) (Kontext.faden s.naechsterFaden) _
        (Kontext.faden s.naechsterFaden) = _
      rw [Function.update_self]

/-- **The premises of the entry statement hold jointly**: a start instruction with no handle to hand over has a step
    in every state. -/
theorem kindStartetBeiAnkunft_erfuellbar :
    ∃ (F : Schrittform) (c : Kontext) (s u : Zustand) (p : Plan),
      F.klasse = .starte ∧ F.ideal c s () [p] u ∧ F.klasse.befugt (F.operand (s.lokal c)) s c := by
  let F : Schrittform := (Befehl.faden (.starte 0 5 .bool [])).form
  exact ⟨F, eintritt, Leerzustand, F.faedenNach eintritt Leerzustand, F.plan (Leerzustand.lokal eintritt) 0, rfl,
    Or.inr ⟨⟨rfl, fun _ h => absurd h List.not_mem_nil⟩, rfl, rfl⟩, ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩

/-- **The entry statement is not trivial**: instructions with different entry positions start threads with different
    first frames, so the statement says where the new thread begins. -/
theorem kindStartetBeiAnkunft_nichtTrivial :
    ∃ (F F' : Schrittform) (c : Kontext) (s : Zustand),
      F.klasse = .starte ∧ F'.klasse = .starte ∧
        ((F.faedenNach c s).lokal (.faden s.naechsterFaden)).pc ≠
          ((F'.faedenNach c s).lokal (.faden s.naechsterFaden)).pc := by
  let F₁ : Schrittform := (Befehl.faden (.starte 0 5 .bool [])).form
  let F₂ : Schrittform := (Befehl.faden (.starte 0 6 .bool [])).form
  have h₁ := Schrittform.faedenNach_starte_pc F₁ rfl eintritt Leerzustand
  have h₂ := Schrittform.faedenNach_starte_pc F₂ rfl eintritt Leerzustand
  refine ⟨F₁, F₂, eintritt, Leerzustand, rfl, rfl, ?_⟩
  rw [h₁, h₂]
  intro h
  exact absurd h (by decide : (5 : Nat) ≠ 6)

/-! ### Start and join order the memory events -/

/-- **Start and join are ordered in the happens-before relation.** In a graph of the memory model let `w` be a release
    publication of a flag, `r` an acquire observation that reads it, `p` an event before `w` in program order and `q` an
    event after `r` in program order. Then `p` happens before `q`. For a start, `p` is an event of the starter before the
    publication of the start flag, `r` the first observation of the child and `q` any later event of the child, so the
    child sees what the starter did before it started it. For a join, `p` is an event of the ending thread before the
    publication of its end flag, `r` the observation of the joiner after its join and `q` any later event of the joiner,
    so the joiner sees what the ended thread did. -/
def FadenHbAussage : Prop :=
  ∀ (E Ort Wert : Type) (G : Speicher.Graph E Ort Wert), G.Wohlgeformt →
    ∀ p w r q : E, G.po p w → G.rf w r → (G.modus w).stark → (G.modus r).stark → G.po r q → G.hb p q

/-- **Start and join are ordered in the happens-before relation** (the proof of `FadenHbAussage`). -/
theorem fadenHb : FadenHbAussage := by
  intro E Ort Wert G hw p w r q po₁ rf ms mr po₂
  have sw : G.sw w r := Speicher.Graph.sw_direkt hw rf ms mr
  exact G.hb_trans (G.hb_trans (G.hb_von_po po₁) (G.hb_von_sw sw)) (G.hb_von_po po₂)

/-- **The premises of the happens-before statement hold jointly**: the message-passing graph with a `seq_cst` flag. -/
theorem fadenHb_erfuellbar :
    ∃ (G : Speicher.Graph Speicher.MpEv Bool Nat), G.Wohlgeformt ∧
      ∃ p w r q : Speicher.MpEv, G.po p w ∧ G.rf w r ∧ (G.modus w).stark ∧ (G.modus r).stark ∧ G.po r q :=
  ⟨Speicher.mpGraph, Speicher.mp_wf, .wx, .wy, .ry, .rx, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
    Or.inl ⟨rfl, rfl⟩, trivial, trivial, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

/-- **The happens-before statement is not trivial**: with a flag mode too weak to synchronise (a relaxed publication of
    the start flag), the model has a graph with the publication, the observation that reads it and the later event, in
    which the starter's earlier event does NOT happen before the child's later event. A start without a publication of
    release strength is an instruction of the model; the checker's refusal of it is what excludes the race. -/
theorem fadenHb_nichtTrivial :
    ∃ (G : Speicher.Graph Speicher.Atom.StEv Bool Nat), G.Wohlgeformt ∧
      ∃ p w r q : Speicher.Atom.StEv, G.po p w ∧ G.rf w r ∧ G.po r q ∧ ¬ ((G.modus w).stark ∧ (G.modus r).stark) ∧
        ¬ G.hb p q := by
  have weak : ¬ ((Speicher.Modus.rlx).stark ∧ (Speicher.Modus.ra).stark) := fun h => h.1
  refine ⟨Speicher.Atom.stGraph .rlx .ra, Speicher.Atom.stGraph_wf _ _, .wx, .wy, .ry, .rx,
    Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, weak, ?_⟩
  intro hh
  rcases Speicher.Atom.stGraph_hb weak hh with ⟨_, e⟩ | ⟨e, _⟩ <;> cases e

/-! ### The step of a lifecycle instruction is determinate -/

/-- **The step of a lifecycle form is determinate**: the guard decides between the refusal and the planned step, and
    each has one plan and one successor. -/
def FadenBestimmtAussage : Prop :=
  ∀ (F : Schrittform), F.Lebenszyklus → ∀ (c : Kontext) (s : Zustand) (w : PUnit) (plans plans' : List Plan)
    (u u' : Zustand), F.ideal c s w plans u → F.ideal c s w plans' u' → plans = plans' ∧ u = u'

/-- **The step of a lifecycle form is determinate** (the proof of `FadenBestimmtAussage`). -/
theorem fadenBestimmt : FadenBestimmtAussage := by
  intro F hk c s w plans plans' u u' h1 h2
  obtain ⟨k, o, t⟩ := F
  rcases hk with hk | hk | hk | hk <;> change k = _ at hk <;> subst hk <;>
    rcases h1 with ⟨n1, p1, u1⟩ | ⟨b1, p1, u1⟩ <;> rcases h2 with ⟨n2, p2, u2⟩ | ⟨b2, p2, u2⟩
  all_goals first
    | exact (n1 b2).elim
    | exact (n2 b1).elim
    | (subst p1
       subst p2
       subst u1
       subst u2
       exact ⟨rfl, rfl⟩)

/-- **The premises of the determinacy statement hold jointly**: a lifecycle form has a step in every state. -/
theorem fadenBestimmt_erfuellbar :
    ∃ (F : Schrittform) (c : Kontext) (s u : Zustand) (p : Plan), F.Lebenszyklus ∧ F.ideal c s () [p] u := by
  let F : Schrittform := (Befehl.faden (.starte 0 5 .bool [])).form
  exact ⟨F, eintritt, Leerzustand, F.faedenNach eintritt Leerzustand, F.plan (Leerzustand.lokal eintritt) 0,
    Or.inl rfl, Or.inr ⟨⟨rfl, fun _ h => absurd h List.not_mem_nil⟩, rfl, rfl⟩⟩

/-- A rule that lets the refusal and the run both happen. -/
def Schrittform.faedenOffen (F : Schrittform) (c : Kontext) (s : Zustand) (plans : List Plan) (u : Zustand) : Prop :=
  (plans = [Semantik.plan] ∧ u = F.verweigert c s) ∨ (plans = [F.plan (s.lokal c) 0] ∧ u = F.faedenNach c s)

/-- **The determinacy statement is not trivial**: the model represents a rule without the guard, which lets the
    refusal and the run both happen, and that rule is not determinate: from one state it has two different plans. -/
theorem fadenBestimmt_nichtTrivial :
    ∃ (F : Schrittform) (c : Kontext) (s : Zustand) (plans plans' : List Plan) (u u' : Zustand),
      F.Lebenszyklus ∧ F.faedenOffen c s plans u ∧ F.faedenOffen c s plans' u' ∧ plans ≠ plans' := by
  let F : Schrittform := (Befehl.faden (.starte 0 5 .bool [])).form
  refine ⟨F, eintritt, Leerzustand, [Semantik.plan], [F.plan (Leerzustand.lokal eintritt) 0],
    F.verweigert eintritt Leerzustand, F.faedenNach eintritt Leerzustand, Or.inl rfl, Or.inl ⟨rfl, rfl⟩,
    Or.inr ⟨rfl, rfl⟩, ?_⟩
  intro h
  have e := (List.cons.inj (congrArg (fun l : List Plan => l.map SchrittPlan.aktion) h)).1
  cases e

/-! ### The kernel statements, together -/

/-- **The kernel statements of the thread lifecycle**, pinned together. -/
def FadenAussagen : Prop :=
  StarteBestimmtAussage ∧ FadenAutoritaetAussage ∧ VerbindeErgebnisAussage ∧ WechsleAussage ∧
    KindStartetBeiAnkunftAussage ∧ FadenHbAussage ∧ FadenBestimmtAussage

/-- The kernel statements hold. -/
theorem fadenAussagen : FadenAussagen :=
  ⟨starteBestimmt, fadenAutoritaet, verbindeErgebnis, wechselKern, kindStartetBeiAnkunft, fadenHb, fadenBestimmt⟩


end Gabbro.Core.Ast.Semantik
