module

public import Core.Beobachtung.Projektion
public import Core.Maschine.Messdaten
public import Core.Katalog.Aussen
public import Core.Katalog.Auswahl
public import Core.Katalog.Erfuellbar
public import Core.Katalog.Fremdkanal

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

/-- The one object classified by the pinned `cProcess` row (PERFECT-MODEL M12-NI). -/
def niObjekt : Objekt := ⟨.cProcess, 1⟩

/-- Only this object carries a compartment; endpoints and every other label stay public. -/
def niEtiketten : Etiketten Objekt :=
  { Etiketten.leer with objekt := fun o => if o = niObjekt then {7} else ∅ }

/-- The offered channel operation on the pinned row: `exchange` with no extra objects. -/
def niKanal : FremdKanal := ⟨0, none⟩

def niHandle : Handle := ⟨0, ⟨niObjekt, 0⟩, [.invoke]⟩

def niFrage : Frage := niKanal.frage niHandle [7]

/-- Two physical snapshots that agree everywhere except the body of `niObjekt`. -/
def niSicht (body : List UInt8) : AussenSicht :=
  { AussenSicht.leer with
    objects := fun o => if o = niObjekt then ⟨0, true, true, body, fun _ => 0⟩
      else AussenSicht.leer.objects o
    channels := fun e i => if e = .cProcess ∧ i = 0 then some niHandle else none }

def niAntwort (body : List UInt8) : Antwort :=
  ⟨⟨niObjekt, 0⟩, [⟨niObjekt, 0⟩], .ok (.exchanged [7] body)⟩

private theorem frage_hoch : oeffentlich (niEtiketten.frage niFrage) = false :=
  (Etiketten.frage_hoch_iff niEtiketten niFrage).2
    ⟨7, Or.inr ⟨⟨niHandle, .invoke⟩, by
        simp only [Frage.zugriffe, niFrage, FremdKanal.frage, AussenOperation.required, List.mem_cons,
          List.not_mem_nil, or_false],
      by simp only [niEtiketten, niObjekt, niHandle, ↓reduceIte, Finset.mem_singleton]⟩⟩

private theorem exchange_angebot : Plattform.x86_64.operationAngeboten niFrage = true :=
  fremdkanal_angebot _ _ _ _

private theorem atomar_exchange (body : List UInt8) :
    atomar Plattform.x86_64 (niSicht body) niFrage = .antwort (niAntwort body) := by
  simp only [atomar, Plattform.operationAngeboten, niFrage, FremdKanal.frage, niHandle, niObjekt,
    List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Frage.zugriffe, AussenOperation.required, niSicht,
    AussenSicht.leer, List.all_cons, AussenSicht.gueltig, BEq.rfl, and_self, Bool.and_self, AussenSicht.herkunft,
    List.mem_cons, List.not_mem_nil, or_false, decide_true, List.all_nil, AussenSicht.wartet, List.map_cons,
    List.map_nil, AussenSicht.erfolg, niAntwort]

private theorem keine_niObjekt (q : Frage) (niedrig : oeffentlich (niEtiketten.frage q) = true) :
    ∀ a ∈ q.zugriffe, a.handle.origin.object ≠ niObjekt := by
  intro a mem gleich
  have hoch : oeffentlich (niEtiketten.frage q) = false :=
    (Etiketten.frage_hoch_iff niEtiketten q).2
      ⟨7, Or.inr ⟨a, mem, by rw [gleich]; simp only [niEtiketten, ↓reduceIte, Finset.mem_singleton]⟩⟩
  rw [niedrig] at hoch
  cases hoch

private theorem herkunft_gleich (b₁ b₂ : List UInt8) {o : Objekt} (h : o ≠ niObjekt) :
    (niSicht b₁).herkunft o = (niSicht b₂).herkunft o := by
  simp only [AussenSicht.herkunft, niSicht, h, ↓reduceIte]

private theorem gueltig_gleich (b₁ b₂ : List UInt8) (q : Frage)
    (keine : ∀ a ∈ q.zugriffe, a.handle.origin.object ≠ niObjekt) :
    ∀ a ∈ q.zugriffe, (niSicht b₁).gueltig q.endpoint a = (niSicht b₂).gueltig q.endpoint a := by
  intro a mem
  have hne := keine a mem
  simp only [AussenSicht.gueltig, niSicht, hne, ↓reduceIte, AussenSicht.herkunft]

private theorem all_gleich {α : Type} (l : List α) {f g : α → Bool}
    (h : ∀ a ∈ l, f a = g a) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.all_cons]
      rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

private theorem map_herkunft_gleich (b₁ b₂ : List UInt8) (l : List Zugriff)
    (keine : ∀ a ∈ l, a.handle.origin.object ≠ niObjekt) :
    l.map (fun a => (niSicht b₁).herkunft a.handle.origin.object) =
      l.map (fun a => (niSicht b₂).herkunft a.handle.origin.object) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons]
      rw [herkunft_gleich b₁ b₂ (keine a List.mem_cons_self)]
      rw [ih (fun b hb => keine b (List.mem_cons_of_mem a hb))]

private theorem wartet_gleich (b₁ b₂ : List UInt8) (q : Frage)
    (hne : q.handle.origin.object ≠ niObjekt) :
    (niSicht b₁).wartet Plattform.x86_64 q = (niSicht b₂).wartet Plattform.x86_64 q := by
  simp only [AussenSicht.wartet, niSicht, hne, ↓reduceIte, Plattform.registerWert, Plattform.geraet,
    Bool.not_and]

private theorem erfolg_gleich (b₁ b₂ : List UInt8) (q : Frage)
    (hne : q.handle.origin.object ≠ niObjekt) :
    (niSicht b₁).erfolg Plattform.x86_64 q = (niSicht b₂).erfolg Plattform.x86_64 q := by
  simp only [AussenSicht.erfolg, niSicht, AussenSicht.leer, hne, ↓reduceIte, Plattform.registerWert,
    Plattform.geraet, Nat.zero_mod]

private theorem bereit_gleich (b₁ b₂ : List UInt8) {o : Objekt} (h : o ≠ niObjekt) :
    ((niSicht b₁).objects o).ready = ((niSicht b₂).objects o).ready := by
  simp only [niSicht, h, ↓reduceIte]

/-- A public question never reaches the one classified object, so its atomic answer is the
    same under both snapshots although their high bodies differ. -/
private theorem atomar_niedrig_gleich (b₁ b₂ : List UInt8) (q : Frage)
    (niedrig : oeffentlich (niEtiketten.frage q) = true) :
    atomar Plattform.x86_64 (niSicht b₁) q = atomar Plattform.x86_64 (niSicht b₂) q := by
  have keine := keine_niObjekt q niedrig
  have hobj : q.handle.origin.object ≠ niObjekt := keine _ List.mem_cons_self
  simp only [atomar]
  rw [all_gleich q.zugriffe (gueltig_gleich b₁ b₂ q keine)]
  rw [herkunft_gleich b₁ b₂ hobj]
  rw [map_herkunft_gleich b₁ b₂ q.zugriffe keine]
  rw [wartet_gleich b₁ b₂ q hobj]
  rw [bereit_gleich b₁ b₂ hobj]
  rw [erfolg_gleich b₁ b₂ q hobj]

private theorem sicht_gleich (b₁ b₂ : List UInt8) :
    niedereAussensicht niEtiketten (niSicht b₁) = niedereAussensicht niEtiketten (niSicht b₂) := by
  unfold niedereAussensicht
  apply Prod.ext
  · funext o
    by_cases h : o = niObjekt
    · subst o
      simp only [sichtbar, oeffentlich, niEtiketten, ↓reduceIte, Finset.singleton_union, Finset.insert_ne_empty,
        decide_false, Bool.false_eq_true]
    · simp only [sichtbar, oeffentlich, niEtiketten, h, ↓reduceIte, Finset.empty_union, decide_eq_true_eq, niSicht]
  · apply Prod.ext
    · funext e i
      rfl
    · funext o bytes
      rfl

/-- The two reference environments have the same TOTAL policy projection: every public sight,
    every potential low request and every DMA entry agrees. Only the hidden high answer differs. -/
private theorem projektion_gleich (b₁ b₂ : List UInt8) :
    politikProjektion niEtiketten
        (Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => niSicht b₁)).politik =
      politikProjektion niEtiketten
        (Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => niSicht b₂)).politik := by
  unfold politikProjektion
  apply Prod.ext
  · funext t history
    change niedereAussensicht niEtiketten (niSicht b₁) =
      niedereAussensicht niEtiketten (niSicht b₂)
    exact sicht_gleich b₁ b₂
  · apply Prod.ext
    · funext t history q
      change sichtbar (niEtiketten.frage q) (atomar Plattform.x86_64 (niSicht b₁) q) =
        sichtbar (niEtiketten.frage q) (atomar Plattform.x86_64 (niSicht b₂) q)
      by_cases hoch : oeffentlich (niEtiketten.frage q) = false
      · simp only [sichtbar, hoch, Bool.false_eq_true, ↓reduceIte]
      · have niedrig : oeffentlich (niEtiketten.frage q) = true := by
          cases h : oeffentlich (niEtiketten.frage q) <;> simp_all
        simp only [sichtbar, niedrig, Bool.false_eq_true, ↓reduceIte]
        exact congrArg some (atomar_niedrig_gleich b₁ b₂ q niedrig)
    · funext t history e phase
      rfl

/-- M12-NI at the policy/catalog boundary: one classified `cProcess` object 1, two reference
    environments with equal total low projection (all potential low requests and DMA), and one
    high valid exchange that succeeds atomically with two different bodies. The physical
    snapshots differ only in that body; commit and run semantics are untouched. The step-level
    machine run, an accepted source program and low traces are NOT built here — that remains
    the open source-run boundary of `ni_erfuellbar`. -/
theorem katalogPolitikNI_erfuellbar :
    ∃ (E : Etiketten Objekt) (h₁ h₂ : Umgebung) (q : Frage) (s₁ s₂ : AussenSicht)
      (a₁ a₂ : Antwort) (t : Nat) (history : AussenVerlauf),
      Hardware Plattform.x86_64.katalog h₁ ∧ Hardware Plattform.x86_64.katalog h₂ ∧
      h₁.politik.sicht t history = s₁ ∧ h₂.politik.sicht t history = s₂ ∧
      h₁.politik.antwort t history q = .antwort a₁ ∧
      h₂.politik.antwort t history q = .antwort a₂ ∧
      E.objekt niObjekt ≠ ∅ ∧ (∀ o, o ≠ niObjekt → E.objekt o = ∅) ∧
      (∀ e, E.endpunkt e = ∅) ∧
      oeffentlich (E.frage q) = false ∧
      Plattform.x86_64.operationAngeboten q = true ∧
      q.zugriffe.all (s₁.gueltig q.endpoint) = true ∧
      q.zugriffe.all (s₂.gueltig q.endpoint) = true ∧
      s₁.wartet Plattform.x86_64 q = false ∧ s₂.wartet Plattform.x86_64 q = false ∧
      atomar Plattform.x86_64 s₁ q = .antwort a₁ ∧
      atomar Plattform.x86_64 s₂ q = .antwort a₂ ∧
      a₁.result.isOk = true ∧ a₂.result.isOk = true ∧ a₁.result ≠ a₂.result ∧
      politikProjektion E h₁.politik = politikProjektion E h₂.politik ∧
      (∀ o, o ≠ niObjekt → s₁.objects o = s₂.objects o) ∧
      s₁.channels = s₂.channels ∧ s₁.names = s₂.names ∧
      (s₁.objects niObjekt).generation = (s₂.objects niObjekt).generation ∧
      (s₁.objects niObjekt).alive = (s₂.objects niObjekt).alive ∧
      (s₁.objects niObjekt).ready = (s₂.objects niObjekt).ready ∧
      (s₁.objects niObjekt).registers = (s₂.objects niObjekt).registers ∧
      (s₁.objects niObjekt).body ≠ (s₂.objects niObjekt).body := by
  refine ⟨niEtiketten,
    Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => niSicht []),
    Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => niSicht [1]),
    niFrage, niSicht [], niSicht [1], niAntwort [], niAntwort [1], 0, [], ?_⟩
  refine ⟨?_, ?_, rfl, rfl, atomar_exchange [], atomar_exchange [1],
    ?_, ?_, ?_, frage_hoch, exchange_angebot, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, projektion_gleich [] [1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Umgebung.referenz_hardware _ _ _ (Plattform.katalog_wohlgeformt _) (Nat.zero_lt_succ 0)
  · exact Umgebung.referenz_hardware _ _ _ (Plattform.katalog_wohlgeformt _) (Nat.zero_lt_succ 0)
  · simp only [niEtiketten, niObjekt, ↓reduceIte, ne_eq, Finset.singleton_ne_empty, not_false_eq_true]
  · intro o h
    simp only [niEtiketten, h, ↓reduceIte]
  · intro e
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact atomar_exchange []
  · exact atomar_exchange [1]
  · rfl
  · rfl
  · intro h
    cases h
  · intro o h
    simp only [niSicht, h, ↓reduceIte]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro h
    cases h

/-- The narrowest sufficient relation on two physical commit snapshots at one real cut: every
    public question receives the same TOTAL atomic decision. It is stated on the total snapshot,
    not on a projection of a filtered history: a high answer in that history may revoke a public
    handle, and a low projection hides handles behind `sichtbar`. -/
def OeffentlicheAntwortKopplung (E : Etiketten Objekt) (p : Plattform)
    (s₁ s₂ : AussenSicht) : Prop :=
  ∀ q, oeffentlich (E.frage q) = true → atomar p s₁ q = atomar p s₂ q

/-- For the named `cProcess` row the relation holds at the witness's real commit snapshots: a
    public question never reaches the one classified object, so its total decision agrees although
    the two high bodies differ. -/
theorem ni_oeffentlicheAntwortKopplung (b₁ b₂ : List UInt8) :
    OeffentlicheAntwortKopplung niEtiketten Plattform.x86_64 (niSicht b₁) (niSicht b₂) := by
  intro q niedrig
  exact atomar_niedrig_gleich b₁ b₂ q niedrig

private def niOeffentlichesObjekt : Objekt := ⟨.hosted, 2⟩

private def niOeffentlicherHandle : Handle :=
  ⟨0, ⟨niOeffentlichesObjekt, 0⟩, [.read]⟩

private def niOeffentlicheFrage : Frage :=
  ⟨.hosted, niOeffentlicherHandle, [], .read⟩

private theorem niOeffentlicherHandle_oeffentlich :
    oeffentlich (niEtiketten.frage niOeffentlicheFrage) = true := by
  cases h : oeffentlich (niEtiketten.frage niOeffentlicheFrage)
  · exfalso
    obtain ⟨teil, klasse | ⟨zugriff, mem, klasse⟩⟩ :=
      (Etiketten.frage_hoch_iff niEtiketten niOeffentlicheFrage).1 h
    · simp only [niEtiketten, Etiketten.leer] at klasse
    · have zug : zugriff = ⟨niOeffentlicherHandle, .read⟩ := by
        simpa only [niOeffentlicheFrage, Frage.zugriffe] using mem
      subst zugriff
      simp [niEtiketten, niObjekt, niOeffentlicherHandle, niOeffentlichesObjekt] at klasse
  · rfl

/-- The public cProcess object is live and readable; its body is carried by `body`. -/
private def niSichtOeffenMit (body : List UInt8) : AussenSicht :=
  { niSicht [] with
    objects := fun o =>
      if o = niOeffentlichesObjekt then ⟨0, true, true, body, fun _ => 0⟩
      else (niSicht []).objects o
    channels := fun e i =>
      if e = .hosted ∧ i = 0 then some niOeffentlicherHandle
      else (niSicht []).channels e i }

private def niSichtRevokation : AussenSicht := niSichtOeffenMit [1]

private theorem atomar_niOeffen (body : List UInt8) :
    atomar Plattform.x86_64 (niSichtOeffenMit body) niOeffentlicheFrage =
      .antwort ⟨⟨niOeffentlichesObjekt, 0⟩, [⟨niOeffentlichesObjekt, 0⟩], .ok (.data body)⟩ := by
  simp only [atomar, Plattform.operationAngeboten, niOeffentlicheFrage, niOeffentlicherHandle,
    niOeffentlichesObjekt, Frage.zugriffe, AussenOperation.required, List.isEmpty_nil,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, AussenSicht.gueltig, AussenSicht.herkunft,
    niSichtOeffenMit, niSicht, AussenSicht.leer, AussenSicht.wartet, AussenSicht.erfolg,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, decide_true,
    beq_iff_eq, and_self, Bool.and_self]

/-- A high answer to the classified question in the TOTAL history: the filter drops it. -/
private def hatHoheAntwort (history : AussenVerlauf) : Bool :=
  history.any fun entry =>
    match entry.2 with
    | .antwort q _ => q == niFrage
    | .frage _ => false

private theorem hatHoheAntwort_niedrig (history : AussenVerlauf) :
    hatHoheAntwort (niedrigerVerlauf niEtiketten history) = false := by
  cases h : hatHoheAntwort (niedrigerVerlauf niEtiketten history)
  · rfl
  · exfalso
    unfold hatHoheAntwort at h
    obtain ⟨entry, mem, wirkt⟩ := List.any_eq_true.mp h
    unfold niedrigerVerlauf at mem
    have gefiltert := (List.mem_filter.mp mem).2
    rcases entry with ⟨t, ereignis⟩
    cases ereignis with
    | frage q => simp at wirkt
    | antwort q a =>
        have gleich : q = niFrage := beq_iff_eq.mp wirkt
        subst q
        change oeffentlich (niEtiketten.frage niFrage) = true at gefiltert
        rw [frage_hoch] at gefiltert
        cases gefiltert

private def niUmgebungAuf : Umgebung :=
  Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => niSichtOeffenMit [])

private def niUmgebungZu : Umgebung :=
  Umgebung.referenz Plattform.x86_64.katalog 1
    (fun _ history => if hatHoheAntwort history then niSichtRevokation else niSichtOeffenMit [])

private theorem niUmgebungAuf_hardware : Hardware Plattform.x86_64.katalog niUmgebungAuf := by
  exact Umgebung.referenz_hardware _ _ _ (Plattform.katalog_wohlgeformt _) (Nat.zero_lt_succ 0)

private theorem niUmgebungZu_hardware : Hardware Plattform.x86_64.katalog niUmgebungZu := by
  exact Umgebung.referenz_hardware _ _ _ (Plattform.katalog_wohlgeformt _) (Nat.zero_lt_succ 0)

private theorem niUmgebungen_projektionGleich :
    politikProjektion niEtiketten niUmgebungAuf.politik =
      politikProjektion niEtiketten niUmgebungZu.politik := by
  unfold politikProjektion
  apply Prod.ext
  · funext t history
    have h := hatHoheAntwort_niedrig history
    simp only [niUmgebungAuf, niUmgebungZu, Umgebung.referenz, h, ↓reduceIte]
  · apply Prod.ext
    · funext t history q
      have h := hatHoheAntwort_niedrig history
      simp only [niUmgebungAuf, niUmgebungZu, Umgebung.referenz, h, ↓reduceIte]
    · funext t history e phase
      rfl

/-- Equal total low projections do not give the relation at a real commit, even under the pinned
    cProcess catalogue row: a high answer in the total history changes a public object's body at
    the commit, an effect the low filter cannot see. This is the exact failing implication. -/
theorem projektionGleich_ohne_antwortKopplung :
    ∃ (h₁ h₂ : Umgebung) (t : Nat) (history : AussenVerlauf) (q : Frage),
      Hardware Plattform.x86_64.katalog h₁ ∧ Hardware Plattform.x86_64.katalog h₂ ∧
      politikProjektion niEtiketten h₁.politik = politikProjektion niEtiketten h₂.politik ∧
      oeffentlich (niEtiketten.frage q) = true ∧
      atomar Plattform.x86_64 (h₁.politik.sicht t history) q ≠
        atomar Plattform.x86_64 (h₂.politik.sicht t history) q := by
  let history : AussenVerlauf := [(0, .antwort niFrage (niAntwort []))]
  have hhoch : hatHoheAntwort history = true := by
    simp only [history, hatHoheAntwort, List.any_cons, List.any_nil, Bool.or_false]
    exact beq_iff_eq.mpr rfl
  refine ⟨niUmgebungAuf, niUmgebungZu, 0, history, niOeffentlicheFrage,
    niUmgebungAuf_hardware, niUmgebungZu_hardware, niUmgebungen_projektionGleich,
    niOeffentlicherHandle_oeffentlich, ?_⟩
  simp only [niUmgebungAuf, niUmgebungZu, Umgebung.referenz, hhoch, ↓reduceIte, atomar_niOeffen]
  simp

end Gabbro.Core.Beobachtung
