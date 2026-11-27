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
        simp [niFrage, FremdKanal.frage, Frage.zugriffe, AussenOperation.required],
      by simp [niEtiketten, niHandle, niObjekt]⟩⟩

private theorem exchange_angebot : Plattform.x86_64.operationAngeboten niFrage = true :=
  fremdkanal_angebot _ _ _ _

private theorem atomar_exchange (body : List UInt8) :
    atomar Plattform.x86_64 (niSicht body) niFrage = .antwort (niAntwort body) := by
  simp [atomar, niFrage, niKanal, niHandle, niObjekt, niSicht, niAntwort,
    FremdKanal.frage, Frage.zugriffe, AussenOperation.required,
    Plattform.operationAngeboten, AussenSicht.gueltig, AussenSicht.herkunft,
    AussenSicht.wartet, AussenSicht.erfolg, AussenSicht.leer]

private theorem keine_niObjekt (q : Frage) (niedrig : oeffentlich (niEtiketten.frage q) = true) :
    ∀ a ∈ q.zugriffe, a.handle.origin.object ≠ niObjekt := by
  intro a mem gleich
  have hoch : oeffentlich (niEtiketten.frage q) = false :=
    (Etiketten.frage_hoch_iff niEtiketten q).2
      ⟨7, Or.inr ⟨a, mem, by rw [gleich]; simp [niEtiketten]⟩⟩
  rw [niedrig] at hoch
  cases hoch

private theorem herkunft_gleich (b₁ b₂ : List UInt8) {o : Objekt} (h : o ≠ niObjekt) :
    (niSicht b₁).herkunft o = (niSicht b₂).herkunft o := by
  simp [AussenSicht.herkunft, niSicht, h]

private theorem gueltig_gleich (b₁ b₂ : List UInt8) (q : Frage)
    (keine : ∀ a ∈ q.zugriffe, a.handle.origin.object ≠ niObjekt) :
    ∀ a ∈ q.zugriffe, (niSicht b₁).gueltig q.endpoint a = (niSicht b₂).gueltig q.endpoint a := by
  intro a mem
  have hne := keine a mem
  simp [AussenSicht.gueltig, AussenSicht.herkunft, niSicht, hne]

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
  simp [AussenSicht.wartet, niSicht, hne, Plattform.registerWert, Plattform.geraet]

private theorem erfolg_gleich (b₁ b₂ : List UInt8) (q : Frage)
    (hne : q.handle.origin.object ≠ niObjekt) :
    (niSicht b₁).erfolg Plattform.x86_64 q = (niSicht b₂).erfolg Plattform.x86_64 q := by
  simp [AussenSicht.erfolg, AussenSicht.herkunft, AussenSicht.leer, niSicht, hne,
    Plattform.registerWert, Plattform.geraet]

private theorem bereit_gleich (b₁ b₂ : List UInt8) {o : Objekt} (h : o ≠ niObjekt) :
    ((niSicht b₁).objects o).ready = ((niSicht b₂).objects o).ready := by
  simp [niSicht, h]

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
      simp [niEtiketten, niSicht, oeffentlich, sichtbar]
    · simp [niEtiketten, niSicht, oeffentlich, sichtbar, h]
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
      · simp [sichtbar, hoch]
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
  refine ⟨?_, ?_, ?_, ?_, ?_, frage_hoch, exchange_angebot, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, projektion_gleich [] [1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Umgebung.referenz_hardware _ _ _ (Plattform.katalog_wohlgeformt _) (by decide)
  · exact Umgebung.referenz_hardware _ _ _ (Plattform.katalog_wohlgeformt _) (by decide)
  · simp [niEtiketten, niObjekt]
  · intro o h
    simp [niEtiketten, h]
  · intro e
    rfl
  · decide
  · decide
  · rfl
  · rfl
  · exact atomar_exchange []
  · exact atomar_exchange [1]
  · rfl
  · rfl
  · intro h
    cases h
  · intro o h
    simp [niSicht, h]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro h
    cases h

end Gabbro.Core.Beobachtung
