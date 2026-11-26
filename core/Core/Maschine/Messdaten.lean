module
public import Core.Katalog.Lauf
public import Core.Katalog.Spekulation
public import Core.Maschine.Kontext
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Lattice.Basic


@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

/-- Timing declarations identify the required hardware duration row and the cost of the fallback. -/
structure Zeitdeklaration where
  zeile : Nat
  frist : Nat
  lateKosten : Nat

/-- The active body, its completed deadline check, or the fallback selected by that check.
    Indices refer to hardware cuts, with the first cut identifying this activation. -/
inductive Zeitphase where
  | rumpf
  | rechtzeitig (geprueft : Nat)
  | late (geprueft : Nat)
  deriving DecidableEq

structure Zeitmarke where
  block : Nat
  anfang : Nat
  phase : Zeitphase
  deriving DecidableEq

/-- Elaborated declarations and layout interpretation. A missing optional resource bound is open.
    The form implementing a timed block exposes its live activations in the local state.
    Cost marks (`durchlauf`/`durchlaufstand`, MK-12) bound the cost of one pass or call each
    (`per_pass bounded n ops`, `costs <= n ops`, `on_exceeded`): `durchlauf` is the declared
    ceiling per open mark (block number), `durchlaufstand` lists the open marks as
    (block number, opening cut) read from the local state. Open marks stay admitted
    (`durchlauf = fun _ => none`). -/
structure Schrankendaten (L Lok : Type) where
  kosten : Option Nat := none
  speicher : Option Nat := none
  stapel : Option Nat := none
  halten : L → Option Nat := fun _ => none
  stapelTiefe : Lok → Nat := fun _ => 0
  zeit : Nat → Option Zeitdeklaration := fun _ => none
  zeitstand : Lok → List Zeitmarke := fun _ => []
  durchlauf : Nat → Option Nat := fun _ => none
  durchlaufstand : Lok → List (Nat × Nat) := fun _ => []
  /-- A restart applies the unit's declared clearing to every local state, so no cost mark
      of an aborted pass survives. The field is stated over the clearing function the
      restart carries: the default stand is empty for every state and discharges this by
      reflexivity; a unit that exposes local marks supplies the proof for its own clearing
      operation. -/
  durchlaufstand_nachVerwerfenLeer : ∀ (verwerfen : Lok → Lok) (l : Lok),
    durchlaufstand (verwerfen l) = [] := by
    intro _ l
    rfl
  /-- The same clearing applies to the time marks. -/
  zeitstand_nachVerwerfenLeer : ∀ (verwerfen : Lok → Lok) (l : Lok),
    zeitstand (verwerfen l) = [] := by
    intro _ l
    rfl

def Schrankendaten.leer : Schrankendaten L Lok := {}

/-- Compartments ordered by inclusion, with union as join and intersection as meet.
    The empty label is public. -/
abbrev Etikett := Finset Nat

/-- Labels are assigned to locations and channel identities, independently of the values they carry.
    Reply metadata for a low question is public together with its result. -/
structure Etiketten (Ort : Type) where
  ort : Ort → Etikett := fun _ => ∅
  bootByte : Nat → Etikett := fun _ => ∅
  persist : Nat → Etikett := fun _ => ∅
  objekt : Objekt → Etikett := fun _ => ∅
  endpunkt : Endpunkt → Etikett := fun _ => ∅
  ausgabe : Nat → Etikett := fun _ => ∅
  ende : Kontext → Etikett := fun _ => ∅

def Etiketten.leer : Etiketten Ort := {}

/-- A low question uses a public interface and only public object identities. -/
def Etiketten.frage (e : Etiketten Ort) (q : Frage) : Etikett :=
  (q.zugriffe.map (fun t => e.objekt t.handle.origin.object)).foldl (· ∪ ·) (e.endpunkt q.endpoint)

/-- The bottom element is visible to the public observer. -/
def oeffentlich (label : Etikett) : Bool :=
  decide (label = ∅)

private theorem mem_foldl_etiketten (teil : Nat) (etiketten : List Etikett) (anfang : Etikett) :
    teil ∈ etiketten.foldl (· ∪ ·) anfang ↔
      teil ∈ anfang ∨ ∃ e ∈ etiketten, teil ∈ e := by
  induction etiketten generalizing anfang with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, or_false]
  | cons e rest ih =>
    rw [List.foldl_cons, ih, Finset.mem_union]
    constructor
    · rintro ((start | first) | ⟨later, mem, part⟩)
      · exact Or.inl start
      · exact Or.inr ⟨e, List.mem_cons_self, first⟩
      · exact Or.inr ⟨later, List.mem_cons_of_mem _ mem, part⟩
    · rintro (start | ⟨label, mem, part⟩)
      · exact Or.inl (Or.inl start)
      · rcases List.mem_cons.mp mem with rfl | later
        · exact Or.inl (Or.inr part)
        · exact Or.inr ⟨label, later, part⟩

/-- Each compartment of a question comes from its endpoint or the origin object of one of
    its handles, including the primary operand and every additional access. -/
theorem Etiketten.mem_frage (e : Etiketten Ort) (q : Frage) (teil : Nat) :
    teil ∈ e.frage q ↔ teil ∈ e.endpunkt q.endpoint ∨
      ∃ a ∈ q.zugriffe, teil ∈ e.objekt a.handle.origin.object := by
  rw [Etiketten.frage, mem_foldl_etiketten]
  constructor
  · rintro (endpoint | ⟨label, mem, part⟩)
    · exact Or.inl endpoint
    · obtain ⟨a, access, rfl⟩ := List.mem_map.mp mem
      exact Or.inr ⟨a, access, part⟩
  · rintro (endpoint | ⟨a, access, part⟩)
    · exact Or.inl endpoint
    · exact Or.inr ⟨_, List.mem_map_of_mem access, part⟩

/-- A question is high exactly when at least one of its classification sources contributes
    a compartment under the existing public projection. -/
theorem Etiketten.frage_hoch_iff (e : Etiketten Ort) (q : Frage) :
    oeffentlich (e.frage q) = false ↔ ∃ teil, teil ∈ e.endpunkt q.endpoint ∨
      ∃ a ∈ q.zugriffe, teil ∈ e.objekt a.handle.origin.object := by
  rw [oeffentlich, decide_eq_false_iff_not]
  exact Finset.nonempty_iff_ne_empty.symm.trans (exists_congr (e.mem_frage q))

def sichtbar (label : Etikett) (datum : A) : Option A :=
  if oeffentlich label then some datum else none


/-- A release declaration exposes the indicated projection of its payload. Two releases at
    the same site may vary only within a fibre of the declared projection. -/
structure Freigabe (Wert : Type) where
  quelle : Etikett
  kanal : Nat
  projektion : Wert → Wert

inductive Ausgabe (Wert : Type) where
  | wert (kanal : Nat) (wert : Wert)
  | freigabe (stelle : Nat) (quelle : Etikett) (wert : Wert)

/-- A place carries a label and a projection of the local store. The projections retain
    the type of the store, and the enumeration and labels are independent of its values. -/
structure LokaleEtiketten (Lok : Type) where
  plaetze : Nat
  etikett : Fin plaetze → Etikett
  lesen : Lok → Fin plaetze → Lok

def LokaleEtiketten.ganz (etikett : Etikett) : LokaleEtiketten Lok :=
  ⟨1, fun _ => etikett, fun s _ => s⟩

def LokaleEtiketten.gleich (e : LokaleEtiketten Lok) (v u : Lok) : Prop :=
  ∀ p, oeffentlich (e.etikett p) = true → e.lesen v p = e.lesen u p

/-- Only public ordinary outputs are visible. A release occurrence is always visible. -/
def Ausgabe.niedrig (e : Etiketten Ort) : Ausgabe Wert → Bool
  | .wert kanal _ => oeffentlich (e.ausgabe kanal)
  | .freigabe _ _ _ => true

/-- Form-owned observation data. Journals in local state are append-only within an activation.
    A speculative execution includes all instruction slots up to its first fence or resolution. -/
structure Flussdaten (Form Lok Ort Wert : Type) where
  konstantzeit : Form → Bool := fun _ => false
  ausgaben : Lok → List (Ausgabe Wert) := fun _ => []
  freigabe : Nat → Option (Freigabe Wert) := fun _ => none
  spekulativ : Form → Lok → Praediktor → List (Option Ort) := fun _ _ _ => []
  lokal : Kontext → LokaleEtiketten Lok := fun _ => .ganz ∅
  kontrolle : Form → Etikett := fun _ => ∅

def Flussdaten.leer : Flussdaten Form Lok Ort Wert := {}

def Flussdaten.ausgabeZuwachs (f : Flussdaten Form Lok Ort Wert) (v u : Lok) : List (Ausgabe Wert) :=
  (f.ausgaben u).drop (f.ausgaben v).length

end Gabbro.Core.Beobachtung
