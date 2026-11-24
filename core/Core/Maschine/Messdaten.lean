module
public import Core.Katalog.Lauf
public import Core.Katalog.Spekulation
public import Core.Maschine.Kontext
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Lattice.Basic


@[expose] public section

namespace Gabbro.Core.Beobachtung


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
    The form implementing a timed block exposes its live activations in the local state. -/
structure Schrankendaten (L Lok : Type) where
  kosten : Option Nat := none
  speicher : Option Nat := none
  stapel : Option Nat := none
  halten : L → Option Nat := fun _ => none
  stapelTiefe : Lok → Nat := fun _ => 0
  zeit : Nat → Option Zeitdeklaration := fun _ => none
  zeitstand : Lok → List Zeitmarke := fun _ => []

def Schrankendaten.leer : Schrankendaten L Lok := {}

open Katalog Maschine

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
  | freigabe (stelle : Nat) (wert : Wert)

/-- Form-owned observation data. Journals in local state are append-only within an activation.
    A speculative execution includes all instruction slots up to its first fence or resolution. -/
structure Flussdaten (Form Lok Ort Wert : Type) where
  konstantzeit : Form → Bool := fun _ => false
  ausgaben : Lok → List (Ausgabe Wert) := fun _ => []
  freigabe : Nat → Option (Freigabe Wert) := fun _ => none
  spekulativ : Form → Lok → Praediktor → List (Option Ort) := fun _ _ _ => []

def Flussdaten.leer : Flussdaten Form Lok Ort Wert := {}

end Gabbro.Core.Beobachtung
