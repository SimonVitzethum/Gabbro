module

public import Core.Maschine.Messdaten
public import Core.Beobachtung.Fluss.Beschriftung.Sicht
public import Mathlib.Data.Finset.Lattice.Basic

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Ast.Semantik

/-- Surface level attribute (D-4): `public` and `secret` are the two named
    spellings, `compartment s` is a free compartment set. Elaboration maps
    every level to an `Etikett`; only this mapping reaches the flow rule. -/
inductive Pegel where
  | public
  | secret
  | compartment (mitglieder : Finset Nat)
  deriving DecidableEq

/-- Elaboration of the type attribute into a compartment label.
    `public` is the empty label, `secret` is the singleton `{0}`,
    a compartment denotes itself. -/
def Pegel.zuEtikett : Pegel → Etikett
  | .public => ∅
  | .secret => {0}
  | .compartment s => s

theorem pegel_public_oeffentlich : oeffentlich Pegel.public.zuEtikett = true := by
  simp only [Pegel.zuEtikett, oeffentlich_leer]

theorem pegel_secret_verborgen : oeffentlich Pegel.secret.zuEtikett = false := by
  simp only [Pegel.zuEtikett, oeffentlich]
  apply decide_eq_false
  intro eq
  have mem : 0 ∈ ({0} : Etikett) := Finset.mem_singleton_self _
  rw [eq] at mem
  exact Finset.notMem_empty _ mem

theorem pegel_compartment_elab (s : Finset Nat) :
    (Pegel.compartment s).zuEtikett = s := rfl

/-- A source type carries its level as an attribute; the checker elaborates
    the attribute, never the type itself, into the label the flow rule reads. -/
structure BeschrifteterTyp where
  pegel : Pegel

def BeschrifteterTyp.etikett (t : BeschrifteterTyp) : Etikett :=
  t.pegel.zuEtikett

/-- The per-position declaration is built from type attributes: every entry
    is the elaboration of the level written at that type. -/
def beschriftungAusPegel (tempPegel lokalPegel : Nat → Nat → Pegel)
    (ergebnis : Pegel) : Ast.Semantik.Beschriftung :=
  { temp := fun pc s => (tempPegel pc s).zuEtikett
    lokal := fun pc i => (lokalPegel pc i).zuEtikett
    ergebnis := ergebnis.zuEtikett }

/-- Every entry of a declaration built from type attributes is the
    elaboration of the written level. The flow rule therefore reads only
    elaborated type attributes. -/
theorem beschriftungAusPegel_elab (tempPegel lokalPegel : Nat → Nat → Pegel)
    (ergebnis : Pegel) (pc s i : Nat) :
    (beschriftungAusPegel tempPegel lokalPegel ergebnis).temp pc s =
      (tempPegel pc s).zuEtikett ∧
    (beschriftungAusPegel tempPegel lokalPegel ergebnis).lokal pc i =
      (lokalPegel pc i).zuEtikett ∧
    (beschriftungAusPegel tempPegel lokalPegel ergebnis).ergebnis =
      ergebnis.zuEtikett :=
  ⟨rfl, rfl, rfl⟩

/-- A release declaration (D-4): the single downgrading form `release … to L`.
    Data only, no propositions and no function parameters: `stelle` selects the
    `Freigabe` entry of the flow data, `quelle` repeats its source label, and
    `ziel` is the declared target level `L`. The side condition (target below
    source) lives in `ReleaseDekl.gilt`, not in the structure. -/
structure ReleaseDekl where
  stelle : Nat
  quelle : Etikett
  ziel : Etikett

/-- The declaration holds of a flow-data release: the site declares the same
    source, and the target is below the source (downgrade, never upgrade). -/
def ReleaseDekl.gilt {Wert : Type} (r : ReleaseDekl) (g : Freigabe Wert) : Prop :=
  r.quelle = g.quelle ∧ r.ziel ⊆ r.quelle

/-- Release is the only downgrading form: every `Freigabe` entry of the flow
    data is covered by a release declaration with the same source. Ordinary
    outputs (`Ausgabe.wert`) carry no declaration and never downgrade. -/
def NurReleaseStuftHerab {Form Lok Ort Wert : Type}
    (fluss : Flussdaten Form Lok Ort Wert) (r : Nat → Option ReleaseDekl) : Prop :=
  ∀ id g, fluss.freigabe id = some g → ∃ d, r id = some d ∧ d.quelle = g.quelle

end Gabbro.Core.Beobachtung
