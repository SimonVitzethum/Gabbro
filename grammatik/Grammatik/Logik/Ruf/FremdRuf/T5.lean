/- Part 5 of `FremdRuf` (C08 foundation): the generalized foreign contract, its
   locality and replay, and the software foreign obligations.

   `AxVor`/`AxNach` evaluate the interface pre/post of `CallContract` at the actual
   call: entry world, original arguments, post world, transported result, entry world
   as `old` -- the same old-state discipline as `ReqAmEintritt`/`EnsAmRueck`. The
   normal post applies only on normal return; reason exits keep owed invariants and
   resources, never an invented normal `result`. `AxVertragONeu` is the generalized
   `AxVertragO`; `AxVorLokal`/`AxNachLokal` are its interim write-carrier locality
   (the guarded pre/post footprints replace this rule); `VertragANeu`,
   `orakelAus_vertrag_neu` and `axWelt_vertrag_neu` replay it through recorded
   answers exactly as `VertragA`/`orakelAus_vertrag`/`axWelt_vertrag` do.

   `axPre_of_contract` reuses the existing pre split (`AxPre`, `AufruferPflicht`,
   `AxVertragOP`, `RufFolgePflicht`) for the caller side. `ForeignPflicht` is the
   software clause of premise (b): every software item's proved realization
   establishes the contract, decodes every answer, meets its boundary clauses and
   realizes its provider facts against the actual binding `O`. Sequential logic
   still quantifies over ALL answers meeting the declared summaries; the caller's
   pre at every call prefix (`CallSitePflicht`) joins from C06; an unexpected
   software answer is `Logik.fremdAntwort`, excluded here by decoding and in runs
   by the existing no-logic-halt conclusion. Only a named hardware-origin decoder
   violation may retain `Hardware.annahme`. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T4
public import Grammatik.Logik.Ruf.FremdRuf.T2
public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Zielsatz.Kern.Spec.Teil1

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-- The interface precondition at the call: the contract pre over the entry world
    and the original arguments. -/
def AxVor (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) (a : D.Ax) (σ0 : World D)
    (ρ : Env D (D.aparams a)) : Prop :=
  wahr? (eval σ0 (ax a).pre σ0 ρ) = true

/-- The interface postcondition on normal return: the contract post over the post
    world and the transported result, with the entry world as `old`. -/
def AxNach (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) (a : D.Ax) (σ0 : World D)
    (ρ : Env D (D.aparams a)) (σ1 : World D) (v : ErgVal D (D.aerg a)) : Prop :=
  wahr? (eval σ0 (ax a).post σ1 (ergEnv (D.aerg a) v ρ)) = true

/-- The generalized contract premise (C08): under the pre, every fitting answer
    meets the post on normal return. Reason outcomes carry no normal post. -/
def AxVertragONeu (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax) (σ0 : World D) (ρ : Env D (D.aparams a)), AxVor ax a σ0 ρ →
    ∀ v : ErgVal D (D.aerg a),
      einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ0.fragt (.inl a)) ρ).2 = some v →
      AxNach ax a σ0 ρ (O.wirkt a (σ0.fragt (.inl a)) ρ).1 v

/-- Pre locality (interim, write carriers only): the pre reads only the entry world
    through the declared frame. The guarded pre footprint replaces this rule. -/
def AxVorLokal (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) : Prop :=
  ∀ (a : D.Ax) (σ σ' : World D) (ρ : Env D (D.aparams a)),
    (∀ t, D.aschreibt a t = true → σ.slots t = σ'.slots t) →
    (∀ g, D.agschreibt a g = true → σ.globs g = σ'.globs g) →
    (AxVor ax a σ ρ ↔ AxVor ax a σ' ρ)

/-- Post locality (interim, write carriers only): the post reads only the post world
    through the declared frame. The guarded post footprint replaces this rule. -/
def AxNachLokal (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) : Prop :=
  ∀ (a : D.Ax) (σ0 σ1 σ1' : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
    (∀ t, D.aschreibt a t = true → σ1.slots t = σ1'.slots t) →
    (∀ g, D.agschreibt a g = true → σ1.globs g = σ1'.globs g) →
    (AxNach ax a σ0 ρ σ1 v ↔ AxNach ax a σ0 ρ σ1' v)

/-- Every recorded axiom answer meets the generalized contract. -/
def VertragANeu (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) (z : Int → Option D.Fn)
    (HA : List (AxEintrag D)) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA →
    ∀ v : ErgVal D (D.aerg a), einpassenErg z (D.aerg a) x.2 = some v → AxNach ax a σ ρ x.1 v

theorem vertragANeu_nil (ax : ∀ a : D.Ax, CallContract D (D.asignatur a))
    (z : Int → Option D.Fn) : VertragANeu ax z ([] : List (AxEintrag D)) :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

/-- The oracle of a record meets the generalized contract when the machine's oracle
    does and every recorded answer does. -/
theorem orakelAus_vertrag_neu {ax : ∀ a : D.Ax, CallContract D (D.asignatur a)} {O : Orakel D}
    (hQ : AxVertragONeu ax O) {HA : List (AxEintrag D)} (hv : VertragANeu ax O.zeiger HA) :
    AxVertragONeu ax (orakelAus O HA) := by
  intro a σ0 ρ hpre v
  simp only [orakelAus]
  split
  · rename_i hex
    intro hfit
    have hpost := hv a (σ0.fragt (.inl a)) ρ _ (Classical.choose_spec hex) v hfit
    -- Replay keys include the question event; contract expressions do not read it.
    exact (congrArg wahr? (eval_spurfrei (ax a).post (σ0.fragt (.inl a)) σ0
      (Classical.choose hex).1 (Classical.choose hex).1 rfl rfl rfl rfl
      (ergEnv (D.aerg a) v ρ))).symm.trans hpost
  · exact hQ a σ0 ρ hpre v

/-- The recorded answer world agrees with the machine's answer world on the axiom's
    declared carriers, so a local generalized post transfers. -/
theorem axWelt_vertrag_neu {ax : ∀ a : D.Ax, CallContract D (D.asignatur a)}
    (hlok : AxNachLokal ax) (e0 : Ereignis D) (a : D.Ax)
    (κ σ₂ : World D) (σ0 : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a))
    (h : AxNach ax a σ0 ρ σ₂ v) : AxNach ax a σ0 ρ (axWelt e0 a κ σ₂) v := by
  exact (hlok a σ0 (axWelt e0 a κ σ₂) σ₂ ρ v (fun t ht => by
      show (if D.aschreibt a t = true then σ₂.slots t else κ.slots t) = σ₂.slots t
      rw [if_pos ht])
    (fun g hg => by
      show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = σ₂.globs g
      rw [if_pos hg])).mpr h

/-- The contract pre as a gate precondition: reuses `AxPre`, hence `AufruferPflicht`,
    `AxVertragOP` and `RufFolgePflicht` for the caller side. -/
def axPre_of_contract (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) : AxPre D :=
  fun a σ ρ => wahr? (eval σ (ax a).pre σ ρ)

theorem aufruferPflicht_axVor (ax : ∀ a : D.Ax, CallContract D (D.asignatur a))
    (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    AufruferPflicht (axPre_of_contract ax) a σ ρ ↔ AxVor ax a σ ρ :=
  Iff.rfl

/-- The software foreign obligations (C08, premise (b) side, over the history `H`):
    every software item's proved realization establishes the generalized contract
    under its pre, decodes every answer (no `Logik.fremdAntwort`), meets its
    boundary clauses at every successful recorded call against the entry live-grant
    inventory, and realizes its provider facts against the actual binding `O`. -/
structure ForeignPflicht (E : Einheit D) (O : Orakel D) (H : List (BoundaryRecord D)) : Prop where
  vertrag : ∀ a : D.Ax, D.axHerkunft a = some .software →
    ∀ (σ0 : World D) (ρ : Env D (D.aparams a)), AxVor E.P.axVertrag a σ0 ρ →
      ∀ v : ErgVal D (D.aerg a),
        einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ0.fragt (.inl a)) ρ).2 = some v →
        AxNach E.P.axVertrag a σ0 ρ (O.wirkt a (σ0.fragt (.inl a)) ρ).1 v
  dekodiert : ∀ a : D.Ax, D.axHerkunft a = some .software →
    ∀ (σ : World D) (ρ : Env D (D.aparams a)),
      (axiomAntwortSonst O a σ ρ).2 ≠ none
  klauseln : ∀ (n : Fin H.length), (H.get n).erfolg = true →
    ∀ c ∈ (E.P.axVertrag (H.get n).ax).grenzen,
      klauselGilt (H.get n).ax (H.get n).eingabe (H.get n).args
        (GrantInventory (H.take n.val)) (H.get n).ausgabe (H.get n).konzession c
  anbieter : ProviderRealisiert O H

/-- Provider fidelity (C08 goal leg): the history realizes against `O`, and the live
    grants are pairwise disjoint -- one global inventory across all threads, so
    per-thread freshness cannot admit cross-thread aliases. -/
def ProviderTreueG (O : Orakel D) (H : List (BoundaryRecord D)) : Prop :=
  ProviderRealisiert O H ∧
  ∀ i j : Fin (GrantInventory H).length, i ≠ j →
    ¬ ((GrantInventory H).get i).ueberschneidet ((GrantInventory H).get j)

/-- The initial-inventory obligation (C08): the source-declared initial grants are
    pairwise disjoint, with provenance and correspondence to initial capabilities
    proved in `StartPflicht`'s extension, rather than an empty external world
    assumed. -/
def GrantsStart (E : Einheit D) : Prop :=
  ∀ i j : Fin E.grants0.length, ∀ ki kj, (E.grants0.get i).konzession = some ki →
    (E.grants0.get j).konzession = some kj → i ≠ j → ¬ ki.ueberschneidet kj

theorem grantsStart_leer (E : Einheit D) (h : E.grants0 = []) : GrantsStart E := by
  unfold GrantsStart
  rw [h]
  intro i j ki kj hki hkj hne
  have h0 : i.val < 0 := by simpa using i.isLt
  omega

end Gabbro.Grammatik
