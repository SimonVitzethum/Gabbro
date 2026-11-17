module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Snapshots
public import Grammatik.Logik.Vertraege.Pruefer.Control.Entry
public import Grammatik.Logik.Invarianten.Frag.Witness

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.SnapshotWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Frag.Symbolic
open Invarianten.Frag.Witness Pruefer.Symbolic

abbrev u32 : Ty := .int 0 (2 ^ 32 - 1)
abbrev symbols : SymEnv declaration Nat [u32] := .cons (.integer (.var 0)) .nil
def actual : Env declaration [u32] := .cons ⟨7, by decide, by decide⟩ .nil
def incoming : Assignment Nat := fun _ => 7
def observations : List (Observation declaration) := [.glob false, .glob true, .slot () () 1]
def frozen : Assignment Nat := Snapshot.extend 1 observations incoming initial

def after : World declaration :=
  { initial with
    globs := fun name => ⟨if name then 8 else 9, by split <;> decide, by split <;> decide⟩
    slots := fun _ _ _ => ⟨9, by decide, by decide⟩ }

theorem extend_preserves_zeuge : frozen 0 = incoming 0 ∧ frozen 4 = incoming 4 :=
  ⟨Snapshot.extend_preserves observations 1 incoming initial 0 (Or.inl (by decide)),
   Snapshot.extend_preserves observations 1 incoming initial 4 (Or.inr (by decide))⟩

theorem extend_realizes_zeuge : Snapshot.Realizes 1 observations frozen initial :=
  Snapshot.extend_realizes observations 1 incoming initial

theorem lookup_sound_zeuge : frozen 1 = assignment initial (.glob false) ∧
    frozen 2 = assignment initial (.glob true) :=
  ⟨Snapshot.lookup_sound observations 1 (.glob false) 1 rfl frozen initial extend_realizes_zeuge,
   Snapshot.lookup_sound observations 1 (.glob true) 2 rfl frozen initial extend_realizes_zeuge⟩

theorem equations_denote_zeuge : (Snapshot.equations 1 observations).denote (values frozen initial) :=
  (Snapshot.equations_denote observations 1 frozen initial).mpr extend_realizes_zeuge

theorem realizes_congr_zeuge : Snapshot.Realizes 1 observations (frozen.bind 4 19) initial := by
  apply (Snapshot.realizes_congr observations 1 frozen (frozen.bind 4 19) initial ?_).mp extend_realizes_zeuge
  intro key lower upper
  have different : key ≠ 4 := by change key < 4 at upper; omega
  simp only [Assignment.bind, different, ↓reduceIte]

def post : Expr declaration [u32] [] .bool :=
  .and (.eq (.glob false (globalAccess false)) (.add (.oldG false (globalAccess false)) (.lit 6)))
    (.and (.not (.eq (.oldG false (globalAccess false)) (.oldG true (globalAccess true))))
      (.eq (.oldS () () (.widen (by decide) (by decide) (.lit 1))
        (fun _ member => nomatch member)) (.lit 4)))

theorem observations_zeuge : Snapshot.names post = observations := rfl

def encoded := (translateSnapshot observations 1 post symbols).toOption.get (by rfl)

theorem old_entry_correspondence_zeuge :
    wahr? (eval initial post after actual) = true ∧ encoded.payload.denote (values frozen after) := by
  have realized : symbols.Realizes frozen after actual :=
    ⟨extend_preserves_zeuge.1, trivial⟩
  have correct := encoded.bool_iff frozen initial after actual extend_realizes_zeuge realized
  have evaluated : wahr? (eval initial post after actual) = true := by decide
  exact ⟨evaluated, correct.mp evaluated⟩

theorem bool_iff_zeuge : wahr? (eval initial post after actual) = true ↔
    encoded.payload.denote (values frozen after) :=
  encoded.bool_iff frozen initial after actual extend_realizes_zeuge ⟨extend_preserves_zeuge.1, trivial⟩

def oldGlobal : Expr declaration [u32] [] (.int 0 10) := .oldG false (globalAccess false)
def encodedGlobal := (translateSnapshot observations 1 oldGlobal symbols).toOption.get (by rfl)

theorem constantIndex_zeuge : encodedGlobal.constantIndex = .error .crossEntry := rfl

theorem snapshotFormula_sound_zeuge :
    (LProp.eq (.var (.inr 1)) (.var (.inl (.glob false)))).denote (values frozen initial) := by
  apply snapshotFormula_sound 1 observations _ incoming initial
  change ∀ a b c : Int, (a = 3 ∧ (b = 8 ∧ (c = 4 ∧ True))) → a = 3
  exact fun _ _ _ selected => selected.1

def currentPost : Expr declaration [u32] [] .bool := .le (.glob false (globalAccess false)) (.lit 10)

theorem snapshotPlan_of_current_zeuge : snapshotPlan currentPost = .ok none :=
  snapshotPlan_of_current currentPost ((currentOnly currentPost).toOption.get (by rfl)) (by rfl)

def bounded : symbols.Bounded 4 :=
  ⟨fun key member => by have same := List.mem_singleton.mp member; subst key; decide, trivial⟩

def region : Snapshot.Region declaration 4 := ⟨1, observations, by decide⟩

theorem region_realizes_congr_zeuge :
    Snapshot.Realizes (Snapshot.regionStart (some region)) (Snapshot.regionNames (some region))
      (frozen.bind 4 19) initial := by
  apply (Snapshot.region_realizes_congr (some region) frozen (frozen.bind 4 19) initial ?_).mp extend_realizes_zeuge
  intro key before
  have different : key ≠ 4 := by omega
  simp only [Assignment.bind, different, ↓reduceIte]

theorem entryContext_locals_zeuge : symbols.Realizes frozen initial actual :=
  entryContext_locals symbols bounded (some region) frozen (initial, actual)
    ⟨⟨extend_preserves_zeuge.1, trivial⟩, extend_realizes_zeuge⟩

theorem entryContext_memory_zeuge : Snapshot.Realizes 1 observations frozen initial :=
  entryContext_memory symbols bounded (some region) frozen (initial, actual)
    ⟨entryContext_locals_zeuge, extend_realizes_zeuge⟩

end Gabbro.Grammatik.Vertraege.Pruefer.SnapshotWitness
