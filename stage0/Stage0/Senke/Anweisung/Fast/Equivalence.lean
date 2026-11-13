module
public import Stage0.Senke.Anweisung.Fast.Blocks
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration} {V : Vertrag D}

/-- Normalize only cache packaging after each constructor's recursive rewrites. -/
local macro "normalize_cached_code" : tactic => `(tactic| (
  simp only [bind, pure, Option.map_bind, Option.bind_map, Function.comp_def,
    apply_ite, Option.map_none, Option.map_some, CodeCache.value_ofPair, CodeCache.size_ofPair,
    CodeCache.append_ofPair, CodeCache.join_ofPair, CodeCache.narrow_ofPair,
    CodeCache.callElse_ofPair, List.append_nil, List.append_assoc, Nat.max_assoc] <;> rfl))

/- Apply recursive equalities to immediate children before simplification.
   Unfold one selected constructor instead of generating all lowering equations. -/
mutual
/-- Cached execution has exactly the original optional code and scratch ceiling. -/
theorem lowSFast_eq (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout)
  (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (reserved : Nat) (sc : List D.Lock) (frame : FrameCache Γ) :
    lowSFast passes A L layout ens pr ex s reserved sc frame =
      (lowS passes A L layout ens pr ex s reserved sc).map CodeCache.ofPair := by
  cases s with
  | assignVar =>
    unfold lowSFast lowS
    simp only [lowEFast_eq, FrameCache.free_eq, FrameCache.slot_eq] <;>
      normalize_cached_code
  | ite c t e =>
    have ht := fun ex => lowBFast_eq passes A L layout ens pr ex t reserved sc frame
    have he := lowBFast_eq passes A L layout ens pr ex e reserved sc frame
    unfold lowSFast lowS
    simp only [lowEFast_eq, ht, he, FrameCache.free_eq] <;>
      normalize_cached_code
  | call =>
    unfold lowSFast lowS
    simp only [lowAFast_eq, FrameCache.free_eq] <;> normalize_cached_code
  | retWhy =>
    unfold lowSFast lowS
    simp only [FrameCache.free_eq] <;> normalize_cached_code
  | ret =>
    unfold lowSFast lowS
    simp only [lowErgFast_eq, FrameCache.free_eq] <;> normalize_cached_code
  | breaking i body => exact lowBFast_eq passes A L layout ens pr ex body reserved sc frame
  | locks lk hr body =>
    have ih := lowBFast_eq passes A L layout ens pr (16 * 17, 16 * 34)
      body reserved (lk :: sc) frame
    unfold lowSFast lowS
    simp only [ih, FrameCache.free_eq] <;> normalize_cached_code
  | assignSlot => rfl
  | assignThru => rfl
  | assignGlob => rfl
  | putBytes => rfl
  | shift => rfl
  | onOption => rfl
  | onTag => rfl
  | onWhy => rfl
  | callInd => rfl
  | traverse => rfl
  | retry => rfl
  | forever => rfl
  | axiomCall => rfl
  | regWrite => rfl
  | transition => rfl
  | publish => rfl
  | advances => rfl
  | retires => rfl
  | leave => rfl
  | next => rfl
  | assignSlotRef => rfl
  | consumeTraverse => rfl
  | retScoped => rfl
  | retWhyScoped => rfl
  | axiomCallElse => rfl
  | callIndElse => rfl
  | assignThruOwn => rfl
termination_by structural s

/-- Cached execution has exactly the original optional code and scratch ceiling. -/
theorem lowBFast_eq (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout)
  (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (reserved : Nat) (sc : List D.Lock) (frame : FrameCache Γ) :
    lowBFast passes A L layout ens pr ex body reserved sc frame =
      (lowB passes A L layout ens pr ex body reserved sc).map CodeCache.ofPair := by
  cases body with
  | nil =>
    unfold lowBFast lowB
    simp only [FrameCache.free_eq] <;> normalize_cached_code
  | cons s rest =>
    have hs := fun ex => lowSFast_eq passes A L layout ens pr ex s reserved sc frame
    have hr := lowBFast_eq passes A L layout ens pr ex rest reserved sc frame
    unfold lowBFast lowB
    simp only [hr, hs] <;> normalize_cached_code
  | bind e rest =>
    have ih := lowBFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowBFast lowB
    simp only [lowEFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | bindCall f args he hp hr rest =>
    have ih := lowBFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowBFast lowB
    simp only [lowAFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | bindCallElse f args he hp hr err rest =>
    have heq := lowEndFast_eq passes A L layout ens pr ex err reserved sc (frame.push _)
    have hrest := fun ex => lowBFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowBFast lowB
    simp only [lowAFast_eq, heq, hrest, FrameCache.free_eq] <;>
      normalize_cached_code
  | narrow e low high err rest =>
    have hr := lowBFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    have he := fun ex => lowEndFast_eq passes A L layout ens pr ex err reserved sc frame
    unfold lowBFast lowB
    simp only [lowEFast_eq, hr, he, FrameCache.free_eq] <;>
      normalize_cached_code
  | narrowRequired e low high rest =>
    have ih := lowBFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowBFast lowB
    simp only [lowEFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | check c err rest =>
    have he := lowEndFast_eq passes A L layout ens pr ex err reserved sc frame
    have hr := fun ex => lowBFast_eq passes A L layout ens pr ex rest reserved sc frame
    unfold lowBFast lowB
    simp only [lowEFast_eq, he, hr, FrameCache.free_eq] <;>
      normalize_cached_code
  | bindCallInd => rfl
  | bindAxiom => rfl
  | bindAxiomElse => rfl
  | regRead => rfl
  | regReadElse => rfl
  | awaits => rfl
  | exchange => rfl
  | float => rfl
  | floatLit => rfl
  | floatOf => rfl
  | floatNarrow => rfl
  | bindAxiomOpt => rfl
  | bindAxiomOptElse => rfl
  | bindCallIndElse => rfl
termination_by structural body

/-- Cached execution has exactly the original optional code and scratch ceiling. -/
theorem lowEndFast_eq (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout)
  (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (body : Endblock D V l Γ Λ) (reserved : Nat) (sc : List D.Lock) (frame : FrameCache Γ) :
    lowEndFast passes A L layout ens pr ex body reserved sc frame =
      (lowEnd passes A L layout ens pr ex body reserved sc).map CodeCache.ofPair := by
  cases body with
  | leave =>
    unfold lowEndFast lowEnd
    simp only [FrameCache.free_eq] <;> normalize_cached_code
  | next =>
    unfold lowEndFast lowEnd
    simp only [FrameCache.free_eq] <;> normalize_cached_code
  | retWhy =>
    unfold lowEndFast lowEnd
    simp only [FrameCache.free_eq] <;> normalize_cached_code
  | ret =>
    unfold lowEndFast lowEnd
    simp only [lowErgFast_eq, FrameCache.free_eq] <;> normalize_cached_code
  | cons s rest =>
    have hs := fun ex => lowSFast_eq passes A L layout ens pr ex s reserved sc frame
    have hr := lowEndFast_eq passes A L layout ens pr ex rest reserved sc frame
    unfold lowEndFast lowEnd
    simp only [hr, hs] <;> normalize_cached_code
  | bind e rest =>
    have ih := lowEndFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowEndFast lowEnd
    simp only [lowEFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | bindCall f args he hp hr rest =>
    have ih := lowEndFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowEndFast lowEnd
    simp only [lowAFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | bindCallElse f args he hp hr err rest =>
    have heq := lowEndFast_eq passes A L layout ens pr ex err reserved sc (frame.push _)
    have hrest := fun ex => lowEndFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowEndFast lowEnd
    simp only [lowAFast_eq, heq, hrest, FrameCache.free_eq] <;>
      normalize_cached_code
  | ite c t e =>
    have ht := fun ex => lowEndFast_eq passes A L layout ens pr ex t reserved sc frame
    have he := lowEndFast_eq passes A L layout ens pr ex e reserved sc frame
    unfold lowEndFast lowEnd
    simp only [lowEFast_eq, ht, he, FrameCache.free_eq] <;>
      normalize_cached_code
  | narrow e low high err rest =>
    have hr := lowEndFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    have he := fun ex => lowEndFast_eq passes A L layout ens pr ex err reserved sc frame
    unfold lowEndFast lowEnd
    simp only [lowEFast_eq, hr, he, FrameCache.free_eq] <;>
      normalize_cached_code
  | narrowRequired e low high rest =>
    have ih := lowEndFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowEndFast lowEnd
    simp only [lowEFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | bindAxiom => rfl
  | bindAxiomElse => rfl
  | regRead => rfl
  | regReadElse => rfl
  | awaits => rfl
  | bindCallInd => rfl
  | exchange => rfl
  | retScoped => rfl
  | retWhyScoped => rfl
  | bindAxiomOpt => rfl
  | bindAxiomOptElse => rfl
  | bindCallIndElse => rfl
  | float => rfl
  | floatLit => rfl
  | floatOf => rfl
  | floatNarrow => rfl
termination_by structural body

end

end Gabbro.Stage0.Senke
