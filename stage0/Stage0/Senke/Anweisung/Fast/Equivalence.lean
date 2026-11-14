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

/- Match syntax directly so structural recursion can identify immediate children.
   Apply their recursive equalities before simplification.
   Unfold one selected constructor instead of generating all lowering equations. -/
mutual
/-- Cached execution has exactly the original optional code and scratch ceiling. -/
theorem lowSFast_eq (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout)
  (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (reserved : Nat) (sc : List D.Lock) (frame : FrameCache Γ) :
    lowSFast passes A L layout ens pr ex s reserved sc frame =
      (lowS passes A L layout ens pr ex s reserved sc).map CodeCache.ofPair :=
  match s with
  | .assignVar .. => by
    unfold lowSFast lowS
    simp only [lowEFast_eq, FrameCache.free_eq, FrameCache.slot_eq]
    split <;> rename_i guard <;>
      (try simp only [guard, ↓reduceIte]) <;> normalize_cached_code
  | .ite c t e => by
    have ht := fun ex => lowBFast_eq passes A L layout ens pr ex t reserved sc frame
    have he := lowBFast_eq passes A L layout ens pr ex e reserved sc frame
    unfold lowSFast lowS
    simp only [lowEFast_eq, ht, he, FrameCache.free_eq] <;>
      normalize_cached_code
  | .call .. => by
    unfold lowSFast lowS
    simp only [lowAFast_eq, FrameCache.free_eq] <;> normalize_cached_code
  | .retWhy .. => by
    unfold lowSFast lowS
    simp only [FrameCache.free_eq]
    split <;> rename_i guard <;>
      (try simp only [guard, ↓reduceIte]) <;> normalize_cached_code
  | .ret .. => by
    unfold lowSFast lowS
    simp only [lowErgFast_eq, FrameCache.free_eq]
    split <;> rename_i guard <;>
      (try simp only [guard, ↓reduceIte]) <;> normalize_cached_code
  | .breaking i body => by exact lowBFast_eq passes A L layout ens pr ex body reserved sc frame
  | .locks lk hr body => by
    have ih := lowBFast_eq passes A L layout ens pr (16 * 17, 16 * 34)
      body reserved (lk :: sc) frame
    unfold lowSFast lowS
    simp only [ih, FrameCache.free_eq]
    split <;> rename_i guard <;>
      (try simp only [guard, ↓reduceIte]) <;> normalize_cached_code
  | .assignSlot .. => by rfl
  | .assignThru .. => by rfl
  | .assignGlob .. => by rfl
  | .putBytes .. => by rfl
  | .shift .. => by rfl
  | .onOption .. => by rfl
  | .onTag .. => by rfl
  | .onWhy .. => by rfl
  | .callInd .. => by rfl
  | .traverse .. => by rfl
  | .retry .. => by rfl
  | .forever .. => by rfl
  | .axiomCall .. => by rfl
  | .regWrite .. => by rfl
  | .transition .. => by rfl
  | .publish .. => by rfl
  | .advances .. => by rfl
  | .retires .. => by rfl
  | .leave .. => by rfl
  | .next .. => by rfl
  | .assignSlotRef .. => by rfl
  | .consumeTraverse .. => by rfl
  | .retScoped .. => by rfl
  | .retWhyScoped .. => by rfl
  | .axiomCallElse .. => by rfl
  | .callIndElse .. => by rfl
  | .assignThruOwn .. => by rfl
termination_by structural s

/-- Cached execution has exactly the original optional code and scratch ceiling. -/
theorem lowBFast_eq (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout)
  (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (reserved : Nat) (sc : List D.Lock) (frame : FrameCache Γ) :
    lowBFast passes A L layout ens pr ex body reserved sc frame =
      (lowB passes A L layout ens pr ex body reserved sc).map CodeCache.ofPair :=
  match body with
  | .nil => by
    unfold lowBFast lowB
    simp only [FrameCache.free_eq] <;> normalize_cached_code
  | .cons s rest => by
    have hs := fun ex => lowSFast_eq passes A L layout ens pr ex s reserved sc frame
    have hr := lowBFast_eq passes A L layout ens pr ex rest reserved sc frame
    unfold lowBFast lowB
    simp only [hr, hs] <;> normalize_cached_code
  | .bind e rest => by
    have ih := lowBFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowBFast lowB
    simp only [lowEFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | .bindCall f args he hp hr rest => by
    have ih := lowBFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowBFast lowB
    simp only [lowAFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | .bindCallElse f args he hp hr err rest => by
    have heq := lowEndFast_eq passes A L layout ens pr ex err reserved sc (frame.push _)
    have hrest := fun ex => lowBFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowBFast lowB
    simp only [lowAFast_eq, heq, hrest, FrameCache.free_eq] <;>
      normalize_cached_code
  | .narrow e low high err rest => by
    have hr := lowBFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    have he := fun ex => lowEndFast_eq passes A L layout ens pr ex err reserved sc frame
    unfold lowBFast lowB
    simp only [lowEFast_eq, hr, he, FrameCache.free_eq] <;>
      normalize_cached_code
  | .narrowRequired e low high rest => by
    have ih := lowBFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowBFast lowB
    simp only [lowEFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | .check c err rest => by
    have he := lowEndFast_eq passes A L layout ens pr ex err reserved sc frame
    have hr := fun ex => lowBFast_eq passes A L layout ens pr ex rest reserved sc frame
    unfold lowBFast lowB
    simp only [lowEFast_eq, he, hr, FrameCache.free_eq] <;>
      normalize_cached_code
  | .bindCallInd .. => by rfl
  | .bindAxiom .. => by rfl
  | .bindAxiomElse .. => by rfl
  | .regRead .. => by rfl
  | .regReadElse .. => by rfl
  | .awaits .. => by rfl
  | .exchange .. => by rfl
  | .float .. => by rfl
  | .floatLit .. => by rfl
  | .floatOf .. => by rfl
  | .floatNarrow .. => by rfl
  | .bindAxiomOpt .. => by rfl
  | .bindAxiomOptElse .. => by rfl
  | .bindCallIndElse .. => by rfl
termination_by structural body

/-- Cached execution has exactly the original optional code and scratch ceiling. -/
theorem lowEndFast_eq (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout)
  (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (body : Endblock D V l Γ Λ) (reserved : Nat) (sc : List D.Lock) (frame : FrameCache Γ) :
    lowEndFast passes A L layout ens pr ex body reserved sc frame =
      (lowEnd passes A L layout ens pr ex body reserved sc).map CodeCache.ofPair :=
  match body with
  | .leave .. => by
    unfold lowEndFast lowEnd
    simp only [FrameCache.free_eq]
    split <;> rename_i guard <;>
      (try simp only [guard, ↓reduceIte]) <;> normalize_cached_code
  | .next .. => by
    unfold lowEndFast lowEnd
    simp only [FrameCache.free_eq]
    split <;> rename_i guard <;>
      (try simp only [guard, ↓reduceIte]) <;> normalize_cached_code
  | .retWhy .. => by
    unfold lowEndFast lowEnd
    simp only [FrameCache.free_eq]
    split <;> rename_i guard <;>
      (try simp only [guard, ↓reduceIte]) <;> normalize_cached_code
  | .ret .. => by
    unfold lowEndFast lowEnd
    simp only [lowErgFast_eq, FrameCache.free_eq]
    split <;> rename_i guard <;>
      (try simp only [guard, ↓reduceIte]) <;> normalize_cached_code
  | .cons s rest => by
    have hs := fun ex => lowSFast_eq passes A L layout ens pr ex s reserved sc frame
    have hr := lowEndFast_eq passes A L layout ens pr ex rest reserved sc frame
    unfold lowEndFast lowEnd
    simp only [hr, hs] <;> normalize_cached_code
  | .bind e rest => by
    have ih := lowEndFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowEndFast lowEnd
    simp only [lowEFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | .bindCall f args he hp hr rest => by
    have ih := lowEndFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowEndFast lowEnd
    simp only [lowAFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | .bindCallElse f args he hp hr err rest => by
    have heq := lowEndFast_eq passes A L layout ens pr ex err reserved sc (frame.push _)
    have hrest := fun ex => lowEndFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowEndFast lowEnd
    simp only [lowAFast_eq, heq, hrest, FrameCache.free_eq] <;>
      normalize_cached_code
  | .ite c t e => by
    have ht := fun ex => lowEndFast_eq passes A L layout ens pr ex t reserved sc frame
    have he := lowEndFast_eq passes A L layout ens pr ex e reserved sc frame
    unfold lowEndFast lowEnd
    simp only [lowEFast_eq, ht, he, FrameCache.free_eq] <;>
      normalize_cached_code
  | .narrow e low high err rest => by
    have hr := lowEndFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    have he := fun ex => lowEndFast_eq passes A L layout ens pr ex err reserved sc frame
    unfold lowEndFast lowEnd
    simp only [lowEFast_eq, hr, he, FrameCache.free_eq] <;>
      normalize_cached_code
  | .narrowRequired e low high rest => by
    have ih := lowEndFast_eq passes A L layout ens pr ex rest reserved sc (frame.push _)
    unfold lowEndFast lowEnd
    simp only [lowEFast_eq, ih, FrameCache.free_eq] <;>
      normalize_cached_code
  | .bindAxiom .. => by rfl
  | .bindAxiomElse .. => by rfl
  | .regRead .. => by rfl
  | .regReadElse .. => by rfl
  | .awaits .. => by rfl
  | .bindCallInd .. => by rfl
  | .exchange .. => by rfl
  | .retScoped .. => by rfl
  | .retWhyScoped .. => by rfl
  | .bindAxiomOpt .. => by rfl
  | .bindAxiomOptElse .. => by rfl
  | .bindCallIndElse .. => by rfl
  | .float .. => by rfl
  | .floatLit .. => by rfl
  | .floatOf .. => by rfl
  | .floatNarrow .. => by rfl
termination_by structural body

end

end Gabbro.Stage0.Senke
