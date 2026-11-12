/-
  Soundness of the declared hold bound (`lock L … held <= n ops`, rule K002).

  The export gate admits a literal hold bound. `HeldBinding.holds` checks, over the lowered
  program, that every `locks L { … }` section of a lock with a declared bound costs at most
  that bound in own steps of machine G (`kostenBlock`, each call counted at the callee's
  declared cost), and calls only functions that declare a cost. This module extracts the
  syntactic fact from that Bool:

  * `holds_haltE`: `holds` gives the walker's `haltE … = true` for every function body;
  * `halt_sectionsS/B/Arms/GArms/E`: the walker implies `sectionsOkS/B/Arms/GArms/E`, the
    same statement read as a Prop over every `locks` section occurring anywhere in the term
    (proved by mutual induction over the walker, one equation per constructor);
  * `holds_sectionsE`: the composition over all functions of a unit accepted by `holds`;
  * `sectionsOkS_locks`: inversion at one section (its body's `kostenBlock` fits under the
    bound of its lock, and its callees declare costs).

  This is item (c) of the task: the syntactic bound for every section body. Items (a) (a
  run-level hold bound between entering and leaving a `locks` section) and (b) (a run-level
  bound for a section body as a block) are NOT proved here, and cannot be proved from what
  exists today:

  * KostenG bounds FRAMES (`kosten_passt_deklaration`: own steps between a frame's `Eintritt`
    and its return are at most the declared cost, counted by `SegLauf`/`segZaehle` under
    `aktivVor`). There is no block-level counting lemma: no notion of "entering a `locks`
    section" on a run, no `SegLauf` restricted to a section body, no bound on the own steps
    taken while a section is open.
  * `Deklaration` carries no hold field (a lock is `rang` and `maskiert` only); the bound
    lives in the source tables `H`, not in the model, so no run-level statement can name it.
  * `Haltezeit` (in `Logik/Fortschritt/Warten.lean`) counts SCHEDULER steps (`zaehl` over a
    `PlanLauf`): own steps plus waiting, at most `h L` own steps of which at most `k L` at a
    `locks` head. This module says nothing about waiting, about steps taken at a `locks`
    head while acquiring, about named stops inside a section (`return`/`leave`/`next`, some
    of which have no release yet -- the eight red `c11-scoped` probes), or about fairness
    and FIFO (`LaufzeitAnnahme`), all of which a run-level hold-time theorem would need.
  * Calls inside a section are counted at the callee's declared cost (`rufeB`); lifting that
    number to runs needs the callee's own frame bound, which is future work of the same kind
    as (b).

  Wiring: this module is built once `public import Grammatik.Parser.Elab.Export.Held.Satz`
  is added to `grammatik/Grammatik.lean` (not done here: no existing file is touched).
-/
module
public import Grammatik.Parser.Elab.Export.HeldBinding
@[expose] public section

namespace Gabbro.Grammatik.Parser.HeldBinding
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

variable {D : Deklaration}

/-! ## 1. The section property, as a Prop over each syntax sort -/

mutual
/-- Every `locks` section occurring in the statement satisfies the declared bound of its
    lock (`kostenBlock` at the callee-cost table, callees with a declared cost), and so does
    every section nested inside. This is the walker's `haltS` read as a Prop. -/
def sectionsOkS (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Prop
  | .locks L _ body =>
    (∀ n, h L = some n → kostenBlock c pa body ≤ n ∧ rufeB Z (fun _ => false) true body = true) ∧
      sectionsOkB h c Z pa body
  | .ite _ t e => sectionsOkB h c Z pa t ∧ sectionsOkB h c Z pa e
  | .onOption _ p a => sectionsOkB h c Z pa p ∧ sectionsOkB h c Z pa a
  | .onTag _ arms => sectionsOkArms h c Z pa arms
  | .onWhy _ arms => sectionsOkGArms h c Z pa arms
  | .callIndElse _ _ _ _ _ err => sectionsOkE h c Z pa err
  | .breaking _ body => sectionsOkB h c Z pa body
  | .traverse _ _ body => sectionsOkB h c Z pa body
  | .consumeTraverse _ _ _ _ _ _ body => sectionsOkB h c Z pa body
  | .retry _ _ body ueber => sectionsOkB h c Z pa body ∧ sectionsOkB h c Z pa ueber
  | .forever _ _ body => sectionsOkB h c Z pa body
  | .axiomCallElse _ _ _ _ _ _ _ _ err => sectionsOkE h c Z pa err
  | .call .. | .callInd .. | .assignSlot .. | .assignThru .. | .assignGlob .. | .putBytes .. |
    .assignVar .. | .shift .. | .axiomCall .. | .regWrite .. | .transition .. | .publish .. |
    .advances .. | .retires .. | .ret .. | .retWhy .. | .retScoped .. | .retWhyScoped .. |
    .leave .. | .next .. | .assignSlotRef .. | .assignThruOwn .. => True

/-- Every `locks` section occurring in the block satisfies the declared bound of its lock. -/
def sectionsOkB (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Prop
  | .nil => True
  | .cons s rest => sectionsOkS h c Z pa s ∧ sectionsOkB h c Z pa rest
  | .bind _ rest => sectionsOkB h c Z pa rest
  | .bindCall _ _ _ _ _ rest => sectionsOkB h c Z pa rest
  | .bindCallInd _ _ _ _ _ rest => sectionsOkB h c Z pa rest
  | .bindCallIndElse _ _ _ _ _ err rest => sectionsOkE h c Z pa err ∧ sectionsOkB h c Z pa rest
  | .bindCallElse _ _ _ _ _ err rest => sectionsOkE h c Z pa err ∧ sectionsOkB h c Z pa rest
  | .bindAxiom _ _ _ _ _ _ _ rest => sectionsOkB h c Z pa rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => sectionsOkE h c Z pa err ∧ sectionsOkB h c Z pa rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => sectionsOkB h c Z pa rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest =>
      sectionsOkE h c Z pa err ∧ sectionsOkB h c Z pa rest
  | .regRead _ _ rest => sectionsOkB h c Z pa rest
  | .regReadElse _ _ _ sonst rest => sectionsOkE h c Z pa sonst ∧ sectionsOkB h c Z pa rest
  | .awaits _ _ _ _ _ rest => sectionsOkB h c Z pa rest
  | .exchange _ _ _ _ rest => sectionsOkB h c Z pa rest
  | .narrow _ _ _ sonst rest => sectionsOkE h c Z pa sonst ∧ sectionsOkB h c Z pa rest
  | .narrowRequired _ _ _ rest => sectionsOkB h c Z pa rest
  | .check _ sonst rest => sectionsOkE h c Z pa sonst ∧ sectionsOkB h c Z pa rest
  | .float _ _ _ _ _ rest => sectionsOkB h c Z pa rest
  | .floatLit _ _ _ rest => sectionsOkB h c Z pa rest
  | .floatOf _ _ _ rest => sectionsOkB h c Z pa rest
  | .floatNarrow _ _ _ sonst rest => sectionsOkE h c Z pa sonst ∧ sectionsOkB h c Z pa rest

/-- Every `locks` section occurring in the option-match arms satisfies its lock's bound. -/
def sectionsOkArms (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    Arms D V l Γ Λ Λ' cs → Prop
  | .nil => True
  | .cons b rest => sectionsOkB h c Z pa b ∧ sectionsOkArms h c Z pa rest

/-- Every `locks` section occurring in the reason-match arms satisfies its lock's bound. -/
def sectionsOkGArms (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Prop
  | .nil => True
  | .cons b rest => sectionsOkB h c Z pa b ∧ sectionsOkGArms h c Z pa rest

/-- Every `locks` section occurring in the end block satisfies the declared bound of its
    lock. Function bodies are end blocks, so this is the sort the top theorem speaks of. -/
def sectionsOkE (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Prop
  | .cons s rest => sectionsOkS h c Z pa s ∧ sectionsOkE h c Z pa rest
  | .bind _ rest => sectionsOkE h c Z pa rest
  | .bindCall _ _ _ _ _ rest => sectionsOkE h c Z pa rest
  | .bindCallElse _ _ _ _ _ err rest => sectionsOkE h c Z pa err ∧ sectionsOkE h c Z pa rest
  | .bindAxiom _ _ _ _ _ _ _ rest => sectionsOkE h c Z pa rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest =>
      sectionsOkE h c Z pa err ∧ sectionsOkE h c Z pa rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => sectionsOkE h c Z pa rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest =>
      sectionsOkE h c Z pa err ∧ sectionsOkE h c Z pa rest
  | .regRead _ _ rest => sectionsOkE h c Z pa rest
  | .regReadElse _ _ _ sonst rest => sectionsOkE h c Z pa sonst ∧ sectionsOkE h c Z pa rest
  | .awaits _ _ _ _ _ rest => sectionsOkE h c Z pa rest
  | .bindCallInd _ _ _ _ _ rest => sectionsOkE h c Z pa rest
  | .bindCallIndElse _ _ _ _ _ err rest =>
      sectionsOkE h c Z pa err ∧ sectionsOkE h c Z pa rest
  | .narrow _ _ _ sonst rest => sectionsOkE h c Z pa sonst ∧ sectionsOkE h c Z pa rest
  | .narrowRequired _ _ _ rest => sectionsOkE h c Z pa rest
  | .exchange _ _ _ _ rest => sectionsOkE h c Z pa rest
  | .ite _ t e => sectionsOkE h c Z pa e ∧ sectionsOkE h c Z pa t
  | .float _ _ _ _ _ rest => sectionsOkE h c Z pa rest
  | .floatLit _ _ _ rest => sectionsOkE h c Z pa rest
  | .floatOf _ _ _ rest => sectionsOkE h c Z pa rest
  | .floatNarrow _ _ _ sonst rest => sectionsOkE h c Z pa sonst ∧ sectionsOkE h c Z pa rest
  | .ret .. | .retWhy .. | .retScoped .. | .retWhyScoped .. | .leave .. | .next .. => True
end

/-! ## 2. The walker implies the section property, by mutual induction -/

mutual
/-- The walker's `haltS` implies the section property of the statement. -/
theorem halt_sectionsS (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool)
    (pa : Nat) : (s : Stmt D V l Γ Λ Λ') → haltS h c Z pa s = true → sectionsOkS h c Z pa s
  | .locks L _ body, hT => by
    simp only [haltS, Bool.and_eq_true] at hT
    simp only [sectionsOkS]
    refine ⟨?_, halt_sectionsB _ _ _ _ body hT.2⟩
    intro n hn
    have hm := hT.1
    rw [hn] at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    exact hm
  | .ite _ t e, hT => by
    simp only [haltS, sectionsOkS, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsB _ _ _ _ t hT.1, halt_sectionsB _ _ _ _ e hT.2⟩
  | .onOption _ p a, hT => by
    simp only [haltS, sectionsOkS, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsB _ _ _ _ p hT.1, halt_sectionsB _ _ _ _ a hT.2⟩
  | .onTag _ arms, hT => by
    simp only [haltS, sectionsOkS] at hT ⊢
    exact halt_sectionsArms _ _ _ _ arms hT
  | .onWhy _ arms, hT => by
    simp only [haltS, sectionsOkS] at hT ⊢
    exact halt_sectionsGArms _ _ _ _ arms hT
  | .callIndElse _ _ _ _ _ err, hT => by
    simp only [haltS, sectionsOkS] at hT ⊢
    exact halt_sectionsE _ _ _ _ err hT
  | .breaking _ body, hT => by
    simp only [haltS, sectionsOkS] at hT ⊢
    exact halt_sectionsB _ _ _ _ body hT
  | .traverse _ _ body, hT => by
    simp only [haltS, sectionsOkS] at hT ⊢
    exact halt_sectionsB _ _ _ _ body hT
  | .consumeTraverse _ _ _ _ _ _ body, hT => by
    simp only [haltS, sectionsOkS] at hT ⊢
    exact halt_sectionsB _ _ _ _ body hT
  | .retry _ _ body ueber, hT => by
    simp only [haltS, sectionsOkS, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsB _ _ _ _ body hT.1, halt_sectionsB _ _ _ _ ueber hT.2⟩
  | .forever _ _ body, hT => by
    simp only [haltS, sectionsOkS] at hT ⊢
    exact halt_sectionsB _ _ _ _ body hT
  | .axiomCallElse _ _ _ _ _ _ _ _ err, hT => by
    simp only [haltS, sectionsOkS] at hT ⊢
    exact halt_sectionsE _ _ _ _ err hT
  | .call .., _ | .callInd .., _ | .assignSlot .., _ |
    .assignThru .., _ | .assignGlob .., _ | .putBytes .., _ |
    .assignVar .., _ | .shift .., _ | .axiomCall .., _ |
    .regWrite .., _ | .transition .., _ | .publish .., _ |
    .advances .., _ | .retires .., _ | .ret .., _ |
    .retWhy .., _ | .retScoped .., _ | .retWhyScoped .., _ |
    .leave .., _ | .next .., _ | .assignSlotRef .., _ |
    .assignThruOwn .., _ => by
    simp only [sectionsOkS]

/-- The walker's `haltB` implies the section property of the block. -/
theorem halt_sectionsB (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool)
    (pa : Nat) : (b : Block D V l Γ Λ Λ') → haltB h c Z pa b = true → sectionsOkB h c Z pa b
  | .nil, _ => by
    simp only [sectionsOkB]
  | .cons s rest, hT => by
    simp only [haltB, sectionsOkB, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsS _ _ _ _ s hT.1, halt_sectionsB _ _ _ _ rest hT.2⟩
  | .bind _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .bindCall _ _ _ _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .bindCallInd _ _ _ _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .bindCallIndElse _ _ _ _ _ err rest, hT => by
    simp only [haltB, sectionsOkB, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ err hT.1, halt_sectionsB _ _ _ _ rest hT.2⟩
  | .bindCallElse _ _ _ _ _ err rest, hT => by
    simp only [haltB, sectionsOkB, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ err hT.1, halt_sectionsB _ _ _ _ rest hT.2⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, hT => by
    simp only [haltB, sectionsOkB, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ err hT.1, halt_sectionsB _ _ _ _ rest hT.2⟩
  | .bindAxiomOpt _ _ _ _ _ _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, hT => by
    simp only [haltB, sectionsOkB, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ err hT.1, halt_sectionsB _ _ _ _ rest hT.2⟩
  | .regRead _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .regReadElse _ _ _ sonst rest, hT => by
    simp only [haltB, sectionsOkB, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ sonst hT.1, halt_sectionsB _ _ _ _ rest hT.2⟩
  | .awaits _ _ _ _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .exchange _ _ _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .narrow _ _ _ sonst rest, hT => by
    simp only [haltB, sectionsOkB, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ sonst hT.1, halt_sectionsB _ _ _ _ rest hT.2⟩
  | .narrowRequired _ _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .check _ sonst rest, hT => by
    simp only [haltB, sectionsOkB, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ sonst hT.1, halt_sectionsB _ _ _ _ rest hT.2⟩
  | .float _ _ _ _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .floatLit _ _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .floatOf _ _ _ rest, hT => by
    simp only [haltB, sectionsOkB] at hT ⊢
    exact halt_sectionsB _ _ _ _ rest hT
  | .floatNarrow _ _ _ sonst rest, hT => by
    simp only [haltB, sectionsOkB, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ sonst hT.1, halt_sectionsB _ _ _ _ rest hT.2⟩

/-- The walker's `haltArms` implies the section property of the option-match arms. -/
theorem halt_sectionsArms (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool)
    (pa : Nat) : (arms : Arms D V l Γ Λ Λ' cs) → haltArms h c Z pa arms = true →
    sectionsOkArms h c Z pa arms
  | .nil, _ => by
    simp only [sectionsOkArms]
  | .cons b rest, hT => by
    simp only [haltArms, sectionsOkArms, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsB _ _ _ _ b hT.1, halt_sectionsArms _ _ _ _ rest hT.2⟩

/-- The walker's `haltGArms` implies the section property of the reason-match arms. -/
theorem halt_sectionsGArms (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool)
    (pa : Nat) : (arms : GrundArms D V l Γ Λ Λ' n) → haltGArms h c Z pa arms = true →
    sectionsOkGArms h c Z pa arms
  | .nil, _ => by
    simp only [sectionsOkGArms]
  | .cons b rest, hT => by
    simp only [haltGArms, sectionsOkGArms, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsB _ _ _ _ b hT.1, halt_sectionsGArms _ _ _ _ rest hT.2⟩

/-- The walker's `haltE` implies the section property of the end block. -/
theorem halt_sectionsE (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool)
    (pa : Nat) : (e : Endblock D V l Γ Λ) → haltE h c Z pa e = true → sectionsOkE h c Z pa e
  | .cons s rest, hT => by
    simp only [haltE, sectionsOkE, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsS _ _ _ _ s hT.1, halt_sectionsE _ _ _ _ rest hT.2⟩
  | .bind _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .bindCall _ _ _ _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .bindCallElse _ _ _ _ _ err rest, hT => by
    simp only [haltE, sectionsOkE, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ err hT.1, halt_sectionsE _ _ _ _ rest hT.2⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, hT => by
    simp only [haltE, sectionsOkE, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ err hT.1, halt_sectionsE _ _ _ _ rest hT.2⟩
  | .bindAxiomOpt _ _ _ _ _ _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, hT => by
    simp only [haltE, sectionsOkE, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ err hT.1, halt_sectionsE _ _ _ _ rest hT.2⟩
  | .regRead _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .regReadElse _ _ _ sonst rest, hT => by
    simp only [haltE, sectionsOkE, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ sonst hT.1, halt_sectionsE _ _ _ _ rest hT.2⟩
  | .awaits _ _ _ _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .bindCallInd _ _ _ _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .bindCallIndElse _ _ _ _ _ err rest, hT => by
    simp only [haltE, sectionsOkE, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ err hT.1, halt_sectionsE _ _ _ _ rest hT.2⟩
  | .narrow _ _ _ sonst rest, hT => by
    simp only [haltE, sectionsOkE, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ sonst hT.1, halt_sectionsE _ _ _ _ rest hT.2⟩
  | .narrowRequired _ _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .exchange _ _ _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .ite _ t e, hT => by
    simp only [haltE, sectionsOkE, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ e hT.1, halt_sectionsE _ _ _ _ t hT.2⟩
  | .float _ _ _ _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .floatLit _ _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .floatOf _ _ _ rest, hT => by
    simp only [haltE, sectionsOkE] at hT ⊢
    exact halt_sectionsE _ _ _ _ rest hT
  | .floatNarrow _ _ _ sonst rest, hT => by
    simp only [haltE, sectionsOkE, Bool.and_eq_true] at hT ⊢
    exact ⟨halt_sectionsE _ _ _ _ sonst hT.1, halt_sectionsE _ _ _ _ rest hT.2⟩
  | .ret .., _ | .retWhy .., _ | .retScoped .., _ |
    .retWhyScoped .., _ | .leave .., _ | .next .., _ => by
    simp only [sectionsOkE]
end

/-! ## 3. From `holds` to the section property of every function body -/

variable (H C : Tafel (String × Nat) (·.1)) (u : UProg)

/-- `holds` gives the walker's check for every function body of the unit. -/
theorem holds_haltE (P : Programm (declOf u)) (passes : Nat)
    (hh : holds H C u P passes = true) (g : Fin u.fns.length) :
    haltE (D := declOf u) (boundOf H u) (CostBinding.decl C u)
      (fun x => (CostBinding.costOf C u x).isSome) passes (P.rumpf g) = true := by
  unfold holds at hh
  rw [Bool.and_eq_true] at hh
  exact (List.all_eq_true.mp hh.2) g (List.mem_finRange g)

/-- **The hold bound holds, syntactically.** On a unit accepted by `HeldBinding.holds`,
    every `locks` section occurring in any function body fits under the declared bound of
    its lock (in `kostenBlock`, calls counted at the callee's declared cost), and its
    callees declare costs. -/
theorem holds_sectionsE (P : Programm (declOf u)) (passes : Nat)
    (hh : holds H C u P passes = true) (g : Fin u.fns.length) :
    sectionsOkE (boundOf H u) (CostBinding.decl C u)
      (fun x => (CostBinding.costOf C u x).isSome) passes (P.rumpf g) :=
  halt_sectionsE _ _ _ _ _ (holds_haltE H C u P passes hh g)

/-- Inversion at one section: its body's `kostenBlock` fits under the bound of its lock,
    and every function it calls declares a cost. -/
theorem sectionsOkS_locks (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool)
    (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (q : sectionsOkS h c Z pa (Stmt.locks L hr body)) :
    (∀ n, h L = some n → kostenBlock c pa body ≤ n ∧ rufeB Z (fun _ => false) true body = true) ∧
      sectionsOkB h c Z pa body := q

end Gabbro.Grammatik.Parser.HeldBinding
