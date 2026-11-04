/- Exact indirect-call signature metadata, connected to the canonical feature walk. -/
module
public import Grammatik.Gen.Abdeckung.Zellen
public import Mathlib.Data.Finset.Basic
@[expose] public section

namespace Gabbro.Grammatik.Gen
open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
variable {D : Deklaration}

/- The finite set visits syntax nodes only. Literal magnitudes and signature-number
   magnitudes never determine a search range. Order and repeated uses do not affect
   contract footprints; distinct signature identities remain distinct. -/
mutual

def sigUsesS {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Finset Nat
  | .ite _ t e => sigUsesB t ∪ sigUsesB e
  | .onOption _ p a => sigUsesB p ∪ sigUsesB a
  | .onTag _ arms => sigUsesArms arms
  | .onWhy _ arms => sigUsesGArms arms
  | .call _ _ _ _ => ∅
  | .callInd (n := n) _ _ _ _ => {n}
  | .callIndElse (n := n) _ _ _ _ _ err => {n} ∪ sigUsesE err
  | .locks _ _ body => sigUsesB body
  | .breaking _ body => sigUsesB body
  | .traverse _ _ body => sigUsesB body
  | .consumeTraverse _ _ _ _ _ _ body => sigUsesB body
  | .retry _ _ body ueber => sigUsesB body ∪ sigUsesB ueber
  | .forever _ _ body => sigUsesB body
  | .assignSlot .. => ∅
  | .assignThru .. | .assignThruOwn .. | .assignSlotRef .. => ∅
  | .assignGlob .. => ∅
  | .putBytes .. => ∅
  | .assignVar .. => ∅
  | .shift .. => ∅
  | .axiomCall .. => ∅
  | .axiomCallElse _ _ _ _ _ _ _ _ err => sigUsesE err
  | .regWrite .. => ∅
  | .transition .. => ∅
  | .publish .. => ∅
  | .advances .. => ∅
  | .retires .. => ∅
  | .ret .. => ∅
  | .retWhy .. => ∅
  | .retScoped .. => ∅
  | .retWhyScoped .. => ∅
  | .leave _ => ∅
  | .next _ => ∅

def sigUsesB {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Finset Nat
  | .nil => ∅
  | .cons s rest => sigUsesS s ∪ sigUsesB rest
  | .bind _ rest => sigUsesB rest
  | .bindCall _ _ _ _ _ rest => sigUsesB rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => {n} ∪ sigUsesB rest
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest => {n} ∪ sigUsesE err ∪ sigUsesB rest
  | .bindCallElse _ _ _ _ _ err rest => sigUsesE err ∪ sigUsesB rest
  | .bindAxiom _ _ _ _ _ _ _ rest => sigUsesB rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => sigUsesE err ∪ sigUsesB rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => sigUsesB rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => sigUsesE err ∪ sigUsesB rest
  | .regRead _ _ rest => sigUsesB rest
  | .regReadElse _ _ _ sonst rest => sigUsesE sonst ∪ sigUsesB rest
  | .awaits _ _ _ _ _ rest => sigUsesB rest
  | .exchange _ _ _ _ rest => sigUsesB rest
  | .narrow _ _ _ sonst rest => sigUsesE sonst ∪ sigUsesB rest
  | .narrowRequired _ _ _ rest => sigUsesB rest
  | .check _ sonst rest => sigUsesE sonst ∪ sigUsesB rest
  | .float _ _ _ _ _ rest => sigUsesB rest
  | .floatLit _ _ _ rest => sigUsesB rest
  | .floatOf _ _ _ rest => sigUsesB rest
  | .floatNarrow _ _ _ sonst rest => sigUsesE sonst ∪ sigUsesB rest

def sigUsesArms {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Finset Nat
  | .nil => ∅
  | .cons b rest => sigUsesB b ∪ sigUsesArms rest

def sigUsesGArms {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Finset Nat
  | .nil => ∅
  | .cons b rest => sigUsesB b ∪ sigUsesGArms rest

def sigUsesE {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Finset Nat
  | .ret .. => ∅
  | .retWhy .. => ∅
  | .retScoped .. => ∅
  | .retWhyScoped .. => ∅
  | .leave _ => ∅
  | .next _ => ∅
  | .cons s rest => sigUsesS s ∪ sigUsesE rest
  | .bind _ rest => sigUsesE rest
  | .bindCall _ _ _ _ _ rest => sigUsesE rest
  | .bindCallElse _ _ _ _ _ err rest => sigUsesE err ∪ sigUsesE rest
  | .bindAxiom _ _ _ _ _ _ _ rest => sigUsesE rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => sigUsesE err ∪ sigUsesE rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => sigUsesE rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => sigUsesE err ∪ sigUsesE rest
  | .regRead _ _ rest => sigUsesE rest
  | .regReadElse _ _ _ sonst rest => sigUsesE sonst ∪ sigUsesE rest
  | .awaits _ _ _ _ _ rest => sigUsesE rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => {n} ∪ sigUsesE rest
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest => {n} ∪ sigUsesE err ∪ sigUsesE rest
  | .narrow _ _ _ sonst rest => sigUsesE sonst ∪ sigUsesE rest
  | .narrowRequired _ _ _ rest => sigUsesE rest
  | .exchange _ _ _ _ rest => sigUsesE rest
  | .ite _ t e => sigUsesE t ∪ sigUsesE e
  | .float _ _ _ _ _ rest => sigUsesE rest
  | .floatLit _ _ _ rest => sigUsesE rest
  | .floatOf _ _ _ rest => sigUsesE rest
  | .floatNarrow _ _ _ sonst rest => sigUsesE sonst ∪ sigUsesE rest
end

/-- The existing feature walk rejects exactly this signature identity. -/
def signatureProbe (k : Nat) : Merkmal D :=
  ⟨fun _ => true, fun n => !(decide (k = n)), fun _ => true⟩

mutual

theorem sigUsesS_iff {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ') (k : Nat), k ∈ sigUsesS s ↔ mS (signatureProbe k) s = false
  | .ite _ t e, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff t k, sigUsesB_iff e k]
  | .onOption _ p a, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff p k, sigUsesB_iff a k]
  | .onTag _ arms, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesArms_iff arms k]
  | .onWhy _ arms, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesGArms_iff arms k]
  | .call _ _ _ _, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .callInd (n := n) _ _ _ _, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .callIndElse (n := n) _ _ _ _ _ err, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff err k]
  | .locks _ _ body, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff body k]
  | .breaking _ body, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff body k]
  | .traverse _ _ body, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff body k]
  | .consumeTraverse _ _ _ _ _ _ body, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff body k]
  | .retry _ _ body ueber, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff body k, sigUsesB_iff ueber k]
  | .forever _ _ body, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff body k]
  | .assignSlot .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .assignThru .., k | .assignThruOwn .., k | .assignSlotRef .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .assignGlob .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .putBytes .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .assignVar .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .shift .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .axiomCall .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .axiomCallElse _ _ _ _ _ _ _ _ err, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff err k]
  | .regWrite .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .transition .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .publish .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .advances .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .retires .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .ret .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .retWhy .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .retScoped .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .retWhyScoped .., k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .leave _, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .next _, k => by simp only [sigUsesS, mS, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]

theorem sigUsesB_iff {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Block D V l Γ Λ Λ') (k : Nat), k ∈ sigUsesB s ↔ mB (signatureProbe k) s = false
  | .nil, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .cons s rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesS_iff s k, sigUsesB_iff rest k]
  | .bind _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .bindCall _ _ _ _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .bindCallInd (n := n) _ _ _ _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff err k, sigUsesB_iff rest k]
  | .bindCallElse _ _ _ _ _ err rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff err k, sigUsesB_iff rest k]
  | .bindAxiom _ _ _ _ _ _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff err k, sigUsesB_iff rest k]
  | .bindAxiomOpt _ _ _ _ _ _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff err k, sigUsesB_iff rest k]
  | .regRead _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .regReadElse _ _ _ sonst rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff sonst k, sigUsesB_iff rest k]
  | .awaits _ _ _ _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .exchange _ _ _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .narrow _ _ _ sonst rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff sonst k, sigUsesB_iff rest k]
  | .narrowRequired _ _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .check _ sonst rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff sonst k, sigUsesB_iff rest k]
  | .float _ _ _ _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .floatLit _ _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .floatOf _ _ _ rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff rest k]
  | .floatNarrow _ _ _ sonst rest, k => by simp only [sigUsesB, mB, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff sonst k, sigUsesB_iff rest k]

theorem sigUsesArms_iff {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    ∀ (s : Arms D V l Γ Λ Λ' cs) (k : Nat), k ∈ sigUsesArms s ↔ mArms (signatureProbe k) s = false
  | .nil, k => by simp only [sigUsesArms, mArms, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .cons b rest, k => by simp only [sigUsesArms, mArms, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff b k, sigUsesArms_iff rest k]

theorem sigUsesGArms_iff {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    ∀ (s : GrundArms D V l Γ Λ Λ' n) (k : Nat), k ∈ sigUsesGArms s ↔ mGArms (signatureProbe k) s = false
  | .nil, k => by simp only [sigUsesGArms, mGArms, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .cons b rest, k => by simp only [sigUsesGArms, mGArms, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesB_iff b k, sigUsesGArms_iff rest k]

theorem sigUsesE_iff {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    ∀ (s : Endblock D V l Γ Λ) (k : Nat), k ∈ sigUsesE s ↔ mE (signatureProbe k) s = false
  | .ret .., k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .retWhy .., k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .retScoped .., k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .retWhyScoped .., k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .leave _, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .next _, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false]
  | .cons s rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesS_iff s k, sigUsesE_iff rest k]
  | .bind _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .bindCall _ _ _ _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .bindCallElse _ _ _ _ _ err rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff err k, sigUsesE_iff rest k]
  | .bindAxiom _ _ _ _ _ _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff err k, sigUsesE_iff rest k]
  | .bindAxiomOpt _ _ _ _ _ _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff err k, sigUsesE_iff rest k]
  | .regRead _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .regReadElse _ _ _ sonst rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff sonst k, sigUsesE_iff rest k]
  | .awaits _ _ _ _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .bindCallInd (n := n) _ _ _ _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff err k, sigUsesE_iff rest k]
  | .narrow _ _ _ sonst rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff sonst k, sigUsesE_iff rest k]
  | .narrowRequired _ _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .exchange _ _ _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .ite _ t e, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff t k, sigUsesE_iff e k]
  | .float _ _ _ _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .floatLit _ _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .floatOf _ _ _ rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff rest k]
  | .floatNarrow _ _ _ sonst rest, k => by simp only [sigUsesE, mE, signatureProbe, Finset.mem_union, Finset.mem_singleton, Finset.not_mem_empty, Bool.and_eq_false_iff, Bool.not_eq_false, decide_eq_true_eq, Bool.true_and, Bool.and_true, Bool.true_eq_false, false_or, or_false, sigUsesE_iff sonst k, sigUsesE_iff rest k]

end

/-- The actual pre/post places of the used pointer interfaces, separate from body reads
    and ordinary callee contracts. The program supplies every contract unchanged. -/
def InterfaceOrte (P : Programm D) (used : Finset Nat) (x : D.Tab ⊕ D.Glob) : Prop :=
  ∃ n ∈ used, x ∈ (P.ptrVertrag n).pre.orte ++ (P.ptrVertrag n).post.orte

theorem interfaceOrte_union (P : Programm D) (a b : Finset Nat) (x : D.Tab ⊕ D.Glob) :
    InterfaceOrte P (a ∪ b) x ↔ InterfaceOrte P a x ∨ InterfaceOrte P b x := by
  simp only [InterfaceOrte, Finset.mem_union, or_and_right, exists_or]

theorem interfaceOrte_empty (P : Programm D) (x : D.Tab ⊕ D.Glob) :
    InterfaceOrte P ∅ x ↔ False := by
  simp only [InterfaceOrte, Finset.not_mem_empty, false_and, exists_false]

theorem interfaceOrte_singleton (P : Programm D) (n : Nat) (x : D.Tab ⊕ D.Glob) :
    InterfaceOrte P {n} x ↔ x ∈ (P.ptrVertrag n).pre.orte ∨ x ∈ (P.ptrVertrag n).post.orte := by
  simp only [InterfaceOrte, Finset.mem_singleton, exists_eq_left, List.mem_append]

end Gabbro.Grammatik.Gen
