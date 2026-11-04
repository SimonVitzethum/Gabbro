/-
  File:      Grammatik/Gen/Abdeckung/Satz/KoerperOrte.lean
  Subject:   THE FOOTPRINT OF A BODY, SPLIT: the model's footprint walk `stmtOrteP P` (`ZielOrt/Grundlage/ZielOrt/T1.lean`)
             reads the places of the body itself AND the contract places of every function the body calls directly
             AND the actual interface pre/post places at every indirect call's signature identity.
             `koerperS/B/E` are the places of the body alone (the same walk without the contracts); the theorem
             `endblockOrteP_iff` splits all three parts. The ordinary callee part uses the feature walk `mE`;
             `sigUsesE` keeps exact used interface identities even when their structural signatures coincide.
             The body summary `Rumpf.schluessel` retains both independently of the program's contracts.

             (`Extraktion.endblockOrte` is NOT this: it leaves out the table a `shift` moves, which the footprint reads.)
-/
module

import Mathlib.Data.Finset.Lattice.Lemmas

import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Gen.Abdeckung.Satz.SignatureUse
import all Init.Data.Repr
@[expose] public section


namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

mutual

/-- The places a statement reads itself (the footprint walk without the callees' contracts). -/
def koerperS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .assignSlot _ _ i e _ _ => i.orte ++ e.orte
  | .assignThru p _ _ _ i e _ _ => p.orte ++ i.orte ++ e.orte
  | .assignThruOwn p _ _ _ i e _ _ _ _ _ _ _ => p.orte ++ i.orte ++ e.orte
  | .assignSlotRef r _ _ _ _ e _ _ => r.orte ++ e.orte
  | .assignGlob _ e _ _ => e.orte
  | .putBytes _ _ _ _ i _ _ e _ _ => i.orte ++ e.orte
  | .assignVar _ e => e.orte
  | .shift t _ _ i _ _ _ _ _ _ => .inl t :: i.orte
  | .ite c t e => c.orte ++ koerperB t ++ koerperB e
  | .onOption o p a => o.orte ++ koerperB p ++ koerperB a
  | .onTag v arms => v.orte ++ koerperArms arms
  | .onWhy r arms => r.orte ++ koerperGArms arms
  | .call _ args _ _ => args.orte
  | .callInd p args _ _ => p.orte ++ args.orte
  | .callIndElse p args _ _ _ err => p.orte ++ args.orte ++ koerperE err
  | .locks _ _ body => koerperB body
  | .breaking _ body => koerperB body
  | .traverse _ inv body => inv.orte ++ koerperB body
  | .consumeTraverse _ member edge inv _ mass body =>
      member.orte ++ edge.orte ++ inv.orte ++ mass.orte ++ koerperB body
  | .retry _ bis body ueber => bis.orte ++ koerperB body ++ koerperB ueber
  | .forever _ inv body => inv.orte ++ koerperB body
  | .axiomCall _ args _ _ _ _ _ => args.orte
  | .axiomCallElse (args := args) (err := err) .. => args.orte ++ koerperE err
  | .regWrite _ _ e => e.orte
  | .transition _ _ _ _ _ _ _ => []
  | .publish _ e _ _ _ _ => e.orte
  | .advances _ _ _ _ => []
  | .retires _ _ _ _ => []
  | .ret e _ => e.orte
  | .retWhy _ _ => []
  | .retScoped e _ => e.orte
  | .retWhyScoped _ _ => []
  | .leave _ => []
  | .next _ => []

def koerperB {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons s rest => koerperS s ++ koerperB rest
  | .bind e rest => e.orte ++ koerperB rest
  | .bindCall _ args _ _ _ rest => args.orte ++ koerperB rest
  | .bindCallInd p args _ _ _ rest => p.orte ++ args.orte ++ koerperB rest
  | .bindCallIndElse p args _ _ _ err rest => p.orte ++ args.orte ++ koerperE err ++ koerperB rest
  | .bindCallElse _ args _ _ _ err rest => args.orte ++ koerperE err ++ koerperB rest
  | .bindAxiom _ args _ _ _ _ _ rest => args.orte ++ koerperB rest
  | .bindAxiomOpt (args := args) (rest := rest) .. => args.orte ++ koerperB rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest => args.orte ++ koerperE err ++ koerperB rest
  | .bindAxiomOptElse (args := args) (err := err) (rest := rest) .. => args.orte ++ koerperE err ++ koerperB rest
  | .regRead _ _ rest => koerperB rest
  | .regReadElse _ _ zusage sonst rest => zusage.orte ++ koerperE sonst ++ koerperB rest
  | .awaits g _ _ _ _ rest => .inr g :: koerperB rest
  | .exchange g neu _ _ rest => .inr g :: neu.orte ++ koerperB rest
  | .narrow e _ _ sonst rest => e.orte ++ koerperE sonst ++ koerperB rest
  | .narrowRequired e _ _ rest => e.orte ++ koerperB rest
  | .check c sonst rest => c.orte ++ koerperE sonst ++ koerperB rest
  | .float _ a b _ _ rest => a.orte ++ b.orte ++ koerperB rest
  | .floatLit _ _ _ rest => koerperB rest
  | .floatOf e _ _ rest => e.orte ++ koerperB rest
  | .floatNarrow e _ _ sonst rest => e.orte ++ koerperE sonst ++ koerperB rest

def koerperE {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (D.Tab ⊕ D.Glob)
  | .ret e _ => e.orte
  | .retWhy _ _ => []
  | .retScoped e _ => e.orte
  | .retWhyScoped _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => koerperS s ++ koerperE rest
  | .bind e rest => e.orte ++ koerperE rest
  | .bindCall _ args _ _ _ rest => args.orte ++ koerperE rest
  | .bindCallElse _ args _ _ _ err rest => args.orte ++ koerperE err ++ koerperE rest
  | .bindAxiom _ args _ _ _ _ _ rest => args.orte ++ koerperE rest
  | .bindAxiomOpt (args := args) (rest := rest) .. => args.orte ++ koerperE rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest => args.orte ++ koerperE err ++ koerperE rest
  | .bindAxiomOptElse (args := args) (err := err) (rest := rest) .. => args.orte ++ koerperE err ++ koerperE rest
  | .regRead _ _ rest => koerperE rest
  | .regReadElse _ _ zusage sonst rest => zusage.orte ++ koerperE sonst ++ koerperE rest
  | .awaits g _ _ _ _ rest => .inr g :: koerperE rest
  | .bindCallInd p args _ _ _ rest => p.orte ++ args.orte ++ koerperE rest
  | .bindCallIndElse p args _ _ _ err rest => p.orte ++ args.orte ++ koerperE err ++ koerperE rest
  | .narrow e _ _ sonst rest => e.orte ++ koerperE sonst ++ koerperE rest
  | .narrowRequired e _ _ rest => e.orte ++ koerperE rest
  | .exchange g neu _ _ rest => .inr g :: neu.orte ++ koerperE rest
  | .ite c t e => c.orte ++ koerperE e ++ koerperE t

  | .float _ a b _ _ rest => a.orte ++ b.orte ++ koerperE rest
  | .floatLit _ _ _ rest => koerperE rest
  | .floatOf e _ _ rest => e.orte ++ koerperE rest
  | .floatNarrow e _ _ sonst rest => e.orte ++ koerperE sonst ++ koerperE rest
def koerperArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    Arms D V l Γ Λ Λ' cs → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons b rest => koerperB b ++ koerperArms rest

def koerperGArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons b rest => koerperB b ++ koerperGArms rest

end

variable [Aufz D]

/-- The probe "does not call `g` directly" (the first part of `Rumpf.schluessel`). -/
def rufNur (g : D.Fn) : Merkmal D := ⟨fun h => !(decide (h = g)), fun _ => true, fun _ => true⟩

@[simp] theorem rufNur_ind (g : D.Fn) (n : Nat) : (rufNur g).ind n = true := by rfl
@[simp] theorem rufNur_sperre (g : D.Fn) (L : D.Lock) : (rufNur g).sperre L = true := by rfl

/-- The contract places of `g`. -/
def vOrte (P : Programm D) (g : D.Fn) : List (D.Tab ⊕ D.Glob) := (P.requires g).orte ++ (P.ensures g).orte

/-- The callee part of the footprint, for a feature value `m g` (false: `g` is called). -/
def Gerufen (P : Programm D) (m : D.Fn → Bool) (x : D.Tab ⊕ D.Glob) : Prop := ∃ g, m g = false ∧ x ∈ vOrte P g

theorem gerufen_und (P : Programm D) (a b : D.Fn → Bool) (x : D.Tab ⊕ D.Glob) :
    Gerufen P (fun g => a g && b g) x ↔ Gerufen P a x ∨ Gerufen P b x := by
  simp only [Gerufen, Bool.and_eq_false_iff, or_and_right, exists_or]

theorem gerufen_wahr (P : Programm D) (x : D.Tab ⊕ D.Glob) : Gerufen P (fun _ => true) x ↔ False := by
  simp only [Gerufen, Bool.true_eq_false, false_and, exists_false]

theorem gerufen_ruf (P : Programm D) (g' : D.Fn) (x : D.Tab ⊕ D.Glob) :
    Gerufen P (fun g => (rufNur g).ruf g') x ↔ x ∈ (P.requires g').orte ∨ x ∈ (P.ensures g').orte := by
  constructor
  · rintro ⟨g, h, hx⟩
    have : g' = g := by simpa [rufNur] using h
    subst this
    exact List.mem_append.1 hx
  · intro h
    exact ⟨g', by simp only [rufNur, decide_true, Bool.not_true], List.mem_append.2 h⟩

/- Keep propositional rearrangement independent of concrete dependent syntax. -/
private def FootprintParts (P : Programm D) (full body : List (D.Tab ⊕ D.Glob))
    (calls : D.Fn → Bool) (used : Finset Nat) : Prop :=
  ∀ x, x ∈ full ↔ x ∈ body ∨ Gerufen P calls x ∨ InterfaceOrte P used x

private theorem parts_regroup {a b c d e f : Prop} :
    ((a ∨ b ∨ c) ∨ (d ∨ e ∨ f)) ↔ (a ∨ d) ∨ (b ∨ e) ∨ (c ∨ f) := by
  constructor
  · rintro ((ha | hb | hc) | (hd | he | hf))
    · exact Or.inl (Or.inl ha)
    · exact Or.inr (Or.inl (Or.inl hb))
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inl (Or.inr hd)
    · exact Or.inr (Or.inl (Or.inr he))
    · exact Or.inr (Or.inr (Or.inr hf))
  · rintro ((ha | hd) | (hb | he) | (hc | hf))
    · exact Or.inl (Or.inl ha)
    · exact Or.inr (Or.inl hd)
    · exact Or.inl (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inl (Or.inr (Or.inr hc))
    · exact Or.inr (Or.inr (Or.inr hf))

private theorem parts_read (P : Programm D) (xs : List (D.Tab ⊕ D.Glob)) :
    FootprintParts P xs xs (fun _ => true) ∅ := by
  intro x; simp only [gerufen_wahr, interfaceOrte_empty, false_or, or_false]

private theorem parts_call (P : Programm D) (f : D.Fn) :
    FootprintParts P (vOrte P f) [] (fun g => (rufNur g).ruf f) ∅ := by
  intro x; simp only [vOrte, List.mem_append, List.not_mem_nil, gerufen_ruf,
    interfaceOrte_empty, false_or, or_false]

private theorem parts_interface (P : Programm D) (n : Nat) :
    FootprintParts P ((P.ptrVertrag n).pre.orte ++ (P.ptrVertrag n).post.orte) []
      (fun _ => true) {n} := by
  intro x; simp only [List.mem_append, List.not_mem_nil, gerufen_wahr,
    interfaceOrte_singleton, false_or]

private theorem parts_join (P : Programm D) {full₁ full₂ body₁ body₂ : List (D.Tab ⊕ D.Glob)}
    {calls₁ calls₂ : D.Fn → Bool} {used₁ used₂ : Finset Nat}
    (h₁ : FootprintParts P full₁ body₁ calls₁ used₁) (h₂ : FootprintParts P full₂ body₂ calls₂ used₂) :
    FootprintParts P (full₁ ++ full₂) (body₁ ++ body₂)
      (fun g => calls₁ g && calls₂ g) (used₁ ∪ used₂) := by
  intro x
  rw [List.mem_append, h₁ x, h₂ x, List.mem_append, gerufen_und, interfaceOrte_union]
  exact parts_regroup

private theorem parts_join_reverse (P : Programm D) {full₁ full₂ body₁ body₂ : List (D.Tab ⊕ D.Glob)}
    {calls₁ calls₂ : D.Fn → Bool} {used₁ used₂ : Finset Nat}
    (h₁ : FootprintParts P full₁ body₁ calls₁ used₁) (h₂ : FootprintParts P full₂ body₂ calls₂ used₂) :
    FootprintParts P (full₂ ++ full₁) (body₂ ++ body₁)
      (fun g => calls₁ g && calls₂ g) (used₁ ∪ used₂) := by
  intro x
  have combined := parts_join P h₂ h₁ x
  simpa only [gerufen_und, interfaceOrte_union, or_comm] using combined

set_option maxHeartbeats 1000000 in
mutual

theorem stmtOrteP_iff (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ') (x : D.Tab ⊕ D.Glob), x ∈ stmtOrteP P s ↔ x ∈ koerperS s ∨ Gerufen P (fun g => mS (rufNur g) s) x ∨ InterfaceOrte P (sigUsesS s) x
  | .assignSlot _ _ i v _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P (i.orte ++ v.orte)) x)
  | .assignThru p _ _ _ i v _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P (p.orte ++ i.orte ++ v.orte)) x)
  | .assignThruOwn p _ _ _ i v _ _ _ _ _ _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P (p.orte ++ i.orte ++ v.orte)) x)
  | .assignSlotRef r _ _ _ _ v _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P (r.orte ++ v.orte)) x)
  | .assignGlob _ v _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P v.orte) x)
  | .putBytes _ _ _ _ i _ _ v _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P (i.orte ++ v.orte)) x)
  | .assignVar _ v, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P v.orte) x)
  | .shift t _ _ i _ _ _ _ _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P (.inl t :: i.orte)) x)
  | .ite c t f, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P c.orte) (parts_join P (blockOrteP_iff P t) (blockOrteP_iff P f))) x)
  | .onOption o p a, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P o.orte) (parts_join P (blockOrteP_iff P p) (blockOrteP_iff P a))) x)
  | .onTag v arms, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (armsOrteP_iff P arms)) x)
  | .onWhy r arms, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P r.orte) (grundArmsOrteP_iff P arms)) x)
  | .call f args _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (parts_call P f)) x)
  | .callInd (n := n) p args _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (p.orte ++ args.orte)) (parts_interface P n)) x)
  | .callIndElse (n := n) p args _ _ _ err, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (p.orte ++ args.orte)) (parts_join P (parts_interface P n) (endblockOrteP_iff P err))) x)
  | .locks _ _ body, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((blockOrteP_iff P body) x)
  | .breaking _ body, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((blockOrteP_iff P body) x)
  | .traverse _ inv body, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P inv.orte) (blockOrteP_iff P body)) x)
  | .consumeTraverse _ member edge inv _ mass body, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (member.orte ++ edge.orte ++ inv.orte ++ mass.orte)) (blockOrteP_iff P body)) x)
  | .retry _ bis body over, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P bis.orte) (parts_join P (blockOrteP_iff P body) (blockOrteP_iff P over))) x)
  | .forever _ inv body, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P inv.orte) (blockOrteP_iff P body)) x)
  | .axiomCall _ args _ _ _ _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P args.orte) x)
  | .axiomCallElse (args := args) (err := err) .., x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (endblockOrteP_iff P err)) x)
  | .regWrite _ _ v, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P v.orte) x)
  | .transition .., x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .publish _ v _ _ _ _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P v.orte) x)
  | .advances .., x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .retires .., x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .ret v _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P v.orte) x)
  | .retWhy .., x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .retScoped v _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P v.orte) x)
  | .retWhyScoped .., x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .leave _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .next _, x => by
      simpa only [stmtOrteP, koerperS, mS, sigUsesS, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)

theorem blockOrteP_iff (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Block D V l Γ Λ Λ') (x : D.Tab ⊕ D.Glob), x ∈ blockOrteP P s ↔ x ∈ koerperB s ∨ Gerufen P (fun g => mB (rufNur g) s) x ∨ InterfaceOrte P (sigUsesB s) x
  | .nil, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .cons st rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (stmtOrteP_iff P st) (blockOrteP_iff P rest)) x)
  | .bind v rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (blockOrteP_iff P rest)) x)
  | .bindCall f args _ _ _ rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (parts_join P (parts_call P f) (blockOrteP_iff P rest))) x)
  | .bindCallInd (n := n) p args _ _ _ rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (p.orte ++ args.orte)) (parts_join P (parts_interface P n) (blockOrteP_iff P rest))) x)
  | .bindCallIndElse (n := n) p args _ _ _ err rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (p.orte ++ args.orte)) (parts_join P (parts_interface P n) (parts_join P (endblockOrteP_iff P err) (blockOrteP_iff P rest)))) x)
  | .bindCallElse f args _ _ _ err rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (parts_join P (parts_call P f) (parts_join P (endblockOrteP_iff P err) (blockOrteP_iff P rest)))) x)
  | .bindAxiom _ args _ _ _ _ _ rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (blockOrteP_iff P rest)) x)
  | .bindAxiomOpt (args := args) (rest := rest) .., x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (blockOrteP_iff P rest)) x)
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (parts_join P (endblockOrteP_iff P err) (blockOrteP_iff P rest))) x)
  | .bindAxiomOptElse (args := args) (err := err) (rest := rest) .., x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (parts_join P (endblockOrteP_iff P err) (blockOrteP_iff P rest))) x)
  | .regRead _ _ rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((blockOrteP_iff P rest) x)
  | .regReadElse _ _ promise other rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P promise.orte) (parts_join P (endblockOrteP_iff P other) (blockOrteP_iff P rest))) x)
  | .awaits g _ _ _ _ rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P [.inr g]) (blockOrteP_iff P rest)) x)
  | .exchange g v _ _ rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (.inr g :: v.orte)) (blockOrteP_iff P rest)) x)
  | .narrow v _ _ other rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (parts_join P (endblockOrteP_iff P other) (blockOrteP_iff P rest))) x)
  | .narrowRequired v _ _ rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (blockOrteP_iff P rest)) x)
  | .check c other rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P c.orte) (parts_join P (endblockOrteP_iff P other) (blockOrteP_iff P rest))) x)
  | .float _ a c _ _ rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (a.orte ++ c.orte)) (blockOrteP_iff P rest)) x)
  | .floatLit _ _ _ rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((blockOrteP_iff P rest) x)
  | .floatOf v _ _ rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (blockOrteP_iff P rest)) x)
  | .floatNarrow v _ _ other rest, x => by
      simpa only [blockOrteP, koerperB, mB, sigUsesB, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (parts_join P (endblockOrteP_iff P other) (blockOrteP_iff P rest))) x)

theorem endblockOrteP_iff (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    ∀ (s : Endblock D V l Γ Λ) (x : D.Tab ⊕ D.Glob), x ∈ endblockOrteP P s ↔ x ∈ koerperE s ∨ Gerufen P (fun g => mE (rufNur g) s) x ∨ InterfaceOrte P (sigUsesE s) x
  | .ret v _, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P v.orte) x)
  | .retWhy .., x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .retScoped v _, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P v.orte) x)
  | .retWhyScoped .., x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .leave _, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .next _, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .cons st rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (stmtOrteP_iff P st) (endblockOrteP_iff P rest)) x)
  | .bind v rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (endblockOrteP_iff P rest)) x)
  | .bindCall f args _ _ _ rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (parts_join P (parts_call P f) (endblockOrteP_iff P rest))) x)
  | .bindCallInd (n := n) p args _ _ _ rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (p.orte ++ args.orte)) (parts_join P (parts_interface P n) (endblockOrteP_iff P rest))) x)
  | .bindCallIndElse (n := n) p args _ _ _ err rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (p.orte ++ args.orte)) (parts_join P (parts_interface P n) (parts_join P (endblockOrteP_iff P err) (endblockOrteP_iff P rest)))) x)
  | .bindCallElse f args _ _ _ err rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (parts_join P (parts_call P f) (parts_join P (endblockOrteP_iff P err) (endblockOrteP_iff P rest)))) x)
  | .bindAxiom _ args _ _ _ _ _ rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (endblockOrteP_iff P rest)) x)
  | .bindAxiomOpt (args := args) (rest := rest) .., x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (endblockOrteP_iff P rest)) x)
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (parts_join P (endblockOrteP_iff P err) (endblockOrteP_iff P rest))) x)
  | .bindAxiomOptElse (args := args) (err := err) (rest := rest) .., x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P args.orte) (parts_join P (endblockOrteP_iff P err) (endblockOrteP_iff P rest))) x)
  | .regRead _ _ rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((endblockOrteP_iff P rest) x)
  | .regReadElse _ _ promise other rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P promise.orte) (parts_join P (endblockOrteP_iff P other) (endblockOrteP_iff P rest))) x)
  | .awaits g _ _ _ _ rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P [.inr g]) (endblockOrteP_iff P rest)) x)
  | .exchange g v _ _ rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (.inr g :: v.orte)) (endblockOrteP_iff P rest)) x)
  | .narrow v _ _ other rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (parts_join P (endblockOrteP_iff P other) (endblockOrteP_iff P rest))) x)
  | .narrowRequired v _ _ rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (endblockOrteP_iff P rest)) x)
  | .ite c t f, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P c.orte) (parts_join_reverse P (endblockOrteP_iff P t) (endblockOrteP_iff P f))) x)
  | .float _ a c _ _ rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P (a.orte ++ c.orte)) (endblockOrteP_iff P rest)) x)
  | .floatLit _ _ _ rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((endblockOrteP_iff P rest) x)
  | .floatOf v _ _ rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (endblockOrteP_iff P rest)) x)
  | .floatNarrow v _ _ other rest, x => by
      simpa only [endblockOrteP, koerperE, mE, sigUsesE, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (parts_read P v.orte) (parts_join P (endblockOrteP_iff P other) (endblockOrteP_iff P rest))) x)

theorem armsOrteP_iff (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    ∀ (s : Arms D V l Γ Λ Λ' cs) (x : D.Tab ⊕ D.Glob), x ∈ armsOrteP P s ↔ x ∈ koerperArms s ∨ Gerufen P (fun g => mArms (rufNur g) s) x ∨ InterfaceOrte P (sigUsesArms s) x
  | .nil, x => by
      simpa only [armsOrteP, koerperArms, mArms, sigUsesArms, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .cons body rest, x => by
      simpa only [armsOrteP, koerperArms, mArms, sigUsesArms, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (blockOrteP_iff P body) (armsOrteP_iff P rest)) x)

theorem grundArmsOrteP_iff (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    ∀ (s : GrundArms D V l Γ Λ Λ' n) (x : D.Tab ⊕ D.Glob), x ∈ grundArmsOrteP P s ↔ x ∈ koerperGArms s ∨ Gerufen P (fun g => mGArms (rufNur g) s) x ∨ InterfaceOrte P (sigUsesGArms s) x
  | .nil, x => by
      simpa only [grundArmsOrteP, koerperGArms, mGArms, sigUsesGArms, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_read P []) x)
  | .cons body rest, x => by
      simpa only [grundArmsOrteP, koerperGArms, mGArms, sigUsesGArms, vOrte, List.append_assoc, List.append_nil, List.nil_append, List.cons_append, Bool.true_and, Bool.and_true, Bool.and_assoc, rufNur_ind, rufNur_sperre, Finset.empty_union, Finset.union_empty, Finset.union_assoc] using ((parts_join P (blockOrteP_iff P body) (grundArmsOrteP_iff P rest)) x)

end

/-- The summary of a body, by parts. -/
structure Schluessel where
  rufe : List Bool
  ind : List Bool
  sperren : List Bool
  gok : Bool
  axAntw : List Bool
  regAntw : List Bool
  regs : List Bool
  orte : List Bool
  signatures : Finset Nat
  deriving DecidableEq

/-- **The cell-relevant summary of a body**: which functions it calls directly and through whose signature, which locks
    it takes, whether it is in the fragment without its indirect-call test, which axioms and registers it answers from,
    which registers it reads, which carriers it reads itself (`koerperE`), and the exact finite set of indirect
    signature identities whose interface contracts it reads. Two bodies with the same summary give a
    program the same cells whatever the other bodies are (`Schluessel.lean`), so a sweep that keeps one body per summary
    reaches the same cells as the full sweep. -/
def Rumpf.schluessel [Zahlen] {f : D.Fn} (b : Rumpf D f) : Schluessel :=
  ⟨(Aufz.fn (D := D)).map fun g => !(mE (rufNur g) b),
   (Aufz.fn (D := D)).map fun g => !(mE ⟨fun _ => true, fun n => !(D.passt g n), fun _ => true⟩ b),
   (Aufz.lock (D := D)).map fun L => !(mE ⟨fun _ => true, fun _ => true, fun L' => !(decide (L' = L))⟩ b),
   b.gOk (fun _ => true) (fun _ => true),
   (Aufz.ax (D := D)).map fun a => decide (Sum.inl a ∈ b.ants),
   (Aufz.reg (D := D)).map fun r => decide (Sum.inr r ∈ b.ants),
   (Aufz.reg (D := D)).map fun r => decide (r ∈ b.regs),
   ((Aufz.tab (D := D)).map Sum.inl ++ (Aufz.glob (D := D)).map Sum.inr).map fun c => istIn (koerperE b) c,
   sigUsesE b⟩

end Gabbro.Grammatik.Gen
