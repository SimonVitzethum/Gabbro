/-
  File:      Grammatik/Gen/Abdeckung/Satz/KoerperOrte.lean
  Subject:   THE FOOTPRINT OF A BODY, SPLIT: the model's footprint walk `stmtOrteP P` (`ZielOrt/Grundlage/ZielOrt/T1.lean`)
             reads the places of the body itself AND the contract places of every function the body calls directly.
             `koerperS/B/E` are the places of the body alone (the same walk without the contracts); the theorem
             `endblockOrteP_iff` says the footprint is exactly those plus the contract places of the functions the
             feature walk `mE` sees called. So the footprint of a body is a function of its body places, its direct
             callees and the contracts, which is what the body summary `Rumpf.schluessel` keeps.

             (`Extraktion.endblockOrte` is NOT this: it leaves out the table a `shift` moves, which the footprint reads.)
-/
import Grammatik.Gen.Abdeckung.Zellen

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

mutual

/-- The places a statement reads itself (the footprint walk without the callees' contracts). -/
def koerperS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .assignSlot _ _ i e _ _ => i.orte ++ e.orte
  | .assignThru p _ _ _ i e _ _ => p.orte ++ i.orte ++ e.orte
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
  | .locks _ _ body => koerperB body
  | .breaking _ body => koerperB body
  | .traverse _ inv body => inv.orte ++ koerperB body
  | .retry _ bis body ueber => bis.orte ++ koerperB body ++ koerperB ueber
  | .forever _ inv body => inv.orte ++ koerperB body
  | .axiomCall _ args _ _ _ _ _ => args.orte
  | .regWrite _ _ e => e.orte
  | .transition _ _ _ _ _ _ _ => []
  | .publish _ e _ _ _ _ => e.orte
  | .advances _ _ _ _ => []
  | .retires _ _ _ _ => []
  | .ret e _ => e.orte
  | .retWhy _ _ => []
  | .leave _ => []
  | .next _ => []

def koerperB {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons s rest => koerperS s ++ koerperB rest
  | .bind e rest => e.orte ++ koerperB rest
  | .bindCall _ args _ _ _ rest => args.orte ++ koerperB rest
  | .bindCallInd p args _ _ _ rest => p.orte ++ args.orte ++ koerperB rest
  | .bindCallElse _ args _ _ _ err rest => args.orte ++ koerperE err ++ koerperB rest
  | .bindAxiom _ args _ _ _ _ _ rest => args.orte ++ koerperB rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest => args.orte ++ koerperE err ++ koerperB rest
  | .regRead _ _ rest => koerperB rest
  | .regReadElse _ _ zusage sonst rest => zusage.orte ++ koerperE sonst ++ koerperB rest
  | .awaits g _ _ _ _ rest => .inr g :: koerperB rest
  | .exchange g neu _ _ rest => .inr g :: neu.orte ++ koerperB rest
  | .narrow e _ _ sonst rest => e.orte ++ koerperE sonst ++ koerperB rest
  | .check c sonst rest => c.orte ++ koerperE sonst ++ koerperB rest
  | .float _ a b _ _ rest => a.orte ++ b.orte ++ koerperB rest
  | .floatLit _ _ _ rest => koerperB rest
  | .floatOf e _ _ rest => e.orte ++ koerperB rest
  | .floatNarrow e _ _ sonst rest => e.orte ++ koerperE sonst ++ koerperB rest

def koerperE {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (D.Tab ⊕ D.Glob)
  | .ret e _ => e.orte
  | .retWhy _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => koerperS s ++ koerperE rest
  | .bind e rest => e.orte ++ koerperE rest
  | .bindCall _ args _ _ _ rest => args.orte ++ koerperE rest
  | .bindCallElse _ args _ _ _ err rest => args.orte ++ koerperE err ++ koerperE rest
  | .bindAxiom _ args _ _ _ _ _ rest => args.orte ++ koerperE rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest => args.orte ++ koerperE err ++ koerperE rest
  | .regRead _ _ rest => koerperE rest
  | .regReadElse _ _ zusage sonst rest => zusage.orte ++ koerperE sonst ++ koerperE rest
  | .awaits g _ _ _ _ rest => .inr g :: koerperE rest
  | .bindCallInd p args _ _ _ rest => p.orte ++ args.orte ++ koerperE rest

def koerperArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
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

@[simp] theorem rufNur_ind (g : D.Fn) (n : Nat) : (rufNur g).ind n = true := rfl
@[simp] theorem rufNur_sperre (g : D.Fn) (L : D.Lock) : (rufNur g).sperre L = true := rfl

/-- The contract places of `g`. -/
def vOrte (P : Programm D) (g : D.Fn) : List (D.Tab ⊕ D.Glob) := (P.requires g).orte ++ (P.ensures g).orte

/-- The callee part of the footprint, for a feature value `m g` (false: `g` is called). -/
def Gerufen (P : Programm D) (m : D.Fn → Bool) (x : D.Tab ⊕ D.Glob) : Prop := ∃ g, m g = false ∧ x ∈ vOrte P g

theorem gerufen_und (P : Programm D) (a b : D.Fn → Bool) (x : D.Tab ⊕ D.Glob) :
    Gerufen P (fun g => a g && b g) x ↔ Gerufen P a x ∨ Gerufen P b x := by
  simp only [Gerufen, Bool.and_eq_false_iff, or_and_right, exists_or]

theorem gerufen_wahr (P : Programm D) (x : D.Tab ⊕ D.Glob) : Gerufen P (fun _ => true) x ↔ False := by
  simp [Gerufen]

theorem gerufen_ruf (P : Programm D) (g' : D.Fn) (x : D.Tab ⊕ D.Glob) :
    Gerufen P (fun g => (rufNur g).ruf g') x ↔ x ∈ (P.requires g').orte ∨ x ∈ (P.ensures g').orte := by
  constructor
  · rintro ⟨g, h, hx⟩
    have : g' = g := by simpa [rufNur] using h
    subst this
    exact List.mem_append.1 hx
  · intro h
    exact ⟨g', by simp [rufNur], List.mem_append.2 h⟩

set_option maxHeartbeats 1000000 in
mutual

theorem stmtOrteP_iff (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ') (x : D.Tab ⊕ D.Glob), x ∈ stmtOrteP P s ↔ x ∈ koerperS s ∨ Gerufen P (fun g => mS (rufNur g) s) x
  | .assignSlot .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .assignThru .., x | .assignSlotRef .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .assignGlob .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .putBytes .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .assignVar .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .shift .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .ite _ t e, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P t x, blockOrteP_iff P e x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .onOption _ p a, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P p x, blockOrteP_iff P a x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .onTag _ arms, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, armsOrteP_iff P arms x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .onWhy _ arms, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, grundArmsOrteP_iff P arms x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .call .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .callInd .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .locks _ _ body, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P body x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .breaking _ body, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P body x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .traverse _ _ body, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P body x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .retry _ _ body ueber, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P body x, blockOrteP_iff P ueber x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .forever _ _ body, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P body x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .axiomCall .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .regWrite .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .transition .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .publish .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .advances .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .retires .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .ret .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .retWhy .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .leave _, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .next _, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])

theorem blockOrteP_iff (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Block D V l Γ Λ Λ') (x : D.Tab ⊕ D.Glob), x ∈ blockOrteP P s ↔ x ∈ koerperB s ∨ Gerufen P (fun g => mB (rufNur g) s) x
  | .nil, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .cons s rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, stmtOrteP_iff P s x, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bind _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bindCall _ _ _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bindCallInd _ _ _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bindCallElse _ _ _ _ _ err rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P err x, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bindAxiom _ _ _ _ _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P err x, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .regRead _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .regReadElse _ _ _ sonst rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P sonst x, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .awaits _ _ _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .exchange _ _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .narrow _ _ _ sonst rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P sonst x, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .check _ sonst rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P sonst x, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .float _ _ _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .floatLit _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .floatOf _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .floatNarrow _ _ _ sonst rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P sonst x, blockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])

theorem endblockOrteP_iff (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    ∀ (s : Endblock D V l Γ Λ) (x : D.Tab ⊕ D.Glob), x ∈ endblockOrteP P s ↔ x ∈ koerperE s ∨ Gerufen P (fun g => mE (rufNur g) s) x
  | .ret .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .retWhy .., x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .leave _, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .next _, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .cons s rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, stmtOrteP_iff P s x, endblockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bind _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bindCall _ _ _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bindCallElse _ _ _ _ _ err rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P err x, endblockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bindAxiom _ _ _ _ _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P err x, endblockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .regRead _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .regReadElse _ _ _ sonst rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P sonst x, endblockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .awaits _ _ _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .bindCallInd _ _ _ _ _ rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, endblockOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])

theorem armsOrteP_iff (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    ∀ (s : Arms D V l Γ Λ Λ' cs) (x : D.Tab ⊕ D.Glob), x ∈ armsOrteP P s ↔ x ∈ koerperArms s ∨ Gerufen P (fun g => mArms (rufNur g) s) x
  | .nil, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .cons b rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P b x, armsOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])

theorem grundArmsOrteP_iff (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    ∀ (s : GrundArms D V l Γ Λ Λ' n) (x : D.Tab ⊕ D.Glob), x ∈ grundArmsOrteP P s ↔ x ∈ koerperGArms s ∨ Gerufen P (fun g => mGArms (rufNur g) s) x
  | .nil, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])
  | .cons b rest, x => by (simp only [stmtOrteP, blockOrteP, endblockOrteP, armsOrteP, grundArmsOrteP, koerperS, koerperB, koerperE, koerperArms, koerperGArms, mS, mB, mE, mArms, mGArms, List.mem_append, List.mem_cons, List.not_mem_nil, gerufen_und, gerufen_ruf, rufNur_ind, rufNur_sperre, Bool.true_and, Bool.and_true, blockOrteP_iff P b x, grundArmsOrteP_iff P rest x] <;> simp only [gerufen_wahr, false_or, or_false, or_assoc, or_left_comm, or_comm])

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
  deriving DecidableEq

/-- **The cell-relevant summary of a body**: which functions it calls directly and through whose signature, which locks
    it takes, whether it is in the fragment without its indirect-call test, which axioms and registers it answers from,
    which registers it reads, and which carriers it reads itself (`koerperE`). Two bodies with the same summary give a
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
   ((Aufz.tab (D := D)).map Sum.inl ++ (Aufz.glob (D := D)).map Sum.inr).map fun c => istIn (koerperE b) c⟩

end Gabbro.Grammatik.Gen
