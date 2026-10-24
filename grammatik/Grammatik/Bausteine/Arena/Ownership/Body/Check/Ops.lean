import Grammatik.Bausteine.Arena.Ownership.Body.Check.Context

/-! Context operations of the executable check: the loop head (names
assigned in the body forget their origin), the exit test, the signature
interface of a function pointer, and boundedness of every context the check
computes. Only soundness matters for the check; the loop head is a choice. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-! ## 1. Names assigned in a body -/

mutual

def assignsS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → List Nat
  | .assignVar x _ => [x.unten]
  | .ite _ t e => assignsB t ++ assignsB e
  | .onOption _ p a => assignsB p ++ assignsB a
  | .onTag _ arms => assignsArms arms
  | .onWhy _ arms => assignsGrund arms
  | .locks _ _ body => assignsB body
  | .breaking _ body => assignsB body
  | .traverse _ _ body => assignsB body
  | .retry _ _ body u => assignsB body ++ assignsB u
  | .forever _ _ body => assignsB body
  | _ => []

def assignsB {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → List Nat
  | .nil => []
  | .cons s rest => assignsS s ++ assignsB rest
  | .bind _ rest => assignsB rest
  | .bindCall _ _ _ _ _ rest => assignsB rest
  | .bindCallInd _ _ _ _ _ rest => assignsB rest
  | .bindCallElse _ _ _ _ _ err rest => assignsE err ++ assignsB rest
  | .bindAxiom _ _ _ _ _ _ _ rest => assignsB rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => assignsE err ++ assignsB rest
  | .regRead _ _ rest => assignsB rest
  | .regReadElse _ _ _ sonst rest => assignsE sonst ++ assignsB rest
  | .awaits _ _ _ _ _ rest => assignsB rest
  | .exchange _ _ _ _ rest => assignsB rest
  | .narrow _ _ _ sonst rest => assignsE sonst ++ assignsB rest
  | .check _ sonst rest => assignsE sonst ++ assignsB rest
  | .float _ _ _ _ _ rest => assignsB rest
  | .floatLit _ _ _ rest => assignsB rest
  | .floatOf _ _ _ rest => assignsB rest
  | .floatNarrow _ _ _ sonst rest => assignsE sonst ++ assignsB rest

def assignsE {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → List Nat
  | .cons s rest => assignsS s ++ assignsE rest
  | .bind _ rest => assignsE rest
  | .bindCall _ _ _ _ _ rest => assignsE rest
  | .bindCallElse _ _ _ _ _ err rest => assignsE err ++ assignsE rest
  | .bindAxiom _ _ _ _ _ _ _ rest => assignsE rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => assignsE err ++ assignsE rest
  | .regRead _ _ rest => assignsE rest
  | .regReadElse _ _ _ sonst rest => assignsE sonst ++ assignsE rest
  | .awaits _ _ _ _ _ rest => assignsE rest
  | .bindCallInd _ _ _ _ _ rest => assignsE rest
  | _ => []

def assignsArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → List Nat
  | .nil => []
  | .cons b rest => assignsB b ++ assignsArms rest

def assignsGrund {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → List Nat
  | .nil => []
  | .cons b rest => assignsB b ++ assignsGrund rest

end

/-- The loop head: every name assigned anywhere in the body forgets its origin. -/
def loopCtx (c : Context) (ps : List Nat) : Context :=
  { c with references := c.references.mapIdx fun p r => if p ∈ ps then none else r }

theorem loopCtx_bounded {c : Context} (hc : c.bounded) (ps : List Nat) : (loopCtx c ps).bounded := by
  refine ⟨hc.1, ?_⟩
  intro ref hm i he
  subst he
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hm
  simp only [loopCtx, List.getElem?_mapIdx] at hp
  cases hq : c.references[p]? with
  | none => rw [hq] at hp; cases hp
  | some r =>
    rw [hq] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    split at hp
    · cases hp
    · subst hp; exact hc.2 _ (List.mem_of_getElem? hq) i rfl

theorem loopCtx_weaker {c : Context} (hc : c.bounded) (ps : List Nat) : Weaker (loopCtx c ps) c := by
  refine ⟨fun _ => rfl, hc.1, by simp [loopCtx], ?_⟩
  intro p o hp
  simp only [loopCtx, List.getElem?_mapIdx] at hp
  cases hq : c.references[p]? with
  | none => rw [hq] at hp; cases hp
  | some r =>
    rw [hq] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    split at hp
    · cases hp
    · subst hp; exact ⟨rfl, hc.2 _ (List.mem_of_getElem? hq) o rfl⟩

/-! ## 2. Exits -/

/-- **`ExitsTo`, decided.** -/
def exitsB (k c : Context) : Bool :=
  decide (k.references.length ≤ c.references.length) &&
    weakerB k { c with references := c.references.take k.references.length }

theorem exitsB_sound {k c : Context} (hk : k.bounded) (hc : c.bounded) (h : exitsB k c = true) : ExitsTo k c := by
  simp only [exitsB, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, weakerB_sound hk ⟨hc.1, fun ref hm => hc.2 ref (List.mem_of_mem_take hm)⟩ h.2⟩

/-! ## 3. Boundedness of the computed contexts -/

theorem Context.assign_bounded {c : Context} (hc : c.bounded) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (x : Var Γ τ) (e : Expr D Γ Λ τ) : (c.assign x (origin c e)).bounded := by
  refine ⟨hc.1, ?_⟩
  intro ref hm i he
  rcases List.mem_or_eq_of_mem_set hm with hm | hm
  · exact hc.2 ref hm i he
  · subst hm
    exact hc.2 (some i) (origin_member c e i he) i rfl

theorem Context.drop_bounded {c : Context} (hc : c.bounded) : c.drop.bounded :=
  ⟨hc.1, fun ref hm => hc.2 ref (List.dropLast_subset _ hm)⟩

theorem Context.bindNone_bounded {c : Context} (hc : c.bounded) : (c.bind none).bounded :=
  Context.bind_bounded hc none (fun _ h => by cases h)

theorem Context.bindOrigin_bounded {c : Context} (hc : c.bounded) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) : (c.bind (origin c e)).bounded :=
  Context.bind_bounded hc _ (fun i hi => hc.2 (some i) (origin_member c e i hi) i rfl)

theorem resultContextB_bounded {c : Context} (hc : c.bounded) (owner : Bool) : (resultContextB c owner).bounded := by
  cases owner
  · exact Context.bindNone_bounded hc
  · exact Context.bindFresh_bounded hc

theorem dropContextB_bounded {c : Context} (hc : c.bounded) (owner : Bool) : (dropContextB c owner).bounded := by
  cases owner
  · exact hc
  · exact Context.drop_bounded (Context.bindFresh_bounded hc)

theorem armBind_bounded {c : Context} (hc : c.bounded) (ca : Option (Int × Int)) : (armBind c ca).bounded := by
  cases ca
  · exact hc
  · exact Context.bindNone_bounded hc

theorem armDrop_bounded {c : Context} (hc : c.bounded) (ca : Option (Int × Int)) : (armDrop c ca).bounded := by
  cases ca
  · exact hc
  · exact Context.drop_bounded hc

theorem consume_bounded {c c2 : Context} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ} {o : Nat}
    (hc : c.bounded) (h : consume c e = some (c2, o)) : c2.bounded := by
  rw [(consume_facts h).2.2]; exact Context.kill_bounded hc o

/-! ## 4. The interface of a function pointer -/

/-- Modes in bottom order, read back into a parameter list. -/
def modesOf : (P : Ctx) → List (Option PassingMode) → Modes P
  | [], _ => .nil
  | _ :: P, l => .cons ((l[P.length]?).getD none) (modesOf P (l.take P.length))

theorem modeList_modesOf : ∀ (P : Ctx) (l : List (Option PassingMode)), l.length = P.length →
    modeList (modesOf P l) = l
  | [], l, h => by simp at h; subst h; rfl
  | τ :: P, l, h => by
    have hl : (l.take P.length).length = P.length := by simp at h ⊢; omega
    simp only [modesOf, modeList, modeList_modesOf P _ hl]
    have hP : P.length < l.length := by simp at h; omega
    rw [List.getElem?_eq_getElem hP, Option.getD_some]
    have ht : l.take (P.length + 1) = l.take P.length ++ [l[P.length]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hP]; rfl
    rw [← ht, List.take_of_length_le (by simp at h; omega)]

end Gabbro.Grammatik.ArenaOwnership.Body
