module

public import Grammatik.Kern.Syntax.Extensions.Zucker.Transition
public import Grammatik.Kern.Syntax.Satz.T1
public import Grammatik.Kern.Syntax.Koernung.Teil1

public section
namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {l : Bool}

namespace TransitionWrite

/-- The specified effect uses entry snapshots, even for a later write.
    This is a relation's world expression, not another source execution path. -/
@[expose] def writtenWorld (write : TransitionWrite D Γ Λ) (entry : World D) (env : Env D Γ)
    (state : World D) : World D :=
  match write with
  | .slot table field numeric index _ target _ =>
      state.schreibSlot table Λ (eval entry index entry env).n field
        (Wert.umTyp numeric.symm (eval entry target entry env))
  | .glob global numeric _ target _ =>
      state.schreibGlob global Λ (Wert.umTyp numeric.symm (eval entry target entry env))

/-- Snapshot-only stores execute exactly the entry-indexed effect. All read
    provenance belongs to the argument capture; the store retains its event. -/
theorem statement_frozen (write : TransitionWrite D Γ Λ) (frozen : write.Frozen)
    (right : write.Permitted V) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (entry state : World D) (env : Env D Γ) :
    execStmt O passes R (write.statement (l := l) right) state env =
      .ok (write.writtenWorld entry env state) env := by
  cases frozen with
  | slot table field numeric index source target guard =>
      simp only [statement, execStmt, orte_umTyp, Expr.orte, List.append_nil,
        eval_umTyp, eval, World.lese, World.merke, List.map_nil, List.nil_append, writtenWorld]
  | glob global numeric source target guard =>
      simp only [statement, execStmt, orte_umTyp, Expr.orte, eval_umTyp, eval,
        World.lese, World.merke, List.map_nil, List.nil_append, writtenWorld]
  | slotConst table field numeric index source target sourceRange targetRange guard =>
      simp only [constEdge, statement, execStmt, orte_umTyp, Expr.orte, List.append_nil,
        eval_umTyp, eval, World.lese, World.merke, List.map_nil, List.nil_append, writtenWorld]

/-- The ordinary frame theorem is retained by the snapshot specification. -/
theorem writtenWorld_frame (write : TransitionWrite D Γ Λ) (right : write.Permitted V)
    (entry state : World D) (env : Env D Γ) :
    Rahmen V.schreibt V.gschreibt state (write.writtenWorld entry env state) := by
  cases write with
  | slot table field numeric index source target guard =>
      exact (rahmen_storeSlot V.schreibt V.gschreibt state table
        (eval entry index entry env).n field (Wert.umTyp numeric.symm (eval entry target entry env)) right).trans
        (rahmen_gleich rfl rfl)
  | glob global numeric source target guard =>
      exact (rahmen_storeGlob V.schreibt V.gschreibt state global
        (Wert.umTyp numeric.symm (eval entry target entry env)) right).trans (rahmen_gleich rfl rfl)

/-- Each captured store establishes its own target equality. -/
theorem writtenWorld_target (write : TransitionWrite D Γ Λ) (frozen : write.Frozen)
    (entry state : World D) (env : Env D Γ) :
    wahr? (eval entry write.targetEq (write.writtenWorld entry env state) env) = true := by
  cases frozen with
  | slot table field numeric index source target guard =>
      simp [targetEq, eval_umTyp, eval, writtenWorld, schreibSlot_slots_same,
        Wert.umTyp_hin_her, wahr?]
  | glob global numeric source target guard =>
      simp [targetEq, eval_umTyp, eval, writtenWorld, World.schreibGlob,
        World.storeGlob, World.merke, Wert.umTyp_hin_her, wahr?]
  | slotConst table field numeric index source target sourceRange targetRange guard =>
      simp [constEdge, targetEq, eval_umTyp, eval, writtenWorld, schreibSlot_slots_same,
        Wert.umTyp_hin_her, wahr?]
      exact Wert.umTyp_umTyp_n _ _ _

/-- Later stores must preserve an earlier target. Distinct places discharge
    this obligation; aliases require an actual equal-result proof. -/
@[expose] def Preserves (earlier later : TransitionWrite D Γ Λ) (entry : World D) (env : Env D Γ) : Prop :=
  ∀ state, eval entry earlier.targetEq (later.writtenWorld entry env state) env =
    eval entry earlier.targetEq state env

end TransitionWrite

/-- The specified post-world: source order, one fixed entry world and one
    captured environment throughout. It preserves the ordinary write trace. -/
@[expose] def transitionWorld (writes : List (TransitionWrite D Γ Λ)) (entry : World D)
    (env : Env D Γ) (state : World D) : World D :=
  writes.foldl (fun state write => write.writtenWorld entry env state) state

/-- Generic expansion correctness for any continuation and any oracle.
    In particular, stores neither call a service nor change linear resources. -/
theorem transitionEnd_correct (writes : List (TransitionWrite D Γ Λ))
    (frozen : ∀ write ∈ writes, write.Frozen) (rights : ∀ write ∈ writes, write.Permitted V)
    (rest : Endblock D V l Γ Λ) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (entry state : World D) (env : Env D Γ) :
    execEnd O passes R (transitionEnd V writes rights rest) state env =
      execEnd O passes R rest (transitionWorld writes entry env state) env := by
  induction writes generalizing state with
  | nil => rfl
  | cons write tail ih =>
      simp only [transitionEnd, execEnd]
      rw [write.statement_frozen (frozen write List.mem_cons_self) _ O passes R entry state env]
      exact ih (fun next member => frozen next (List.mem_cons_of_mem _ member))
        (fun next member => rights next (List.mem_cons_of_mem _ member)) _

/-- The complete ordered expansion stays within the declared function frame. -/
theorem transitionWorld_frame (writes : List (TransitionWrite D Γ Λ))
    (rights : ∀ write ∈ writes, write.Permitted V) (entry state : World D) (env : Env D Γ) :
    Rahmen V.schreibt V.gschreibt state (transitionWorld writes entry env state) := by
  induction writes generalizing state with
  | nil => exact rahmen_gleich rfl rfl
  | cons write tail ih =>
      exact (write.writtenWorld_frame (rights write List.mem_cons_self) entry state env).trans
        (ih (fun next member => rights next (List.mem_cons_of_mem _ member)) _)

theorem transitionWorld_preserves (writes : List (TransitionWrite D Γ Λ))
    (target : TransitionWrite D Γ Λ) (entry : World D) (env : Env D Γ)
    (preserved : ∀ write ∈ writes, target.Preserves write entry env) (state : World D) :
    eval entry target.targetEq (transitionWorld writes entry env state) env =
      eval entry target.targetEq state env := by
  induction writes generalizing state with
  | nil => rfl
  | cons write tail ih =>
      change eval entry target.targetEq
        (transitionWorld tail entry env (write.writtenWorld entry env state)) env = _
      rw [ih (fun next member => preserved next (List.mem_cons_of_mem _ member))]
      exact preserved write List.mem_cons_self state

/-- Ordered non-clobbering stores establish every declared target, rather
    than merely the last one. No atomic multi-place transaction is claimed. -/
theorem transitionWorld_targets (writes : List (TransitionWrite D Γ Λ))
    (frozen : ∀ write ∈ writes, write.Frozen) (entry : World D) (env : Env D Γ)
    (independent : writes.Pairwise (fun earlier later => earlier.Preserves later entry env))
    (state : World D) :
    ∀ write ∈ writes,
      wahr? (eval entry write.targetEq (transitionWorld writes entry env state) env) = true := by
  induction writes generalizing state with
  | nil => intro write member; cases member
  | cons write tail ih =>
      obtain ⟨head, tailIndependent⟩ := List.pairwise_cons.mp independent
      intro target member
      rcases List.mem_cons.mp member with same | member
      · rw [same]
        change wahr? (eval entry write.targetEq
          (transitionWorld tail entry env (write.writtenWorld entry env state)) env) = true
        rw [transitionWorld_preserves tail write entry env head]
        exact write.writtenWorld_target (frozen write List.mem_cons_self) entry state env
      · exact ih (fun next member => frozen next (List.mem_cons_of_mem _ member))
          tailIndependent (write.writtenWorld entry env state) target member

theorem transitionEnsures_iff (writes : List (TransitionWrite D Γ Λ))
    (entry state : World D) (env : Env D Γ) :
    wahr? (eval entry (transitionEnsures writes) state env) = true ↔
      ∀ write ∈ writes, wahr? (eval entry write.targetEq state env) = true := by
  induction writes with
  | nil => simp [transitionEnsures, eval, wahr?]
  | cons write tail ih =>
      change (wahr? (eval entry write.targetEq state env) &&
        wahr? (eval entry (transitionEnsures tail) state env)) = true ↔ _
      rw [Bool.and_eq_true, ih]
      constructor
      · rintro ⟨first, rest⟩ target member
        rcases List.mem_cons.mp member with same | member
        · subst same; exact first
        · exact rest target member
      · intro all
        exact ⟨all write List.mem_cons_self,
          fun next member => all next (List.mem_cons_of_mem _ member)⟩

/-- No clause disappears into the transition's edge projection. The caller
    owes every source equality and the original explicit requires clause. -/
theorem transitionRequires_iff (writes : List (TransitionWrite D Γ Λ))
    (clause : Expr D Γ Λ .bool) (entry state : World D) (env : Env D Γ) :
    wahr? (eval entry (transitionRequires writes clause) state env) = true ↔
      (∀ write ∈ writes, wahr? (eval entry write.sourceEq state env) = true) ∧
      wahr? (eval entry clause state env) = true := by
  induction writes with
  | nil => simp only [transitionRequires, List.foldr, List.not_mem_nil, false_implies,
      implies_true, true_and]
  | cons write tail ih =>
      change (wahr? (eval entry write.sourceEq state env) &&
        wahr? (eval entry (transitionRequires tail clause) state env)) = true ↔ _
      rw [Bool.and_eq_true, ih]
      constructor
      · rintro ⟨first, rest, pre⟩
        exact ⟨fun next member => by
          rcases List.mem_cons.mp member with same | member
          · subst same; exact first
          · exact rest next member, pre⟩
      · rintro ⟨all, pre⟩
        exact ⟨all write List.mem_cons_self,
          (fun next member => all next (List.mem_cons_of_mem _ member)), pre⟩

/-- A certified generated fragment has the exact ordered snapshot effect;
    this statement executes the real program body, not a parallel machine. -/
theorem TransitionExpansion.body_correct {P : Programm D} {function : D.Fn}
    (expansion : TransitionExpansion P function) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (entry state : World D) (env : Env D (D.params function)) :
    execEnd O passes R (P.rumpf function) state env =
      execEnd O passes R (transitionReturn (vertragVon D function) expansion.result_none
        (by rw [expansion.resources] : (Signatur.anfang D (D.signatur function)).Perm (vertragVon D function).ende))
        (transitionWorld expansion.writes entry env state) env := by
  rw [expansion.body_exact]
  exact transitionEnd_correct expansion.writes expansion.frozen expansion.rights _
    O passes R entry state env

/-- Joint semantic closure of a generated fragment. The independent-target
    premise is required at this entry; the emitter may not drop or guess it. -/
theorem TransitionExpansion.correct {P : Programm D} {function : D.Fn}
    (expansion : TransitionExpansion P function) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (entry : World D) (env : Env D (D.params function))
    (independent : expansion.writes.Pairwise
      (fun earlier later => earlier.Preserves later entry env)) :
    execEnd O passes R (P.rumpf function) entry env =
      execEnd O passes R (transitionReturn (vertragVon D function) expansion.result_none
        (by rw [expansion.resources] : (Signatur.anfang D (D.signatur function)).Perm (vertragVon D function).ende))
        (transitionWorld expansion.writes entry env entry) env ∧
    Rahmen (D.schreibt function) (D.gschreibt function) entry
      (transitionWorld expansion.writes entry env entry) ∧
    wahr? (eval entry (transitionEnsures expansion.writes)
      (transitionWorld expansion.writes entry env entry) env) = true := by
  refine ⟨?_, transitionWorld_frame expansion.writes expansion.rights entry entry env, ?_⟩
  · exact expansion.body_correct O passes R entry entry env
  · exact (transitionEnsures_iff _ _ _ _).mpr
      (transitionWorld_targets expansion.writes expansion.frozen entry env independent entry)

/-- Constant-edge expansion agrees with the existing shift on legal entry
    memory. The primitive shift also records its explicit pre-state read;
    the generated function records that read in its requires check instead. -/
theorem transition_constant_shift (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (table : D.Tab) (field : D.Feld table) {lo hi : Int}
    (numeric : D.typ table field = .int lo hi) (index : Var Γ (.index (D.count table)))
    (source target : Int) (range : lo ≤ target ∧ target ≤ hi)
    (edge : D.erlaubt table field source target = true)
    (right : V.schreibt table = true) (guard : darf D table Λ)
    (state : World D) (env : Env D Γ)
    (legal : (Wert.umTyp numeric (state.slots table (env.get index).n field)).n = source) :
    let value : Wert D (D.typ table field) := Wert.umTyp numeric.symm ⟨target, range.1, range.2⟩
    let shifted := (state.lese Λ [.inl table]).schreibSlot table Λ (env.get index).n field value
    let stored := state.schreibSlot table Λ (env.get index).n field value
    execStmt O passes R (Stmt.shift (V := V) (l := l) table field numeric (.var index)
      source target range edge right guard) state env = .ok shifted env ∧
    execStmt O passes R (Stmt.assignSlot (V := V) (l := l) table field (.var index)
      ((Expr.widen range.1 range.2 (.lit target)).umTyp numeric.symm) right guard) state env =
        .ok stored env ∧ shifted.slots = stored.slots ∧ shifted.globs = stored.globs := by
  dsimp only
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp only [execStmt, Expr.orte, eval]
    change (if (Wert.umTyp numeric (state.slots table (env.get index).n field)).n = source
      then _ else _) = _
    rw [if_pos legal]
    rfl
  · simp only [execStmt, orte_umTyp, Expr.orte, List.append_nil, eval_umTyp, eval]
    rfl

end Gabbro.Grammatik
