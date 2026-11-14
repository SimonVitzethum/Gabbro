/- The idle-root translation preserves the cost of user syntax. Transport of resource/type
   indices changes no cost; the only new function is not called by any translated body. -/
module
public import Grammatik.Logik.Fortschritt.Halten.Pruefung
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe
@[expose] public section

namespace Gabbro.Grammatik
namespace HaltRuhe
variable {D : Deklaration}

@[simp] theorem kostenNutz_cast {Γ : Ctx} {Λ : List (Res D)} {a b : Option Ty}
    (h : a = b) (e : NutzlastExpr D Γ Λ a) : kostenNutz (h ▸ e) = kostenNutz e := by
  subst h
  rfl

@[simp] theorem kostenArgs_cast {Γ : Ctx} {Λ : List (Res D)} {a b : List Ty}
    (h : a = b) (e : Args D Γ Λ a) : kostenArgs (h ▸ e) = kostenArgs e := by
  subst h
  rfl

theorem ibR_arbeit {ts : List Ty} {τ : Ty} (op : IntBuiltin ts τ) :
    (ibR op).arbeit = op.arbeit := by
  cases op <;> rfl

private theorem cost_congr₂ (f : Nat → Nat → Nat) {a a' b b' : Nat}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl

mutual
theorem kostenExpr_ru {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) :
    kostenExpr (ruE e) = kostenExpr e := by
  match e with
  | .lit _ | .tru | .fls | .var _ | .glob _ _ | .ptrOf .. | .fnref .. | .oldG ..
  | .none _ | .why .. | .forallSlots .. | .existsSlots .. | .arrNil | .strLit .. => rfl
  | .slot _ _ i _ | .oldS _ _ i _ => exact (congrArg (1 + ·) (kostenExpr_ru i) :)
  | .thru p _ _ _ i _ | .thruOwn p _ _ _ i _ _ _ _ _ _ =>
    exact (cost_congr₂ (fun x y => 1 + x + y) (kostenExpr_ru p) (kostenExpr_ru i) :)
  | .slotRef r .. => exact (congrArg (1 + ·) (kostenExpr_ru r) :)
  | .widen _ _ a | .neg a | .not a | .some a | .istSome a | .strLen a | .strWeit _ a
  | .prodGet a _ => exact (congrArg (1 + ·) (kostenExpr_ru a) :)
  | .refEq a b | .add a b | .sub a b | .mul a b | .div _ _ a b | .rem _ _ a b
  | .sdiv _ a b | .srem _ a b | .band _ _ a b | .bor _ _ _ _ _ a b
  | .bxor _ _ _ _ _ a b | .shl _ _ _ _ _ a b | .shr _ _ _ _ _ a b
  | .lt a b | .le a b | .eq a b | .fllt a b | .flle a b | .and a b | .or a b
  | .reaches _ _ _ a b _ | .arrCons a b | .arrGet a b | .strCat a b | .strGet a b
  | .strEq a b | .strLt a b | .eng a _ _ b | .prodSet a _ b =>
    exact (cost_congr₂ (fun x y => 1 + x + y) (kostenExpr_ru a) (kostenExpr_ru b) :)
  | .getBytes _ _ _ _ i _ _ _ => exact (congrArg (1 + ·) (kostenExpr_ru i) :)
  | .case _ _ payload =>
    simp only [ruE, kostenExpr, kostenNutz_cast]
    exact (congrArg (1 + ·) (kostenNutz_ru payload) :)
  | .arrSet a i v | .wenn a i v =>
    exact (cost_congr₂ (· + ·)
      (cost_congr₂ (fun x y => 1 + x + y) (kostenExpr_ru a) (kostenExpr_ru i))
      (kostenExpr_ru v) :)
  | .intBuiltin1 op a =>
    exact (cost_congr₂ (· + ·) (ibR_arbeit op) (kostenExpr_ru a) :)
  | .intBuiltin2 op a b =>
    exact (cost_congr₂ (· + ·)
      (cost_congr₂ (· + ·) (ibR_arbeit op) (kostenExpr_ru a)) (kostenExpr_ru b) :)
  | .count n body => exact (congrArg (fun x => 1 + n * (x + 1)) (kostenExpr_ru body) :)
  | .prod _ args =>
    simp only [ruE, kostenExpr, kostenArgs_cast]
    exact kostenArgs_ru args
termination_by structural e

theorem kostenNutz_ru {Γ : Ctx} {Λ : List (Res D)} {c : Option Ty}
    (e : NutzlastExpr D Γ Λ c) : kostenNutz (ruN e) = kostenNutz e := by
  match e with
  | .empty => rfl
  | .val e => exact kostenExpr_ru e
termination_by structural e

theorem kostenArgs_ru {Γ : Ctx} {Λ : List (Res D)} {ts : List Ty} (args : Args D Γ Λ ts) :
    kostenArgs (ruA args) = kostenArgs args := by
  match args with
  | .nil => rfl
  | .cons e rest => exact cost_congr₂ (· + ·) (kostenExpr_ru e) (kostenArgs_ru rest)
termination_by structural args
end

theorem kostenErg_ru {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} (e : ErgExpr D Γ Λ o) :
    kostenErg (ruErg e) = kostenErg e := by
  cases e with
  | empty => rfl
  | val e => exact kostenExpr_ru e

@[simp] theorem kostenExpr_umΛ {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (h : Λ = Λ')
    (e : Expr D Γ Λ τ) : kostenExpr (Expr.umΛ h e) = kostenExpr e := by
  subst h
  rfl

@[simp] theorem kostenExpr_umΓ {Γ Γ' : Ctx} {Λ : List (Res D)} {τ : Ty} (h : Γ = Γ')
    (e : Expr D Γ Λ τ) : kostenExpr (Expr.umΓ h e) = kostenExpr e := by
  subst h
  rfl

/-- **The return-predicate price of a user function is unchanged by the idle root** (C05): its
    `ensures` and owed invariants are the translated ones of `P`, owed exactly as in `P`. -/
theorem kostenEpilog_mitRuhe (P : Programm D) (f : D.Fn) :
    kostenEpilog P.mitRuhe (some f) = kostenEpilog P f := by
  have he : kostenExpr (P.mitRuhe.ensures (some f)) = kostenExpr (P.ensures f) := by
    exact (kostenExpr_umΓ (ergCtx_map (D.params f) (D.erg f))
      (Expr.umΛ (ende_map (vertragVon D f)) (ruE (P.ensures f)))).trans
      ((kostenExpr_umΛ (ende_map (vertragVon D f)) (ruE (P.ensures f))).trans
        (kostenExpr_ru (P.ensures f)))
  have hi : (fun i => kostenExpr (P.mitRuhe.invariante i)) =
      (fun i => kostenExpr (P.invariante i)) := by
    funext i
    exact (kostenExpr_umΛ (invSicht_map (D := D) i) (ruE (P.invariante i))).trans
      (kostenExpr_ru (P.invariante i))
  unfold kostenEpilog
  rw [he, hi]
  rfl

section Transport
variable (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}

@[simp] theorem kostenStmt_nachΛ {Λ a b : List (Res D)} (h : a = b)
    (s : Stmt D V l Γ Λ a) : kostenStmt ep c pa (Stmt.nachΛ h s) = kostenStmt ep c pa s := by
  subst h
  rfl

@[simp] theorem kostenBlock_vorΛ {a b Λ : List (Res D)} (h : a = b)
    (s : Block D V l Γ a Λ) : kostenBlock ep c pa (Block.vorΛ h s) = kostenBlock ep c pa s := by
  subst h
  rfl

@[simp] theorem kostenEnd_umΛ {a b : List (Res D)} (h : a = b)
    (s : Endblock D V l Γ a) : kostenEnd ep c pa (Endblock.umΛ h s) = kostenEnd ep c pa s := by
  subst h
  rfl

@[simp] theorem kostenSonst_umΛ {a b : List (Res D)} (h : a = b)
    (s : Endblock D V l Γ a) : kostenSonst ep c pa (Endblock.umΛ h s) = kostenSonst ep c pa s := by
  subst h
  rfl
end Transport

@[simp] theorem entfZ_nachΛ {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ a b : List (Res D)} (h : a = b) (s : Stmt D V l Γ Λ a) :
    entfZ (Stmt.nachΛ h s) = entfZ s := by
  subst h
  rfl

theorem entfZ_ru {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') : entfZ (ruS s) = entfZ s := by
  cases s <;> simp only [ruS] <;> (try erw [entfZ_nachΛ]) <;>
    (try simp only [entfZ, GEntfaltbar, ↓reduceIte]) <;> rfl

section Costs
variable (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}

/- Every case unfolds one constructor, transports the index casts, and rewrites the
   translated subterms by the recursive cost laws (`erw`: the translated indices agree
   only definitionally). -/
mutual
theorem kostenStmt_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') :
    kostenStmt ep (fun (g : Option D.Fn) => g.elim 0 c) pa (ruS s) = kostenStmt ep c pa s := by
  match s with
  | .assignSlot .. | .assignThru .. | .assignGlob .. | .putBytes .. | .assignVar .. | .shift ..
  | .ite .. | .onOption .. | .onTag .. | .onWhy .. | .call .. | .callInd .. | .locks ..
  | .breaking .. | .traverse .. | .retry .. | .forever .. | .axiomCall .. | .regWrite ..
  | .transition .. | .publish .. | .advances .. | .retires .. | .ret .. | .retWhy .. | .leave ..
  | .next .. | .assignSlotRef .. | .consumeTraverse .. | .retScoped .. | .retWhyScoped ..
  | .axiomCallElse .. | .callIndElse .. | .assignThruOwn .. =>
    (try simp only [ruS, kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
        entfZ_ru, Option.elim_some, Option.elim_none])
    repeat
      (first
        | erw [kostenStmt_nachΛ]
        | erw [kostenBlock_vorΛ]
        | erw [kostenEnd_umΛ]
        | erw [kostenSonst_umΛ]
        | erw [kostenExpr_ru]
        | erw [kostenArgs_ru]
        | erw [kostenErg_ru]
        | erw [kostenStmt_ru]
        | erw [kostenBlock_ru]
        | erw [kostenArms_ru]
        | erw [kostenGrundArms_ru]
        | erw [kostenEnd_ru]
        | erw [kostenSonst_ru]
        | simp only [kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
        entfZ_ru, Option.elim_some, Option.elim_none]
        )
    try rfl
termination_by sizeOf s

theorem kostenBlock_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') :
    kostenBlock ep (fun (g : Option D.Fn) => g.elim 0 c) pa (ruB b) = kostenBlock ep c pa b := by
  match b with
  | .nil .. | .cons .. | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse ..
  | .bindAxiom .. | .bindAxiomElse .. | .regRead .. | .regReadElse .. | .awaits ..
  | .exchange .. | .narrow .. | .check .. | .float .. | .floatLit .. | .floatOf ..
  | .floatNarrow .. | .narrowRequired .. | .bindCallIndElse .. =>
    (try simp only [ruB, kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
        entfZ_ru, Option.elim_some, Option.elim_none])
    repeat
      (first
        | erw [kostenStmt_nachΛ]
        | erw [kostenBlock_vorΛ]
        | erw [kostenEnd_umΛ]
        | erw [kostenSonst_umΛ]
        | erw [kostenExpr_ru]
        | erw [kostenArgs_ru]
        | erw [kostenErg_ru]
        | erw [kostenStmt_ru]
        | erw [kostenBlock_ru]
        | erw [kostenArms_ru]
        | erw [kostenGrundArms_ru]
        | erw [kostenEnd_ru]
        | erw [kostenSonst_ru]
        | simp only [kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
        entfZ_ru, Option.elim_some, Option.elim_none]
        )
    try rfl
  | .bindAxiomOpt (e := none) (rest := rest) .. | .bindAxiomOptElse (e := none) (rest := rest) ..
  | .bindAxiomOpt (e := some _) (rest := rest) ..
  | .bindAxiomOptElse (e := some _) (rest := rest) .. =>
    (try simp only [ruB, kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
      entfZ_ru, Option.elim_some, Option.elim_none])
    repeat
      (first
        | erw [kostenBlock_ru rest]
        | erw [kostenStmt_nachΛ]
        | erw [kostenBlock_vorΛ]
        | erw [kostenEnd_umΛ]
        | erw [kostenSonst_umΛ]
        | erw [kostenExpr_ru]
        | erw [kostenArgs_ru]
        | erw [kostenErg_ru]
        | erw [kostenStmt_ru]
        | erw [kostenBlock_ru]
        | erw [kostenArms_ru]
        | erw [kostenGrundArms_ru]
        | erw [kostenEnd_ru]
        | erw [kostenSonst_ru]
        | simp only [kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
      entfZ_ru, Option.elim_some, Option.elim_none]
        )
    try rfl
termination_by sizeOf b

theorem kostenArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) :
    kostenArms ep (fun (g : Option D.Fn) => g.elim 0 c) pa (ruArms arms) = kostenArms ep c pa arms := by
  match arms with
  | .nil => rfl
  | .cons (c := none) b rest | .cons (c := some _) b rest =>
    exact cost_congr₂ max (kostenBlock_ru b) (kostenArms_ru rest)
termination_by sizeOf arms

theorem kostenGrundArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) :
    kostenGrundArms ep (fun (g : Option D.Fn) => g.elim 0 c) pa (ruGArms arms) =
      kostenGrundArms ep c pa arms := by
  match arms with
  | .nil => rfl
  | .cons b rest =>
    exact cost_congr₂ max (kostenBlock_ru b) (kostenGrundArms_ru rest)
termination_by sizeOf arms

theorem kostenEnd_ru {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    kostenEnd ep (fun (g : Option D.Fn) => g.elim 0 c) pa (ruEnd e) = kostenEnd ep c pa e := by
  match e with
  | .ret .. | .retWhy .. | .leave .. | .next .. | .cons .. | .bind .. | .bindCall ..
  | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse .. | .regRead .. | .regReadElse ..
  | .awaits .. | .bindCallInd .. | .narrow .. | .exchange .. | .ite .. | .narrowRequired ..
  | .retScoped .. | .retWhyScoped .. | .bindCallIndElse .. | .float .. | .floatLit ..
  | .floatOf .. | .floatNarrow .. =>
    (try simp only [ruEnd, kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
        entfZ_ru, Option.elim_some, Option.elim_none])
    repeat
      (first
        | erw [kostenStmt_nachΛ]
        | erw [kostenBlock_vorΛ]
        | erw [kostenEnd_umΛ]
        | erw [kostenSonst_umΛ]
        | erw [kostenExpr_ru]
        | erw [kostenArgs_ru]
        | erw [kostenErg_ru]
        | erw [kostenStmt_ru]
        | erw [kostenBlock_ru]
        | erw [kostenArms_ru]
        | erw [kostenGrundArms_ru]
        | erw [kostenEnd_ru]
        | erw [kostenSonst_ru]
        | simp only [kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
        entfZ_ru, Option.elim_some, Option.elim_none]
        )
    try rfl
  | .bindAxiomOpt (e := none) (rest := rest) .. | .bindAxiomOptElse (e := none) (rest := rest) ..
  | .bindAxiomOpt (e := some _) (rest := rest) ..
  | .bindAxiomOptElse (e := some _) (rest := rest) .. =>
    (try simp only [ruEnd, kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
      entfZ_ru, Option.elim_some, Option.elim_none])
    repeat
      (first
        | erw [kostenEnd_ru rest]
        | erw [kostenSonst_ru rest]
        | erw [kostenStmt_nachΛ]
        | erw [kostenBlock_vorΛ]
        | erw [kostenEnd_umΛ]
        | erw [kostenSonst_umΛ]
        | erw [kostenExpr_ru]
        | erw [kostenArgs_ru]
        | erw [kostenErg_ru]
        | erw [kostenStmt_ru]
        | erw [kostenBlock_ru]
        | erw [kostenArms_ru]
        | erw [kostenGrundArms_ru]
        | erw [kostenEnd_ru]
        | erw [kostenSonst_ru]
        | simp only [kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
      entfZ_ru, Option.elim_some, Option.elim_none]
        )
    try rfl
termination_by sizeOf e

theorem kostenSonst_ru {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    kostenSonst ep (fun (g : Option D.Fn) => g.elim 0 c) pa (ruEnd e) = kostenSonst ep c pa e := by
  match e with
  | .ret .. | .retWhy .. | .leave .. | .next .. | .cons .. | .bind .. | .bindCall ..
  | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse .. | .regRead .. | .regReadElse ..
  | .awaits .. | .bindCallInd .. | .narrow .. | .exchange .. | .ite .. | .narrowRequired ..
  | .retScoped .. | .retWhyScoped .. | .bindCallIndElse .. | .float .. | .floatLit ..
  | .floatOf .. | .floatNarrow .. =>
    (try simp only [ruEnd, kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
        entfZ_ru, Option.elim_some, Option.elim_none])
    repeat
      (first
        | erw [kostenStmt_nachΛ]
        | erw [kostenBlock_vorΛ]
        | erw [kostenEnd_umΛ]
        | erw [kostenSonst_umΛ]
        | erw [kostenExpr_ru]
        | erw [kostenArgs_ru]
        | erw [kostenErg_ru]
        | erw [kostenStmt_ru]
        | erw [kostenBlock_ru]
        | erw [kostenArms_ru]
        | erw [kostenGrundArms_ru]
        | erw [kostenEnd_ru]
        | erw [kostenSonst_ru]
        | simp only [kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
        entfZ_ru, Option.elim_some, Option.elim_none]
        )
    try rfl
  | .bindAxiomOpt (e := none) (rest := rest) .. | .bindAxiomOptElse (e := none) (rest := rest) ..
  | .bindAxiomOpt (e := some _) (rest := rest) ..
  | .bindAxiomOptElse (e := some _) (rest := rest) .. =>
    (try simp only [ruEnd, kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
      entfZ_ru, Option.elim_some, Option.elim_none])
    repeat
      (first
        | erw [kostenEnd_ru rest]
        | erw [kostenSonst_ru rest]
        | erw [kostenStmt_nachΛ]
        | erw [kostenBlock_vorΛ]
        | erw [kostenEnd_umΛ]
        | erw [kostenSonst_umΛ]
        | erw [kostenExpr_ru]
        | erw [kostenArgs_ru]
        | erw [kostenErg_ru]
        | erw [kostenStmt_ru]
        | erw [kostenBlock_ru]
        | erw [kostenArms_ru]
        | erw [kostenGrundArms_ru]
        | erw [kostenEnd_ru]
        | erw [kostenSonst_ru]
        | simp only [kostenStmt, kostenBlock, kostenEnd, kostenSonst, kostenExpr_ru, kostenArgs_ru, kostenErg_ru,
      entfZ_ru, Option.elim_some, Option.elim_none]
        )
    try rfl
termination_by sizeOf e
end
end Costs
end HaltRuhe
end Gabbro.Grammatik
