module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T3.Teil1Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T3.Teil1Basis

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T2

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 5. Loops and abrupt exits: the steps, the peels, the sequential outcomes -/

section Schleifen

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem w_dannTrav {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.traverse t inv body) rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.trav t inv body (alleIndizes (D.count t)) (.dann rest k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannTrav M f l Γ Λ Λ'' t inv body rest k ρ hhead, zustandG_neu rfl rfl⟩

theorem w_travNext {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (i : Wert D (.index (D.count t))) (is : List (Wert D (.index (D.count t))))
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .trav t inv body (i :: is) k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ inv.orte) inv ((M.weltVon f).lese Λ inv.orte) ρ)
      = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons i ρ)
        (.dann body (.travRest t inv body is k)) ((M.weltVon f).lese Λ inv.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.travNext M f l Γ Λ t inv body i is k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_travFort {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t))))
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (i : Wert D (.index (D.count t)))
    (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ,
      .travRest t inv body is k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.trav t inv body is k) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.travFort M f l Γ Λ t inv body is k i ρ hhead, zustandG_neu rfl rfl⟩

theorem w_travDone {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .trav t inv body [] k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ inv.orte) inv ((M.weltVon f).lese Λ inv.orte) ρ)
      = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k
        ((M.weltVon f).lese Λ inv.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.travDone M f l Γ Λ t inv body k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_dannRetry {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.retry n bis body ueber) rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.wieder n bis body ueber (.dann rest k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRetry M f l Γ Λ Λ Λ'' n bis body ueber rest k ρ hhead,
    zustandG_neu rfl rfl⟩

theorem w_wiederUeber {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (bis : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .wieder 0 bis body ueber k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons (.ite bis .nil ueber) .nil) k) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.wiederUeber M f l Γ Λ bis body ueber k ρ hhead, zustandG_neu rfl rfl⟩

theorem w_wiederWeiter {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .wieder (n + 1) bis body ueber k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ bis.orte) bis ((M.weltVon f).lese Λ bis.orte) ρ)
      = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k
        ((M.weltVon f).lese Λ bis.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.wiederWeiter M f l Γ Λ n bis body ueber k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_wiederSchritt {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .wieder (n + 1) bis body ueber k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ bis.orte) bis ((M.weltVon f).lese Λ bis.orte) ρ)
      = false)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann body (.wiederRest n bis body ueber k)) ((M.weltVon f).lese Λ bis.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.wiederSchritt M f l Γ Λ n bis body ueber k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_wiederFort {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λ, ρ, .wiederRest n bis body ueber k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.wieder n bis body ueber k) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.wiederFort M f l Γ Λ n bis body ueber k ρ hhead, zustandG_neu rfl rfl⟩

theorem w_dannForever {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.forever a inv body) rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.ewig a passes inv body (.dann rest k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannForever M f l Γ Λ Λ Λ'' a inv body rest k ρ hhead,
    zustandG_neu rfl rfl⟩

theorem w_ewigWeiter {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a (n + 1) inv body k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ inv.orte) inv ((M.weltVon f).lese Λ inv.orte) ρ)
      = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann body (.ewigRest a n inv body k)) ((M.weltVon f).lese Λ inv.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.ewigWeiter M f l Γ Λ a n inv body k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_ewigFort {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λ, ρ, .ewigRest a n inv body k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.ewig a n inv body k) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.ewigFort M f l Γ Λ a n inv body k ρ hhead, zustandG_neu rfl rfl⟩

end Schleifen
/-! ### Abrupt exits: the exit statement, the loop shims, the peels -/

/-- The abrupt exit statement of kind `w` (`true`: `leave`, `false`: `next`),
    at any holdings, inside a loop (`hl`). -/
def abbS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (hl : l = true) :
    Bool → Stmt D V l Γ Λ Λ
  | true => .leave hl
  | false => .next hl

section Ausgaenge

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- Holdings exactly held carry backwards along a block: a block keeps the
    held locks of its holdings (`Block.held_iff`). -/
theorem heldB_block {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λx Λ : List (Res D)}
    (r : Block D V l Γ Λx Λ) {bo : Option Int} {h : List D.Lock} (hh : HeldB bo Λ h) :
    HeldB bo Λx h :=
  heldB_iff (fun L => (Block.held_iff r L).symm) hh

/-- `leave` at the `traverse` shim: the invariant is read, the loop is left. -/
theorem w_leaveTrav {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λx : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t))))
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (r : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
      .dann (.cons (abbS rfl true) r) (.travRest t inv body is k)⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ inv.orte) inv ((M.weltVon f).lese Λ inv.orte) ρ)
      = true)
    (hΛ : HeldIn Λx (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k
        ((M.weltVon f).lese Λ inv.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannLeaveTrav M f l Γ Λ t inv body is k r i ρ rfl hhead _ _ [] rfl rfl
    (fun _ _ h => absurd h List.not_mem_nil) _ rfl hw _ rfl hΛ, zustandG_neu rfl rfl⟩

/-- `next` at the `traverse` shim: the next index. -/
theorem w_nextTrav {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λx : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t))))
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (r : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
      .dann (.cons (abbS rfl false) r) (.travRest t inv body is k)⟩)
    (hΛ : HeldIn Λx (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.trav t inv body is k) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannNextTrav M f l Γ Λ t inv body is k r i ρ rfl hhead _ _ [] rfl rfl
    (fun _ _ h => absurd h List.not_mem_nil) hΛ, zustandG_neu rfl rfl⟩

/-- `leave`/`next` at the `retry` shim. -/
theorem w_abbWieder {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λx : List (Res D)} (w : Bool)
    (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (r : Block D (vertragVon D z.kopf.f) true Γ Λx Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λx, ρ,
      .dann (.cons (abbS rfl w) r) (.wiederRest n bis body ueber k)⟩)
    (hΛ : HeldIn Λx (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (match w with | true => k | false => .wieder n bis body ueber k) (M.weltVon f) := by
  subst hz
  cases w with
  | true =>
    exact ⟨_, RufSchrittG.dannLeaveWieder M f l Γ Λ n bis body ueber k r ρ rfl hhead _ _ []
      rfl rfl (fun _ _ h => absurd h List.not_mem_nil) hΛ, zustandG_neu rfl rfl⟩
  | false =>
    exact ⟨_, RufSchrittG.dannNextWieder M f l Γ Λ n bis body ueber k r ρ rfl hhead _ _ []
      rfl rfl (fun _ _ h => absurd h List.not_mem_nil) hΛ, zustandG_neu rfl rfl⟩

/-- `leave`/`next` at the `forever` shim. -/
theorem w_abbEwig {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λx : List (Res D)} (w : Bool)
    (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (r : Block D (vertragVon D z.kopf.f) true Γ Λx Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λx, ρ,
      .dann (.cons (abbS rfl w) r) (.ewigRest a n inv body k)⟩)
    (hΛ : HeldIn Λx (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (match w with | true => k | false => .ewig a n inv body k) (M.weltVon f) := by
  subst hz
  cases w with
  | true =>
    exact ⟨_, RufSchrittG.dannLeaveEwig M f l Γ Λ a n inv body k r ρ rfl hhead _ _ []
      rfl rfl (fun _ _ h => absurd h List.not_mem_nil) hΛ, zustandG_neu rfl rfl⟩
  | false =>
    exact ⟨_, RufSchrittG.dannNextEwig M f l Γ Λ a n inv body k r ρ rfl hhead _ _ []
      rfl rfl (fun _ _ h => absurd h List.not_mem_nil) hΛ, zustandG_neu rfl rfl⟩

end Ausgaenge
end Gabbro.Grammatik
