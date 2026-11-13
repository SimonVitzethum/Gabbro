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

mutual
theorem kostenExpr_ru {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) :
    kostenExpr (ruE e) = kostenExpr e := by
  cases e <;> simp only [ruE, kostenExpr, kostenNutz_cast, kostenArgs_cast,
    kostenExpr_ru, kostenNutz_ru, kostenArgs_ru, ibR_arbeit]
termination_by structural e

theorem kostenNutz_ru {Γ : Ctx} {Λ : List (Res D)} {c : Option Ty}
    (e : NutzlastExpr D Γ Λ c) : kostenNutz (ruN e) = kostenNutz e := by
  cases e <;> simp only [ruN, kostenNutz, kostenExpr_ru]
termination_by structural e

theorem kostenArgs_ru {Γ : Ctx} {Λ : List (Res D)} {ts : List Ty} (args : Args D Γ Λ ts) :
    kostenArgs (ruA args) = kostenArgs args := by
  cases args <;> simp only [ruA, kostenArgs, kostenExpr_ru, kostenArgs_ru]
termination_by structural args
end

@[simp] theorem kostenExpr_umΓ {Γ Γ' : Ctx} {Λ : List (Res D)} {τ : Ty}
    (h : Γ = Γ') (e : Expr D Γ Λ τ) : kostenExpr (Expr.umΓ h e) = kostenExpr e := by
  subst h
  rfl

@[simp] theorem kostenExpr_umΛ {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (h : Λ = Λ') (e : Expr D Γ Λ τ) : kostenExpr (Expr.umΛ h e) = kostenExpr e := by
  subst h
  rfl

/-- User returns retain their predicate costs when the idle root is added. -/
theorem kostenEpilog_ru (P : Programm D) (f : D.Fn) :
    kostenEpilog P.mitRuhe (some f) = kostenEpilog P f := by
  simp only [kostenEpilog, Programm.mitRuhe, kostenExpr_umΓ, kostenExpr_umΛ,
    kostenExpr_ru] <;> rfl

theorem kostenErg_ru {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} (e : ErgExpr D Γ Λ o) :
    kostenErg (ruErg e) = kostenErg e := by
  cases e <;> simp only [ruErg, kostenErg, kostenExpr_ru]

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
  cases s <;> simp only [ruS, entfZ_nachΛ, entfZ, GEntfaltbar, ↓reduceIte]

section Costs
variable (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}

mutual
theorem kostenStmt_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') :
    kostenStmt ep (fun g => g.elim 0 c) pa (ruS s) = kostenStmt ep c pa s := by
  cases s <;> simp only [ruS, kostenStmt_nachΛ, kostenStmt, kostenExpr_ru, kostenArgs_ru,
    kostenErg_ru, kostenBlock_ru, kostenArms_ru, kostenGrundArms_ru, kostenSonst_umΛ,
    kostenSonst_ru, Option.elim]
termination_by structural s

theorem kostenBlock_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') :
    kostenBlock ep (fun g => g.elim 0 c) pa (ruB b) = kostenBlock ep c pa b := by
  cases b <;> simp only [ruB, kostenBlock, kostenBlock_vorΛ, kostenStmt_ru,
    kostenExpr_ru, kostenArgs_ru, kostenBlock_ru, kostenSonst_umΛ, kostenSonst_ru, Option.elim]
termination_by structural b

theorem kostenArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) :
    kostenArms ep (fun g => g.elim 0 c) pa (ruArms arms) = kostenArms ep c pa arms := by
  cases arms <;> simp only [ruArms, kostenArms, kostenBlock_ru, kostenArms_ru]
termination_by structural arms

theorem kostenGrundArms_ru {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) :
    kostenGrundArms ep (fun g => g.elim 0 c) pa (ruGArms arms) = kostenGrundArms ep c pa arms := by
  cases arms <;> simp only [ruGArms, kostenGrundArms, kostenBlock_ru, kostenGrundArms_ru]
termination_by structural arms

theorem kostenEnd_ru {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    kostenEnd ep (fun g => g.elim 0 c) pa (ruEnd e) = kostenEnd ep c pa e := by
  cases e <;> simp only [ruEnd, kostenEnd, kostenEnd_umΛ, kostenSonst_umΛ,
    kostenExpr_ru, kostenArgs_ru, kostenErg_ru, entfZ_ru, kostenStmt_ru,
    kostenEnd_ru, kostenSonst_ru, Option.elim]
termination_by structural e

theorem kostenSonst_ru {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    kostenSonst ep (fun g => g.elim 0 c) pa (ruEnd e) = kostenSonst ep c pa e := by
  cases e <;> simp only [ruEnd, kostenSonst, kostenSonst_umΛ,
    kostenExpr_ru, kostenArgs_ru, kostenErg_ru, kostenStmt_ru, kostenSonst_ru, Option.elim]
termination_by structural e
end
end Costs
end HaltRuhe
end Gabbro.Grammatik
