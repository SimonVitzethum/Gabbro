/- Part 11a of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T10
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Is the statement a `traverse`? -/
def Stmt.istTraverse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .traverse .. => true
  | _ => false

/-- Does the residue start with a `traverse` statement? (Refutes heads whose
    statement differs where the holdings indices do not unify.) -/
def GRest.kopfTraverse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende (.cons s _) => s.istTraverse
  | .dann (.cons s _) _ => s.istTraverse
  | _ => false

set_option hygiene false in
/-- Close a step case whose head shape cannot be the given one, or whose
    side condition contradicts it. -/
macro "kopfweg" : tactic => `(tactic| (
  first
  | (rw [hR] at hhead; cases hhead; done)
  | (rw [hR] at hhead
     have hk := congrArg (fun x => GRest.kopfTraverse x.2.2.2.2) hhead
     simp [GRest.kopfTraverse, Stmt.istTraverse] at hk; done)
  | (rw [hR] at hhead; cases hhead; simp [Stmt.istBlatt] at hleaf; done)
  | (rw [hR] at hhead; cases hhead; simp [execStmt] at hstep; done)
  | (rw [hS] at hpop; cases hpop; done)))

set_option hygiene false in
/-- `kopfweg` with the head equation found by its type rather than by position:
    `cases` orders constructor fields by dependency, so positional names drift. -/
macro "kopfwegH" : tactic => `(tactic| (
  have hhead := ‹(M.faeden f).kopf.rest = _›
  (try have hleaf := ‹Stmt.istBlatt _ = true›)
  (try have hstep := ‹execStmt _ _ _ _ _ _ = _›)
  (try have hpop := ‹(M.faeden f).stapel = _›)
  kopfweg))

/-- At a head `ende (traverse …; rest)` every step of `f` is the unfold
    `endeEntf`. (The first disjunct, frame, stack and log kept, was the bare
    lock steps, removed from G on 2026-09-13; it is kept in the statement
    and no longer produced.) -/
theorem trav_ende_schritt {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Endblock D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons (.traverse t inv body) rest)⟩) :
    (∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩) ∨
    (∃ sp, M'.faeden f = ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
      ⟨l, Γ, Λ, ρ, .dann (.cons (.traverse t inv body) .nil) (.ende rest)⟩⟩, sp, z.log⟩) := by
  subst hz
  cases hs with
  | g1 hs =>
    cases hs with
    | endeBindAxiomOpt =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | blatt _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
    | ruf =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueck =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeEntf _ _ _ _ _ _ _ _ hhead => (rw [hR] at hhead; cases hhead; exact Or.inr ⟨_, rufUpdateG_self _ _ _⟩)
    | endeForm _ _ _ _ _ _ hent hhead => (rw [hR] at hhead; cases hhead; exact absurd hent (by simp only [EndEntfaltbar, Bool.false_eq_true, not_false_eq_true]))
    | dannBlatt =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLeer =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannIteWahr =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannIteFalsch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannOnOptionSome =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannOnOptionNone =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannOnTagSome =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannOnTagNone =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannOnGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeBind =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBind =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannNarrowOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeBindAxiom =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g2 hs =>
    cases hs with
    | dannNarrowElse =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannPruefWahr =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannPruefFalsch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBreaking =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLocks =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | freiGib =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | schrumpfVergiss =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannTrav =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | travNext =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | travFort =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | travDone =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRetry =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | wiederUeber =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | wiederWeiter =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | wiederSchritt =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | wiederFort =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannForever =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | ewigWeiter =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | ewigFort =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rufDann =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g3 hs =>
    cases hs with
    | dannAxiomCallElseOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannAxiomCallElseGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannCallInd =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rufCallInd =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindCall =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindCallInd =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindCallElse =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindCallIndElse =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannCallIndElse =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckBind =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLeaveTrav =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannNextTrav =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLeaveWieder =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannNextWieder =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLeaveEwig =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g4 hs =>
    cases hs with
    | dannNextEwig =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelDannLeave =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelDannNext =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelSchrumpfLeave =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelSchrumpfNext =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelFreiLeave =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelFreiNext =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelAbbruchLeave =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelAbbruchNext =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRet =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckCons =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRetBind =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckConsBind =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g5 hs =>
    cases hs with
    | dannBindAxiomOpt =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindAxiomOptElseOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindAxiomOptElseGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRegLies =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRegLiesElseWahr =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRegLiesElseFalsch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannAwaits =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannExchange =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannGleit =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannGleitLit =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannGleitVon =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannGleitNarrowOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannGleitNarrowElse =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindAxiom =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindAxiomElseOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindAxiomElseGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckConsGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRetGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g6 hs =>
    cases hs with
    | endeBindAxiomOptElseOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeBindAxiomOptElseGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeBindAxiomElseOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeBindAxiomElseGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g7 hs =>
    cases hs with
    | dannVerbrauch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | verbrauchWeiter =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | verbrauchLeer =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | verbrauchFort =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLeaveVerbrauch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannNextVerbrauch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckScopedWert ρ r e R hhead hret
    | rueckScopedWertDirekt ρ r e R hhead hret =>
      rcases GRest.scopedWert_faelle hret with hr | ⟨rest, hr⟩ | ⟨Λ', rest, k, hr⟩ <;>
        subst r <;> (have hhead := hhead; kopfweg)
    | rueckScopedGrund ρ r grund R hhead hret
    | rueckScopedGrundDirekt ρ r grund R hhead hret =>
      rcases GRest.scopedGrund_faelle hret with hr | ⟨rest, hr⟩ | ⟨Λ', rest, k, hr⟩ <;>
        subst r <;> (have hhead := hhead; kopfweg)
    | rueckFreigabe ρ a L remaining hhead =>
      rw [hR] at hhead
      cases hhead
      cases hcov
    | rueckFreigabeLetzte ρ a L hhead z hantwort =>
      rw [hR] at hhead
      cases hhead
      cases hcov

end Gabbro.Grammatik
