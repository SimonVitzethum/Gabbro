import Grammatik.Bausteine.Arena.Ownership.Bodies

/-! An owned allocation returned by an actual G function. Both allocator
paths are covered and every request has an explicit failure continuation.
The provider's readiness expression belongs to source/user logic. -/

namespace Gabbro.Grammatik.ArenaOwnership

open ArenaDyn

variable {D : Deklaration}

def factoryContract (A : FreiForm D) (f : D.Fn)
    (he : D.erg f = some (Ty.index (D.count A.tab))) : Contract D f where
  requires := fun _ _ _ => True
  ensures := fun frame s _ s' answer =>
    match answer with
    | .value v => ∃ h, h.slot = (ergWert he v).n ∧ s.allocate frame h.slot = some (s', h)
    | .reason _ => s' = s

section Source

variable (A : FreiForm D) (f : D.Fn)
variable (he : D.erg f = some (Ty.index (D.count A.tab)))
variable (oom : Fin (D.gruende f))
variable (ready : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool)
variable (v : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) (D.typ A.tab A.feld))
variable (hwT : (vertragVon D f).schreibt A.tab = true)
variable (hLT : darf D A.tab (Signatur.anfang D (D.signatur f)))
variable (hwU : (vertragVon D f).gschreibt A.zaehl = true)
variable (hLU : gdarf D A.zaehl (Signatur.anfang D (D.signatur f)))
variable (hwF : (vertragVon D f).gschreibt A.kopf = true)
variable (hLF : gdarf D A.kopf (Signatur.anfang D (D.signatur f)))
variable (hLC : gdarf D A.komm (Signatur.anfang D (D.signatur f)))
variable (hend : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende)

def factoryFailure : Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)) :=
  .retWhy oom hend

def factoryReturn : Block D (vertragVon D f) false
    (Ty.index (D.count A.tab) :: D.params f) (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)) :=
  .cons (.ret (valueResult he (.var .here)) hend) .nil

def factoryHasFree : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool :=
  .lt (Expr.umTyp A.hkopf (.glob A.kopf hLF)) (.lit (D.count A.tab))

def factoryBlock : Block D (vertragVon D f) false (D.params f)
    (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)) :=
  .check ready (factoryFailure f oom hend)
    (.cons (.ite (factoryHasFree A f hLF)
      (Block.freiNimm A v hwT hLT hwF hLF (factoryFailure f oom hend) (factoryReturn A f he hend))
      (Block.dynAlloc A.toDynForm v hwT hLT hwU hLU hLC (factoryFailure f oom hend) (factoryReturn A f he hend))) .nil)

def factoryBody : Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)) :=
  .cons (.ite .tru (factoryBlock A f he oom ready v hwT hLT hwU hLU hwF hLF hLC hend) .nil)
    (factoryFailure f oom hend)

end Source

section Proof

variable (A : FreiForm D) (f : D.Fn)
variable (he : D.erg f = some (Ty.index (D.count A.tab)))
variable (oom : Fin (D.gruende f))
variable (ready : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool)
variable (v : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) (D.typ A.tab A.feld))
variable (hwT : (vertragVon D f).schreibt A.tab = true)
variable (hLT : darf D A.tab (Signatur.anfang D (D.signatur f)))
variable (hwU : (vertragVon D f).gschreibt A.zaehl = true)
variable (hLU : gdarf D A.zaehl (Signatur.anfang D (D.signatur f)))
variable (hwF : (vertragVon D f).gschreibt A.kopf = true)
variable (hLF : gdarf D A.kopf (Signatur.anfang D (D.signatur f)))
variable (hLC : gdarf D A.komm (Signatur.anfang D (D.signatur f)))
variable (hend : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende)
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g)
variable (frame : Frame) (s : State) (σ : World D) (ρ : Env D (D.params f))

theorem factory_return_post {σ' : World D} {s' : State} {h : Handle}
    (k : Wert D (Ty.index (D.count A.tab)))
    (ha : s'.agrees A σ') (hf : A.FreiOk σ')
    (hs : s.allocate frame k.n = some (s', h)) (hk : h.slot = k.n) :
    (factoryContract A f he).blockPost A frame s ρ
      (execBlock O passes R (factoryReturn A f he hend) σ' (.cons k ρ)).schrumpf := by
  apply Contract.blockPost_shrink
  refine ⟨s', State.agrees_reads ha _ _, free_invariant_reads hf _ _, h, ?_, ?_⟩
  · let result : ErgExpr D (Ty.index (D.count A.tab) :: D.params f)
        (Signatur.anfang D (D.signatur f)) (D.erg f) := valueResult he (.var .here)
    let sw := σ'.lese (Signatur.anfang D (D.signatur f)) result.orte
    change h.slot = (ergWert he (evalErg sw result sw (.cons k ρ))).n
    have hv := congrArg (fun w => w.n) (valueResult_eval (Λ := Signatur.anfang D (D.signatur f)) he (.var .here) sw sw (.cons k ρ))
    have hv' : (ergWert he (evalErg sw result sw (.cons k ρ))).n = k.n := by
      simpa only [eval, Env.get] using hv
    exact hk.trans hv'.symm
  · rw [hk]
    exact hs

theorem factory_block_checked (ha : s.agrees A σ) (hf : A.FreiOk σ) :
    (factoryContract A f he).blockPost A frame s ρ
      (execBlock O passes R (factoryBlock A f he oom ready v hwT hLT hwU hLU hwF hLF hLC hend) σ ρ) := by
  let Λ := Signatur.anfang D (D.signatur f)
  let σ1 := σ.lese Λ ready.orte
  have ha1 : s.agrees A σ1 := State.agrees_reads ha _ _
  have hf1 : A.FreiOk σ1 := free_invariant_reads hf _ _
  change (factoryContract A f he).blockPost A frame s ρ
    (if wahr? (eval σ1 ready σ1 ρ) then
      execBlock O passes R
        (.cons (.ite (factoryHasFree A f hLF)
          (Block.freiNimm A v hwT hLT hwF hLF (factoryFailure f oom hend) (factoryReturn A f he hend))
          (Block.dynAlloc A.toDynForm v hwT hLT hwU hLU hLC (factoryFailure f oom hend) (factoryReturn A f he hend))) .nil) σ1 ρ
    else (execEnd O passes R (factoryFailure f oom hend) σ1 ρ).zuAusgang)
  split
  · let test := factoryHasFree A f hLF
    let σ2 := σ1.lese Λ test.orte
    have ha2 : s.agrees A σ2 := State.agrees_reads ha1 _ _
    have hf2 : A.FreiOk σ2 := free_invariant_reads hf1 _ _
    have htest : wahr? (eval σ2 test σ2 ρ) = decide (A.kopfSt σ2 < D.count A.tab) := by
      simp only [test, factoryHasFree, eval, wahr?, eval_umTyp]
      rfl
    apply Contract.blockPost_ite
    rw [htest]
    split
    · rename_i hfree
      have hroom : A.kopfSt σ2 < D.count A.tab := of_decide_eq_true hfree
      obtain ⟨s', h, sw, k, hrun, hs, hslot, has, _, hfs, _⟩ := allocate_reuse_execution O passes R A s frame v
        hwT hLT hwF hLF (factoryFailure f oom hend) (factoryReturn A f he hend) σ2 ρ ha2 hf2 hroom
      rw [hrun]
      exact factory_return_post A f he hend O passes R frame s ρ k has hfs hs hslot
    · let guard := Block.dynUnterKomm (Γ := D.params f) A.toDynForm hLU hLC
      let σ3 := σ2.lese Λ guard.orte
      have ha3 : s.agrees A σ3 := State.agrees_reads ha2 _ _
      have hf3 : A.FreiOk σ3 := free_invariant_reads hf2 _ _
      have hguard : wahr? (eval σ3 guard σ3 ρ) = decide (A.stand σ3 < A.komSt σ3) := by
        simp only [guard, Block.dynUnterKomm, eval, wahr?, eval_umTyp]
        rfl
      change (factoryContract A f he).blockPost A frame s ρ
        (if wahr? (eval σ3 guard σ3 ρ) then
          execBlock O passes R
            (Block.arenaAlloc A.toArenaForm v hwT hLT hwU hLU (factoryFailure f oom hend) (factoryReturn A f he hend)) σ3 ρ
        else (execEnd O passes R (factoryFailure f oom hend) σ3 ρ).zuAusgang)
      rw [hguard]
      split
      · rename_i hcommitted
        have hlt : A.stand σ3 < A.komSt σ3 := of_decide_eq_true hcommitted
        have hroom : A.stand σ3 < D.count A.tab := by have := A.komSt_le σ3; omega
        obtain ⟨s', h, sw, k, hrun, hs, hslot, has, _, hfs, _⟩ := allocate_fresh_execution O passes R A s frame v
          hwT hLT hwU hLU (factoryFailure f oom hend) (factoryReturn A f he hend) σ3 ρ ha3 hf3 hroom
        rw [hrun]
        exact factory_return_post A f he hend O passes R frame s ρ k has hfs hs hslot
      · exact ⟨s, ha3, hf3, rfl⟩
  · exact ⟨s, ha1, hf1, rfl⟩

theorem factory_checked (ha : s.agrees A σ) (hf : A.FreiOk σ) :
    (factoryContract A f he).bodyPost A frame s ρ
      (execEnd O passes R (factoryBody A f he oom ready v hwT hLT hwU hLU hwF hLF hLC hend) σ ρ) := by
  have hp := factory_block_checked A f he oom ready v hwT hLT hwU hLU hwF hLF hLC hend O passes R frame s
    (σ.lese (Signatur.anfang D (D.signatur f)) []) ρ
    (State.agrees_reads ha _ _) (free_invariant_reads hf _ _)
  simp only [factoryBody, execEnd, execStmt, Expr.orte, eval, wahr?, ite_true]
  generalize ho : execBlock O passes R
    (factoryBlock A f he oom ready v hwT hLT hwU hLU hwF hLF hLC hend)
    (σ.lese (Signatur.anfang D (D.signatur f)) []) ρ = out at hp ⊢
  cases out <;> first | exact hp | exact False.elim hp

theorem factory_oom_path
    (hno : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) ready.orte) ready
      (σ.lese (Signatur.anfang D (D.signatur f)) ready.orte) ρ) = false) :
    execBlock O passes R (factoryBlock A f he oom ready v hwT hLT hwU hLU hwF hLF hLC hend) σ ρ =
      .why (σ.lese (Signatur.anfang D (D.signatur f)) ready.orte) oom := by
  change (if wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) ready.orte) ready
      (σ.lese (Signatur.anfang D (D.signatur f)) ready.orte) ρ) then _ else _) = _
  rw [hno]
  rfl

end Proof

#print axioms factory_checked
#print axioms factory_oom_path

end Gabbro.Grammatik.ArenaOwnership
