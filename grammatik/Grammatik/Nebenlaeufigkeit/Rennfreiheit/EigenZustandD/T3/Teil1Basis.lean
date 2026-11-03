module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T2
import all Init.Data.Repr
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

@[expose] public section



namespace Gabbro.Grammatik.EZD

open Gabbro.Grammatik
variable {D : Deklaration}

/-- `next` keeps every table slot (control step, memory-free). -/
theorem next_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {h : l = true}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.next (V := V) (l := l) h)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-! ## 6. Call leaves: `call`/`callInd` through `keinRuf` yield no world.

  The machine fires leaves through `execStmt O passes keinRuf`: the call
  handler is `keinRuf`, which answers every call with
  `.logik (.abstieg f)`. Hence a firing equation `hstep` for a `call` or
  `callInd` leaf reduces to `none = some σ'` -- vacuous. Both lemmas use
  every premise: `hs` to rewrite the statement, `hstep` to close. -/

/-- `call` through `keinRuf` yields no world: the slot goal is vacuous. -/
theorem call_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {fn : D.Fn} {args : Args D Γ Λ (D.params fn)}
    {hp : RufPasst D V (D.signatur fn) Λ} {hr : D.gruende fn = 0}
    (s : Stmt D V l Γ Λ (nach D fn Λ))
    (hs : s = Stmt.call (V := V) fn args hp hr)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  have hR : keinRuf (D := D) fn (sg.lese Λ args.orte)
      (evalArgs (sg.lese Λ args.orte) args (sg.lese Λ args.orte) rho) =
      RufAusgang.logik (.abstieg fn) := rfl
  simp only [execStmt] at hstep
  rw [hR] at hstep
  simp only [Ausgang.welt] at hstep
  exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

/-- `callInd` through `keinRuf` yields no world: the slot goal is vacuous. -/
theorem callInd_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
    {hp : RufPasst D V (D.sigNr n) Λ} {hr : (D.sigNr n).gruende = 0}
    (s : Stmt D V l Γ Λ (nachSig D (D.sigNr n) Λ))
    (hs : s = Stmt.callInd (V := V) p args hp hr)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt] at hstep
  revert hstep
  generalize hP : eval (sg.lese Λ (p.orte ++ args.orte)) p
      (sg.lese Λ (p.orte ++ args.orte)) rho = pv
  intro hstep
  cases pv with
  | mk fn hf =>
      simp only at hstep
      have hR : keinRuf (D := D) fn (sg.lese Λ (p.orte ++ args.orte))
          (umsig hf (evalArgs (sg.lese Λ (p.orte ++ args.orte)) args
            (sg.lese Λ (p.orte ++ args.orte)) rho)) =
          RufAusgang.logik (.abstieg fn) := rfl
      rw [hR] at hstep
      simp only [Ausgang.welt] at hstep
      exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

/-- `callIndElse` through `keinRuf` yields no world: the slot goal is vacuous. -/
theorem callIndElse_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
    {he : (D.sigNr n).erg = some τ} {hp : RufPasst D V (D.sigNr n) Λ} {hr : 0 < (D.sigNr n).gruende}
    {err : Endblock D V l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ)}
    (s : Stmt D V l Γ Λ (nachSig D (D.sigNr n) Λ))
    (hs : s = Stmt.callIndElse (V := V) p args he hp hr err)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, indSonst] at hstep
  revert hstep
  generalize hP : eval (sg.lese Λ (p.orte ++ args.orte)) p
      (sg.lese Λ (p.orte ++ args.orte)) rho = pv
  intro hstep
  cases pv with
  | mk fn hf =>
      simp only at hstep
      have hR : keinRuf (D := D) fn (sg.lese Λ (p.orte ++ args.orte))
          (umsig hf (evalArgs (sg.lese Λ (p.orte ++ args.orte)) args
            (sg.lese Λ (p.orte ++ args.orte)) rho)) =
          RufAusgang.logik (.abstieg fn) := rfl
      rw [hR] at hstep
      simp only [Ausgang.welt] at hstep
      exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

/-! ## 7. Other-table and degenerate arms: slots of `t` survive writes to `t₂ ≠ t`.

  Each lemma takes the firing equation for ONE constructor form with an
  explicit inequality hypothesis. All premises are used: `hstep` fixes the
  outcome, the inequality selects the `storeSlot_andere`/`schreibBytes_slots_other`
  leg. -/

/-- `assignSlot t₂` with `t₂ ≠ t` keeps every slot of `t`. -/
theorem assignSlot_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t₂ : D.Tab} {f₂ : D.Feld t₂}
    {i : Expr D Γ Λ (.index (D.count t₂))} {e : Expr D Γ Λ (D.typ t₂ f₂)}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignSlot (V := V) (l := l) t₂ f₂ i e hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt
      = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.assignSlot (V := V) (l := l) t₂ f₂ i e hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n f₂
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t₂ Λ
      (eval (σ.lese Λ (i.orte ++ e.orte)) i
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n f₂
      (eval (σ.lese Λ (i.orte ++ e.orte)) e
        (σ.lese Λ (i.orte ++ e.orte)) ρ)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  show ((σ.lese Λ (i.orte ++ e.orte)).storeSlot t₂ _ f₂ _).slots t k f =
    σ.slots t k f
  rw [storeSlot_andere _ _ _ _ _ _ hne]
  rfl

/-- `assignDurch t₂` with `t₂ ≠ t` keeps every slot of `t`. -/
theorem assignDurch_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} {read : Bool}
    {p : Expr D Γ Λ (.ptr (.table n (read, true) space))} {t₂ : D.Tab} {ht₂ : D.capTab space n = some t₂}
    {f₂ : D.Feld t₂}
    {i : Expr D Γ Λ (.index (D.count t₂))} {e : Expr D Γ Λ (D.typ t₂ f₂)}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignThru (V := V) (l := l) p t₂ ht₂ f₂ i e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.assignThru (V := V) (l := l) p t₂ ht₂ f₂ i e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f₂
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t₂ Λ
      (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
        (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f₂
      (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
        (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  show ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).storeSlot t₂ _ f₂ _).slots t k f =
    σ.slots t k f
  rw [storeSlot_andere _ _ _ _ _ _ hne]
  rfl

/-- `assignDurchOwn t₂` with `t₂ ≠ t` keeps every slot of `t`: the same
    underlying table access as `assignDurch`. -/
theorem assignDurchOwn_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} {read : Bool} {space o : Nat}
    {p : Expr D Γ Λ (.ptr ⟨space, ⟨read, true, some o⟩, .table n⟩)}
    {t₂ : D.Tab} {ht₂ : D.capTab space n = some t₂}
    {f₂ : D.Feld t₂}
    {i : Expr D Γ Λ (.index (D.count t₂))} {e : Expr D Γ Λ (D.typ t₂ f₂)}
    {m : D.Marke} {s : Nat} {ho : D.ownerNr o = some m} {he : m ∈ D.eigner t₂}
    {hg : Sum.inr (m, s) ∈ D.braucht t₂}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignThruOwn (V := V) (l := l) p t₂ ht₂ f₂ i e m s ho he hg hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.assignThruOwn (V := V) (l := l) p t₂ ht₂ f₂ i e m s ho he hg hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f₂
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t₂ Λ
      (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
        (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f₂
      (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
        (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  show ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).storeSlot t₂ _ f₂ _).slots t k f =
    σ.slots t k f
  rw [storeSlot_andere _ _ _ _ _ _ hne]
  rfl

/-- `assignSlotRef t₂` with `t₂ ≠ t` keeps every slot of `t`. -/
theorem assignSlotRef_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat}
    {r : Expr D Γ Λ (.ref n)} {t₂ : D.Tab} {ht₂ : D.tabNr n = some t₂} {ho : D.offen t₂ = true}
    {f₂ : D.Feld t₂}
    {e : Expr D Γ Λ (D.typ t₂ f₂)}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignSlotRef (V := V) (l := l) r t₂ ht₂ ho f₂ e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.assignSlotRef (V := V) (l := l) r t₂ ht₂ ho f₂ e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (r.orte ++ e.orte)).schreibSlot t₂ Λ
        ((eval (σ.lese Λ (r.orte ++ e.orte)) r
          (σ.lese Λ (r.orte ++ e.orte)) ρ).zelle : Int) f₂
        (eval (σ.lese Λ (r.orte ++ e.orte)) e
          (σ.lese Λ (r.orte ++ e.orte)) ρ)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (r.orte ++ e.orte)).schreibSlot t₂ Λ
      ((eval (σ.lese Λ (r.orte ++ e.orte)) r
        (σ.lese Λ (r.orte ++ e.orte)) ρ).zelle : Int) f₂
      (eval (σ.lese Λ (r.orte ++ e.orte)) e
        (σ.lese Λ (r.orte ++ e.orte)) ρ)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  show ((σ.lese Λ (r.orte ++ e.orte)).storeSlot t₂ _ f₂ _).slots t k f =
    σ.slots t k f
  rw [storeSlot_andere _ _ _ _ _ _ hne]
  rfl

end Gabbro.Grammatik.EZD
