/-
  File:      Grammatik/ArenaErkZeugeSchleife.lean
  Subject:   THE RECOGNIZER'S LOOP RULES ON A REAL ARENA (PLAN-DYNAMIC.md section 8a.1, third pass): loop bodies it
             ACCEPTS and RUNS, and a planted defect it REJECTS, on the concrete four-slot arena of `ArenaDynZeuge.lean`
             (slot `1` on the free list, list `2 -> 0`), declared as an arena with a list (`KL`).

  Accepted (witnesses, run from the real world `w0`):
    * `drain`        -- `retry` whose body pops the head and releases it: after two passes the list is empty, the third
                        pass finds the `else` of the pop and returns; the free list is `0 -> 2 -> 1`;
    * `drainForever` -- the same body under `forever`: it ends the same way;
    * `fuell`        -- `traverse` over every slot of the table with a payload store: it falls off, every payload is `7`.
  Rejected (planted defect):
    * `schiebeSchleife` -- a slot taken off the free list and linked in AGAIN on every pass of a `retry`: the second pass
                        links a member (a self loop), so no derivation can exist -- through the soundness theorem and a
                        real run (and by the loop rule itself: the state of the slot is not an invariant of the body).

  The runs are evaluated by the kernel (`decide +kernel`); the invariant of the world a run ends in is the recognizer's
  promise (`erk_koerper`).
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkennerZeuge

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace InvDynZeuge

/-- The `else` branches of the loop bodies below: they return, and store nothing. -/
def vollT : Endblock FD FV true [] [] := Endblock.ret ErgExpr.empty (List.Perm.refl _)

theorem rein_vollT : Rein vollT := Rein.ret _ _

/-! ### Accepted: draining the list -/

/-- Pop the head and release it. -/
def drainKoerper : Block FD FV true [] [] [] :=
  Block.linkPop LL LG rfl (fgdarf _) fdarf vollT
    (Block.freiVar FA (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil)

/-- The body keeps the loop state `leer` (nothing known). -/
theorem erk_drainKoerper : ∃ a1 : Abs, Erk KL Abs.leer drainKoerper a1 :=
  ⟨_, Erk.pop ⟨LL, LG⟩ rfl rfl (fgdarf _) fdarf vollT _ rein_vollT
    (Erk.frei (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil (by simp only [Abs.ext, Var.pos])
      (Erk.nil _))⟩

/-- Up to four passes of the body. -/
def drain : Block FD FV false [] [] [] :=
  Block.cons (Stmt.retry 4 Expr.fls drainKoerper Block.nil) Block.nil

/-- **The recognizer accepts the loop** -- from a state that knows nothing. -/
theorem erk_drain : ∃ a' : Abs, Erk KL Abs.leer drain a' := by
  obtain ⟨a1, hb⟩ := erk_drainKoerper
  exact ⟨_, Erk.retry (k0 := Abs.leer) (a1 := a1) (au := Abs.leer) (a3 := Abs.leer) 4 Expr.fls drainKoerper
    Block.nil Block.nil (fun _ => Or.inl rfl) hb (fun _ => Or.inr rfl) (Erk.nil _) (fun _ => Or.inl rfl)
    (fun _ => Or.inl rfl) (Erk.nil _)⟩

/-- The outcome of the run, as a decidable fact: it returns in a world with the empty list and the head `0` of the
    free list. -/
def drainOk : Bool :=
  match execBlock (V := FV) oF 0 rF drain w0 .nil with
  | .zurueck σ' _ => decide (LG.st σ' = 4 ∧ FA.kopfSt σ' = 0 ∧ FA.naechst σ' 0 = 2 ∧ FA.naechst σ' 2 = 1)
  | _ => false

theorem drainOk_wahr : drainOk = true := by decide +kernel

/-- **Run on the real world:** the loop pops `2`, releases it, pops `0`, releases it, and returns at the empty list; the
    invariant holds there, as the recognizer promised. -/
theorem drain_zeuge : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF drain w0 .nil = .zurueck σ' () ∧ KL.Ok σ' ∧
    LG.st σ' = 4 ∧ FA.kopfSt σ' = 0 ∧ FA.naechst σ' 0 = 2 ∧ FA.naechst σ' 2 = 1 := by
  obtain ⟨a', h⟩ := erk_drain
  have hd := drainOk_wahr
  unfold drainOk at hd
  revert hd
  generalize hx : execBlock (V := FV) oF 0 rF drain w0 .nil = o
  have hpost := erk_koerper_lauf oF 0 rF KL h w0 .nil ok_w0 hx
  cases o with
  | zurueck σ' v =>
    intro hd
    have hv : v = () := rfl
    subst hv
    simp only [decide_eq_true_eq] at hd
    exact ⟨σ', rfl, hpost, hd⟩
  | ok _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | why _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | leave _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | next _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | logik _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | hardware _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])

/-! ### Accepted: the same body under `forever` -/

def drainForever : Block FD FV false [] [] [] :=
  Block.cons (Stmt.forever () Expr.tru drainKoerper) Block.nil

theorem erk_drainForever : ∃ a' : Abs, Erk KL Abs.leer drainForever a' := by
  obtain ⟨a1, hb⟩ := erk_drainKoerper
  exact ⟨_, Erk.forever (K := KL) (V := FV) (l := false) (Γ := []) (Λ := []) (Λ' := []) (a := Abs.leer)
    (a' := Abs.leer) (k0 := Abs.leer) (a1 := a1) (() : FD.Annahme) Expr.tru drainKoerper Block.nil (fun _ => Or.inl rfl) hb
    (fun _ => Or.inr rfl) (Erk.nil _)⟩

def drainForeverOk : Bool :=
  match execBlock (V := FV) oF 10 rF drainForever w0 .nil with
  | .zurueck σ' _ => decide (LG.st σ' = 4 ∧ FA.kopfSt σ' = 0)
  | _ => false

theorem drainForeverOk_wahr : drainForeverOk = true := by decide +kernel

/-- **Run on the real world** (ten passes are given): the loop ends at the empty list with a return. -/
theorem drainForever_zeuge : ∃ σ' : World FD, execBlock (V := FV) oF 10 rF drainForever w0 .nil = .zurueck σ' () ∧
    KL.Ok σ' ∧ LG.st σ' = 4 ∧ FA.kopfSt σ' = 0 := by
  obtain ⟨a', h⟩ := erk_drainForever
  have hd := drainForeverOk_wahr
  unfold drainForeverOk at hd
  revert hd
  generalize hx : execBlock (V := FV) oF 10 rF drainForever w0 .nil = o
  have hpost := erk_koerper_lauf oF 10 rF KL h w0 .nil ok_w0 hx
  cases o with
  | zurueck σ' v =>
    intro hd
    have hv : v = () := rfl
    subst hv
    simp only [decide_eq_true_eq] at hd
    exact ⟨σ', rfl, hpost, hd⟩
  | ok _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | why _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | leave _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | next _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | logik _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | hardware _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])

/-! ### Accepted: `traverse` with a payload store -/

/-- The payload of slot `k`, as a number. -/
def nutz (σ : World FD) (k : Int) : Int :=
  (Wert.umTyp (show FD.typ FA.tab FA.feld = Ty.int 0 255 from by decide) (σ.slots FA.tab k FA.feld)).n

/-- Store `7` into the payload of every slot. -/
def fuellKoerper : Block FD FV true G1 [] [] :=
  Block.cons (Stmt.assignSlot FA.tab FA.feld (Expr.var (.here : Var G1 _)) (Expr.weaken sieben) rfl fdarf)
    Block.nil

def fuell : Block FD FV false [] [] [] :=
  Block.cons (Stmt.traverse () Expr.tru fuellKoerper) Block.nil

theorem erk_fuell : ∃ a' : Abs, Erk KL Abs.leer fuell a' := by
  have hb : Erk KL (Abs.leer.ext .offen) fuellKoerper (Abs.leer.ext .offen) :=
    Erk.nutzlast (Expr.var (.here : Var G1 _)) (Expr.weaken sieben) rfl fdarf _ (Erk.nil _)
  exact ⟨_, Erk.traverse (K := KL) (V := FV) (l := false) (Γ := []) (Λ := []) (Λ' := []) (a := Abs.leer)
    (a' := Abs.leer) (k0 := Abs.leer) (a1 := Abs.leer.ext .offen) (() : FD.Tab) Expr.tru fuellKoerper Block.nil
    (fun _ => Or.inl rfl) hb (fun _ => Or.inl rfl) (Erk.nil _)⟩

def fuellOk : Bool :=
  match execBlock (V := FV) oF 0 rF fuell w0 .nil with
  | .ok σ' _ => decide (nutz σ' 0 = 7 ∧ nutz σ' 3 = 7 ∧ LG.st σ' = 2 ∧ FA.kopfSt σ' = 1)
  | _ => false

theorem fuellOk_wahr : fuellOk = true := by decide +kernel

/-- **Run on the real world:** every slot has the payload `7`, and the list, the head and the free list are as before. -/
theorem fuell_zeuge : ∃ σ' : World FD, execBlock (V := FV) oF 0 rF fuell w0 .nil = .ok σ' .nil ∧ KL.Ok σ' ∧
    nutz σ' 0 = 7 ∧ nutz σ' 3 = 7 ∧ LG.st σ' = 2 ∧ FA.kopfSt σ' = 1 := by
  obtain ⟨a', h⟩ := erk_fuell
  have hd := fuellOk_wahr
  unfold fuellOk at hd
  revert hd
  generalize hx : execBlock (V := FV) oF 0 rF fuell w0 .nil = o
  have hpost := erk_koerper_lauf oF 0 rF KL h w0 .nil ok_w0 hx
  cases o with
  | ok σ' ρ =>
    intro hd
    cases ρ
    simp only [decide_eq_true_eq] at hd
    exact ⟨σ', rfl, hpost.1, hd⟩
  | zurueck _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | why _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | leave _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | next _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | logik _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | hardware _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])

/-! ### Planted defect: a slot linked in again on every pass -/

/-- Link the owned slot in. -/
def schiebeKoerper : Block FD FV true G1 [] [] :=
  Block.linkPush LL LG (.here : Var G1 _) rfl fdarf rfl (fgdarf _) .nil

/-- Take slot `1` off the free list, then link it in on every pass of a `retry`. -/
def schiebeSchleife : Block FD FV false [] [] [] :=
  Block.freiNimm FA sieben rfl fdarf rfl (fgdarf _) voll0
    (Block.cons (Stmt.retry 4 Expr.fls schiebeKoerper Block.nil) Block.nil)

def schiebeOk : Bool :=
  match execBlock (V := FV) oF 0 rF schiebeSchleife w0 .nil with
  | .ok σ' _ => decide (LG.st σ' = 1 ∧ LL.wert σ' 1 = 1)
  | _ => false

theorem schiebeOk_wahr : schiebeOk = true := by decide +kernel

/-- **No derivation:** the run links slot `1` in on the first pass and AGAIN on the second, so the slot is linked into
    itself and no list exists -- the invariant the derivation would have promised is broken. By the loop rule itself the
    state of the slot is no loop invariant: the push makes it a member, and `Abs.Schwacher` allows no change of status. -/
theorem schiebeSchleife_abgelehnt (a' : Abs) : ¬ Erk KL Abs.leer schiebeSchleife a' := by
  intro h
  have hd := schiebeOk_wahr
  unfold schiebeOk at hd
  revert hd
  generalize hx : execBlock (V := FV) oF 0 rF schiebeSchleife w0 .nil = o
  have hpost := erk_koerper_lauf oF 0 rF KL h w0 .nil ok_w0 hx
  cases o with
  | ok σ' ρ =>
    intro hd
    simp only [decide_eq_true_eq] at hd
    exact liste_schleife_bricht FA LL LG σ' 1 (by decide) hd.1 hd.2 (listOk_von hpost.1)
  | zurueck _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | why _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | leave _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | next _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | logik _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | hardware _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])

end InvDynZeuge

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.InvDynZeuge.erk_drain
#print axioms Gabbro.Grammatik.InvDynZeuge.drain_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.erk_drainForever
#print axioms Gabbro.Grammatik.InvDynZeuge.drainForever_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.erk_fuell
#print axioms Gabbro.Grammatik.InvDynZeuge.fuell_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.schiebeSchleife_abgelehnt
