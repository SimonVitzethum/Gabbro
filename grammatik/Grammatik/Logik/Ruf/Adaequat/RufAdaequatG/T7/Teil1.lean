module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T6

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

theorem grundWahlG_ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    arms.ohneOrakel = true → (grundWahlG arms r).ohneOrakel = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => by
      simp only [GrundArms.ohneOrakel, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => by
      simp only [GrundArms.ohneOrakel, Bool.and_eq_true] at h
      exact grundWahlG_ohneOrakel rest _ h.2

/-! ## 14. The sequential semantics does not see the trace (oracle-free) -/

/-- Two worlds with the same shared memory (traces may differ). -/
def SG (σ σ' : World D) : Prop := σ.slots = σ'.slots ∧ σ.globs = σ'.globs

theorem SG.speicher {σ σ' : World D} (h : SG σ σ') : σ.speicher = σ'.speicher := by
  unfold World.speicher
  rw [h.1, h.2]

theorem SG.lese {σ σ' : World D} (h : SG σ σ') (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) : SG (σ.lese Λ os) (σ'.lese Λ os) := h

theorem SG.nimmt {σ σ' : World D} (h : SG σ σ') (L : D.Lock) : SG (σ.nimmt L) (σ'.nimmt L) := h

theorem SG.gibt {σ σ' : World D} (h : SG σ σ') (L : D.Lock) : SG (σ.gibt L) (σ'.gibt L) := h

/-- Releasing the same scope list on both sides keeps `SG`. -/
theorem SG.gibt_foldl : ∀ (Ls : List D.Lock) (σ σ' : World D),
    SG σ σ' → SG (Ls.foldl World.gibt σ) (Ls.foldl World.gibt σ')
  | [], _, _, h => h
  | _ :: Ls, σ, σ', h => SG.gibt_foldl Ls _ _ (h.gibt _)

theorem SG.schreibSlot {σ σ' : World D} (h : SG σ σ') (t : D.Tab) (Λ : List (Res D))
    (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    SG (σ.schreibSlot t Λ k f v) (σ'.schreibSlot t Λ k f v) := by
  refine ⟨?_, h.2⟩
  show (σ.storeSlot t k f v).slots = (σ'.storeSlot t k f v).slots
  simp only [World.storeSlot]
  rw [h.1]

theorem SG.schreibGlob {σ σ' : World D} (h : SG σ σ') (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) : SG (σ.schreibGlob g Λ v) (σ'.schreibGlob g Λ v) := by
  refine ⟨h.1, ?_⟩
  show (σ.storeGlob g v).globs = (σ'.storeGlob g v).globs
  simp only [World.storeGlob]
  rw [h.2]

theorem SG.putBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) : ∀ (bs : List Byte) (σ σ' : World D) (k : Int), SG σ σ' →
    SG (σ.schreibBytes t f hf Λ k bs) (σ'.schreibBytes t f hf Λ k bs)
  | [], _, _, _, h => h
  | _ :: bs, _, _, k, h =>
      SG.putBytes t f hf Λ bs _ _ (k + 1) (h.schreibSlot t Λ k f _)

theorem SG.eval {σ σ' : World D} (h : SG σ σ') {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (ρ : Env D Γ) : eval σ e σ ρ = eval σ' e σ' ρ :=
  eval_liest_nur_speicher_diag e σ σ' ρ (fun t k f => by rw [h.1]) (fun g => by rw [h.2])

theorem SG.evalErg {σ σ' : World D} (h : SG σ σ') {Γ : Ctx} {Λ : List (Res D)}
    {e : Option Ty} (x : ErgExpr D Γ Λ e) (ρ : Env D Γ) :
    evalErg σ x σ ρ = evalErg σ' x σ' ρ := by
  cases x with
  | empty => rfl
  | val e => exact h.eval e ρ

/-- Outcomes that agree up to the trace: same kind, same memory, same
    environment or value; every other kind agrees on the kind only. -/
def AusSG {V : Vertrag D} {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Ausgang V l Γ → Prop
  | .ok σ ρ, .ok σ' ρ' => SG σ σ' ∧ ρ = ρ'
  | .zurueck σ v, .zurueck σ' v' => SG σ σ' ∧ v = v'
  | .ok .., _ => False
  | _, .ok .. => False
  | .zurueck .., _ => False
  | _, .zurueck .. => False
  | _, _ => True

def EndSG {V : Vertrag D} {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → EndAusgang V l Γ → Prop
  | .zurueck σ v, .zurueck σ' v' => SG σ σ' ∧ v = v'
  | .zurueck .., _ => False
  | _, .zurueck .. => False
  | _, _ => True

section AusSGLemmas

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- Continuing after a statement preserves agreement. -/
theorem AusSG.widen {o o' : Ausgang V l Γ} (h : AusSG o o')
    (g g' : World D → Env D Γ → Ausgang V l Γ)
    (hg : ∀ σ σ' ρ, SG σ σ' → AusSG (g σ ρ) (g' σ' ρ)) :
    AusSG (match o with | .ok σ ρ => g σ ρ | o => o)
      (match o' with | .ok σ ρ => g' σ ρ | o => o) := by
  cases o with
  | ok σ ρ =>
    cases o' with
    | ok σ' ρ' =>
      obtain ⟨hs, rfl⟩ := h
      exact hg σ σ' ρ hs
    | _ => exact False.elim h
  | _ =>
    cases o' with
    | ok => exact False.elim h
    | _ => exact h

theorem AusSG.schrumpf {τ : Ty} {o o' : Ausgang V l (τ :: Γ)} (h : AusSG o o') :
    AusSG o.schrumpf o'.schrumpf := by
  cases o <;> cases o' <;> simp_all [AusSG, Ausgang.schrumpf]

theorem AusSG.schrumpfArm (c : Option Ty) {o o' : Ausgang V l (ArmCtx Γ c)}
    (h : AusSG o o') : AusSG (o.schrumpfArm c) (o'.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some p => exact AusSG.schrumpf h

theorem AusSG.gibt {o o' : Ausgang V l Γ} (h : AusSG o o') (L : D.Lock) :
    AusSG (o.mapWelt (·.gibt L)) (o'.mapWelt (·.gibt L)) := by
  cases o <;> cases o' <;> simp_all [AusSG, Ausgang.mapWelt, SG, World.gibt]

theorem EndSG.zuAusgang {o o' : EndAusgang V l Γ} (h : EndSG o o') :
    AusSG o.zuAusgang o'.zuAusgang := by
  cases o <;> cases o' <;> simp_all [AusSG, EndSG, EndAusgang.zuAusgang]

theorem EndSG.schrumpf {τ : Ty} {o o' : EndAusgang V l (τ :: Γ)} (h : EndSG o o') :
    EndSG o.schrumpf o'.schrumpf := by
  cases o <;> cases o' <;> simp_all [EndSG, EndAusgang.schrumpf]

/-- `execEnd` of `s; rest` from agreeing statement outcomes. -/
theorem EndSG.widen {o o' : Ausgang V l Γ} (h : AusSG o o')
    (g g' : World D → Env D Γ → EndAusgang V l Γ)
    (hg : ∀ σ σ' ρ, SG σ σ' → EndSG (g σ ρ) (g' σ' ρ)) :
    EndSG (match o with
        | .ok σ' ρ' => g σ' ρ'
        | .zurueck σ' v => .zurueck σ' v
        | .why σ' r => .why σ' r
        | .leave h σ' ρ' => .leave h σ' ρ'
        | .next h σ' ρ' => .next h σ' ρ'
        | .logik e => .logik e
        | .hardware e => .hardware e)
      (match o' with
        | .ok σ' ρ' => g' σ' ρ'
        | .zurueck σ' v => .zurueck σ' v
        | .why σ' r => .why σ' r
        | .leave h σ' ρ' => .leave h σ' ρ'
        | .next h σ' ρ' => .next h σ' ρ'
        | .logik e => .logik e
        | .hardware e => .hardware e) := by
  cases o with
  | ok σ ρ =>
    cases o' with
    | ok σ' ρ' =>
      obtain ⟨hs, rfl⟩ := h
      exact hg σ σ' ρ hs
    | _ => exact False.elim h
  | zurueck σ v =>
    cases o' with
    | zurueck σ' v' => exact h
    | _ => exact False.elim h
  | _ =>
    cases o' with
    | ok => exact False.elim h
    | zurueck => exact False.elim h
    | _ => trivial

end AusSGLemmas
/-- The `narrow` step of `execBlock` with the narrowed value abstracted
    (the `dite` carries proofs about it, so it cannot be rewritten in place). -/
def narrowWeiter (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {lo hi lo' hi' : Int}
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (sonst : Endblock D V l Γ Λ)
    (ρ : Env D Γ) (v : Zahl lo hi) (σ₁ : World D) : Ausgang V l Γ :=
  if h : lo' ≤ v.n ∧ v.n ≤ hi' then
    (execBlock O passes keinRuf rest σ₁ (.cons (τ := .int lo' hi') ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
  else (execEnd O passes keinRuf sonst σ₁ ρ).zuAusgang

theorem execBlock_narrow (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes keinRuf (.narrow e lo' hi' sonst rest) σ ρ =
      narrowWeiter O passes rest sonst ρ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)
        (σ.lese Λ e.orte) := by rfl

section Spur

variable (O : Orakel D) (passes : Nat) {V : Vertrag D} (A : D.Lock → Prop)

/-- A block's outcome agrees, up to the trace, from worlds with one memory. -/
def SGB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
    AusSG (execBlock O passes keinRuf b σ ρ) (execBlock O passes keinRuf b σ' ρ)

end Spur
end Gabbro.Grammatik
