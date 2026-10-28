/- Part 7 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T6

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

theorem AusSG.schrumpfArm (c : Option (Int × Int)) {o o' : Ausgang V l (ArmCtx Γ c)}
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
        (σ.lese Λ e.orte) := rfl

section Spur

variable (O : Orakel D) (passes : Nat) {V : Vertrag D} (A : D.Lock → Prop)

/-- A block's outcome agrees, up to the trace, from worlds with one memory. -/
def SGB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
    AusSG (execBlock O passes keinRuf b σ ρ) (execBlock O passes keinRuf b σ' ρ)

set_option maxHeartbeats 800000 in
mutual

theorem stmtSG : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), StmtG A mr s → s.ohneOrakel = true →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      AusSG (execStmt O passes keinRuf s σ ρ) (execStmt O passes keinRuf s σ' ρ)
  | _, _, _, Λ₀, _, .assignSlot t f' i e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (i.orte ++ e.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.eval e]
      exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
  | _, _, _, Λ₀, _, .assignThru p t ht f' i e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (p.orte ++ i.orte ++ e.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.eval e]
      exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
  | _, _, _, Λ₀, _, .assignSlotRef r t ht ho f' e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (r.orte ++ e.orte)
      simp only [execStmt]
      rw [h1.eval r, h1.eval e]
      exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
  | _, _, _, Λ₀, _, .assignGlob g e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      rw [h1.eval e]
      exact ⟨h1.schreibGlob _ _ _, rfl⟩
  | _, _, _, Λ₀, _, .putBytes t f' hf n i hlo hhi e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (i.orte ++ e.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.eval e]
      exact ⟨SG.putBytes _ _ _ _ _ _ _ _ h1, rfl⟩
  | _, _, _, Λ₀, _, .assignVar x e, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      rw [h1.eval e]
      exact ⟨h1, rfl⟩
  | _, _, _, Λ₀, _, .shift t f' hτ i von nach hn he hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (.inl t :: i.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.1]
      split
      · exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
      · trivial
  | _, _, _, _, _, .regWrite r hk e, _, _ => by
      intro σ σ' ρ h
      simp only [execStmt]
      exact ⟨h.lese _ _, rfl⟩
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _, _ => by
      intro σ σ' ρ h
      simp only [execStmt]
      exact ⟨h, rfl⟩
  | _, _, _, Λ₀, _, .publish g e payload hp hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      rw [h1.eval e]
      exact ⟨h1.schreibGlob _ _ _, rfl⟩
  | _, _, _, _, _, .advances m a h hs, _, _ => by
      intro σ σ' ρ h'
      simp only [execStmt]
      exact ⟨h', rfl⟩
  | _, _, _, _, _, .retires m s h a, _, _ => by
      intro σ σ' ρ h'
      simp only [execStmt]
      exact ⟨h', rfl⟩
  | _, _, _, Λ₀, _, .ite c t e, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨ht, he⟩ := hs.ite_inv
      simp only [Stmt.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ c.orte
      simp only [execStmt]
      rw [h1.eval c]
      split
      · exact blockSG t ht ho.1 _ _ _ h1
      · exact blockSG e he ho.2 _ _ _ h1
  | _, _, _, Λ₀, _, .onOption o p a, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      simp only [Stmt.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ o.orte
      simp only [execStmt]
      rw [h1.eval o]
      split
      · exact AusSG.schrumpf (blockSG p hp ho.1 _ _ _ h1)
      · exact blockSG a ha ho.2 _ _ _ h1
  | _, _, _, Λ₀, _, .onTag w arms, hs, ho => by
      intro σ σ' ρ h
      have ha := hs.onTag_inv
      simp only [Stmt.ohneOrakel] at ho
      have h1 := h.lese Λ₀ w.orte
      simp only [execStmt]
      rw [execArms_wahl, execArms_wahl, h1.eval w]
      exact AusSG.schrumpfArm _ (armsSG arms ha ho _ _ _ _ h1)
  | _, _, _, Λ₀, _, .onWhy r arms, hs, ho => by
      intro σ σ' ρ h
      have ha := hs.onGrund_inv
      simp only [Stmt.ohneOrakel] at ho
      have h1 := h.lese Λ₀ r.orte
      simp only [execStmt]
      rw [execGrund_wahlW O passes keinRuf arms, execGrund_wahlW O passes keinRuf arms,
        h1.eval r]
      exact grundSG arms ha ho _ _ _ _ h1
  | _, _, _, _, _, .call .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .callInd .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .locks L hr body, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hb⟩ := hs.locks_inv
      simp only [Stmt.ohneOrakel] at ho
      simp only [execStmt]
      exact AusSG.gibt (blockSG body hb ho _ _ _ (h.nimmt L)) L
  | _, _, _, _, _, .breaking i body, hs, ho => by
      intro σ σ' ρ h
      have hb := hs.breaking_inv
      simp only [Stmt.ohneOrakel] at ho
      simp only [execStmt]
      exact blockSG body hb ho _ _ _ h
  | _, _, _, _, _, .traverse .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retry .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .forever .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .axiomCall .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, Λ₀, _, .ret e hperm, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      exact ⟨h1, h1.evalErg e ρ⟩
  | _, _, _, _, _, .retWhy .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .leave .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .next .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])

theorem blockSG : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), BlockG A mr b → b.ohneOrakel = true → SGB O passes b
  | _, _, _, _, _, .nil, _, _ => by
      intro σ σ' ρ h
      exact ⟨h, rfl⟩
  | _, _, _, _, _, .cons s rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨hs, hr⟩ := hb.cons_inv
      simp only [Block.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := stmtSG s hs ho.1 _ _ ρ h
      simp only [execBlock]
      generalize execStmt O passes keinRuf s σ ρ = o at h1 ⊢
      generalize execStmt O passes keinRuf s σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | (obtain ⟨hs1, rfl⟩ := h1; exact blockSG rest hr ho.2 _ _ _ hs1)
  | _, _, _, Λ₀, _, .bind e rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.bind_inv
      simp only [Block.ohneOrakel] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      exact AusSG.schrumpf (blockSG rest hr ho _ _ _ h1)
  | _, _, _, _, _, .bindCall .., hb, _ => by cases hb
  | _, _, _, _, _, .bindCallInd .., hb, _ => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb, _ => by cases hb
  | _, _, _, _, _, .bindAxiom .., hb, _ => by cases hb
  | _, _, _, _, _, .bindAxiomElse .., hb, _ => by cases hb
  | _, _, _, _, _, .regRead .., _, ho => by simp only [Block.ohneOrakel, Bool.false_eq_true] at ho
  | _, _, _, _, _, .regReadElse .., _, ho => by simp only [Block.ohneOrakel, Bool.false_eq_true] at ho
  | _, _, _, _, _, .awaits .., _, ho => by simp only [Block.ohneOrakel, Bool.false_eq_true] at ho
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.exchange_inv
      simp only [Block.ohneOrakel] at ho
      have h1 := h.lese Λ₀ (.inr g :: neuE.orte)
      simp only [execBlock]
      have hg : (σ.lese Λ₀ (.inr g :: neuE.orte)).globs g =
          (σ'.lese Λ₀ (.inr g :: neuE.orte)).globs g := by rw [h1.2]
      rw [hg, h1.eval neuE]
      exact AusSG.schrumpf (blockSG rest hr ho _ _ _ (h1.schreibGlob _ _ _))
  | _, _, _, Λ₀, _, .narrow e lo' hi' sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
      simp only [Block.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ e.orte
      rw [execBlock_narrow, execBlock_narrow, h1.eval e]
      unfold narrowWeiter
      split
      · exact AusSG.schrumpf (blockSG rest hr ho.2 _ _ _ h1)
      · exact EndSG.zuAusgang (endSG sonst hs ho.1 _ _ _ h1)
  | _, _, _, Λ₀, _, .check c sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
      simp only [Block.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ c.orte
      simp only [execBlock]
      rw [h1.eval c]
      split
      · exact blockSG rest hr ho.2 _ _ _ h1
      · exact EndSG.zuAusgang (endSG sonst hs ho.1 _ _ _ h1)
  | _, _, _, Λ₀, _, .float op a b lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleit_inv
      simp only [Block.ohneOrakel] at ho
      have h1 := h.lese Λ₀ (a.orte ++ b.orte)
      simp only [execBlock]
      rw [h1.eval a, h1.eval b]
      split
      · exact AusSG.schrumpf (blockSG rest hr ho _ _ _ h1)
      · trivial
  | _, _, _, _, _, .floatLit q lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleitLit_inv
      simp only [Block.ohneOrakel] at ho
      simp only [execBlock]
      split
      · exact AusSG.schrumpf (blockSG rest hr ho _ _ _ h)
      · trivial
  | _, _, _, Λ₀, _, .floatOf e lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleitVon_inv
      simp only [Block.ohneOrakel] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      split
      · exact AusSG.schrumpf (blockSG rest hr ho _ _ _ h1)
      · trivial
  | _, _, _, Λ₀, _, .floatNarrow e lo hi sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
      simp only [Block.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      split
      · exact AusSG.schrumpf (blockSG rest hr ho.2 _ _ _ h1)
      · exact EndSG.zuAusgang (endSG sonst hs ho.1 _ _ _ h1)

theorem endSG : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), EndG A e → e.ohneOrakel = true →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      EndSG (execEnd O passes keinRuf e σ ρ) (execEnd O passes keinRuf e σ' ρ)
  | _, _, Λ₀, .ret e hperm, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execEnd]
      exact ⟨h1, h1.evalErg e ρ⟩
  | _, _, _, .retWhy .., he, _ => by cases he
  | _, _, _, .leave .., he, _ => by cases he
  | _, _, _, .next .., he, _ => by cases he
  | _, _, _, .cons s rest, he, ho => by
      intro σ σ' ρ h
      obtain ⟨hs, hr, _⟩ := he.cons_inv
      simp only [Endblock.ohneOrakel, Bool.and_eq_true] at ho
      have h1 := stmtSG s hs ho.1 _ _ ρ h
      simp only [execEnd]
      generalize execStmt O passes keinRuf s σ ρ = o at h1 ⊢
      generalize execStmt O passes keinRuf s σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | trivial
        | (obtain ⟨hs1, rfl⟩ := h1; exact endSG rest hr ho.2 _ _ _ hs1)
  | _, _, Λ₀, .bind e rest, he, ho => by
      intro σ σ' ρ h
      have hr := he.bind_inv
      simp only [Endblock.ohneOrakel] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execEnd]
      rw [h1.eval e]
      exact EndSG.schrumpf (endSG rest hr ho _ _ _ h1)

theorem armsSG : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    ArmsG A mr arms → arms.ohneOrakel = true → ∀ (v : Wert D (.sum cs)),
    SGB O passes (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ho, ⟨⟨0, _⟩, _⟩ => by
      simp only [Arms.ohneOrakel, Bool.and_eq_true] at ho
      exact blockSG b ha.cons_inv.1 ho.1
  | _, _, _, _, _, _, .cons _ rest, ha, ho, ⟨⟨_ + 1, _⟩, _⟩ => by
      simp only [Arms.ohneOrakel, Bool.and_eq_true] at ho
      exact armsSG rest ha.cons_inv.2 ho.2 _

theorem grundSG : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsG A mr arms → arms.ohneOrakel = true →
    ∀ (r : Fin n), SGB O passes (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ho, ⟨0, _⟩ => by
      simp only [GrundArms.ohneOrakel, Bool.and_eq_true] at ho
      exact blockSG b ha.cons_inv.1 ho.1
  | _, _, _, _, _, _, .cons _ rest, ha, ho, ⟨_ + 1, _⟩ => by
      simp only [GrundArms.ohneOrakel, Bool.and_eq_true] at ho
      exact grundSG rest ha.cons_inv.2 ho.2 _

end

end Spur
/-! ## 15. What a residue still returns: the frame semantics `semR`

    `semR k σ ρ` runs the residue `k` sequentially: an end block by
    `execEnd`, a `dann b k` by `execBlock b` and then `k`, a `schrumpf` by
    dropping the innermost binding, a `frei L` by the `gibt L` of its
    `locks`. Only a return counts (`REnde.zurueck`); every other outcome is
    `sonst`. Loop shims and `wartet` are outside the fragment (`sonst`). -/

inductive REnde (V : Vertrag D) where
  | zurueck (σ : World D) (v : ErgVal D V.erg)
  | sonst

/-- Agreement of frame results up to the trace. -/
def REnde.gleich {V : Vertrag D} : REnde V → REnde V → Prop
  | .zurueck σ v, .zurueck σ' v' => SG σ σ' ∧ v = v'
  | .sonst, .sonst => True
  | _, _ => False


end Gabbro.Grammatik
