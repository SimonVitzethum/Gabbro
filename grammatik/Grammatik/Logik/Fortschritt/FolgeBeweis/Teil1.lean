module

public import Grammatik.Logik.Fortschritt.Folge

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The check: monotone in the bit, stable under selection -/

section Hilfen

variable (Φ : Folge D) {V : Vertrag D}

theorem fNach_blatt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (w : Bool)
    (s : Stmt D V l Γ Λ Λ') (h : s.istBlatt = true) : fNach Φ w s = w := by
  cases s <;> simp_all [Stmt.istBlatt, fNach]

theorem fNach_entf {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (w : Bool)
    (s : Stmt D V l Γ Λ Λ') (h : GEntfaltbar s = true) : fNach Φ w s = false := by
  cases s <;> simp_all [GEntfaltbar, fNach]

theorem fS_mono {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (e w : Bool)
    (s : Stmt D V l Γ Λ Λ') (h : fS Φ e false s = true) : fS Φ e w s = true := by
  cases s <;> simp_all [fS]

theorem fNach_mono {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (w : Bool)
    (s : Stmt D V l Γ Λ Λ') (h : fNach Φ false s = true) : fNach Φ w s = true := by
  cases s <;> simp_all [fNach]

/-- The check of a block is monotone in the armed bit. -/
theorem fB_mono {l : Bool} {Γ : Ctx} :
    ∀ {Λ Λ' : List (Res D)} (e : Bool) (b : Block D V l Γ Λ Λ') (w w' : Bool),
      (w = true → w' = true) → fB Φ e w b = true → fB Φ e w' b = true
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, e, .cons s rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢
      refine ⟨?_, fB_mono e rest _ _ ?_ h.2⟩
      · cases s <;> simp_all [fS] <;> (cases w <;> cases w' <;> simp_all)
      · cases s <;> simp_all [fNach]
  | _, _, e, .bind _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .bindCall g _ _ _ _ rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
      exact ⟨h.1.imp id hw, h.2⟩
  | _, _, e, .bindCallInd _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
      exact ⟨h.1.imp id hw, h.2⟩
  | _, _, e, .bindCallElse g _ _ _ _ err rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
      exact ⟨⟨h.1.1.imp id hw, h.1.2⟩, h.2⟩
  | _, _, e, .bindAxiom _ _ _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .bindAxiomElse _ _ _ _ _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fB_mono e rest _ _ hw h.2⟩
  | _, _, e, .bindAxiomOpt _ _ _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .bindAxiomOptElse _ _ _ _ _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fB_mono e rest _ _ hw h.2⟩
  | _, _, e, .regRead _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .regReadElse _ _ _ sonst rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fB_mono e rest _ _ hw h.2⟩
  | _, _, e, .awaits _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .exchange _ _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .narrow _ _ _ sonst rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fB_mono e rest _ _ hw h.2⟩
  | _, _, e, .narrowRequired _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .check _ sonst rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fB_mono e rest _ _ hw h.2⟩
  | _, _, e, .float _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .floatLit _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .floatOf _ _ _ rest, w, w', hw, h => by
      simp only [fB] at h ⊢; exact fB_mono e rest _ _ hw h
  | _, _, e, .floatNarrow _ _ _ sonst rest, w, w', hw, h => by
      simp only [fB, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fB_mono e rest _ _ hw h.2⟩

/-- The check of an end block is monotone in the armed bit. -/
theorem fE_mono {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Bool) (b : Endblock D V l Γ Λ) (w w' : Bool),
      (w = true → w' = true) → fE Φ e w b = true → fE Φ e w' b = true
  | _, _, e, .ret _ _, w, w', hw, h => by
      simp only [fE, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢; exact h.imp id hw
  | _, _, e, .retWhy _ _, w, w', hw, h => by
      simp only [fE, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢; exact h.imp id hw
  | _, _, e, .retScoped _ _, w, w', hw, h => by
      simp only [fE, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢; exact h.imp id hw
  | _, _, e, .retWhyScoped _ _, w, w', hw, h => by
      simp only [fE, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢; exact h.imp id hw
  | _, _, _, .leave _, _, _, _, _ => rfl
  | _, _, _, .next _, _, _, _, _ => rfl
  | _, _, e, .cons s rest, w, w', hw, h => by
      simp only [fE, Bool.and_eq_true] at h ⊢
      refine ⟨?_, fE_mono e rest _ _ ?_ h.2⟩
      · cases s <;> simp_all [fS] <;> (cases w <;> cases w' <;> simp_all)
      · cases s <;> simp_all [fNach]
  | _, _, e, .bind _ rest, w, w', hw, h => by
      simp only [fE] at h ⊢; exact fE_mono e rest _ _ hw h
  | _, _, e, .bindCall g _ _ _ _ rest, w, w', hw, h => by
      simp only [fE, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
      exact ⟨h.1.imp id hw, h.2⟩
  | _, _, e, .bindCallElse g _ _ _ _ err rest, w, w', hw, h => by
      simp only [fE, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
      exact ⟨⟨h.1.1.imp id hw, h.1.2⟩, h.2⟩
  | _, _, e, .bindAxiom _ _ _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fE] at h ⊢; exact fE_mono e rest _ _ hw h
  | _, _, e, .bindAxiomElse _ _ _ _ _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fE, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fE_mono e rest _ _ hw h.2⟩
  | _, _, e, .bindAxiomOpt _ _ _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fE] at h ⊢; exact fE_mono e rest _ _ hw h
  | _, _, e, .bindAxiomOptElse _ _ _ _ _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fE, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fE_mono e rest _ _ hw h.2⟩
  | _, _, e, .regRead _ _ rest, w, w', hw, h => by
      simp only [fE] at h ⊢; exact fE_mono e rest _ _ hw h
  | _, _, e, .regReadElse _ _ _ sonst rest, w, w', hw, h => by
      simp only [fE, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fE_mono e rest _ _ hw h.2⟩
  | _, _, e, .awaits _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fE] at h ⊢; exact fE_mono e rest _ _ hw h
  | _, _, e, .bindCallInd _ _ _ _ _ rest, w, w', hw, h => by
      simp only [fE, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
      exact ⟨h.1.imp id hw, h.2⟩
  | _, _, e, .narrow _ _ _ _ rest, w, w', hw, h => by
      simp only [fE, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fE_mono e rest _ _ hw h.2⟩
  | _, _, e, .narrowRequired _ _ _ rest, w, w', hw, h => by
      simp only [fE] at h ⊢; exact fE_mono e rest _ _ hw h
  | _, _, e, .exchange _ _ _ _ rest, w, w', hw, h => by
      simp only [fE] at h ⊢; exact fE_mono e rest _ _ hw h
  | _, _, e, .ite _ t _, w, w', hw, h => by
      simp only [fE, Bool.and_eq_true] at h ⊢; exact ⟨h.1, fE_mono e t _ _ hw h.2⟩

/-- The residue predicate is monotone in the armed bit. -/
theorem fR_mono (e : Bool) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ) (w w' : Bool),
      (w = true → w' = true) → k.fR Φ e w → k.fR Φ e w'
  | _, _, _, .ende b, w, w', hw, h => fE_mono Φ e b w w' hw h
  | _, _, _, .dann b k, w, w', hw, h => ⟨fB_mono Φ e b w w' hw h.1, h.2⟩
  | _, _, _, .schrumpf k, w, w', hw, h => fR_mono e k w w' hw h
  | _, _, _, .frei _ k, w, w', hw, h => fR_mono e k w w' hw h
  | _, _, _, .trav .., _, _, _, h => h
  | _, _, _, .travRest .., _, _, _, h => h
  | _, _, _, .wieder .., _, _, _, h => h
  | _, _, _, .wiederRest .., _, _, _, h => h
  | _, _, _, .ewig .., _, _, _, h => h
  | _, _, _, .ewigRest .., _, _, _, h => h
  | _, _, _, .wartet b k, w, w', hw, h => ⟨fB_mono Φ e b w w' hw h.1, h.2⟩
  | _, _, _, .wartetSonst _ err b k, w, w', hw, h => ⟨h.1, fB_mono Φ e b w w' hw h.2.1, h.2.2⟩
  | _, _, _, .abbruch _, _, _, _, h => h
  | _, _, _, .leer, _, _, _, h => h

theorem fR_von_false (e : Bool) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (k : GRest D V l Γ Λ) (w : Bool) (h : k.fR Φ e false) : k.fR Φ e w :=
  fR_mono Φ e k false w (fun h => absurd h Bool.false_ne_true) h

theorem fB_von_false (e : Bool) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (w : Bool) (h : fB Φ e false b = true) : fB Φ e w b = true :=
  fB_mono Φ e b false w (fun h => absurd h Bool.false_ne_true) h

/-- An end block run as a block is checked as the end block. -/
theorem fB_alsBlock (e : Bool) {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (b : Endblock D V l Γ Λ) (w : Bool),
      fB Φ e w b.alsBlock.2 = fE Φ e w b
  | _, _, .ret _ _, w => by simp only [Endblock.alsBlock, fB, fS, Bool.and_true, fE]
  | _, _, .retWhy _ _, w => by simp only [Endblock.alsBlock, fB, fS, Bool.and_true, fE]
  | _, _, .retScoped _ _, w => by simp only [Endblock.alsBlock, fB, fS, Bool.and_true, fE]
  | _, _, .retWhyScoped _ _, w => by simp only [Endblock.alsBlock, fB, fS, Bool.and_true, fE]
  | _, _, .leave _, w => by simp only [Endblock.alsBlock, fB, fS, Bool.and_self, fE]
  | _, _, .next _, w => by simp only [Endblock.alsBlock, fB, fS, Bool.and_self, fE]
  | _, _, .cons s rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .bind _ rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .bindCall _ _ _ _ _ rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .bindAxiom _ _ _ _ _ _ _ rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .bindCallElse _ _ _ _ _ _ rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .bindAxiomElse _ _ _ _ _ _ _ _ _ rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ _ rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .regRead r hk rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .regReadElse r hk z sonst rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .awaits g pl hp hL hat rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .bindCallInd p args he hp hr rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .narrow _ _ _ sonst rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .narrowRequired _ _ _ rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .exchange _ _ _ _ rest, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e rest]
  | _, _, .ite _ t _, w => by
      simp only [Endblock.alsBlock, fB, fE, fB_alsBlock e t]

theorem fB_armWahlG (e : Bool) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    fArms Φ e arms = true → fB Φ e false (armWahlG arms v).2.1 = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩, h => by
      simp only [fArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨⟨n + 1, hn⟩, nutz⟩, h => by
      simp only [fArms, Bool.and_eq_true] at h
      exact fB_armWahlG e rest _ h.2

theorem fB_grundWahlG (e : Bool) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    fGArms Φ e arms = true → fB Φ e false (grundWahlG arms r) = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩, h => by
      simp only [fGArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨k + 1, hk⟩, h => by
      simp only [fGArms, Bool.and_eq_true] at h
      exact fB_grundWahlG e rest _ h.2

/-- A residue standing at a return, checked at bit `w`, demands `w` if its frame's returns
    are ordered. -/
theorem fR_anRueck (e : Bool) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : GRest D V l Γ Λ) (w : Bool) (ha : r.anRueck = true) (h : r.fR Φ e w)
    (he : e = true) : w = true := by
  subst he
  cases r with
  | ende b =>
      cases b with
      | ret _ _ => simpa [GRest.fR, fE] using h
      | retWhy _ _ => simpa [GRest.fR, fE] using h
      | cons s _ =>
          cases s <;> simp_all [GRest.anRueck, Endblock.istRueck, Stmt.istRueck, GRest.fR, fE, fS]
      | _ => simp only [GRest.anRueck, Endblock.istRueck, Bool.false_eq_true] at ha
  | dann b _ =>
      cases b with
      | cons s _ =>
          cases s <;> simp_all [GRest.anRueck, Block.istRueck, Stmt.istRueck, GRest.fR, fB, fS]
      | _ => simp only [GRest.anRueck, Block.istRueck, Bool.false_eq_true] at ha
  | _ => simp only [GRest.anRueck, Bool.false_eq_true] at ha

end Hilfen

/-! ## 2. The thread invariant -/

/-- Every suspended caller passes the check at the bit its callee's return will give it. -/
def FolgeStapel (Φ : Folge D) : D.Fn → List (RufRahmenG D) → Prop
  | _, [] => True
  | oben, F :: rest => F.rest.2.2.2.2.fR Φ (Φ.ende F.f) (Φ.vor oben) ∧ FolgeStapel Φ F.f rest

/-- **The thread invariant of the order leg.** -/
def FolgeInvG (Φ : Folge D) (z : RufFadenG D) : Prop :=
  z.kopf.rest.2.2.2.2.fR Φ (Φ.ende z.kopf.f) (Armiert Φ z.log) ∧
    FolgeStapel Φ z.kopf.f z.stapel ∧ FolgeLog Φ z.log

/-! ## 3. Every rule keeps the invariant -/

theorem armiert_aus {b w : Bool} (hk : b = false ∨ w = true) (hb : b = true) : w = true := by
  rcases hk with h | h
  · rw [h] at hb; exact absurd hb Bool.false_ne_true
  · exact h

section Schritt

variable {P : Programm D} {O : Orakel D} {pa : Nat} (Φ : Folge D)

set_option hygiene false in
/-- A head-local step: stack and log unchanged, the residue moves. -/
macro "kopfF" : tactic => `(tactic| (
  dsimp only; rw [rufUpdateG_self]
  refine ⟨?_, hst, hlog⟩
  dsimp only; rw [hw]
  rw [‹(M.faeden f).kopf.rest = _›] at hk
  dsimp only at hk ⊢
  simp only [GRest.fR, fE, fB, fS, fNach, fB_alsBlock, Bool.and_eq_true] at hk ⊢))

end Schritt
end Gabbro.Grammatik
