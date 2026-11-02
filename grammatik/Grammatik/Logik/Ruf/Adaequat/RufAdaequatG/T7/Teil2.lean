module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T6
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T7.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Spur
variable (O : Orakel D) (passes : Nat) {V : Vertrag D} (A : D.Lock → Prop)

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
  | _, _, _, _, _, .callIndElse .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
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
  | _, _, _, _, _, .consumeTraverse .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retry .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .forever .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .axiomCall .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .axiomCallElse .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, Λ₀, _, .ret e hperm, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      exact ⟨h1, h1.evalErg e ρ⟩
  | _, _, _, _, _, .retWhy .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retScoped .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retWhyScoped .., hs, _ => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
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
  | _, _, _, _, _, .bindCallIndElse .., hb, _ => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb, _ => by cases hb
  | _, _, _, _, _, .bindAxiom .., hb, _ => by cases hb
  | _, _, _, _, _, .bindAxiomElse .., hb, _ => by cases hb
  | _, _, _, _, _, .bindAxiomOpt .., hb, _ => by cases hb
  | _, _, _, _, _, .bindAxiomOptElse .., hb, _ => by cases hb
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
  | _, _, _, _, _, .narrowRequired _ _ _ _, hb, _ => by cases hb
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
  | _, _, _, .retScoped .., he, _ => by cases he
  | _, _, _, .retWhyScoped .., he, _ => by cases he
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
  | _, _, _, .narrowRequired _ _ _ _, he, _ => by cases he

theorem armsSG : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs),
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
