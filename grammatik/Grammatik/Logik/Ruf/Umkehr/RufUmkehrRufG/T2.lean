/- Part 2 of 6 of `RufUmkehrRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufUmkehrRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

section SpurK

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  (A : D.Lock → Prop) (C : D.Fn → Prop) (hR : RufSG R C)
include hR

/-- A block's outcome agrees, up to the trace, from worlds with one memory. -/
def SGBK {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
    AusSG (execBlock O passes R b σ ρ) (execBlock O passes R b σ' ρ)

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 800000 in
mutual

theorem stmtSGK : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), StmtR A C mr s → s.kOk = true →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      AusSG (execStmt O passes R s σ ρ) (execStmt O passes R s σ' ρ)
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
      simp only [Stmt.kOk, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ c.orte
      simp only [execStmt]
      rw [h1.eval c]
      split
      · exact blockSGK t ht ho.1 _ _ _ h1
      · exact blockSGK e he ho.2 _ _ _ h1
  | _, _, _, Λ₀, _, .onOption o p a, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      simp only [Stmt.kOk, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ o.orte
      simp only [execStmt]
      rw [h1.eval o]
      split
      · exact AusSG.schrumpf (blockSGK p hp ho.1 _ _ _ h1)
      · exact blockSGK a ha ho.2 _ _ _ h1
  | _, _, _, Λ₀, _, .onTag w arms, hs, ho => by
      intro σ σ' ρ h
      have ha := hs.onTag_inv
      simp only [Stmt.kOk] at ho
      have h1 := h.lese Λ₀ w.orte
      simp only [execStmt]
      rw [execArms_wahl, execArms_wahl, h1.eval w]
      exact AusSG.schrumpfArm _ (armsSGK arms ha ho _ _ _ _ h1)
  | _, _, _, Λ₀, _, .onWhy r arms, hs, ho => by
      intro σ σ' ρ h
      have ha := hs.onGrund_inv
      simp only [Stmt.kOk] at ho
      have h1 := h.lese Λ₀ r.orte
      simp only [execStmt]
      rw [execGrund_wahlW O passes R arms, execGrund_wahlW O passes R arms, h1.eval r]
      exact grundSGK arms ha ho _ _ _ _ h1
  | _, _, _, Λ₀, _, .call g args hp hr, hs, _ => by
      intro σ σ' ρ h
      have hC := hs.call_inv
      have h1 := h.lese Λ₀ args.orte
      simp only [execStmt]
      rw [h1.evalArgs args ρ]
      have hRg := hR g hC _ _ (evalArgs (σ'.lese Λ₀ args.orte) args (σ'.lese Λ₀ args.orte) ρ) h1
      generalize R g (σ.lese Λ₀ args.orte) _ = o at hRg ⊢
      generalize R g (σ'.lese Λ₀ args.orte) _ = o' at hRg ⊢
      cases o with
      | ok σ1 v1 =>
        cases o' with
        | ok σ2 v2 => exact ⟨hRg.1, rfl⟩
        | _ => exact hRg.elim
      | why _ r => exact (Fin.cast hr r).elim0
      | logik e =>
        cases o' with
        | ok => exact hRg.elim
        | why _ r => exact (Fin.cast hr r).elim0
        | _ => trivial
      | hardware e =>
        cases o' with
        | ok => exact hRg.elim
        | why _ r => exact (Fin.cast hr r).elim0
        | _ => trivial
  | _, _, _, _, _, .callInd .., _, ho => by simp only [Stmt.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .locks L hr body, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hb, _⟩ := hs.locks_inv
      simp only [Stmt.kOk] at ho
      simp only [execStmt]
      exact AusSG.gibt (blockSGK body hb ho _ _ _ (h.nimmt L)) L
  | _, _, _, _, _, .breaking i body, hs, ho => by
      intro σ σ' ρ h
      have hb := hs.breaking_inv
      simp only [Stmt.kOk] at ho
      simp only [execStmt]
      exact blockSGK body hb ho _ _ _ h
  | _, _, _, _, _, .traverse .., _, ho => by simp only [Stmt.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .retry .., _, ho => by simp only [Stmt.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .forever .., _, ho => by simp only [Stmt.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .axiomCall .., _, ho => by simp only [Stmt.kOk, Bool.false_eq_true] at ho
  | _, _, _, Λ₀, _, .ret e hperm, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      exact ⟨h1, h1.evalErg e ρ⟩
  | _, _, _, _, _, .retWhy .., _, ho => by simp only [Stmt.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .leave .., _, ho => by simp only [Stmt.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .next .., _, ho => by simp only [Stmt.kOk, Bool.false_eq_true] at ho

theorem blockSGK : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), BlockR A C mr b → b.kOk = true → SGBK O passes R b
  | _, _, _, _, _, .nil, _, _ => by
      intro σ σ' ρ h
      exact ⟨h, rfl⟩
  | _, _, _, _, _, .cons s rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨hs, hr⟩ := hb.cons_inv
      simp only [Block.kOk, Bool.and_eq_true] at ho
      have h1 := stmtSGK s hs ho.1 _ _ ρ h
      simp only [execBlock]
      generalize execStmt O passes R s σ ρ = o at h1 ⊢
      generalize execStmt O passes R s σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | (obtain ⟨hs1, rfl⟩ := h1; exact blockSGK rest hr ho.2 _ _ _ hs1)
  | _, _, _, Λ₀, _, .bind e rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.bind_inv
      simp only [Block.kOk] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      exact AusSG.schrumpf (blockSGK rest hr ho _ _ _ h1)
  | _, _, _, Λ₀, _, .bindCall g args he hp hr rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨hC, hrest⟩ := hb.bindCall_inv
      simp only [Block.kOk] at ho
      have h1 := h.lese Λ₀ args.orte
      simp only [execBlock]
      rw [h1.evalArgs args ρ]
      have hRg := hR g hC _ _ (evalArgs (σ'.lese Λ₀ args.orte) args (σ'.lese Λ₀ args.orte) ρ) h1
      generalize R g (σ.lese Λ₀ args.orte) _ = o at hRg ⊢
      generalize R g (σ'.lese Λ₀ args.orte) _ = o' at hRg ⊢
      cases o with
      | ok σ1 v1 =>
        cases o' with
        | ok σ2 v2 =>
          obtain ⟨hs2, rfl⟩ := hRg
          exact AusSG.schrumpf (blockSGK rest hrest ho _ _ _ hs2)
        | _ => exact hRg.elim
      | why _ r => exact (Fin.cast hr r).elim0
      | logik e =>
        cases o' with
        | ok => exact hRg.elim
        | why _ r => exact (Fin.cast hr r).elim0
        | _ => trivial
      | hardware e =>
        cases o' with
        | ok => exact hRg.elim
        | why _ r => exact (Fin.cast hr r).elim0
        | _ => trivial
  | _, _, _, _, _, .bindCallInd .., _, ho => by simp only [Block.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .bindCallElse .., _, ho => by simp only [Block.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .bindAxiom .., _, ho => by simp only [Block.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .bindAxiomElse .., _, ho => by simp only [Block.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .regRead .., _, ho => by simp only [Block.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .regReadElse .., _, ho => by simp only [Block.kOk, Bool.false_eq_true] at ho
  | _, _, _, _, _, .awaits .., _, ho => by simp only [Block.kOk, Bool.false_eq_true] at ho
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.exchange_inv
      simp only [Block.kOk] at ho
      have h1 := h.lese Λ₀ (.inr g :: neuE.orte)
      simp only [execBlock]
      have hg : (σ.lese Λ₀ (.inr g :: neuE.orte)).globs g =
          (σ'.lese Λ₀ (.inr g :: neuE.orte)).globs g := by rw [h1.2]
      rw [hg, h1.eval neuE]
      exact AusSG.schrumpf (blockSGK rest hr ho _ _ _ (h1.schreibGlob _ _ _))
  | _, _, _, Λ₀, _, .narrow e lo' hi' sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
      simp only [Block.kOk, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ e.orte
      rw [execBlock_narrowK, execBlock_narrowK, h1.eval e]
      unfold narrowWeiterK
      split
      · exact AusSG.schrumpf (blockSGK rest hr ho.2 _ _ _ h1)
      · exact EndSG.zuAusgang (endSGK sonst hs ho.1 _ _ _ h1)
  | _, _, _, Λ₀, _, .check c sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
      simp only [Block.kOk, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ c.orte
      simp only [execBlock]
      rw [h1.eval c]
      split
      · exact blockSGK rest hr ho.2 _ _ _ h1
      · exact EndSG.zuAusgang (endSGK sonst hs ho.1 _ _ _ h1)
  | _, _, _, Λ₀, _, .float op a b lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleit_inv
      simp only [Block.kOk] at ho
      have h1 := h.lese Λ₀ (a.orte ++ b.orte)
      simp only [execBlock]
      rw [h1.eval a, h1.eval b]
      split
      · exact AusSG.schrumpf (blockSGK rest hr ho _ _ _ h1)
      · trivial
  | _, _, _, _, _, .floatLit q lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleitLit_inv
      simp only [Block.kOk] at ho
      simp only [execBlock]
      split
      · exact AusSG.schrumpf (blockSGK rest hr ho _ _ _ h)
      · trivial
  | _, _, _, Λ₀, _, .floatOf e lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleitVon_inv
      simp only [Block.kOk] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      split
      · exact AusSG.schrumpf (blockSGK rest hr ho _ _ _ h1)
      · trivial
  | _, _, _, Λ₀, _, .floatNarrow e lo hi sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
      simp only [Block.kOk, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      split
      · exact AusSG.schrumpf (blockSGK rest hr ho.2 _ _ _ h1)
      · exact EndSG.zuAusgang (endSGK sonst hs ho.1 _ _ _ h1)

theorem endSGK : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), EndR A C e → e.kOk = true →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      EndSG (execEnd O passes R e σ ρ) (execEnd O passes R e σ' ρ)
  | _, _, Λ₀, .ret e hperm, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execEnd]
      exact ⟨h1, h1.evalErg e ρ⟩
  | _, _, _, .retWhy .., _, ho => by simp only [Endblock.kOk, Bool.false_eq_true] at ho
  | _, _, _, .leave .., _, ho => by simp only [Endblock.kOk, Bool.false_eq_true] at ho
  | _, _, _, .next .., _, ho => by simp only [Endblock.kOk, Bool.false_eq_true] at ho
  | _, _, _, .cons s rest, he, ho => by
      intro σ σ' ρ h
      obtain ⟨hs, hr, _⟩ := he.cons_inv
      simp only [Endblock.kOk, Bool.and_eq_true] at ho
      have h1 := stmtSGK s hs ho.1 _ _ ρ h
      simp only [execEnd]
      generalize execStmt O passes R s σ ρ = o at h1 ⊢
      generalize execStmt O passes R s σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | trivial
        | (obtain ⟨hs1, rfl⟩ := h1; exact endSGK rest hr ho.2 _ _ _ hs1)
  | _, _, Λ₀, .bind e rest, he, ho => by
      intro σ σ' ρ h
      have hr := he.bind_inv
      simp only [Endblock.kOk] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execEnd]
      rw [h1.eval e]
      exact EndSG.schrumpf (endSGK rest hr ho _ _ _ h1)

theorem armsSGK : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    ArmsR A C mr arms → arms.kOk = true → ∀ (v : Wert D (.sum cs)),
    SGBK O passes R (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ho, ⟨⟨0, _⟩, _⟩ => by
      simp only [Arms.kOk, Bool.and_eq_true] at ho
      exact blockSGK b ha.cons_inv.1 ho.1
  | _, _, _, _, _, _, .cons _ rest, ha, ho, ⟨⟨_ + 1, _⟩, _⟩ => by
      simp only [Arms.kOk, Bool.and_eq_true] at ho
      exact armsSGK rest ha.cons_inv.2 ho.2 _

theorem grundSGK : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsR A C mr arms → arms.kOk = true →
    ∀ (r : Fin n), SGBK O passes R (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ho, ⟨0, _⟩ => by
      simp only [GrundArms.kOk, Bool.and_eq_true] at ho
      exact blockSGK b ha.cons_inv.1 ho.1
  | _, _, _, _, _, _, .cons _ rest, ha, ho, ⟨_ + 1, _⟩ => by
      simp only [GrundArms.kOk, Bool.and_eq_true] at ho
      exact grundSGK rest ha.cons_inv.2 ho.2 _

end

/-- Frame results do not see the trace (covered residues of the converse). -/
theorem semK_SG : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ), RestK A C r →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      (semK O passes R r σ ρ).gleich (semK O passes R r σ' ρ)
  | _, _, _, .ende e, hr => by
      intro σ σ' ρ h
      obtain ⟨he, ho⟩ := hr.ende_inv
      exact endErg_SG (endSGK O passes R A C hR e he ho σ σ' ρ h)
  | _, _, _, .dann b k, hr => by
      intro σ σ' ρ h
      obtain ⟨⟨_, hb⟩, ho, hk⟩ := hr.dann_inv
      have h1 := blockSGK O passes R A C hR b hb ho σ σ' ρ h
      rw [semK_dann, semK_dann]
      generalize execBlock O passes R b σ ρ = o at h1 ⊢
      generalize execBlock O passes R b σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | trivial
        | (obtain ⟨hs1, rfl⟩ := h1; exact semK_SG k hk _ _ _ hs1)
  | _, _, _, .schrumpf k, hr => by
      intro σ σ' ρ h
      exact semK_SG k hr.schrumpf_inv σ σ' ρ.tail h
  | _, _, _, .frei L k, hr => by
      intro σ σ' ρ h
      exact semK_SG k hr.frei_inv (σ.gibt L) (σ'.gibt L) ρ (h.gibt L)
  | _, _, _, .trav .., hr => by cases hr
  | _, _, _, .travRest .., hr => by cases hr
  | _, _, _, .wieder .., hr => by cases hr
  | _, _, _, .wiederRest .., hr => by cases hr
  | _, _, _, .ewig .., hr => by cases hr
  | _, _, _, .ewigRest .., hr => by cases hr
  | _, _, _, .wartet .., hr => by cases hr
  | _, _, _, .wartetSonst .., hr => by cases hr
  | _, _, _, .abbruch _, _ => fun _ _ _ _ => REnde.gleich_refl _
  | _, _, _, .leer, _ => fun _ _ _ _ => REnde.gleich_refl _

end SpurK
/-- **The body-running handler does not see the trace** on the callees the
    converse admits, at every depth. -/
theorem rufRumpf_SG (P : Programm D) (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) :
    ∀ d, RufSG (rufRumpf P O passes d) (TiefK P A d)
  | 0 => fun _ hC => (hC : False).elim
  | d + 1 => by
      intro g hC σ σ' ρ h
      obtain ⟨he, ho⟩ := hC
      have h1 := endSGK O passes (rufRumpf P O passes d) A (TiefK P A d) (rufRumpf_SG P O passes A d)
        (P.rumpf g) he ho σ σ' ρ h
      simp only [rufRumpf]
      generalize execEnd (V := vertragVon D g) O passes (rufRumpf P O passes d) (P.rumpf g) σ ρ = o
        at h1 ⊢
      generalize execEnd (V := vertragVon D g) O passes (rufRumpf P O passes d) (P.rumpf g) σ' ρ = o'
        at h1 ⊢
      cases o with
      | zurueck σ1 v1 =>
        cases o' with
        | zurueck σ2 v2 => exact h1
        | leave h' => exact absurd h' (by decide)
        | next h' => exact absurd h' (by decide)
        | _ => exact h1.elim
      | leave h' => exact absurd h' (by decide)
      | next h' => exact absurd h' (by decide)
      | _ =>
        cases o' with
        | zurueck => exact h1.elim
        | leave h' => exact absurd h' (by decide)
        | next h' => exact absurd h' (by decide)
        | _ => trivial

/-! ## 4. Each machine step keeps the frame semantics, with calls -/


end Gabbro.Grammatik
