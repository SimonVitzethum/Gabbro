/-
  File:      Grammatik/Speichermodell/AtomarRuhe.lean
  Subject:   The idle root (MitRuhe.lean) and the semantics with the atomic rely: a body of
             `P.mitRuhe` under `execStmtHA` runs as the body of `P`, the atomic environment
             translated like the lock move (`hA`). The copy of MitRuheSperre.lean §4/§5 over
             `execStmtHA`. Opus lane O25b, 2026-09-26. Standalone.
-/
module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre
public import Grammatik.Speichermodell.Maschine.SperreSemA
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A read through translated environments is the translated read. -/
theorem leseA_worldR {A : AUmwelt D} {A' : AUmwelt D.mitRuhe}
    (hA : ∀ X σ, A' X (worldR σ) = worldR (A X σ)) (σ : World D) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) :
    leseA A' (worldR σ) (Λ.map resR) os = worldR (leseA A σ Λ os) := by
  unfold leseA
  rw [lese_worldR, hA]

section HilfenA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)

theorem execStmtHA_nachΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (s : Stmt D V l Γ Λ Λ₁) (σ : World D) (ρ : Env D Γ) :
    execStmtHA S O U A passes R (Stmt.nachΛ h s) σ ρ = execStmtHA S O U A passes R s σ ρ := by
  subst h; rfl

theorem execBlockHA_vorΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂)
    (b : Block D V l Γ Λ₁ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlockHA S O U A passes R (Block.vorΛ h b) σ ρ = execBlockHA S O U A passes R b σ ρ := by
  subst h; rfl

theorem execEndHA_umΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (e : Endblock D V l Γ Λ₁) (σ : World D) (ρ : Env D Γ) :
    execEndHA S O U A passes R (Endblock.umΛ h e) σ ρ = execEndHA S O U A passes R e σ ρ := by
  subst h; rfl

end HilfenA

/-! ## 5. Every statement, block and end block, up to the label -/

section HauptA

variable (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe) (hO : OrakelRu O O')
  (U : Umwelt D) (U' : Umwelt D.mitRuhe) (A : AUmwelt D) (A' : AUmwelt D.mitRuhe) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ))
  (hA : ∀ X σ, A' X (worldR σ) = worldR (A X σ))
  (hR : RufRel R R')

include hO hU hA hR

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_assignSlot {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.assignSlot t f i e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.assignSlot t f i e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  rw [orte2, leseA_worldR hA, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_assignThru {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t ht f i e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t ht f i e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  rw [show (ruE p).orte ++ (ruE i).orte ++ (ruE e).orte = p.orte ++ i.orte ++ e.orte from
    kongr₂ (· ++ ·) (orte2 p i) (ruE_orte e), leseA_worldR hA, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_assignThruOwn {V : vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (m)
    (s)
    (ho)
    (he)
    (hg)
    (hm)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) p t ht f i e m s ho he hg hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) p t ht f i e m s ho he hg hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  rw [show (ruE p).orte ++ (ruE i).orte ++ (ruE e).orte = p.orte ++ i.orte ++ e.orte from
    kongr₂ (· ++ ·) (orte2 p i) (ruE_orte e), leseA_worldR hA, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_assignSlotRef {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (r)
    (t)
    (ht)
    (ho)
    (f)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  rw [show (ruE r).orte ++ (ruE e).orte = r.orte ++ e.orte from
    kongr₂ (· ++ ·) (ruE_orte r) (ruE_orte e), leseA_worldR hA, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_assignGlob {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.assignGlob g e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.assignGlob g e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru, schreibGlob_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_putBytes {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (t)
    (f)
    (hf)
    (n)
    (i)
    (hlo)
    (hhi)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  rw [orte2, leseA_worldR hA, eval_ru, eval_ru, schreibBytes_worldR t f hf]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_assignVar {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (x)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.assignVar (τ := zi_τ) x e : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.assignVar (τ := zi_τ) x e : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru, envR_set]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_shift {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lo)
    (hi)
    (t)
    (f)
    (hτ)
    (i)
    (von)
    (nach)
    (hn)
    (he)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.shift (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.shift (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  erw [show (Sum.inl t :: (ruE i).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inl t :: i.orte from congrArg (Sum.inl t :: ·) (ruE_orte i)]
  erw [leseA_worldR hA, eval_ru]
  erw [slotInt_cast_worldR _ t f hτ (congrArg tyR hτ)]
  by_cases hc : (hτ ▸ (leseA A σ Λ (Sum.inl t :: i.orte)).slots t
      (eval (leseA A σ Λ (Sum.inl t :: i.orte)) i (leseA A σ Λ (Sum.inl t :: i.orte)) ρ).n f :
      Wert D (.int lo hi)).n = von
  · erw [if_pos hc, if_pos hc, int_cast_gen' (D.typ t f) lo hi hτ (congrArg tyR hτ) _,
      schreibSlot_worldR]
    rfl
  · erw [if_neg hc, if_neg hc]
    rfl

end HauptA
end Gabbro.Grammatik
