/- Part 3 of 4 of `HoareRegeln` (split by instrumente/teile/lean-teilen.py; the umbrella `HoareRegeln.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Hoare.HoareRegeln.T2

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

theorem blockOhneRuf_Runabhaengig {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Block D V l Γ Λ Λ') (h : BlockOhneRuf b)
    (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ :=
  BlockOhneRuf.rec
    (motive_1 := fun s _ => ∀ (σ : World D) (ρ : Env D _),
      execStmt O passes R₁ s σ ρ = execStmt O passes R₂ s σ ρ)
    (motive_2 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    (motive_3 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execEnd O passes R₁ b σ ρ = execEnd O passes R₂ b σ ρ)
    (motive_4 := fun arms _ => ∀ (v : Wert D _) (σ : World D) (ρ : Env D _),
      execArms O passes R₁ arms v σ ρ = execArms O passes R₂ arms v σ ρ)
    (motive_5 := fun arms _ => ∀ (r : Fin _) (σ : World D) (ρ : Env D _),
      execGrund O passes R₁ arms r σ ρ = execGrund O passes R₂ arms r σ ρ)
    (fun t f i e hw hL σ ρ => rfl)
    (fun n p t ht f i e hw hL σ ρ => rfl)
    (fun g e hw hL σ ρ => rfl)
    (fun t f hf n i hlo hhi e hw hL σ ρ => rfl)
    (fun x e σ ρ => rfl)
    (fun t f hτ i von nach hn he hw hL σ ρ => by
        simp only [execStmt]
)
    (fun c t e ht he iht ihe σ ρ => by
        have ht' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iht σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execStmt, ht', he']
)
    (fun o p a hp ha ihp iha σ ρ => by
        have hp' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihp σ ρ
        have ha' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iha σ ρ
        simp only [execStmt]
        split
        next _ => simp only [hp']
        next _ => simp only [ha']
)
    (fun v arms ha iha σ ρ => by
        -- `execArms` runs at the read world; keep the world explicit.
        show execStmt O passes R₁ (.onTag (V := V) v arms) σ ρ =
          execStmt O passes R₂ (.onTag (V := V) v arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun r arms ha iha σ ρ => by
        show execStmt O passes R₁ (.onWhy (V := V) r arms) σ ρ =
          execStmt O passes R₂ (.onWhy (V := V) r arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun L hr body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun i body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun t inv body hb ihb σ ρ => by
        exact traverseKey O passes R₁ R₂ t inv body (fun σ ρ => ihb σ ρ) (alleIndizes (D.count t)) σ ρ)
    (fun n bis body ueberlauf hb hu ihb ihu σ ρ => by
        exact retryKey O passes R₁ R₂ n bis body ueberlauf (fun σ ρ => ihb σ ρ) (fun σ ρ => ihu σ ρ) σ ρ)
    (fun a inv body hb ihb σ ρ => by
        exact foreverKey O passes R₁ R₂ a inv body (fun σ ρ => ihb σ ρ) σ ρ)
    (fun a args h hw hg hd hgd σ ρ => by
  simp only [execStmt]
)
    (fun r hk e σ ρ => rfl)
    (fun r hk m hm hl maske bits σ ρ => rfl)
    (fun g e payload hp hw hL σ ρ => rfl)
    (fun m a h hs σ ρ => rfl)
    (fun m s h a σ ρ => rfl)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hs', hr']
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun r hk rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hein : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            by_cases hzu : D.rzusage r v = true
            · simp only [hzu, if_pos hzu, hr']
            · simp only [if_neg hzu]
)
    (fun r hk zusage sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hein : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            split
            next _ => simp only [hr']
            next _ => simp only [he']
)
    (fun g payload hp hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        by_cases hs : O.sichtbar g σ = true
        · simp only [hs, if_pos hs, hr']
        · simp only [if_neg hs]
)
    (fun g neu hw hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun e lo' hi' sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun c sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun op a b lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (gleitRechne op _ _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun q lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (bruch q) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (gleitAusInt _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi _ with
        | none => simp only [hg, he']
        | some v => simp only [hg, hr']

)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hs']
        cases execStmt O passes R₂ s σ ρ with
        | ok σ1 ρ1 => simp only [hr']
        | zurueck σ1 v => rfl
        | why σ1 r => rfl
        | leave h σ1 ρ1 => rfl
        | next h σ1 ρ1 => rfl
        | logik e => rfl
        | hardware e => rfl
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hr']

)
    (fun v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz => exact idx.elim0
)
    (fun b rest hb hr ihb ihr v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz =>
            cases idx with
            | mk k hk =>
                exact armsOhneRuf_RunabhaengigAux O passes R₁ R₂ b rest
                  (fun σ ρ => ihb σ ρ)
                  (fun w σ ρ => ihr w σ ρ)
                  k hk nutz σ ρ)
    (fun r σ ρ => by exact r.elim0)
    (fun b rest hb hr ihb ihr r σ ρ => by
      cases r with
      | mk k hk =>
          cases k with
          | zero =>
              have hbeq := ihb σ ρ
              simp only [execGrund, hbeq]
          | succ n =>
              have hk' : n < _ := Nat.lt_of_succ_lt_succ hk
              have hstep : execGrund O passes R₁ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₁ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              have hstep2 : execGrund O passes R₂ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₂ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              rw [hstep, hstep2]
              exact ihr _ _ _)
    h σ ρ

theorem endOhneRuf_Runabhaengig {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (b : Endblock D V l Γ Λ) (h : EndOhneRuf b)
    (σ : World D) (ρ : Env D Γ) :
    execEnd O passes R₁ b σ ρ = execEnd O passes R₂ b σ ρ :=
  EndOhneRuf.rec
    (motive_1 := fun s _ => ∀ (σ : World D) (ρ : Env D _),
      execStmt O passes R₁ s σ ρ = execStmt O passes R₂ s σ ρ)
    (motive_2 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ b σ ρ = execBlock O passes R₂ b σ ρ)
    (motive_3 := fun b _ => ∀ (σ : World D) (ρ : Env D _),
      execEnd O passes R₁ b σ ρ = execEnd O passes R₂ b σ ρ)
    (motive_4 := fun arms _ => ∀ (v : Wert D _) (σ : World D) (ρ : Env D _),
      execArms O passes R₁ arms v σ ρ = execArms O passes R₂ arms v σ ρ)
    (motive_5 := fun arms _ => ∀ (r : Fin _) (σ : World D) (ρ : Env D _),
      execGrund O passes R₁ arms r σ ρ = execGrund O passes R₂ arms r σ ρ)
    (fun t f i e hw hL σ ρ => rfl)
    (fun n p t ht f i e hw hL σ ρ => rfl)
    (fun g e hw hL σ ρ => rfl)
    (fun t f hf n i hlo hhi e hw hL σ ρ => rfl)
    (fun x e σ ρ => rfl)
    (fun t f hτ i von nach hn he hw hL σ ρ => by
        simp only [execStmt]
)
    (fun c t e ht he iht ihe σ ρ => by
        have ht' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iht σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execStmt, ht', he']
)
    (fun o p a hp ha ihp iha σ ρ => by
        have hp' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihp σ ρ
        have ha' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => iha σ ρ
        simp only [execStmt]
        split
        next _ => simp only [hp']
        next _ => simp only [ha']
)
    (fun v arms ha iha σ ρ => by
        -- `execArms` runs at the read world; keep the world explicit.
        show execStmt O passes R₁ (.onTag (V := V) v arms) σ ρ =
          execStmt O passes R₂ (.onTag (V := V) v arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun r arms ha iha σ ρ => by
        show execStmt O passes R₁ (.onWhy (V := V) r arms) σ ρ =
          execStmt O passes R₂ (.onWhy (V := V) r arms) σ ρ
        simp only [execStmt]
        exact iha _ _ _
)
    (fun L hr body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun i body hb ihb σ ρ => by
        have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihb σ ρ
        simp only [execStmt, hb']
)
    (fun t inv body hb ihb σ ρ => by
        exact traverseKey O passes R₁ R₂ t inv body (fun σ ρ => ihb σ ρ) (alleIndizes (D.count t)) σ ρ)
    (fun n bis body ueberlauf hb hu ihb ihu σ ρ => by
        exact retryKey O passes R₁ R₂ n bis body ueberlauf (fun σ ρ => ihb σ ρ) (fun σ ρ => ihu σ ρ) σ ρ)
    (fun a inv body hb ihb σ ρ => by
        exact foreverKey O passes R₁ R₂ a inv body (fun σ ρ => ihb σ ρ) σ ρ)
    (fun a args h hw hg hd hgd σ ρ => by
  simp only [execStmt]
)
    (fun r hk e σ ρ => rfl)
    (fun r hk m hm hl maske bits σ ρ => rfl)
    (fun g e payload hp hw hL σ ρ => rfl)
    (fun m a h hs σ ρ => rfl)
    (fun m s h a σ ρ => rfl)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hs', hr']
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun r hk rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hein : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            by_cases hzu : D.rzusage r v = true
            · simp only [hzu, if_pos hzu, hr']
            · simp only [if_neg hzu]
)
    (fun r hk zusage sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hein : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
        | none => simp only [hein]
        | some v =>
            simp only [hein]
            split
            next _ => simp only [hr']
            next _ => simp only [he']
)
    (fun g payload hp hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        by_cases hs : O.sichtbar g σ = true
        · simp only [hs, if_pos hs, hr']
        · simp only [if_neg hs]
)
    (fun g neu hw hL rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock, hr']
)
    (fun e lo' hi' sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun c sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        split
        next _ => simp only [hr']
        next _ => simp only [he']
)
    (fun op a b lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (gleitRechne op _ _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun q lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (bruch q) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi (gleitAusInt _) with
        | none => simp only [hg]
        | some v => simp only [hg, hr']
)
    (fun e lo hi sonst rest he hr ihe ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        have he' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihe σ ρ
        simp only [execBlock]
        cases hg : gleitPasst lo hi _ with
        | none => simp only [hg, he']
        | some v => simp only [hg, hr']

)
    (fun e hΛ σ ρ => rfl)
    (fun r hΛ σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun h σ ρ => rfl)
    (fun s rest hs hr ihs ihr σ ρ => by
        have hs' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihs σ ρ
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hs']
        cases execStmt O passes R₂ s σ ρ with
        | ok σ1 ρ1 => simp only [hr']
        | zurueck σ1 v => rfl
        | why σ1 r => rfl
        | leave h σ1 ρ1 => rfl
        | next h σ1 ρ1 => rfl
        | logik e => rfl
        | hardware e => rfl
)
    (fun e rest hr ihr σ ρ => by
        have hr' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => ihr σ ρ
        simp only [execEnd, hr']

)
    (fun v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz => exact idx.elim0
)
    (fun b rest hb hr ihb ihr v σ ρ => by
        subst_vars
        cases v with
        | mk idx nutz =>
            cases idx with
            | mk k hk =>
                exact armsOhneRuf_RunabhaengigAux O passes R₁ R₂ b rest
                  (fun σ ρ => ihb σ ρ)
                  (fun w σ ρ => ihr w σ ρ)
                  k hk nutz σ ρ)
    (fun r σ ρ => by exact r.elim0)
    (fun b rest hb hr ihb ihr r σ ρ => by
      cases r with
      | mk k hk =>
          cases k with
          | zero =>
              have hbeq := ihb σ ρ
              simp only [execGrund, hbeq]
          | succ n =>
              have hk' : n < _ := Nat.lt_of_succ_lt_succ hk
              have hstep : execGrund O passes R₁ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₁ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              have hstep2 : execGrund O passes R₂ (GrundArms.cons b rest) ⟨n + 1, hk⟩ σ ρ =
                  execGrund O passes R₂ rest ⟨n, hk'⟩ σ ρ := by
                simp only [execGrund]
              rw [hstep, hstep2]
              exact ihr _ _ _)
    h σ ρ


