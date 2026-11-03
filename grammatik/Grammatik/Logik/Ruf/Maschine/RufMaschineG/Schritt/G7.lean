module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Steps of `RufSchrittG`, group 7** (`dannVerbrauch` … `dannNextVerbrauch`):
    the consuming traversal (`traverse … by consuming`, C11), mirroring the
    `trav` steps of group 2 round by round: unfold (no reads, like
    `dannTrav`), select in the current world (invariant, member/edge and
    measure reads, in the order `execStmt` records them), empty selection
    (like `travDone`), resume with the strict measure fall (like `travFort`
    plus the fall check against the round-entry measure), and `leave`/`next`
    out of the body (like `dannLeaveTrav`/`dannNextTrav` plus the fall
    check). A cyclic edge with members left, a failed invariant and a
    non-falling measure have no step -- the thread is stuck, exactly where
    the sequential run answers `.logik .schleife`. `RufSchrittG`
    (RufMaschineG/T2.lean) is the union of the 7 groups. -/
inductive RufSchrittG7 (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineG D → Faden → RufMaschineG D → Prop where
  | dannVerbrauch (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D))
      (t : D.Tab)
      (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
      (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
      (inv : Expr D Γ Λ .bool) (bound : Int)
      (mass : Expr D Γ Λ (.int 0 bound))
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons
          (.consumeTraverse t member edge inv bound mass body) rest) k⟩) :
      RufSchrittG7 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ,
              .verbrauch t member edge inv bound mass body
                ((D.count t).toNat + bound.toNat + 1) (.dann rest k)⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | verbrauchWeiter (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab)
      (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
      (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
      (inv : Expr D Γ Λ .bool) (bound : Int)
      (mass : Expr D Γ Λ (.int 0 bound))
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (rest : Nat)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .verbrauch t member edge inv bound mass body
          (rest + 1) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (σ₂ : World D) (hs₂ : σ₂ = σ₁.lese Λ (member.orte ++ edge.orte))
      (v : Wert D (.index (D.count t)))
      (hv : verbrauchWahl (alleIndizes (D.count t))
        (fun k => wahr? (eval σ₂ member σ₂ (.cons k ρ)))
        (fun j k => wahr? (eval σ₂ edge σ₂ (.cons j (.cons k ρ))))
        (fun j k => decide (j.n = k.n)) = some v)
      (σ₃ : World D) (hs₃ : σ₃ = σ₂.lese Λ mass.orte)
      (m : Int) (hm : m = (eval σ₃ mass σ₃ ρ).n)
      (neu : List (Ereignis D)) (hneu : σ₃.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG7 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, .index (D.count t) :: Γ, Λ, .cons v ρ,
              .dann body (.verbrauchRest t member edge inv bound mass body
                rest m k)⟩⟩,
            σ₃.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | verbrauchLeer (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab)
      (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
      (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
      (inv : Expr D Γ Λ .bool) (bound : Int)
      (mass : Expr D Γ Λ (.int 0 bound))
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (rest : Nat)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .verbrauch t member edge inv bound mass body
          (rest + 1) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (σ₂ : World D) (hs₂ : σ₂ = σ₁.lese Λ (member.orte ++ edge.orte))
      (hleer : verbrauchWahl (alleIndizes (D.count t))
        (fun k => wahr? (eval σ₂ member σ₂ (.cons k ρ)))
        (fun j k => wahr? (eval σ₂ edge σ₂ (.cons j (.cons k ρ))))
        (fun j k => decide (j.n = k.n)) = none)
      (hkein : ((alleIndizes (D.count t)).all fun k =>
        !(wahr? (eval σ₂ member σ₂ (.cons k ρ)))) = true)
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG7 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | verbrauchFort (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab)
      (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
      (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
      (inv : Expr D Γ Λ .bool) (bound : Int)
      (mass : Expr D Γ Λ (.int 0 bound))
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (rest : Nat) (vor : Int)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ,
         .verbrauchRest t member edge inv bound mass body rest vor k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ mass.orte)
      (m' : Int) (hm' : m' = (eval σ₁ mass σ₁ ρ).n)
      (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG7 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .verbrauch t member edge inv bound mass body
               rest k⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannLeaveVerbrauch (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab)
      (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
      (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
      (inv : Expr D Γ Λ .bool) (bound : Int)
      (mass : Expr D Γ Λ (.int 0 bound))
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (rest : Nat) (vor : Int)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (restb : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λx Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λx Λx) restb)
           (.verbrauchRest t member edge inv bound mass body rest vor k)⟩)
      (σ' : World D) (ρ' : Env D (.index (D.count t) :: Γ))
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λx Λx) (M.weltVon f)
          (.cons i ρ)) =
        Ausgang.leave (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hleave σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (σm : World D) (hsm : σm = σ'.lese Λ mass.orte)
      (m' : Int) (hm' : m' = (eval σm mass σm ρ).n)
      (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor)
      (σ₁ : World D) (hs₁ : σ₁ = σm.lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu₁ : List (Ereignis D))
      (hneu₁ : σ₁.spur = neu₁ ++ (M.faeden f).spur)
      (hΛ : HeldIn Λx (offen (M.faeden f).spur)) :
      RufSchrittG7 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f (neu ++ neu₁), M.start⟩
  | dannNextVerbrauch (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab)
      (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
      (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
      (inv : Expr D Γ Λ .bool) (bound : Int)
      (mass : Expr D Γ Λ (.int 0 bound))
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (rest : Nat) (vor : Int)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (restb : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λx Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λx Λx) restb)
           (.verbrauchRest t member edge inv bound mass body rest vor k)⟩)
      (σ' : World D) (ρ' : Env D (.index (D.count t) :: Γ))
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λx Λx) (M.weltVon f)
          (.cons i ρ)) =
        Ausgang.next (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hnext σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (σm : World D) (hsm : σm = σ'.lese Λ mass.orte)
      (m' : Int) (hm' : m' = (eval σm mass σm ρ'.tail).n)
      (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor)
      (neum : List (Ereignis D))
      (hneum : σm.spur = neum ++ (M.faeden f).spur)
      (hΛ : HeldIn Λx (offen (M.faeden f).spur)) :
      RufSchrittG7 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ'.tail, .verbrauch t member edge inv bound mass body
               rest k⟩⟩,
            σm.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f (neu ++ neum), M.start⟩

  /-- Evaluate once, release lexical scopes in their declared order, then
      resume the caller or leave a completed root residue. -/
  | rueckScopedWert (M : RufMaschineG D) (f : Faden)
      {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
      (r : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
      (R : RueckRessourcen D (vertragVon D (M.faeden f).kopf.f) Λ)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
      (hret : r.scopedWert = some (e, R))
      (hscope : scopesOkScopes (vertragVon D (M.faeden f).kopf.f).haelt
        (vertragVon D (M.faeden f).kopf.f).boden R.scopes = true)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (σ₁ σ₂ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (hs₂ : σ₂ = R.scopes.foldl World.gibt σ₁)
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (z : RufFadenG D)
      (hantwort : rufAntwortG (M.faeden f) σ₁ σ₂ (.inl (evalErg σ₁ e σ₁ ρ)) = some z) :
      RufSchrittG7 P O passes M f
        ⟨σ₂.speicher, rufUpdateG M.faeden f z, M.lauf ++ rufEigenG f neu, M.start⟩
  /-- The reason channel performs the same cleanup without an expression read. -/
  | rueckScopedGrund (M : RufMaschineG D) (f : Faden)
      {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
      (r : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (grund : Fin (vertragVon D (M.faeden f).kopf.f).gruende)
      (R : RueckRessourcen D (vertragVon D (M.faeden f).kopf.f) Λ)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
      (hret : r.scopedGrund = some (grund, R))
      (hscope : scopesOkScopes (vertragVon D (M.faeden f).kopf.f).haelt
        (vertragVon D (M.faeden f).kopf.f).boden R.scopes = true)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (σ₂ : World D) (hs₂ : σ₂ = R.scopes.foldl World.gibt (M.weltVon f))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (z : RufFadenG D)
      (hantwort : rufAntwortG (M.faeden f) (M.weltVon f) σ₂ (.inr grund) = some z) :
      RufSchrittG7 P O passes M f
        ⟨σ₂.speicher, rufUpdateG M.faeden f z, M.lauf ++ rufEigenG f neu, M.start⟩

end Gabbro.Grammatik
