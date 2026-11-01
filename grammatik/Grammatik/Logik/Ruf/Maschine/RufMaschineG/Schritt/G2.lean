module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Steps of `RufSchrittG`, group 2** (`dannNarrowElse` … `rufDann`): the rules of the call machine G,
    verbatim; `RufSchrittG` (RufMaschineG/T2.lean) is the union of the 6 groups. -/
inductive RufSchrittG2 (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineG D → Faden → RufMaschineG D → Prop where
  | dannNarrowElse (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (lo hi lo' hi' : Int)
      (e : Expr D Γ Λ (.int lo hi))
      (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (.int lo' hi' :: Γ)
        Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.narrow e lo' hi' sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (h : ¬ (lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'))
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann sonst.alsBlock.2 (.abbruch k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannPruefWahr (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (c : Expr D Γ Λ .bool)
      (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.check c sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ c.orte)
      (hw : wahr? (eval σ₁ c σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann rest k⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannPruefFalsch (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (c : Expr D Γ Λ .bool)
      (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.check c sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ c.orte)
      (hw : wahr? (eval σ₁ c σ₁ ρ) = false)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann sonst.alsBlock.2 (.abbruch k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannBreaking (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (i : D.Inv)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.breaking i body) rest) k⟩) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann body (.dann rest k)⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | dannLocks (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D))
      (L : D.Lock)
      (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) l Γ
        (Res.held L :: Λ) (Res.held L :: Λ))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hr body) rest) k⟩)
      (hself : L ∉ offen (M.faeden f).spur)
      (hrang : ∀ K ∈ offen (M.faeden f).spur, D.rang K < D.rang L)
      (hfrei : RufFreiG M f L) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Res.held L :: Λ, ρ,
              .dann body (.frei L (.dann rest k))⟩⟩,
            Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
            (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f [Ereignis.nimmt L (offen (M.faeden f).spur)],
         M.start⟩
  | freiGib (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (L : D.Lock)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Res.held L :: Λ, ρ, .frei L k⟩) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f [Ereignis.gibt L], M.start⟩
  | schrumpfVergiss (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (v : Wert D τ) (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, τ :: Γ, Λ, .cons v ρ, .schrumpf k⟩) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | dannTrav (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.traverse t inv body) rest) k⟩) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ,
              .trav t inv body (alleIndizes (D.count t)) (.dann rest k)⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | travNext (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (i : Wert D (.index (D.count t)))
      (is : List (Wert D (.index (D.count t))))
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .trav t inv body (i :: is) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ,
              .dann body (.travRest t inv body is k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | travFort (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (is : List (Wert D (.index (D.count t))))
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ,
         .travRest t inv body is k⟩) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .trav t inv body is k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | travDone (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .trav t inv body [] k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannRetry (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.retry n bis body ueber) rest) k⟩) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .wieder n bis body ueber (.dann rest k)⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  /-- The budget is spent: `bis` is checked once more, as an `if` over the
      overflow block (a pass that made `bis` true is a success) -- the
      sequential `retryLauf`'s `0` case, corrected 2026-09-13. -/
  | wiederUeber (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .wieder 0 bis body ueber k⟩) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann (.cons (.ite bis .nil ueber) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | wiederWeiter (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .wieder (n + 1) bis body ueber k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ bis.orte)
      (hw : wahr? (eval σ₁ bis σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | wiederSchritt (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .wieder (n + 1) bis body ueber k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ bis.orte)
      (hw : wahr? (eval σ₁ bis σ₁ ρ) = false)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λ, ρ,
              .dann body (.wiederRest n bis body ueber k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | wiederFort (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ, .wiederRest n bis body ueber k⟩) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .wieder n bis body ueber k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | dannForever (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (a : D.Annahme) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.forever a inv body) rest) k⟩) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .ewig a passes inv body (.dann rest k)⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | ewigWeiter (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ewig a (n + 1) inv body k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λ, ρ,
              .dann body (.ewigRest a n inv body k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | ewigFort (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ, .ewigRest a n inv body k⟩) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .ewig a n inv body k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | rufDann (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (g : D.Fn) (args : Args D Γ Λ (D.params g))
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ)
      (hr : D.gruende g = 0)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ (nach D g Λ) Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.call g args hp hr) rest) k⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ args.orte)
      (rho : Env D (D.params g))
      (hrho : rho = evalArgs s0 args s0 ρ)
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG2 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩

end Gabbro.Grammatik
