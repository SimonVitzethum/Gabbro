module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Steps of `RufSchrittG`, group 5** (`rueckConsGrund` … `dannBindAxiomElseGrund`): the rules of the call machine G,
    verbatim; `RufSchrittG` (RufMaschineG/T2.lean) is the union of the 6 groups. -/
inductive RufSchrittG5 (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineG D → Faden → RufMaschineG D → Prop where
  | rueckConsGrund (M : RufMaschineG D) (f : Faden)
      {lk : Bool} {Γk : Ctx} {Λk : List (Res D)}
      (r : Fin (vertragVon D (M.faeden f).kopf.f).gruende)
      (hperm : Λk.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (restk : Endblock D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk)
      (ρ : Env D Γk)
      (hhead : (M.faeden f).kopf.rest =
        ⟨lk, Γk, Λk, ρ, .ende (.cons (.retWhy r hperm) restk)⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rst)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      (hΛ : HeldIn Λk (offen (M.faeden f).spur))
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (rg : Fin (D.gruende g)) (hrg : rg = hfg ▸ r)
      (hn : D.gruende g = n) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            (M.faeden f).spur,
            (RufEreignisF.why g rho rg s0 (M.weltVon f)) :: (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | dannRetGrund (M : RufMaschineG D) (f : Faden)
      {lk : Bool} {Γk : Ctx} {Λk Λk'' : List (Res D)}
      (r : Fin (vertragVon D (M.faeden f).kopf.f).gruende)
      (hperm : Λk.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (restk : Block D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk Λk'')
      (kk : GRest D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk'')
      (ρ : Env D Γk)
      (hhead : (M.faeden f).kopf.rest =
        ⟨lk, Γk, Λk, ρ, .dann (.cons (.retWhy r hperm) restk) kk⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rst)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      (hΛ : HeldIn Λk (offen (M.faeden f).spur))
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (rg : Fin (D.gruende g)) (hrg : rg = hfg ▸ r)
      (hn : D.gruende g = n) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            (M.faeden f).spur,
            (RufEreignisF.why g rho rg s0 (M.weltVon f)) :: (M.faeden f).log⟩,
         M.lauf, M.start⟩

  | dannRegLies (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.regRead r hk rest) k⟩)
      (v : Wert D (D.rtyp r))
      (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (.inr (.inl r)))) = some v)
      (hz : D.rzusage r v = true)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, D.rtyp r :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            Ereignis.fremd (.inr (.inl r)) :: (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f [Ereignis.fremd (.inr (.inl r))], M.start⟩
  | dannRegLiesElseWahr (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool)
      (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.regReadElse r hk zusage sonst rest) k⟩)
      (v : Wert D (D.rtyp r))
      (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (.inr (.inl r)))) = some v)
      (σ₁ : World D) (hs₁ : σ₁ = ((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte)
      (hw : wahr? (eval σ₁ zusage σ₁ (.cons v ρ)) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, D.rtyp r :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannRegLiesElseFalsch (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool)
      (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.regReadElse r hk zusage sonst rest) k⟩)
      (v : Wert D (D.rtyp r))
      (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (.inr (.inl r)))) = some v)
      (σ₁ : World D) (hs₁ : σ₁ = ((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte)
      (hw : wahr? (eval σ₁ zusage σ₁ (.cons v ρ)) = false)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann sonst.alsBlock.2 (.abbruch k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannAwaits (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
      (hL : gdarf D g Λ) (hat : D.atomar g = true)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (D.gtyp g :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.awaits g payload hp hL hat rest) k⟩)
      (hvis : O.sichtbar g ((M.weltVon f).fragt (.inr (.inr g))) = true)
      (σ₁ : World D) (hs₁ : σ₁ = ((M.weltVon f).fragt (.inr (.inr g))).lese Λ [.inr g])
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, D.gtyp g :: Γ, Λ, .cons (σ₁.globs g) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannExchange (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (g : D.Glob) (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
      (hw : (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
      (hL : gdarf D g Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (D.gtyp g :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.exchange g neuE hw hL rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ (.inr g :: neuE.orte))
      (σ₂ : World D)
      (hs₂ : σ₂ = σ₁.schreibGlob g Λ (eval σ₁ neuE σ₁ (.cons (σ₁.globs g) ρ)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, D.gtyp g :: Γ, Λ, .cons (σ₁.globs g) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannGleit (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (l₁ h₁ l₂ h₂ : Int × Int)
      (op : GleitOp) (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂))
      (lo hi : Int × Int)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.float op a b lo hi rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ (a.orte ++ b.orte))
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi
        (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) = some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannGleitLit (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (q lo hi : Int × Int)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.floatLit q lo hi rest) k⟩)
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi (bruch q) = some v) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | dannGleitVon (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (l₁ h₁ : Int)
      (e : Expr D Γ Λ (.int l₁ h₁)) (lo hi : Int × Int)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.floatOf e lo hi rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) = some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannGleitNarrowOk (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (l₁ h₁ : Int × Int)
      (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
      (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.floatNarrow e lo hi sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x = some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannGleitNarrowElse (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (l₁ h₁ : Int × Int)
      (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
      (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.floatNarrow e lo hi sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (hn : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x = none)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann sonst.alsBlock.2 (.abbruch k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannBindAxiom (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindAxiom a args he hw hg hd hgd rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some v))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩

  /-- A fallible foreign call (C-free lane, 2026-09-30) answers a value: the rest runs with it. -/
  | dannBindAxiomElseOk
      (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindAxiomElse a args he hr hw hg hd hgd err rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .dann rest (.schrumpf k)⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  /-- It answers a reason: the `else` block runs with it bound, in block position (as `rueckGrund` for a call). -/
  | dannBindAxiomElseGrund
      (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindAxiomElse a args he hr hw hg hd hgd err rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (r : Fin (D.agruende a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inr r)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG5 P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .why (D.agruende a) :: Γ, Λ, (Env.cons (τ := .why (D.agruende a)) r ρ), .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩

end Gabbro.Grammatik
