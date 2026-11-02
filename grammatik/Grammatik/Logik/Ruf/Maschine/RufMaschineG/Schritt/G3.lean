module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Steps of `RufSchrittG`, group 3** (`dannCallInd` … `dannLeaveEwig`): the rules of the call machine G,
    verbatim; `RufSchrittG` (RufMaschineG/T2.lean) is the union of the 6 groups. -/
inductive RufSchrittG3 (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineG D → Faden → RufMaschineG D → Prop where
  | dannCallInd (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (n : Nat) (p : Expr D Γ Λ (.fnptr n))
      (args : Args D Γ Λ (D.sigNr n).params)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ)
      (hr : (D.sigNr n).gruende = 0)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ (nachSig D (D.sigNr n) Λ) Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.callInd p args hp hr) rest) k⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ (p.orte ++ args.orte))
      (g : D.Fn) (hg : D.passt g n = true)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG3 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩ ::
              (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | rufCallInd (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (p : Expr D Γ Λ (.fnptr n))
      (args : Args D Γ Λ (D.sigNr n).params)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ)
      (hr : (D.sigNr n).gruende = 0)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ
        (nachSig D (D.sigNr n) Λ))
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.cons (.callInd p args hp hr) rest)⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ (p.orte ++ args.orte))
      (g : D.Fn) (hg : D.passt g n = true)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG3 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩ ::
              (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | dannBindCall (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ)
      (hr : D.gruende g = 0)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ)
        (nach D g Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindCall g args he hp hr rest) k⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ args.orte)
      (rho : Env D (D.params g))
      (hrho : rho = evalArgs s0 args s0 ρ)
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG3 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
              (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | dannBindCallInd (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (n : Nat) (p : Expr D Γ Λ (.fnptr n))
      (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ)
      (hr : (D.sigNr n).gruende = 0)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ)
        (nachSig D (D.sigNr n) Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindCallInd p args he hp hr rest) k⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ (p.orte ++ args.orte))
      (g : D.Fn) (hg : D.passt g n = true)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG3 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩ ::
              (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | dannBindCallElse (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ)
      (hr : 0 < D.gruende g)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l
        (.why (D.gruende g) :: Γ) (nach D g Λ))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ)
        (nach D g Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindCallElse g args he hp hr err rest) k⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ args.orte)
      (rho : Env D (D.params g))
      (hrho : rho = evalArgs s0 args s0 ρ)
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG3 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ ::
              (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | rueckBind (M : RufMaschineG D) (f : Faden)
      (caller : RufRahmenG D) (rest : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rest)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
        ∃ (n : Nat) (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ),
          caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      {lr : Bool} (Γc : Ctx) (Λc : List (Res D))
      (e : ErgExpr D Γc Λc (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λc.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (ρ : Env D Γc)
      (_ : (M.faeden f).kopf.rest = ⟨lr, Γc, Λc, ρ, .ende (.ret e hperm)⟩)
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (hΛ : HeldIn Λc (offen (M.faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = (M.weltVon f).lese Λc e.orte)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (he : D.erg g = some τ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG3 P O passes M f
        ⟨s1.speicher,
         rufUpdateG M.faeden f
           ⟨rest,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
              .dann restb (.schrumpf k)⟩⟩,
            s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | dannLeaveTrav (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (is : List (Wert D (.index (D.count t))))
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λx Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λx Λx) rest)
           (.travRest t inv body is k)⟩)
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
      (σ₁ : World D) (hs₁ : σ₁ = σ'.lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu₁ : List (Ereignis D))
      (hneu₁ : σ₁.spur = neu₁ ++ (M.faeden f).spur)
      (hΛ : HeldIn Λx (offen (M.faeden f).spur)) :
      RufSchrittG3 P O passes M f
        ⟨σ₁.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f (neu ++ neu₁), M.start⟩
  | dannNextTrav (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (is : List (Wert D (.index (D.count t))))
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λx Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λx Λx) rest)
           (.travRest t inv body is k)⟩)
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
      (hΛ : HeldIn Λx (offen (M.faeden f).spur)) :
      RufSchrittG3 P O passes M f
        ⟨σ'.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ'.tail, .trav t inv body is k⟩⟩,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannLeaveWieder (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λx Λ)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λx, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λx Λx) rest)
           (.wiederRest n bis body ueber k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λx Λx) (M.weltVon f) ρ) =
        Ausgang.leave (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hleave σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (hΛ : HeldIn Λx (offen (M.faeden f).spur)) :
      RufSchrittG3 P O passes M f
        ⟨σ'.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', k⟩⟩,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannNextWieder (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (n : Nat) (bis : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ueber : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λx Λ)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λx, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λx Λx) rest)
           (.wiederRest n bis body ueber k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λx Λx) (M.weltVon f) ρ) =
        Ausgang.next (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hnext σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (hΛ : HeldIn Λx (offen (M.faeden f).spur)) :
      RufSchrittG3 P O passes M f
        ⟨σ'.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', .wieder n bis body ueber k⟩⟩,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannLeaveEwig (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λx Λ)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λx, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λx Λx) rest)
           (.ewigRest a n inv body k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λx Λx) (M.weltVon f) ρ) =
        Ausgang.leave (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hleave σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (hΛ : HeldIn Λx (offen (M.faeden f).spur)) :
      RufSchrittG3 P O passes M f
        ⟨σ'.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', k⟩⟩,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  /-- A fallible foreign call as a statement («C08»): checked sugar over
      `bindAxiomOptElse` with an empty success tail. The success value is
      discarded (`rest` runs in `Γ`); the reason branch and both return paths
      are the block form's, so no dispatch is duplicated. -/
  | dannAxiomCallElseOk (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (hr : 0 < D.agruende a)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l
        (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ
        (nachSig D (D.asignatur a) Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.axiomCallElse e a args he hp hd hgd hr err) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG3 P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, nachSig D (D.asignatur a) Λ, ρ, .dann rest k⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannAxiomCallElseGrund (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (hr : 0 < D.agruende a)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l
        (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ
        (nachSig D (D.asignatur a) Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.axiomCallElse e a args he hp hd hgd hr err) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (r : Fin (D.agruende a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inr r)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG3 P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, reasonTy (D.agruende a) :: Γ, nachSig D (D.asignatur a) Λ,
              (Env.cons (τ := reasonTy (D.agruende a)) r ρ),
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  /-- A fallible indirect call in `Block` position («C07»): the shape of
      `dannBindCallElse` over the pointer type. The pointer is evaluated once,
      the actual conforming function is called with transported arguments, and
      the caller waits in `wartetSonst` with the pointer type's channel: a
      normal return exposes the transported value to `rest`, a reason runs
      `err`. Existing pop rules (`rueckBind`, `rueckGrund`, …) resume it. -/
  | dannBindCallIndElse (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (n : Nat) (p : Expr D Γ Λ (.fnptr n))
      (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ)
      (hr : 0 < (D.sigNr n).gruende)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l
        (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ)
        (nachSig D (D.sigNr n) Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindCallIndElse p args he hp hr err rest) k⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ (p.orte ++ args.orte))
      (g : D.Fn) (hg : D.passt g n = true)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG3 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ,
               .wartetSonst (D.sigNr n).gruende err rest k⟩⟩ ::
              (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  /-- A fallible indirect call as a statement («C07»): checked sugar over
      `bindCallIndElse` with an empty success tail, fused into one push. The pointer is
      evaluated once, the actual conforming function is called with transported arguments,
      and the caller waits in `wartetSonst` with the pointer type's channel: a normal return
      runs the empty tail (the value is discarded, `rest` continues in `Γ`), a reason runs
      `err`. Existing pop rules (`rueckBind`, `rueckGrund`, …) resume it unchanged. The
      fusion keeps one dispatch and one wait: a two-step desugar would thread the block
      form's bound value through a statement that binds nothing. -/
  | dannCallIndElse (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (n : Nat) (p : Expr D Γ Λ (.fnptr n))
      (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ)
      (hr : 0 < (D.sigNr n).gruende)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l
        (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ
        (nachSig D (D.sigNr n) Λ) Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.callIndElse p args he hp hr err) rest) k⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ (p.orte ++ args.orte))
      (g : D.Fn) (hg : D.passt g n = true)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG3 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ,
               .wartetSonst (D.sigNr n).gruende err .nil (.dann rest k)⟩⟩ ::
              (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩

end Gabbro.Grammatik
