module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Steps of `RufSchrittG`, group 4** (`dannNextEwig` … `rueckGrund`): the rules of the call machine G,
    verbatim; `RufSchrittG` (RufMaschineG/T2.lean) is the union of the 6 groups. -/
inductive RufSchrittG4 (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineG D → Faden → RufMaschineG D → Prop where
  | dannNextEwig (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      {Λx : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λx Λ)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λx, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λx Λx) rest)
           (.ewigRest a n inv body k)⟩)
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
      RufSchrittG4 P O passes M f
        ⟨σ'.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', .ewig a n inv body k⟩⟩,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | peelDannLeave (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) {Λ1 Λ2 : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ1)
      (b : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ1 Λ2)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ2)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) rest) (.dann b k)⟩) :
      RufSchrittG4 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λ2, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ2 Λ2) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | peelDannNext (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) {Λ1 Λ2 : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ1)
      (b : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ1 Λ2)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ2)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) rest) (.dann b k)⟩) :
      RufSchrittG4 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λ2, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ2 Λ2) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | peelSchrumpfLeave (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) {Λ1 : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true (τ :: Γ) Λ Λ1)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ1)
      (ρ : Env D (τ :: Γ))
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, τ :: Γ, Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (τ :: Γ) Λ Λ) rest) (.schrumpf k)⟩) :
      RufSchrittG4 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ.tail,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | peelSchrumpfNext (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) {Λ1 : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true (τ :: Γ) Λ Λ1)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ1)
      (ρ : Env D (τ :: Γ))
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, τ :: Γ, Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (τ :: Γ) Λ Λ) rest) (.schrumpf k)⟩) :
      RufSchrittG4 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ.tail,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | peelFreiLeave (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (L : D.Lock) {Λ1 : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ (Res.held L :: Λ1))
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ1)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) rest) (.frei L k)⟩) :
      RufSchrittG4 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f [Ereignis.gibt L], M.start⟩
  | peelFreiNext (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (L : D.Lock) {Λ1 : List (Res D)}
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ (Res.held L :: Λ1))
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ1)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) rest) (.frei L k)⟩) :
      RufSchrittG4 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λ1, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ1 Λ1) .nil) k⟩⟩,
            Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f [Ereignis.gibt L], M.start⟩
  /-- `leave` out of an `else` branch: it reaches the continuation the
      branch was run in front of (`GRest.abbruch`, 2026-09-13). -/
  | peelAbbruchLeave (M : RufMaschineG D) (f : Faden)
      (Γ : Ctx) (Λ Λ1 Λk : List (Res D))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ1)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λk)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) rest) (.abbruch k)⟩) :
      RufSchrittG4 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λk, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λk Λk) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  /-- `next` out of an `else` branch, likewise. -/
  | peelAbbruchNext (M : RufMaschineG D) (f : Faden)
      (Γ : Ctx) (Λ Λ1 Λk : List (Res D))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ1)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λk)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) rest) (.abbruch k)⟩) :
      RufSchrittG4 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λk, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λk Λk) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | dannRet (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D))
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λ.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.ret e hperm) rest) k⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rst)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = (M.weltVon f).lese Λ e.orte)
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ (M.faeden f).spur)
      (hnw : caller.wartend = false) :
      RufSchrittG4 P O passes M f
        ⟨s1.speicher,
         rufUpdateG M.faeden f
           ⟨rst, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | rueckCons (M : RufMaschineG D) (f : Faden)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rst) {lr : Bool}
      (Γ : Ctx) (Λ : List (Res D))
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λ.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) lr Γ Λ)
      (ρ : Env D Γ)
      (_ : (M.faeden f).kopf.rest =
        ⟨lr, Γ, Λ, ρ, .ende (.cons (.ret e hperm) rest)⟩)
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = (M.weltVon f).lese Λ e.orte)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ (M.faeden f).spur)
      (hnw : caller.wartend = false) :
      RufSchrittG4 P O passes M f
        ⟨s1.speicher,
         rufUpdateG M.faeden f
           ⟨rst, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩

  | dannRetBind (M : RufMaschineG D) (f : Faden)
      (lk : Bool) (Γk : Ctx) (Λk Λk'' : List (Res D))
      (e : ErgExpr D Γk Λk (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λk.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (restk : Block D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk Λk'')
      (kk : GRest D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk'')
      (ρ : Env D Γk)
      (hhead : (M.faeden f).kopf.rest =
        ⟨lk, Γk, Λk, ρ, .dann (.cons (.ret e hperm) restk) kk⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rst)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
        ∃ (n : Nat) (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ),
          caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      (hΛ : HeldIn Λk (offen (M.faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = (M.weltVon f).lese Λk e.orte)
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (he : D.erg g = some τ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG4 P O passes M f
        ⟨s1.speicher,
         rufUpdateG M.faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
              .dann restb (.schrumpf k)⟩⟩,
            s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | rueckConsBind (M : RufMaschineG D) (f : Faden)
      (lk : Bool) (Γk : Ctx) (Λk : List (Res D))
      (e : ErgExpr D Γk Λk (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λk.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (restk : Endblock D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk)
      (ρ : Env D Γk)
      (hhead : (M.faeden f).kopf.rest =
        ⟨lk, Γk, Λk, ρ, .ende (.cons (.ret e hperm) restk)⟩)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rst)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
        ∃ (n : Nat) (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ),
          caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩)
      (hΛ : HeldIn Λk (offen (M.faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = (M.weltVon f).lese Λk e.orte)
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (he : D.erg g = some τ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG4 P O passes M f
        ⟨s1.speicher,
         rufUpdateG M.faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
              .dann restb (.schrumpf k)⟩⟩,
            s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩

  /- The error channel of `let x = g(…) else { err }`: a callee that answers
     a reason (`retGrund r`, from `ende`, an `ende` cons head, or a block)
     pops into its caller waiting in `wartetSonst`, which runs `err` with
     `r` bound -- exactly `execBlock`'s `.why σ' r` arm. The pop reads
     nothing (`execEnd`/`execStmt` of `retGrund` read nothing) and logs
     `grund`. -/
  | rueckGrund (M : RufMaschineG D) (f : Faden)
      {lk : Bool} {Γk : Ctx} {Λk : List (Res D)}
      (r : Fin (vertragVon D (M.faeden f).kopf.f).gruende)
      (hperm : Λk.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (ρ : Env D Γk)
      (hhead : (M.faeden f).kopf.rest = ⟨lk, Γk, Λk, ρ, .ende (.retWhy r hperm)⟩)
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
      RufSchrittG4 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            (M.faeden f).spur,
            (RufEreignisF.why g rho rg s0 (M.weltVon f)) :: (M.faeden f).log⟩,
         M.lauf, M.start⟩

end Gabbro.Grammatik
