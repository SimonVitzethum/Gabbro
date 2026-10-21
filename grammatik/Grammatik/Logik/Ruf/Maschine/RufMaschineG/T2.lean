/- Part 2 of 7 of `RufMaschineG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufMaschineG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **One step of the call machine with compound statements.** `blatt`,
    `ruf`, `rueck` are the F steps (residues wrapped in `GRest.ende`); the
    `dann*`/`ende*`/`frei`/`trav`/`wieder`/`ewig` steps unfold compounds
    into the continuation residue. Reads go through the read world
    `(weltVon).lese Λ orte` exactly as `execStmt` reads them.

    Lock discipline (repaired 2026-09-13): a lock is taken ONLY by the
    `locks` unfold (`dannLocks`) and released ONLY by its release marker
    (`freiGib`, and the `frei` peels of `leave`/`next`) -- the structured
    `locks L { … }` of the surface language. The bare `nimmt`/`gibt` steps
    of the old PC machine (take or release any lock at any time) are gone;
    a start thread holds its signature locks from the start machine on
    (`RufStartG`). Every step that reads the thread world (`weltVon`, a
    `lese`) or writes memory demands `HeldIn` of the head's static
    holdings: every lock they name is held. (Until the held-set relaxation of
    2026-09-13 it demanded `HeldGenau`, EQUAL sets; a callee now runs under
    the extra locks of its caller -- `RufPasst.hh` is `⊆` -- and those are
    held by the thread but not named by the callee frame.) Hence "static
    holdings ⊆ held locks" is an invariant of every run
    (`rufG_haelt_statisch`), and the side condition always holds. -/
inductive RufSchrittG (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineG D → Faden → RufMaschineG D → Prop where
  | blatt (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (σ' : World D) (ρ' : Env D Γ) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ) =
        Ausgang.ok (D := D) (V := vertragVon D (M.faeden f).kopf.f) σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
      RufSchrittG P O passes M f
        ⟨σ'.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ', ρ', .ende rest⟩⟩,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | ruf (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (g : D.Fn) (args : Args D Γ Λ (D.params g))
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ)
      (hr : D.gruende g = 0)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ (nach D g Λ))
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.cons (.call g args hp hr) rest)⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ args.orte)
      (rho : Env D (D.params g))
      (hrho : rho = evalArgs s0 args s0 ρ)
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩ :: (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | rueck (M : RufMaschineG D) (f : Faden)
      (caller : RufRahmenG D) (rest : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rest) {lr : Bool}
      (Γ : Ctx) (Λ : List (Res D))
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λ.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (ρ : Env D Γ)
      (_ : (M.faeden f).kopf.rest = ⟨lr, Γ, Λ, ρ, .ende (.ret e hperm)⟩)
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
      RufSchrittG P O passes M f
        ⟨s1.speicher,
         rufUpdateG M.faeden f
           ⟨rest, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | endeEntf (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hent : GEntfaltbar s = true)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann (.cons s .nil) (.ende rest)⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  /-- An end-block former that is not a statement (`EndEntfaltbar`) is unfolded into BLOCK
      position, as the `else` branches are (Track P, 2026-10-18): the block steps then run it. -/
  | endeForm (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (e : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hl : l = false)
      (hent : EndEntfaltbar e = true)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende e⟩) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | dannBlatt (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons s rest) k⟩)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur))
      (σ' : World D) (ρ' : Env D Γ) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ) =
        Ausgang.ok (D := D) (V := vertragVon D (M.faeden f).kopf.f) σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
      RufSchrittG P O passes M f
        ⟨σ'.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ', ρ', .dann rest k⟩⟩,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannLeer (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann .nil k⟩) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | dannIteWahr (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (c : Expr D Γ Λ .bool)
      (t e : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.ite c t e) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ c.orte)
      (hw : wahr? (eval σ₁ c σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann t (.dann rest k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannIteFalsch (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (c : Expr D Γ Λ .bool)
      (t e : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.ite c t e) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ c.orte)
      (hw : wahr? (eval σ₁ c σ₁ ρ) = false)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann e (.dann rest k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannOnOptionSome (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Int)
      (o : Expr D Γ Λ (.opt n))
      (p : Block D (vertragVon D (M.faeden f).kopf.f) l (.index n :: Γ) Λ Λ')
      (a : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.onOption o p a) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ o.orte)
      (v : Wert D (.index n)) (hv : eval σ₁ o σ₁ ρ = Option.some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .index n :: Γ, Λ, .cons v ρ,
              .dann p (.schrumpf (.dann rest k))⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannOnOptionNone (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Int)
      (o : Expr D Γ Λ (.opt n))
      (p : Block D (vertragVon D (M.faeden f).kopf.f) l (.index n :: Γ) Λ Λ')
      (a : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.onOption o p a) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ o.orte)
      (hv : eval σ₁ o σ₁ ρ = Option.none)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann a (.dann rest k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannOnTagSome (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (cs : List (Option (Int × Int)))
      (v : Expr D Γ Λ (.sum cs))
      (arms : Arms D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ' cs)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.onTag v arms) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ v.orte)
      (lo hi : Int)
      (b : Block D (vertragVon D (M.faeden f).kopf.f) l (.int lo hi :: Γ) Λ Λ')
      (nutz : Nutzlast (some (lo, hi)))
      (hw : armWahlG arms (eval σ₁ v σ₁ ρ) = ⟨some (lo, hi), b, nutz⟩)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .int lo hi :: Γ, Λ, armEnv nutz ρ,
              .dann b (.schrumpf (.dann rest k))⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannOnTagNone (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (cs : List (Option (Int × Int)))
      (v : Expr D Γ Λ (.sum cs))
      (arms : Arms D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ' cs)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.onTag v arms) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ v.orte)
      (b : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (nutz : Nutzlast none)
      (hw : armWahlG arms (eval σ₁ v σ₁ ρ) = ⟨none, b, nutz⟩)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, armEnv nutz ρ, .dann b (.dann rest k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannOnGrund (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Nat)
      (r : Expr D Γ Λ (.why n))
      (arms : GrundArms D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ' n)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.onWhy r arms) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ r.orte)
      (b : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (hw : grundWahlG arms (eval σ₁ r σ₁ ρ) = b)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann b (.dann rest k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | endeBind (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (e : Expr D Γ Λ τ)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bind e rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (eval σ₁ e σ₁ ρ) ρ, .ende rest⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  /-- `let x = g(…);` of a foreign body at the top level of a body (C-free lane,
      2026-09-30): `dannBindAxiom` with an end-block rest, which runs on as `.ende`. -/
  | endeBindAxiom (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiom a args he hw hg hd hgd rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some v))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .ende rest⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannBind (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (e : Expr D Γ Λ τ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bind e rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (eval σ₁ e σ₁ ρ) ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannNarrowOk (M : RufMaschineG D) (f : Faden)
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
      (h : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi')
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .int lo' hi' :: Γ, Λ,
              .cons ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩ ρ,
              .dann rest (.schrumpf k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      (g : D.Fn) (hg : D.sig g = n)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
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
      (g : D.Fn) (hg : D.sig g = n)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      (g : D.Fn) (hg : D.sig g = n)
      (hv : eval s0 p s0 ρ = ⟨g, hg⟩)
      (rho : Env D (D.params g))
      (hrho : rho = umsig hg (evalArgs s0 args s0 ρ))
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
        ⟨σ'.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', k⟩⟩,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨rst,
            ⟨caller.f, caller.rho, caller.s0,
             ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            (M.faeden f).spur,
            (RufEreignisF.why g rho rg s0 (M.weltVon f)) :: (M.faeden f).log⟩,
         M.lauf, M.start⟩
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (M.weltVon f)) = some v)
      (hz : D.rzusage r v = true)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, D.rtyp r :: Γ, Λ, .cons v ρ,
              .dann rest (.schrumpf k)⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
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
      (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (M.weltVon f)) = some v)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ zusage.orte)
      (hw : wahr? (eval σ₁ zusage σ₁ (.cons v ρ)) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
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
      (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (M.weltVon f)) = some v)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ zusage.orte)
      (hw : wahr? (eval σ₁ zusage σ₁ (.cons v ρ)) = false)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
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
      (hvis : O.sichtbar g (M.weltVon f) = true)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ [.inr g])
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
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
      RufSchrittG P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .why (D.agruende a) :: Γ, Λ, (Env.cons (τ := .why (D.agruende a)) r ρ), .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  /-- The same at the top level of a body: a value. -/
  | endeBindAxiomElseOk
      (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomElse a args he hr hw hg hd hgd err rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .ende rest⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  /-- The same at the top level of a body: a reason. -/
  | endeBindAxiomElseGrund
      (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomElse a args he hr hw hg hd hgd err rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (r : Fin (D.agruende a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inr r)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .why (D.agruende a) :: Γ, Λ, (Env.cons (τ := .why (D.agruende a)) r ρ), .ende err⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩


end Gabbro.Grammatik
