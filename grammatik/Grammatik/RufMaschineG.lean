/-
  File:      Grammatik/RufMaschineG.lean
  Subject:   THE CALL MACHINE WITH COMPOUND STATEMENTS (attempt G) -- the F
              machine (frames with stored environments, call-log fidelity
              `rufF_treu`) extended with a residue that can hold
              "block, then rest", so every compound statement form unfolds
              step by step instead of getting stuck.

  Why: `RufMaschineF.lean` steps only leaves (`blatt`), calls (`ruf`) and
  returns (`rueck`); a body with `if`, `match`, a `let` binding, a `locks`
  block or a loop cannot advance (see its CUTS). Here the frame residue is
  a `GRest`: an `Endblock` (`ende`), a `Block` followed by a rest (`dann`),
  an environment shrink (`schrumpf`), a lock release marker (`frei`), and
  bounded-loop states (`trav`/`wieder`/`ewig` with their remaining bound).
  New steps unfold compounds into that residue; none touches the call log,
  so fidelity (`rufG_treu`) follows the F proof pattern.
-/
import Grammatik.Maschine
import Grammatik.VertragOrtB
import Grammatik.RufMaschineF

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Residues with continuations -/

/-- The residue of a running frame: what is left to do. `ende` is a plain
    end block; `dann b k` runs the block `b` first, then `k`; `schrumpf`
    drops one bound value from the environment; `frei L` releases the lock
    `L` (taken by a `locks` unfold) and continues; `trav`/`wieder`/`ewig`
    are bounded loops with their remaining indices/tries/budget, each with
    a `Rest` shim that runs one body iteration at the loop context and
    then resumes the loop. -/
inductive GRest (D : Deklaration) (V : Vertrag D) : Bool → Ctx → List (Res D) → Type where
  | ende {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      Endblock D V l Γ Λ → GRest D V l Γ Λ
  | dann {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
      Block D V l Γ Λ Λ' → GRest D V l Γ Λ' → GRest D V l Γ Λ
  | schrumpf {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} :
      GRest D V l Γ Λ → GRest D V l (τ :: Γ) Λ
  | frei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      (L : D.Lock) → GRest D V l Γ Λ → GRest D V l Γ (Res.held L :: Λ)
  | trav {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
      (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
      (ks : List (Wert D (.index (D.count t)))) :
      GRest D V l Γ Λ → GRest D V l Γ Λ
  | travRest {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
      (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
      (ks : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ) :
      GRest D V true (.index (D.count t) :: Γ) Λ
  | wieder {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (n : Nat)
      (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueber : Block D V l Γ Λ Λ) :
      GRest D V l Γ Λ → GRest D V l Γ Λ
  | wiederRest {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (n : Nat)
      (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ) : GRest D V true Γ Λ
  | ewig {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme) (n : Nat)
      (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) :
      GRest D V l Γ Λ → GRest D V l Γ Λ
  | ewigRest {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme) (n : Nat)
      (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (k : GRest D V l Γ Λ) : GRest D V true Γ Λ
  | wartet {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') :
      GRest D V l Γ Λ

/-- One frame: as in F, but the residue is a `GRest`. -/
structure RufRahmenG (D : Deklaration) where
  f : D.Fn
  rho : Env D (D.params f)
  s0 : World D
  rest :
    Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
      Env D Γ × GRest D (vertragVon D f) l Γ Λ

structure RufFadenG (D : Deklaration) where
  stapel : List (RufRahmenG D)
  kopf : RufRahmenG D
  spur : List (Ereignis D)
  log : List (RufEreignisF D)

structure RufMaschineG (D : Deklaration) where
  speicher : Speicher D
  faeden : Faden → RufFadenG D
  lauf : Lauf D
  start : World D

/-- The current world of thread `f`: live shared memory plus its own trace. -/
def RufMaschineG.weltVon (M : RufMaschineG D) (f : Faden) : World D :=
  M.speicher.welt (M.faeden f).spur

/-- No thread other than `f` holds `L` right now -- the scheduler rule side. -/
def RufFreiG (M : RufMaschineG D) (f : Faden) (L : D.Lock) : Prop :=
  ∀ g, g ≠ f → L ∉ offen (M.faeden g).spur

/-- The new run events of one step, all attributed to the acting thread. -/
def rufEigenG (f : Faden) (neu : List (Ereignis D)) : Lauf D :=
  neu.reverse.map fun e => Schritt.mk f e

/-- One thread state replaced, all others kept. -/
def rufUpdateG (m : Faden → RufFadenG D) (f : Faden) (z : RufFadenG D) :
    Faden → RufFadenG D :=
  fun g => if g = f then z else m g

theorem rufUpdateG_self (m : Faden → RufFadenG D) (f : Faden) (z : RufFadenG D) :
    rufUpdateG m f z f = z := by
  simp [rufUpdateG]

theorem rufUpdateG_noteq (m : Faden → RufFadenG D) (f g : Faden) (h : g ≠ f)
    (z : RufFadenG D) :
    rufUpdateG m f z g = m g := by
  simp [rufUpdateG, h]

/-! ## 2. Which compounds unfold -/

/-- Compounds with an unfold step: `ite`, `onOption`, `onTag`, `onGrund`,
    `locks`, `breaking` and the bounded loops. `call`/`callInd` are excluded
    (the `ruf`/`rufDann` and `callInd` steps handle them); the bind-call and
    register/atomic/float `Block` forms have their own `dann` steps. -/
def GEntfaltbar {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite .. => true
  | .onOption .. => true
  | .onTag .. => true
  | .onGrund .. => true
  | .locks .. => true
  | .breaking .. => true
  | .traverse .. => true
  | .retry .. => true
  | .forever .. => true
  | _ => false

/-- Arm selection for `onTag`: the VALUE's index chooses the arm and the
    VALUE's payload feeds it (like `execArms`, but returning the chosen arm
    instead of running it). The `nil` case cannot fire (`Fin 0` is empty). -/
def armWahlG {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → Wert D (.sum cs) →
      Σ c : Option (Int × Int), Block D V l (ArmCtx Γ c) Λ Λ' × Nutzlast c
  | .nil, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨⟨0, _⟩, nutz⟩ => ⟨_, b, nutz⟩
  | .cons _ rest, ⟨⟨n + 1, h⟩, nutz⟩ =>
      armWahlG rest ⟨⟨n, Nat.lt_of_succ_lt_succ h⟩, by simpa using nutz⟩

/-- Arm selection for `onGrund`: the VALUE's index chooses the arm
    (like `execGrund`, but returning the chosen arm instead of running it). -/
def grundWahlG {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Fin n → Block D V l Γ Λ Λ'
  | .nil, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨0, _⟩ => b
  | .cons _ rest, ⟨k + 1, h⟩ =>
      grundWahlG rest ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-! ## 3. The step relation: F steps plus compound unfolds -/

/-- **One step of the call machine with compound statements.** `blatt`,
    `nimmt`, `gibt`, `ruf`, `rueck` are the F steps (residues wrapped in
    `GRest.ende`); the `dann*`/`ende*`/`frei`/`trav`/`wieder`/`ewig` steps
    unfold compounds into the continuation residue. Reads go through the
    read world `(weltVon).lese Λ orte` exactly as `execStmt` reads them. -/
inductive RufSchrittG (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineG D → Faden → RufMaschineG D → Prop where
  | blatt (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
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
  | nimmt (M : RufMaschineG D) (f : Faden) (L : D.Lock)
      (hself : L ∉ offen (M.faeden f).spur)
      (hrang : ∀ K ∈ offen (M.faeden f).spur, D.rang K < D.rang L)
      (hfrei : RufFreiG M f L) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel, (M.faeden f).kopf,
            Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
            (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f [Ereignis.nimmt L (offen (M.faeden f).spur)],
         M.start⟩
  | gibt (M : RufMaschineG D) (f : Faden) (L : D.Lock)
      (hhaelt : L ∈ offen (M.faeden f).spur) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel, (M.faeden f).kopf,
            Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f [Ereignis.gibt L], M.start⟩
  | ruf (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (g : D.Fn) (args : Args D Γ Λ (D.params g))
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ)
      (hr : D.gruende g = 0)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ (nach D g Λ))
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.cons (.call g args hp hr) rest)⟩)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ args.orte)
      (rho : Env D (D.params g))
      (hrho : rho = evalArgs s0 args s0 ρ)
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).kopf :: (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, .ende (P.rumpf g)⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | rueck (M : RufMaschineG D) (f : Faden)
      (caller : RufRahmenG D) (rest : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rest)
      (Γ : Ctx) (Λ : List (Res D))
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λ.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (ρ : Env D Γ)
      (_ : (M.faeden f).kopf.rest = ⟨false, Γ, Λ, ρ, .ende (.ret e hperm)⟩)
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = (M.weltVon f).lese Λ e.orte)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ (M.faeden f).spur) :
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
  | dannBlatt (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons s rest) k⟩)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (r : Expr D Γ Λ (.grund n))
      (arms : GrundArms D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ' n)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.onGrund r arms) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ r.orte)
      (b : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (hw : grundWahlG arms (eval σ₁ r σ₁ ρ) = b)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (eval σ₁ e σ₁ ρ) ρ, .ende rest⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannBind (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty)
      (e : Expr D Γ Λ τ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bind e rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .ende sonst⟩⟩,
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
        ⟨l, Γ, Λ, ρ, .dann (.pruefung c sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ c.orte)
      (hw : wahr? (eval σ₁ c σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
        ⟨l, Γ, Λ, ρ, .dann (.pruefung c sonst rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ c.orte)
      (hw : wahr? (eval σ₁ c σ₁ ρ) = false)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .ende sonst⟩⟩,
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
  | dannTravWeiter (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.traverse t inv body) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ,
              .trav t inv body (alleIndizes (D.count t)) (.dann rest k)⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | dannTravFertig (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D))
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.cons (.traverse t inv body) rest) k⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = false)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .dann rest k⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
        ⟨l, Γ, Λ, ρ, .trav t inv body [] k⟩) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
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
             ⟨l, Γ, Λ, ρ, .dann ueber k⟩⟩,
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) :
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
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
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
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
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
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
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
           ⟨(M.faeden f).kopf :: (M.faeden f).stapel,
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
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
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
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
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
        (.grund (D.gruende g) :: Γ) (nach D g Λ))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ)
        (nach D g Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindCallElse g args he hp hr err rest) k⟩)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
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
  | rueckBind (M : RufMaschineG D) (f : Faden)
      (caller : RufRahmenG D) (rest : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rest)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ')
      (ρc : Env D Γ)
      (hcaller : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩)
      (Γc : Ctx) (Λc : List (Res D))
      (e : ErgExpr D Γc Λc (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λc.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (ρ : Env D Γc)
      (_ : (M.faeden f).kopf.rest = ⟨false, Γc, Λc, ρ, .ende (.ret e hperm)⟩)
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (hΛ : HeldGenau Λc (offen (M.faeden f).spur))
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
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λ Λ) rest)
           (.travRest t inv body is k)⟩)
      (σ' : World D) (ρ' : Env D (.index (D.count t) :: Γ))
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λ Λ) (M.weltVon f)
          (.cons i ρ)) =
        Ausgang.leave (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hleave σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (σ₁ : World D) (hs₁ : σ₁ = σ'.lese Λ inv.orte)
      (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
      (neu₁ : List (Ereignis D))
      (hneu₁ : σ₁.spur = neu₁ ++ (M.faeden f).spur) :
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
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true
        (.index (D.count t) :: Γ) Λ Λ)
      (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λ Λ) rest)
           (.travRest t inv body is k)⟩)
      (σ' : World D) (ρ' : Env D (.index (D.count t) :: Γ))
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true (.index (D.count t) :: Γ) Λ Λ) (M.weltVon f)
          (.cons i ρ)) =
        Ausgang.next (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hnext σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
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
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) rest)
           (.wiederRest n bis body ueber k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) (M.weltVon f) ρ) =
        Ausgang.leave (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hleave σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
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
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) rest)
           (.wiederRest n bis body ueber k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) (M.weltVon f) ρ) =
        Ausgang.next (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hnext σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
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
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) rest)
           (.ewigRest a n inv body k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) (M.weltVon f) ρ) =
        Ausgang.leave (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hleave σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
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
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) rest)
           (.ewigRest a n inv body k)⟩)
      (σ' : World D) (ρ' : Env D Γ)
      (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf
          ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ Λ Λ) (M.weltVon f) ρ) =
        Ausgang.next (D := D) (V := vertragVon D (M.faeden f).kopf.f)
          hnext σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
      RufSchrittG P O passes M f
        ⟨σ'.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ', .ewig a n inv body k⟩⟩,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩

  | peelDannLeave (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (b : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)
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
             ⟨true, Γ, Λ, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | peelDannNext (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (b : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)
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
             ⟨true, Γ, Λ, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | peelSchrumpfLeave (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true (τ :: Γ) Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)
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
             ⟨true, Γ, Λ, ρ.tail,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | peelSchrumpfNext (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true (τ :: Γ) Λ Λ)
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)
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
             ⟨true, Γ, Λ, ρ.tail,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ) .nil) k⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | peelFreiLeave (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (L : D.Lock)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ
        (Res.held L :: Λ) (Res.held L :: Λ))
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)
      (ρ : Env D Γ)
      (hleave : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Res.held L :: Λ, ρ,
         .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ (Res.held L :: Λ) (Res.held L :: Λ)) rest) (.frei L k)⟩) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λ, ρ,
              .dann (.cons ((.leave hleave) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ) .nil) k⟩⟩,
            Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f [Ereignis.gibt L], M.start⟩
  | peelFreiNext (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (L : D.Lock)
      (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ
        (Res.held L :: Λ) (Res.held L :: Λ))
      (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)
      (ρ : Env D Γ)
      (hnext : true = true)
      (hhead : (M.faeden f).kopf.rest =
        ⟨true, Γ, Res.held L :: Λ, ρ,
         .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden f).kopf.f)
            true Γ (Res.held L :: Λ) (Res.held L :: Λ)) rest) (.frei L k)⟩) :
      RufSchrittG P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨true, Γ, Λ, ρ,
              .dann (.cons ((.next hnext) : Stmt D
                (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ) .nil) k⟩⟩,
            Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f [Ereignis.gibt L], M.start⟩
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
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = (M.weltVon f).lese Λ e.orte)
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
        ⟨s1.speicher,
         rufUpdateG M.faeden f
           ⟨rst, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩
  | rueckCons (M : RufMaschineG D) (f : Faden)
      (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (hpop : (M.faeden f).stapel = caller :: rst)
      (Γ : Ctx) (Λ : List (Res D))
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λ.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) false Γ Λ)
      (ρ : Env D Γ)
      (_ : (M.faeden f).kopf.rest =
        ⟨false, Γ, Λ, ρ, .ende (.cons (.ret e hperm) rest)⟩)
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = (M.weltVon f).lese Λ e.orte)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ (M.faeden f).spur) :
      RufSchrittG P O passes M f
        ⟨s1.speicher,
         rufUpdateG M.faeden f
           ⟨rst, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu,
         M.start⟩

/-! ## 4. Reachability -/

/-- The start machine: every thread in its entry frame with the entry
    environment and an `ende` residue over the function body. -/
def RufStartG (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    RufMaschineG D :=
  ⟨sp, fun f =>
    let ⟨g, rho⟩ := init f
    ⟨[], ⟨g, rho, sp.welt [],
      ⟨false, D.params g, Signatur.anfang D (D.signatur g),
       rho, .ende (P.rumpf g)⟩⟩,
     [], [RufEreignisF.eintritt g rho (sp.welt [])]⟩,
   [], sp.welt []⟩

/-- Reachable machines, generated from `M0` by the step relation. -/
inductive RufErreichbarG (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : RufMaschineG D) : RufMaschineG D → Prop where
  | start : RufErreichbarG P O passes M0 M0
  | schritt (M M' : RufMaschineG D) (f : Faden)
      (h : RufErreichbarG P O passes M0 M) (hs : RufSchrittG P O passes M f M') :
      RufErreichbarG P O passes M0 M'

/-! ## 5. Matching entries and returns: the call-log invariant -/

/-- The key of a frame: function, actual parameters, entry world.
    Residue and local context are NOT part of the key. -/
def RufSchluesselG (r : RufRahmenG D) :
    Σ f : D.Fn, Env D (D.params f) × World D :=
  ⟨r.f, r.rho, r.s0⟩

/-- The key stack of a thread: head frame first. -/
def RufFadenSchluesselG (z : RufFadenG D) :
    List (Σ f : D.Fn, Env D (D.params f) × World D) :=
  (z.kopf :: z.stapel).map RufSchluesselG

/-- A log matches its key stack. -/
inductive RufLogPasstG :
    List (Σ f : D.Fn, Env D (D.params f) × World D) →
    List (RufEreignisF D) → Prop where
  | leer : RufLogPasstG [] []
  | eintritt (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
      (log : List (RufEreignisF D))
      (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
      (h : RufLogPasstG ks log) :
      RufLogPasstG (⟨f, rho, s0⟩ :: ks)
        (RufEreignisF.eintritt f rho s0 :: log)
  | rueck (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
      (log : List (RufEreignisF D))
      (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
      (v : ErgVal D (D.erg f)) (s1 : World D)
      (h : RufLogPasstG (⟨f, rho, s0⟩ :: ks) log) :
      RufLogPasstG ks
        (RufEreignisF.rueck f rho v s0 s1 :: log)

/-- A thread state satisfies the invariant: its log matches its key stack. -/
def RufFadenPasstG (z : RufFadenG D) : Prop :=
  RufLogPasstG (RufFadenSchluesselG z) z.log

/-- A `rueck` entry in the log carries matched data. -/
def rufRueckGedecktG (log : List (RufEreignisF D)) : Prop :=
  ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g))
    (s0 s1 : World D),
    RufEreignisF.rueck g rho v s0 s1 ∈ log →
      RufEreignisF.eintritt g rho s0 ∈ log

/-- Auxiliary: every key ON the stack has its entry in the log. Every
    premise is used: `hmem` selects the stack side in each case. -/
theorem rufLogPasstG_mem_eintritt
    (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (log : List (RufEreignisF D)) (h : RufLogPasstG ks log)
    (k : Σ f : D.Fn, Env D (D.params f) × World D) (hmem : k ∈ ks) :
    RufEreignisF.eintritt k.1 k.2.1 k.2.2 ∈ log := by
  induction h with
  | leer =>
      simp at hmem
  | eintritt s l f rho s0 htail ih =>
      rw [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · subst hmem
        exact List.mem_cons_self
      · have htailmem := ih hmem
        exact List.mem_cons_of_mem _ htailmem
  | rueck s l f rho s0 vv ss1 htail ih =>
      have htailmem := ih (List.mem_cons_of_mem _ hmem)
      exact List.mem_cons_of_mem _ htailmem

/-- Every well-formed log stack ends in the matching entry. -/
theorem rufLogPasstG_eintritt_mem
    (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (log : List (RufEreignisF D)) (h : RufLogPasstG ks log)
    (k : Σ f : D.Fn, Env D (D.params f) × World D)
    (rest : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (hcon : ks = k :: rest) :
    RufEreignisF.eintritt k.1 k.2.1 k.2.2 ∈ log := by
  have hmem : k ∈ ks := by rw [hcon]; exact List.mem_cons_self
  exact rufLogPasstG_mem_eintritt ks log h k hmem

/-- Every well-formed log has matched returns. -/
theorem rufLogPasstG_gedeckt
    (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (log : List (RufEreignisF D)) (h : RufLogPasstG ks log) :
    rufRueckGedecktG log := by
  induction h with
  | leer =>
      intro f rho v s0 s1 hm
      simp at hm
  | eintritt ks log f rho s0 htail ih =>
      intro g rho' v s0' s1 hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp at hm
      · have hmem := ih g rho' v s0' s1 hm
        rw [List.mem_cons]
        exact Or.inr hmem
  | rueck ks log f rho s0 v s1 htail ih =>
      intro g rho' w s0' s1' hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · cases hm
        have hmem : RufEreignisF.eintritt f rho s0 ∈ log :=
          rufLogPasstG_eintritt_mem (⟨f, rho, s0⟩ :: ks) log htail
            ⟨f, rho, s0⟩ ks rfl
        rw [List.mem_cons]
        exact Or.inr hmem
      · have hmem := ih g rho' w s0' s1' hm
        rw [List.mem_cons]
        exact Or.inr hmem

/-! ## 6. Preservation of the invariant along steps -/

/-- Key-stack helper: a step that keeps function, parameters and entry
    world keeps the key stack. Both the kept triple and `h` feed the goal. -/
theorem rufFadenSchluesselG_behalte (z : RufFadenG D)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ' : Env D Γ)
    (rb : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (spur : List (Ereignis D)) :
    RufFadenSchluesselG
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ, ρ', rb⟩⟩,
       spur, z.log⟩ =
      RufFadenSchluesselG z := by
  simp [RufFadenSchluesselG, RufSchluesselG]

/-- Invariant helper: a step that keeps the key triple and the log keeps
    a well-formed thread. Used by every non-call step below. -/
theorem rufFadenPasstG_behalte (z : RufFadenG D)
    (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ' : Env D Γ)
    (rb : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (spur : List (Ereignis D)) (h : RufFadenPasstG z) :
    RufFadenPasstG
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ, ρ', rb⟩⟩,
       spur, z.log⟩ := by
  unfold RufFadenPasstG
  rw [rufFadenSchluesselG_behalte]
  exact h

/-- The machine invariant: every thread's log matches its key stack. -/
def RufMaschinePasstG (M : RufMaschineG D) : Prop :=
  ∀ f, RufFadenPasstG (M.faeden f)

/-- The start machine satisfies the invariant. Every premise is used:
    `hlog` names the start log, `hkeys` the start key stack. -/
theorem rufStartG_passt (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    RufMaschinePasstG (RufStartG P sp init) := by
  intro f
  have hpair : ∃ g rho, init f = (⟨g, rho⟩ : Σ f : D.Fn, Env D (D.params f)) :=
    ⟨(init f).1, (init f).2, by cases init f with | mk g rho => rfl⟩
  obtain ⟨g, rho, hif⟩ := hpair
  have hstart : (RufStartG (D := D) P sp init).faeden f =
      (match init f with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', sp.welt [],
          ⟨false, D.params g', Signatur.anfang D (D.signatur g'),
           rho', .ende (P.rumpf g')⟩⟩ : RufRahmenG D),
         [], [RufEreignisF.eintritt g' rho' (sp.welt [])]⟩ :
          RufFadenG D)) := rfl
  have hlog : ((RufStartG P sp init).faeden f).log =
      [RufEreignisF.eintritt g rho (sp.welt [])] := by
    rw [hstart, hif]
  have hkeys : RufFadenSchluesselG ((RufStartG P sp init).faeden f) =
      [⟨g, rho, sp.welt []⟩] := by
    rw [hstart, hif]
    rfl
  unfold RufFadenPasstG
  rw [hkeys, hlog]
  exact RufLogPasstG.eintritt [] [] _ _ _ RufLogPasstG.leer

/-- Push helper: pushing a callee frame with its entry event keeps a
    well-formed thread well-formed, whatever residues either frame carries
    (keys ignore residues). `hcaller` fixes the pushed caller key,
    `hcallee` the callee key; both feed the rewrite `e`, `h` the log. -/
theorem rufPushG_passt (z : RufFadenG D)
    (caller callee : RufRahmenG D)
    (hcaller : RufSchluesselG caller = RufSchluesselG z.kopf)
    (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D)
    (hcallee : RufSchluesselG callee = ⟨g, rho, s0⟩)
    (spur : List (Ereignis D))
    (h : RufFadenPasstG z) :
    RufFadenPasstG
      ⟨caller :: z.stapel, callee, spur,
       (RufEreignisF.eintritt g rho s0) :: z.log⟩ := by
  have e : RufFadenSchluesselG
      (⟨caller :: z.stapel, callee, spur,
        (RufEreignisF.eintritt g rho s0) :: z.log⟩ : RufFadenG D) =
      (⟨g, rho, s0⟩ :
        Σ f : D.Fn, Env D (D.params f) × World D) ::
        RufFadenSchluesselG z := by
    simp only [RufFadenSchluesselG, List.map_cons, hcallee, hcaller]
  unfold RufFadenPasstG
  rw [e]
  exact RufLogPasstG.eintritt _ _ g rho s0 h

/-- Pop helper: popping the head frame to a new head with the CALLER's key,
    logging the return, keeps a well-formed thread well-formed. `hpop`
    fixes the old stack, `hkeyNeu` the new head key, `hhead` the old head
    key; all three feed the rewrites, `h` the log. -/
theorem rufPopG_passt (z : RufFadenG D)
    (caller : RufRahmenG D) (rest : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rest)
    (neu : RufRahmenG D)
    (hkeyNeu : RufSchluesselG neu = RufSchluesselG caller)
    (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g))
    (s0 s1 : World D)
    (hhead : RufSchluesselG z.kopf =
      (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D))
    (spur : List (Ereignis D))
    (h : RufFadenPasstG z) :
    RufFadenPasstG
      ⟨rest, neu, spur,
       (RufEreignisF.rueck g rho v s0 s1) :: z.log⟩ := by
  have hk : RufFadenSchluesselG z =
      RufSchluesselG z.kopf ::
        ((caller :: rest).map RufSchluesselG) := by
    have e : RufFadenSchluesselG z =
        RufSchluesselG z.kopf ::
          ((z.stapel.map RufSchluesselG)) := by
      simp [RufFadenSchluesselG]
    rw [e, hpop]
  have htail : RufFadenSchluesselG
      (⟨rest, neu, spur,
        (RufEreignisF.rueck g rho v s0 s1) :: z.log⟩ : RufFadenG D) =
      (caller :: rest).map RufSchluesselG := by
    simp only [RufFadenSchluesselG, List.map_cons, hkeyNeu]
  unfold RufFadenPasstG at h ⊢
  rw [hk, hhead] at h
  rw [htail]
  exact RufLogPasstG.rueck _ _ g rho s0 v s1 h

/-- One step preserves the invariant for the ACTING thread.
    `ruf` pushes the callee key with its entry event; `rueck` pops the
    head key with its return event; every other step keeps the key triple
    and the log, so `rufFadenPasstG_behalte` closes it. Every premise of
    the step is used: `hhead`/`hΛ` fix the firing frame, `hstep`/`hrho`/
    `hv` the computed data, `hpop`/`hfg`/`hrho`/`hs0` the popped frame. -/
theorem rufSchrittG_passt_acting (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) (f : Faden)
    (h : RufFadenPasstG (M.faeden f))
    (hs : RufSchrittG P O passes M f M') :
    RufFadenPasstG (M'.faeden f) := by
  cases hs with
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      have hkeys : RufFadenPasstG
          (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        have e : RufFadenSchluesselG
            (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
              RufFadenG D) =
            (⟨g, rho, s0⟩ :
              Σ f : D.Fn, Env D (D.params f) × World D) ::
              RufFadenSchluesselG (M.faeden f) := by
          simp [RufFadenSchluesselG, RufSchluesselG]
        unfold RufFadenPasstG
        rw [e]
        exact RufLogPasstG.eintritt _ _ g rho s0 h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨(M.faeden f).kopf :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | rueck caller rest hpop Γ Λ e hperm ρ hh g hfg rho hr s0 hs0 hΛ s1 hs1 v hv
      neu hneu =>
      have hkeys : RufFadenPasstG
          (⟨rest, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        have hhead : RufSchluesselG (M.faeden f).kopf =
            (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
          cases hfg
          simp_all [RufSchluesselG]
        have hk : RufFadenSchluesselG (M.faeden f) =
            RufSchluesselG (M.faeden f).kopf ::
              ((caller :: rest).map RufSchluesselG) := by
          have e : RufFadenSchluesselG (M.faeden f) =
              RufSchluesselG (M.faeden f).kopf ::
                ((M.faeden f).stapel.map RufSchluesselG) := by
            simp [RufFadenSchluesselG]
          rw [e, hpop]
        have htail : RufFadenSchluesselG
            (⟨rest, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
              RufFadenG D) =
            (caller :: rest).map RufSchluesselG := by
          simp [RufFadenSchluesselG]
        unfold RufFadenPasstG at h ⊢
        rw [hk, hhead] at h
        rw [htail]
        exact RufLogPasstG.rueck _ _ g rho s0 v s1 h
      have heq : (⟨s1.speicher,
          rufUpdateG M.faeden f
            ⟨rest, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨rest, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho
      neu hneu =>
      have hkeys : RufFadenPasstG
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        have e : RufFadenSchluesselG
            (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
                ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
              RufFadenG D) =
            (⟨g, rho, s0⟩ :
              Σ f : D.Fn, Env D (D.params f) × World D) ::
              RufFadenSchluesselG (M.faeden f) := by
          simp [RufFadenSchluesselG, RufSchluesselG]
        unfold RufFadenPasstG
        rw [e]
        exact RufLogPasstG.eintritt _ _ g rho s0 h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
               ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv
      rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
         ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
               ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩ ::
               (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩ ::
              (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv
      rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        (M.faeden f).kopf
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨(M.faeden f).kopf :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0
      rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
         ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
               ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
               (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
              (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0
      hs0 g hg hv rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
         ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
               ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩ ::
               (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩ ::
              (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0
      hs0 rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
         ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
               ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
               (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
              (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | rueckBind caller rest hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ
      hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      have hhead : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeyNeu : RufSchluesselG
          (⟨caller.f, caller.rho, caller.s0,
            ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
             .dann restb (.schrumpf k)⟩⟩ : RufRahmenG D) =
          RufSchluesselG caller := by
        simp [RufSchluesselG]
      have hkeys := rufPopG_passt (M.faeden f) caller rest hpop
        ⟨caller.f, caller.rho, caller.s0,
         ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
          .dann restb (.schrumpf k)⟩⟩
        hkeyNeu g rho v s0 s1 hhead s1.spur h
      have heq : (⟨s1.speicher,
          rufUpdateG M.faeden f
            ⟨rest,
             ⟨caller.f, caller.rho, caller.s0,
              ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
               .dann restb (.schrumpf k)⟩⟩,
             s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨rest,
           ⟨caller.f, caller.rho, caller.s0,
            ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
             .dann restb (.schrumpf k)⟩⟩,
           s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1
      g hfg rho hrho s0 hs0 v hv neu hneu =>
      have hheadkey : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeys := rufPopG_passt (M.faeden f) caller rst hpop caller rfl
        g rho v s0 s1 hheadkey s1.spur h
      have heq : (⟨s1.speicher,
          rufUpdateG M.faeden f
            ⟨rst, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨rst, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hh g hfg rho hrho s0 hs0
      hΛ s1 hs1 v hv neu hneu =>
      have hheadkey : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeys := rufPopG_passt (M.faeden f) caller rst hpop caller rfl
        g rho v s0 s1 hheadkey s1.spur h
      have heq : (⟨s1.speicher,
          rufUpdateG M.faeden f
            ⟨rst, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨rst, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | _ =>
      simp only [rufUpdateG_self]
      exact rufFadenPasstG_behalte _ _ _ _ _ _ _ h

/-- One step preserves the invariant at an UNTOUCHED thread: the
    result machine's thread state equals the old one. `hne` selects the
    untouched side and is consumed by the simp set. -/
theorem rufSchrittG_passt_anders (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) (f f' : Faden) (hne : f' ≠ f)
    (hs : RufSchrittG P O passes M f M') :
    M'.faeden f' = M.faeden f' := by
  cases hs <;> (simp_all [rufUpdateG_noteq])

/-- One step preserves the invariant for EVERY thread. Both `hact`
    (acting side) and the untouched side feed the conclusion; `hne`
    selects the side. -/
theorem rufSchrittG_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) (f : Faden)
    (h : RufMaschinePasstG M)
    (hs : RufSchrittG P O passes M f M') :
    RufMaschinePasstG M' := by
  intro f'
  by_cases hne : f' = f
  · subst hne
    exact rufSchrittG_passt_acting P O passes M M' f' (h f') hs
  · rw [rufSchrittG_passt_anders P O passes M M' f f' hne hs]
    exact h f'

/-- The invariant holds at every reachable machine. Both `hbase` (start
    evidence) and the step evidence feed the conclusion. -/
theorem rufErreichbarG_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D)
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) :
    RufMaschinePasstG M := by
  induction h with
  | start => exact rufStartG_passt P sp init
  | schritt M M' f hbase hs ih =>
      exact rufSchrittG_passt P O passes M M' f ih hs

/-- **Return fidelity.** Every `rueck` event in a reachable thread log has
    its matching `eintritt` event in the same log. Every premise is used:
    `h` selects the reachable machine, `hmem` the log event. -/
theorem rufG_treu (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D)
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) (f : Faden) :
    ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log →
      RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log := by
  have hmach := rufErreichbarG_passt P O passes sp init M h
  have hthread := hmach f
  unfold RufFadenPasstG at hthread
  have hged := rufLogPasstG_gedeckt (RufFadenSchluesselG (M.faeden f))
    (M.faeden f).log hthread
  unfold rufRueckGedecktG at hged
  intro g rho v s0 s1 hmem
  exact hged g rho v s0 s1 hmem

/-! ## 7. Witness: an `if` whose taken branch writes a table

    The witness reuses the F declaration `rufDF` (one table, `Bool`
    functions, no locks): the callee `true` runs an `if` whose taken
    branch is the writing leaf, the caller `false` reuses the F caller
    body (a call to `true`). -/

/-- The condition: the literal `true`, so the taken branch fires. -/
def cG : Expr rufDF (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) .bool :=
  .wahr

/-- The taken branch: the writing leaf, then nothing. -/
def thenG : Block rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .cons leafSF .nil

/-- The else branch: nothing. -/
def elseG : Block rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .nil

/-- The `if` statement. -/
def iteG : Stmt rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .ite cG thenG elseG

/-- The `if` unfolds. -/
theorem iteG_entf : GEntfaltbar iteG = true := rfl

/-- The callee body: the `if`, then the parameter return `restF`. -/
def calleeG : Endblock rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .cons iteG restF

/-- The program: trivial contracts, callee with the `if`, caller reused. -/
def gP : Programm rufDF where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | true => calleeG
    | false => rufCallerRumpfF

/-- The callee body is what `gP` runs at `true`. -/
theorem gP_rumpf_true : gP.rumpf rufIncF = calleeG := rfl

def M0G : RufMaschineG rufDF := RufStartG gP spF initF

/-- The start head is the caller body with the entry environment. -/
theorem M0G_kopf :
    (M0G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF),
     rhoCallerF, .ende rufCallerRumpfF⟩ := by
  have hstart : (RufStartG (D := rufDF) gP spF initF).faeden 0 =
      (match initF 0 with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', spF.welt [],
          ⟨false, rufDF.params g', Signatur.anfang rufDF (rufDF.signatur g'),
           rho', .ende (gP.rumpf g')⟩⟩ : RufRahmenG rufDF),
       [], [RufEreignisF.eintritt g' rho' (spF.welt [])]⟩ :
          RufFadenG rufDF)) := rfl
  have hif : initF 0 = (⟨rufCallerF, rhoCallerF⟩ :
      Σ f : rufDF.Fn, Env rufDF (rufDF.params f)) := by
    simp only [initF]
  have hM : M0G.faeden 0 =
      (⟨[], (⟨rufCallerF, rhoCallerF, spF.welt [],
        ⟨false, rufDF.params rufCallerF,
         Signatur.anfang rufDF (rufDF.signatur rufCallerF),
         rhoCallerF, .ende (gP.rumpf rufCallerF)⟩⟩ : RufRahmenG rufDF),
       [], [RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])]⟩ :
        RufFadenG rufDF) := by
    simp only [M0G]
    rw [hstart, hif]
  have hrumpf : gP.rumpf rufCallerF = rufCallerRumpfF := rfl
  rw [hM, hrumpf]

/-- Reachability from `RufStartG`: `M0G` IS the start machine. -/
theorem M0G_start : M0G = RufStartG gP spF initF := rfl

/-! ## 8. The witness run: call, unfold, branch, write, return -/

/-- The machine after the `ruf` step: caller suspended, callee installed
    with the `if` body. -/
def M1G : RufMaschineG rufDF :=
  ⟨M0G.speicher,
   rufUpdateG M0G.faeden 0
     ⟨(M0G.faeden 0).kopf :: (M0G.faeden 0).stapel,
      ⟨rufIncF, rufRhoF, M0G.weltVon 0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF),
        rufRhoF, .ende (gP.rumpf rufIncF)⟩⟩,
      (M0G.weltVon 0).spur,
      (RufEreignisF.eintritt rufIncF rufRhoF (M0G.weltVon 0)) ::
        (M0G.faeden 0).log⟩,
   M0G.lauf ++ rufEigenG 0 [],
   M0G.start⟩

/-- Step 1 fires the `ruf` rule on the caller frame. Every premise feeds
    the constructor: `hhead`/`hΛ` fix the frame, `hs0`/`hrho`/`hneu` the
    entry data. -/
theorem schritt1G : RufSchrittG gP rufOF 0 M0G 0 M1G := by
  have hhead : (M0G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufCallerF, [],
       rhoCallerF,
       .ende (.cons (.call rufIncF rufArgsF rufHpF rfl)
         ((rufDF_params rufCallerF).symm ▸
           (.ret (.wert ((.weiter (by decide) (by decide) (.var .hier) :
             Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
           Endblock rufDF (vertragVon rufDF rufCallerF) false
             (rufDF.params rufIncF) (nach rufDF rufIncF [])))⟩ := by
    rw [M0G_kopf]
    rfl
  have hΛ : HeldGenau ([] : List (Res rufDF)) (offen (M0G.faeden 0).spur) :=
    heldLeerF _
  have hs0 : M0G.weltVon 0 =
      (M0G.weltVon 0).lese [] (Args.orte rufArgsF) := by
    rw [argsOrteF]
    rfl
  have hrho : rufRhoF = evalArgs (M0G.weltVon 0) rufArgsF
      (M0G.weltVon 0) rhoCallerF := by
    have hw : M0G.weltVon 0 = spF.welt [] := rfl
    rw [hw]
    rfl
  have hneu : (M0G.weltVon 0).spur = [] ++ (M0G.faeden 0).spur := rfl
  exact RufSchrittG.ruf M0G 0 false (rufDF.params rufCallerF) [] rufIncF
    rufArgsF rufHpF rfl _ rhoCallerF hhead hΛ _ hs0 _ hrho _ hneu

/-- Step 1 as reachability. -/
theorem reach1G : RufErreichbarG gP rufOF 0 M0G M1G := by
  exact RufErreichbarG.schritt _ _ 0 RufErreichbarG.start schritt1G

/-- The callee head after the call is the `if` body with `rufRhoF`. -/
theorem M1G_kopf :
    (M1G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .ende (.cons iteG restF)⟩ := rfl

/-- The thread world is unchanged by the call (no new events). -/
theorem M1G_welt : M1G.weltVon 0 = spF.welt [] := rfl

/-- The machine after the unfold: the `if` moved into `dann` position. -/
def M2G : RufMaschineG rufDF :=
  ⟨M1G.speicher,
   rufUpdateG M1G.faeden 0
     ⟨(M1G.faeden 0).stapel,
      ⟨(M1G.faeden 0).kopf.f, (M1G.faeden 0).kopf.rho, (M1G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann (.cons iteG .nil) (.ende restF)⟩⟩,
      (M1G.faeden 0).spur, (M1G.faeden 0).log⟩,
   M1G.lauf, M1G.start⟩

/-- Step 2 fires `endeEntf`: the compound head moves into `dann`. -/
theorem schritt2G : RufSchrittG gP rufOF 0 M1G 0 M2G :=
  RufSchrittG.endeEntf M1G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    iteG restF rufRhoF iteG_entf M1G_kopf

/-- Step 2 as reachability. -/
theorem reach2G : RufErreichbarG gP rufOF 0 M0G M2G := by
  exact RufErreichbarG.schritt _ _ 0 reach1G schritt2G

/-- The unfolded head. -/
theorem M2G_kopf :
    (M2G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann (.cons iteG .nil) (.ende restF)⟩ := rfl

/-- The thread world is unchanged by the unfold. -/
theorem M2G_welt : M2G.weltVon 0 = spF.welt [] := rfl

theorem cG_orte : cG.orte = [] := rfl

/-- The machine after the branch: the taken writing branch runs first,
    then the empty rest, then the return. The condition reads nothing,
    so the world is unchanged. -/
def M3G : RufMaschineG rufDF :=
  ⟨M2G.speicher,
   rufUpdateG M2G.faeden 0
     ⟨(M2G.faeden 0).stapel,
      ⟨(M2G.faeden 0).kopf.f, (M2G.faeden 0).kopf.rho, (M2G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩⟩,
      (M2G.weltVon 0).spur, (M2G.faeden 0).log⟩,
   M2G.lauf ++ rufEigenG 0 [],
   M2G.start⟩

/-- Step 3 fires `dannIteWahr`: the condition is the literal `true`. -/
theorem schritt3G : RufSchrittG gP rufOF 0 M2G 0 M3G := by
  have hhead : (M2G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .dann (.cons (.ite cG thenG elseG) .nil) (.ende restF)⟩ := M2G_kopf
  have hs₁ : M2G.weltVon 0 =
      (M2G.weltVon 0).lese
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) cG.orte := by
    rw [cG_orte]
    rfl
  have hw : wahr? (eval (M2G.weltVon 0) cG (M2G.weltVon 0) rufRhoF) = true :=
    rfl
  have hneu : (M2G.weltVon 0).spur = [] ++ (M2G.faeden 0).spur := rfl
  exact RufSchrittG.dannIteWahr M2G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    cG thenG elseG .nil (.ende restF) rufRhoF hhead _ hs₁ hw _ hneu

/-- Step 3 as reachability. -/
theorem reach3G : RufErreichbarG gP rufOF 0 M0G M3G := by
  exact RufErreichbarG.schritt _ _ 0 reach2G schritt3G

/-- The taken branch, unfolded. -/
theorem M3G_kopf :
    (M3G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩ := rfl

/-- The thread world is unchanged by the branch choice. -/
theorem M3G_welt : M3G.weltVon 0 = spF.welt [] := rfl

/-- The machine after the writing leaf: memory moved to `outWF`, the
    branch block is done. -/
def M4G : RufMaschineG rufDF :=
  ⟨outWF.speicher,
   rufUpdateG M3G.faeden 0
     ⟨(M3G.faeden 0).stapel,
      ⟨(M3G.faeden 0).kopf.f, (M3G.faeden 0).kopf.rho, (M3G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann .nil (.dann .nil (.ende restF))⟩⟩,
      outWF.spur, (M3G.faeden 0).log⟩,
   M3G.lauf ++ rufEigenG 0 outWF.spur,
   M3G.start⟩

/-- Step 4 fires `dannBlatt` on the writing leaf -- the memory move. -/
theorem schritt4G : RufSchrittG gP rufOF 0 M3G 0 M4G := by
  have hhead : (M3G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .dann (.cons leafSF .nil) (.dann .nil (.ende restF))⟩ := M3G_kopf
  have hΛ : HeldGenau (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (M3G.faeden 0).spur) :=
    heldLeerF _
  have hstep : (execStmt rufOF 0 (R := keinRuf)
      (V := vertragVon rufDF (M3G.faeden 0).kopf.f)
      leafSF (M3G.weltVon 0) rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF (M3G.faeden 0).kopf.f)
        outWF rufRhoF := by
    rw [M3G_welt]
    exact leafSF_ok
  have hneu : outWF.spur = outWF.spur ++ (M3G.faeden 0).spur := by
    have hspur : (M3G.faeden 0).spur = [] := rfl
    rw [hspur, List.append_nil]
  have hkein : ∀ (L : rufDF.Lock) (h : List rufDF.Lock),
      Ereignis.nimmt L h ∉ (outWF.spur : List (Ereignis rufDF)) := by
    intro L h hm
    exact nomatch L
  exact RufSchrittG.dannBlatt M3G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF .nil (.dann .nil (.ende restF)) rufRhoF leafSF_blatt hhead hΛ
    outWF rufRhoF outWF.spur hstep hneu hkein

/-- Step 4 as reachability. -/
theorem reach4G : RufErreichbarG gP rufOF 0 M0G M4G := by
  exact RufErreichbarG.schritt _ _ 0 reach3G schritt4G

/-- The finished branch, behind two empty blocks. -/
theorem M4G_kopf :
    (M4G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann .nil (.dann .nil (.ende restF))⟩ := rfl

/-- The machine after the first empty block completes. -/
def M5G : RufMaschineG rufDF :=
  ⟨M4G.speicher,
   rufUpdateG M4G.faeden 0
     ⟨(M4G.faeden 0).stapel,
      ⟨(M4G.faeden 0).kopf.f, (M4G.faeden 0).kopf.rho, (M4G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .dann .nil (.ende restF)⟩⟩,
      (M4G.faeden 0).spur, (M4G.faeden 0).log⟩,
   M4G.lauf, M4G.start⟩

/-- Step 5 fires `dannLeer`: the branch block is done. -/
theorem schritt5G : RufSchrittG gP rufOF 0 M4G 0 M5G :=
  RufSchrittG.dannLeer M4G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (.dann .nil (.ende restF)) rufRhoF M4G_kopf

/-- Step 5 as reachability. -/
theorem reach5G : RufErreichbarG gP rufOF 0 M0G M5G := by
  exact RufErreichbarG.schritt _ _ 0 reach4G schritt5G

/-- The second empty block, done. -/
theorem M5G_kopf :
    (M5G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .dann .nil (.ende restF)⟩ := rfl

/-- The machine after the second empty block completes: the return. -/
def M6G : RufMaschineG rufDF :=
  ⟨M5G.speicher,
   rufUpdateG M5G.faeden 0
     ⟨(M5G.faeden 0).stapel,
      ⟨(M5G.faeden 0).kopf.f, (M5G.faeden 0).kopf.rho, (M5G.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
        .ende restF⟩⟩,
      (M5G.faeden 0).spur, (M5G.faeden 0).log⟩,
   M5G.lauf, M5G.start⟩

/-- Step 6 fires `dannLeer` again: the `if` scaffolding is gone. -/
theorem schritt6G : RufSchrittG gP rufOF 0 M5G 0 M6G :=
  RufSchrittG.dannLeer M5G 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (.ende restF) rufRhoF M5G_kopf

/-- Step 6 as reachability. -/
theorem reach6G : RufErreichbarG gP rufOF 0 M0G M6G := by
  exact RufErreichbarG.schritt _ _ 0 reach5G schritt6G

/-- The return residue: the parameter return. -/
theorem M6G_kopf :
    (M6G.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .ende (.ret eF (by decide))⟩ := rfl

/-- The return world: the callee thread world read at the (empty) result
    places. -/
def s1G : World rufDF :=
  (M6G.weltVon 0).lese
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (ErgExpr.orte eF)

/-- The machine after the `rueck` step: caller restored, return logged. -/
def M7G : RufMaschineG rufDF :=
  ⟨(M6G.weltVon 0).speicher,
   rufUpdateG M6G.faeden 0
     ⟨[], (M0G.faeden 0).kopf, s1G.spur,
      [RufEreignisF.rueck rufIncF rufRhoF vF (M0G.weltVon 0) s1G] ++
        (M6G.faeden 0).log⟩,
   M6G.lauf ++ rufEigenG 0 [],
   M6G.start⟩

/-- Step 7 fires `rueck`: the callee frame pops to the waiting caller.
    Every premise feeds the constructor: `hpop`/`hfg`/`hrho`/`hs0`
    select the head frame, `hΛ` the lock state, `hs1`/`hv`/`hneu` the
    return data. -/
theorem schritt7G : RufSchrittG gP rufOF 0 M6G 0 M7G := by
  have hpop : (M6G.faeden 0).stapel = [(M0G.faeden 0).kopf] := rfl
  have hhead : (M6G.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF),
       rufRhoF, .ende (.ret eF (by decide))⟩ := M6G_kopf
  have hfg : (M6G.faeden 0).kopf.f = rufIncF := rfl
  have hrho : (M6G.faeden 0).kopf.rho = hfg ▸ rufRhoF := rfl
  have hs0 : (M6G.faeden 0).kopf.s0 = M0G.weltVon 0 := rfl
  have hΛ : HeldGenau (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (M6G.faeden 0).spur) := by
    have e : offen (M6G.faeden 0).spur = [] := rfl
    rw [e]
    exact heldLeerF []
  have hs1 : s1G =
      (M6G.weltVon 0).lese (Signatur.anfang rufDF (rufDF.signatur rufIncF))
        (ErgExpr.orte eF) := rfl
  have hv : vF = hfg ▸ evalErg s1G eF s1G rufRhoF := rfl
  have hneu : s1G.spur = [] ++ (M6G.faeden 0).spur := rfl
  exact RufSchrittG.rueck M6G 0 (M0G.faeden 0).kopf [] hpop _ _ _ _ _
    hhead _ hfg rufRhoF hrho _ hs0 hΛ _ hs1 _ hv _ hneu

/-- Step 7 as reachability: seven steps FROM THE START STATE. -/
theorem reach7G : RufErreichbarG gP rufOF 0 M0G M7G := by
  exact RufErreichbarG.schritt _ _ 0 reach6G schritt7G

/-- The witness run reaches `M7G` from the start state. -/
theorem reach7G_start :
    RufErreichbarG gP rufOF 0 (RufStartG gP spF initF) M7G := by
  rw [← M0G_start]
  exact reach7G

/-- The witness log of thread 0: return, callee entry, caller entry. -/
theorem M7G_log : (M7G.faeden 0).log =
    [RufEreignisF.rueck rufIncF rufRhoF vF (M0G.weltVon 0) s1G,
     RufEreignisF.eintritt rufIncF rufRhoF (M0G.weltVon 0),
     RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] := rfl

/-- The final memory carries the written value at slot 0 (via `outWF`). -/
theorem M7G_slot : M7G.speicher.slots () 0 () =
    (⟨2, by decide, by decide⟩ : Wert rufDF (rufDF.typ () ())) := by
  have hhit := outWF_moves.1
  have hmem : M7G.speicher.slots () 0 () = outWF.slots () 0 () := rfl
  rw [hmem]
  exact hhit

/-- Memory really moved: slot 0 reads `2`, the start reads `0`. Both
    conjuncts feed the inequality below. -/
theorem M7G_moves : M7G.speicher.slots () 0 () ≠
    spF.slots () 0 () := by
  have h2 := M7G_slot
  have h0 : spF.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert rufDF (rufDF.typ () ())) := rfl
  rw [h2, h0]
  intro hcon
  have hn : ((⟨2, by decide, by decide⟩ :
      Wert rufDF (rufDF.typ () ())).n) = ((⟨0, by decide, by decide⟩ :
      Wert rufDF (rufDF.typ () ())).n) := congrArg Zahl.n hcon
  simp at hn

/-- **Witness for `rufG_treu`.** The premises of `rufG_treu` are
    instantiated JOINTLY with concrete values: the program `gP` (callee
    with an `if` whose taken branch writes), the oracle `rufOF`, zero
    passes, start memory `spF`, every thread at the caller entry with
    `initF`, the reached machine `M7G` (reached FROM THE START STATE by
    `reach7G_start`: `ruf` pushes the callee, `endeEntf` unfolds the
    `if`, `dannIteWahr` takes the writing branch, `dannBlatt` runs the
    writing leaf -- slot 0 moves 0 -> 2 by `M7G_moves`, a step that
    changes memory -- two `dannLeer` steps drain the scaffolding,
    `rueck` pops it), and thread `0`. The log contains the `rueck`
    event, and the matching `eintritt` sits below it in the same log.
    The fourth conjunct is the non-degeneracy: the run moves memory.
    Every premise is used: `h` is the reachability, `hmem` the log
    membership, the move the memory change. -/
theorem rufG_treu_zeuge :
    ∃ (M : RufMaschineG rufDF) (f : Faden)
      (g : rufDF.Fn) (rho : Env rufDF (rufDF.params g))
      (v : ErgVal rufDF (rufDF.erg g)) (s0 s1 : World rufDF),
      RufErreichbarG gP rufOF 0 (RufStartG gP spF initF) M ∧
        RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log ∧
        RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log ∧
        M.speicher.slots () 0 () ≠ spF.slots () 0 () := by
  exact ⟨M7G, 0, rufIncF, rufRhoF, vF, M0G.weltVon 0, s1G,
    reach7G_start, by rw [M7G_log]; exact List.mem_cons_self,
    by rw [M7G_log]; exact List.mem_cons_of_mem _ (List.mem_cons_self),
    M7G_moves⟩

/-! ## CUTS:
  - Stepwise coverage. Unfold steps exist for `ite` (both directions),
    `onOption` (some/none), `locks` (take into `dann`, release at `frei`),
    `breaking`, `traverse` (one index at a time via `trav`/`travRest`),
    `retry` (one try at a time via `wieder`/`wiederRest`, overflow arm at
    zero), `forever` (one iteration at a time via `ewig`/`ewigRest` with
    the `passes` budget), `let` (`endeBind`/`dannBind` with `schrumpf`),
    `narrow` and `pruefung` (both outcomes). NOT covered: `onTag` and
    `onGrund` (need the arm-selection helpers `waehleArm`/`waehleGrund`,
    which live only in the reference branch, not in this tree), indirect
    calls `callInd`, and the `Block` binders `bindCall`/`bindCallInd`/
    `bindCallElse`/`bindAxiom`/`regLies`/`regLiesElse`/`awaits`/`exchange`/
    `gleit`/`gleitLit`/`gleitVon`/`gleitNarrow` (a `dann` head with one of
    these has no firing step and gets stuck). Calls inside unfolded
    blocks fire `rufDann`; calls in `ende` position fire `ruf`.
  - Loop exits are partial: `leave`/`next` inside a loop body run through
    `execStmt` only as leaves of `dannBlatt`, whose `.ok` outcome they
    never produce, so the iteration gets stuck instead of exiting;
    `forever` with exhausted budget and a false invariant have no step
    (the reference machine reports `hardware .fortschritt` / `logik
    .schleife` there); `retGrund` at the head has no step.
  - Top-level `ret` with an empty call stack has no step (as in F): the
    witness returns through a call, like every `rueck`.
  - No contract discharge: the machine never gates on contracts, and no
    theorem connects `rueck` events to `ReqAmEintritt`/`EnsAmRueck`. The
    events carry the actual values such a theorem would need.
-/

#print axioms Gabbro.Grammatik.rufG_treu
#print axioms Gabbro.Grammatik.rufG_treu_zeuge
#print axioms Gabbro.Grammatik.rufSchrittG_passt
#print axioms Gabbro.Grammatik.rufErreichbarG_passt
#print axioms Gabbro.Grammatik.schritt4G
#print axioms Gabbro.Grammatik.reach7G_start
#print axioms Gabbro.Grammatik.M7G_moves

end Gabbro.Grammatik
