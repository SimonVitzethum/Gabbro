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
  bounded-loop states (`trav`/`wieder`/`ewig` with their remaining bound),
  and the residues of a caller waiting for a bound value (`wartet`, and
  `wartetSonst`, which keeps the else block of `let x = g(…) else { … }`).
  New steps unfold compounds into that residue; only pushes and pops touch
  the call log (`eintritt`, `rueck`, and `grund` for the error channel), so
  fidelity (`rufG_treu`) follows the F proof pattern. A waiting caller is
  resumed only by a binding pop: no reachable head waits
  (`rufG_nie_wartend`).
-/
import Grammatik.Kern.Semantik.Maschine
import Grammatik.Logik.Vertraege.VertragOrtB
import Grammatik.Logik.Ruf.RufMaschineF

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Residues with continuations -/

/-- An end block as a block, with the holdings it ends at. An end block
    never falls through (it ends in `return`, a reason, `leave` or `next`),
    so the block's end holdings are those of its last statement. The
    residue of an `else` branch runs it in BLOCK position, so that a
    `leave`/`next` in it reaches the enclosing loop (`GRest.abbruch`,
    2026-09-13; before, the else branch replaced the residue and dropped the
    loop's continuation). -/
def Endblock.alsBlock {V : Vertrag D} {l : Bool} : {Γ : Ctx} → {Λ : List (Res D)} →
    Endblock D V l Γ Λ → Σ Λ' : List (Res D), Block D V l Γ Λ Λ'
  | _, Λ, .ret e h => ⟨Λ, .cons (.ret e h) .nil⟩
  | _, Λ, .retWhy r h => ⟨Λ, .cons (.retWhy r h) .nil⟩
  | _, Λ, .leave h => ⟨Λ, .cons (.leave h) .nil⟩
  | _, Λ, .next h => ⟨Λ, .cons (.next h) .nil⟩
  | _, _, .cons s rest => ⟨rest.alsBlock.1, .cons s rest.alsBlock.2⟩
  | _, _, .bind e rest => ⟨rest.alsBlock.1, .bind e rest.alsBlock.2⟩
  | _, _, .bindAxiom a args he hw hg hd hgd rest =>
      ⟨rest.alsBlock.1, .bindAxiom a args he hw hg hd hgd rest.alsBlock.2⟩
  | _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest =>
      ⟨rest.alsBlock.1, .bindAxiomElse a args he hr hw hg hd hgd err rest.alsBlock.2⟩

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
  /-- A caller waiting in `let x = g(…) else { err }`: a normal return binds
      `x` and runs `rest` (as `wartet`); a reason `r : Fin n` runs `err`
      with `r` bound. -/
  | wartetSonst {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (n : Nat)
      (err : Endblock D V l (.why n :: Γ) Λ)
      (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') :
      GRest D V l Γ Λ
  /-- The continuation behind an `else` branch (and behind the reason
      block of `let … else`): the branch never falls through; a `leave` or
      `next` in it reaches `k` (`peelAbbruchLeave`/`peelAbbruchNext`), a
      return pops the frame. Its holdings index is free. -/
  | abbruch {l : Bool} {Γ : Ctx} {Λ Λk : List (Res D)} :
      GRest D V l Γ Λk → GRest D V l Γ Λ

/-- **An end block run as a block means what it meant**: its outcome is
    the end block's, as an `Ausgang` (it never ends normally). -/
theorem Endblock.execBlock_alsBlock (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
      execBlock O passes R e.alsBlock.2 σ ρ = (execEnd O passes R e σ ρ).zuAusgang
  | _, _, .ret _ _, _, _ => rfl
  | _, _, .retWhy _ _, _, _ => rfl
  | _, _, .leave _, _, _ => rfl
  | _, _, .next _, _, _ => rfl
  | _, _, .cons s rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      cases execStmt O passes R s σ ρ with
      | ok σ' ρ' => exact Endblock.execBlock_alsBlock O passes R rest σ' ρ'
      | _ => rfl
  | _, _, .bind e rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      rw [Endblock.execBlock_alsBlock O passes R rest]
      cases execEnd O passes R rest _ _ <;> rfl
  | _, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · rfl
  | _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · cases execEnd O passes R err _ _ <;> rfl
      · rfl

/-- A residue that waits for a callee's answer (`wartet`/`wartetSonst`):
    only a BINDING pop may resume it. -/
def GRest.wartend {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .wartet .. => true
  | .wartetSonst .. => true
  | _ => false

/-- One frame: as in F, but the residue is a `GRest`. -/
structure RufRahmenG (D : Deklaration) where
  f : D.Fn
  rho : Env D (D.params f)
  s0 : World D
  rest :
    Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
      Env D Γ × GRest D (vertragVon D f) l Γ Λ

/-- The frame waits for a callee's answer. -/
def RufRahmenG.wartend (r : RufRahmenG D) : Bool := r.rest.2.2.2.2.wartend

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
  | .onWhy .. => true
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


end Gabbro.Grammatik
