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
module
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1Basis
import all Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1Basis
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Logik.Vertraege.Locations.VertragOrtB
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

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
  simp only [rufUpdateG, ↓reduceIte]

theorem rufUpdateG_noteq (m : Faden → RufFadenG D) (f g : Faden) (h : g ≠ f)
    (z : RufFadenG D) :
    rufUpdateG m f z g = m g := by
  simp only [rufUpdateG, h, ↓reduceIte]

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
  /-- C11 consuming traversal has no unfold step yet: no `GRest` selection
      continuation is proved, so the machine refuses it here. The sequential
      `execStmt` placeholder runs it as a fixed sweep; export refuses the
      source form until the current-state selector bridge lands. -/
  | .consumeTraverse .. => false
  | _ => false

/-- The end-block formers that the machine unfolds into block position (`endeForm`): the
    residue `.ende e` becomes `.dann e.alsBlock.2 (.abbruch .leer)`, and the BLOCK steps run it
    (the fall-through is never reached: an end block does not fall off). The formers
    with a step of their own (`cons`, `bind`, `bindAxiom`, `bindAxiomElse`, the returns) are not
    listed. Written without a wildcard, so a new `Endblock` former must be placed here. -/
def EndEntfaltbar {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => false
  | .retWhy .. => false
  | .leave .. => false
  | .next .. => false
  | .cons .. => false
  | .bind .. => false
  | .bindCall .. => true
  | .bindCallElse .. => true
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .regRead .. => true
  | .regReadElse .. => true
  | .awaits .. => true
  | .bindCallInd .. => true
  | .narrow .. => true
  | .narrowRequired .. => true
  | .exchange .. => true
  | .ite .. => true
  /-- C11 scoped returns are terminal in the placeholder: they do not unfold
      into block position beyond `alsBlock`, and no step rule consumes the
      pending scope unwinding yet. -/
  | .retScoped .. => false
  | .retWhyScoped .. => false

/-- Arm selection for `onTag`: the VALUE's index chooses the arm and the
    VALUE's payload feeds it (like `execArms`, but returning the chosen arm
    instead of running it). The `nil` case cannot fire (`Fin 0` is empty). -/
def armWahlG {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} :
    Arms D V l Γ Λ Λ' cs → Wert D (.sum cs) →
      Σ c : Option Ty, Block D V l (ArmCtx Γ c) Λ Λ' × Nutzlast D.Fn D.passt c
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
