/-
  File:      Grammatik/Folge.lean
  Subject:   THE ORDER OF EFFECTS, STATED OVER MACHINE G (OFFEN O1, Opus agent G,
             2026-09-26) -- definitions only; the proofs are Grammatik/FolgeBeweis.lean.

  OFFEN O1 recorded four obligations (`L24`, `L34`, `L50`, `L52`) that "the semantics cannot
  state", because `programmlogik/Gabbro/Body.lean`'s `exec` is big-step. The goal theorem does
  not stand on that semantics: its runs are those of machine G, which is SMALL-STEP (every
  leaf statement, every unfold, every push and pop is its own step), whose threads carry an
  event trace (`spur`) and a CALL LOG (`log`: `eintritt`, `rueck`, `grund`, newest first).
  Intermediate states exist there, and so does the order of calls.

  Two of the four are about the ORDER of effects:
  * `L50` -- "`Flush`: the flush completed BEFORE the reply" (`let r2 = request_flush(…);
    reply4(EP, …);`);
  * `L52` -- "`Stop`: the reply still goes out BEFORE the service ends" (`reply4(…); return`).
  Both are one shape: an event (the entry of `reply4`; the return of the service) is
  IMMEDIATELY preceded, in its thread's call log, by the return of a named function (the
  flush; the reply). This file states that shape (`FolgeLog`, `FolgeG`) and the static
  premise under which the language carries it (`FolgeOk`): in every body, every call of a
  function in `ruf` and every return of a function in `ende` stands directly behind a call of
  a function in `vor`, with only log-silent statements (leaves: assignments, axiom calls,
  register accesses, bindings) in between. No `sorry`, no axiom, no new rule of G.

  WHY "IMMEDIATELY" AND NOT "SOMETIME BEFORE". `flush ∧ reply` -- both happened -- is the
  weakening V1 warned about (`messung/GABBROV-V1.md`: "type-checks, reads right, and is a
  strictly weaker statement wearing the obligation's name"). `FolgeLog` is about the POSITION
  of the events: the log entry directly older than every entry of `reply4` is a return of
  the flush. A log in which both occur but the reply comes first, or a second reply follows
  one flush, violates it (`folgeLog_nicht_schwach`, FolgeBeweis.lean).

  WHAT THE CHECK IS. A linear scan per block with one bit `w` ("armed": the last log event of
  this thread is a return of a `vor` function, and nothing logged since). A call of `g` sets
  `w := vor g`; a leaf keeps `w`; a compound statement, an indirect call and every sub-block
  start from `w := false` (conservative). A call of a `ruf` function (directly, or indirectly
  through a signature in `ind`) and a return of an `ende` function demand `w`. The residue
  predicate `GRest.fR` carries the same check over the continuation layers of machine G.
-/
import Grammatik.Verklemmung

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The order specification -/

/-- **An order specification** over the functions of a declaration:
    * `vor` -- the predecessors: the function whose return must come directly before;
    * `ruf` -- every ENTRY of such a function must directly follow a return of a `vor`;
    * `ind` -- signatures whose indirect calls are treated as calls of a `ruf` function
      (`FolgeOk` demands `ind (D.sig g)` for every `ruf g`, so no entry escapes through a
      function pointer);
    * `ende` -- every RETURN (value or reason) of such a function, and the end of a thread
      whose start function is one, must directly follow a return of a `vor`. -/
structure Folge (D : Deklaration) where
  vor : D.Fn → Bool
  ruf : D.Fn → Bool
  ind : Nat → Bool
  ende : D.Fn → Bool

/-! ## 2. The static check -/

section Pruef

variable (Φ : Folge D) {V : Vertrag D}

/-- The armed bit after a statement: a direct call of `g` leaves `vor g`; a leaf keeps it; an
    indirect call and a compound statement clear it. -/
def fNach {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (w : Bool) : Stmt D V l Γ Λ Λ' → Bool
  | .call g _ _ _ => Φ.vor g
  | .callInd .. => false
  | .ite .. => false
  | .onOption .. => false
  | .onTag .. => false
  | .onGrund .. => false
  | .locks .. => false
  | .breaking .. => false
  | .traverse .. => false
  | .retry .. => false
  | .forever .. => false
  | _ => w

mutual

/-- One statement, entered with armed bit `w`, in a frame whose returns are ordered iff `e`. -/
def fS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (e w : Bool) : Stmt D V l Γ Λ Λ' → Bool
  | .call g _ _ _ => !Φ.ruf g || w
  | .callInd (n := n) .. => !Φ.ind n || w
  | .ret .. => !e || w
  | .retGrund .. => !e || w
  | .ite _ t f => fB e false t && fB e false f
  | .onOption _ p a => fB e false p && fB e false a
  | .onTag _ arms => fArms e arms
  | .onGrund _ arms => fGArms e arms
  | .locks _ _ body => fB e false body
  | .breaking _ body => fB e false body
  | .traverse _ _ body => fB e false body
  | .retry _ _ body ueber => fB e false body && fB e false ueber
  | .forever _ _ body => fB e false body
  | .assignSlot .. => true
  | .assignDurch .. => true
  | .assignGlob .. => true
  | .schreibBytes .. => true
  | .assignVar .. => true
  | .uebergang .. => true
  | .axiomCall .. => true
  | .regSchreib .. => true
  | .transition .. => true
  | .publish .. => true
  | .advances .. => true
  | .retires .. => true
  | .leave _ => true
  | .next _ => true

/-- A block entered with armed bit `w`. -/
def fB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (e w : Bool) : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => fS e w s && fB e (fNach Φ w s) rest
  | .bind _ rest => fB e w rest
  | .bindCall g _ _ _ _ rest => (!Φ.ruf g || w) && fB e (Φ.vor g) rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => (!Φ.ind n || w) && fB e false rest
  | .bindCallElse g _ _ _ _ err rest =>
      (!Φ.ruf g || w) && fE e false err && fB e (Φ.vor g) rest
  | .bindAxiom _ _ _ _ _ _ _ rest => fB e w rest
  | .regLies _ _ rest => fB e w rest
  | .regLiesElse _ _ _ sonst rest => fE e false sonst && fB e w rest
  | .awaits _ _ _ _ rest => fB e w rest
  | .exchange _ _ _ _ rest => fB e w rest
  | .narrow _ _ _ sonst rest => fE e false sonst && fB e w rest
  | .pruefung _ sonst rest => fE e false sonst && fB e w rest
  | .gleit _ _ _ _ _ rest => fB e w rest
  | .gleitLit _ _ _ rest => fB e w rest
  | .gleitVon _ _ _ rest => fB e w rest
  | .gleitNarrow _ _ _ sonst rest => fE e false sonst && fB e w rest

/-- The arms of a `match`: each is a sub-block, entered unarmed. -/
def fArms {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (e : Bool) : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => fB e false b && fArms e rest

def fGArms {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (e : Bool) : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => fB e false b && fGArms e rest

/-- An end block entered with armed bit `w`. -/
def fE {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e w : Bool) : Endblock D V l Γ Λ → Bool
  | .ret .. => !e || w
  | .retGrund .. => !e || w
  | .leave _ => true
  | .next _ => true
  | .cons s rest => fS e w s && fE e (fNach Φ w s) rest
  | .bind _ rest => fE e w rest

end

/-- **The residue predicate**: the check, carried over every continuation layer of a frame.
    The block in front runs with the frame's armed bit; every continuation behind it, every
    loop body and every `else` branch is checked unarmed. -/
def GRest.fR (e : Bool) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Bool → GRest D V l Γ Λ → Prop
  | _, _, _, w, .ende b => fE Φ e w b = true
  | _, _, _, w, .dann b k => fB Φ e w b = true ∧ k.fR e false
  | _, _, _, w, .schrumpf k => k.fR e w
  | _, _, _, w, .frei _ k => k.fR e w
  | _, _, _, _, .trav _ _ body _ k => fB Φ e false body = true ∧ k.fR e false
  | _, _, _, _, .travRest _ _ body _ k => fB Φ e false body = true ∧ k.fR e false
  | _, _, _, _, .wieder _ _ body ueber k =>
      fB Φ e false body = true ∧ fB Φ e false ueber = true ∧ k.fR e false
  | _, _, _, _, .wiederRest _ _ body ueber k =>
      fB Φ e false body = true ∧ fB Φ e false ueber = true ∧ k.fR e false
  | _, _, _, _, .ewig _ _ _ body k => fB Φ e false body = true ∧ k.fR e false
  | _, _, _, _, .ewigRest _ _ _ body k => fB Φ e false body = true ∧ k.fR e false
  | _, _, _, w, .wartet b k => fB Φ e w b = true ∧ k.fR e false
  | _, _, _, w, .wartetSonst _ err b k =>
      fE Φ e false err = true ∧ fB Φ e w b = true ∧ k.fR e false
  | _, _, _, _, .abbruch k => k.fR e false

end Pruef

/-- **The static premise of the order leg**: every body passes the check unarmed, and every
    `ruf` function's signature is among the indirectly checked ones. Decidable for a concrete
    program (a finite `D.Fn`). -/
def FolgeOk (P : Programm D) (Φ : Folge D) : Prop :=
  (∀ f, fE Φ (Φ.ende f) false (P.rumpf f) = true) ∧ (∀ g, Φ.ruf g = true → Φ.ind (D.sig g) = true)

/-! ## 3. The order in the call log -/

/-- The log is ARMED: its newest event is a return of a `vor` function. -/
def Armiert (Φ : Folge D) : List (RufEreignisF D) → Bool
  | .rueck g .. :: _ => Φ.vor g
  | _ => false

/-- The event is ORDERED by `Φ`: an entry of a `ruf` function, a return of an `ende` one. -/
def Pflichtig (Φ : Folge D) : RufEreignisF D → Bool
  | .eintritt g .. => Φ.ruf g
  | .rueck g .. => Φ.ende g
  | .grund g .. => Φ.ende g

/-- **The order in a call log** (newest first): every ordered event, except the thread's
    start entry (the oldest event), has as its DIRECT predecessor a return of a `vor`
    function. -/
def FolgeLog (Φ : Folge D) : List (RufEreignisF D) → Prop
  | [] => True
  | ev :: rest => (rest ≠ [] → Pflichtig Φ ev = true → Armiert Φ rest = true) ∧ FolgeLog Φ rest

/-- **The order leg at a machine `M`**: for every order specification the program passes,
    every thread's call log is ordered, and a FINISHED thread whose start function is an
    `ende` function ended directly behind a return of a `vor` function. -/
def FolgeG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ Φ : Folge D, FolgeOk P Φ → ∀ t,
    FolgeLog Φ (M.faeden t).log ∧
    ((M.faeden t).stapel = [] → (M.faeden t).kopf.rest.2.2.2.2.anRueck = true →
      Φ.ende (M.faeden t).kopf.f = true → Armiert Φ (M.faeden t).log = true)

end Gabbro.Grammatik
