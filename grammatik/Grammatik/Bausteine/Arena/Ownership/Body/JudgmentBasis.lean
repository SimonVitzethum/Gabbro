module
public import Grammatik.Bausteine.Arena.Ownership.Body.Shapes
@[expose] public section


/-! **The general ownership body judgment** over G's actual syntax.

`OB A I out k c b c'` says: started in the source context `c`, the block `b`
of a function with result kind `out` keeps the ownership discipline and
falls off in `c'`; a `leave`/`next` leaves in a context that exits to the
loop context `k`. One rule per G form: every expression evaluated is
access-checked against the current context, every store keeps the
allocator words and links, the executed allocator forms move rights, every
call (direct or through a pointer) hands its arguments over by the callee's
interface, branches join in a common weaker context and loops keep an
invariant context. A form without a rule (a raw store into a link or an
allocator word, an unframed foreign body, an access without a current
right) has no derivation. Soundness: `Body/Sound.lean`. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-! ## 1. Context operations of the rules -/

/-- A store into table `t` at index `i`: into the arena only through a current right. -/
def storeCheck (A : FreiForm D) (c : Context) {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) {lo hi : Int}
    (i : Expr D Γ Λ (.int lo hi)) : Bool :=
  if t = A.tab then accessCheck c i else true

/-- Assigning a variable gives its name the origin of the new value. -/
def _root_.Gabbro.Grammatik.ArenaOwnership.Source.Context.assign (c : Context) {Γ : Ctx} {τ : Ty}
    (x : Var Γ τ) (o : Option Nat) : Context :=
  { c with references := c.references.set x.unten o }

/-- The context inside a case arm: a payload binder carries no grant. -/
def armBind (c : Context) : Option Ty → Context
  | none => c
  | some _ => c.bind none

def armDrop (c : Context) : Option Ty → Context
  | none => c
  | some _ => c.drop

/-- The caller context after a discarded result, by result kind. -/
def dropContextB (c : Context) (owner : Bool) : Context := if owner then c.bindFresh.drop else c

/-! ## 2. What an outcome promises -/

section Post

variable (A : FreiForm D) (fr : Frame) (s0 : State) {V : Vertrag D} (out : Flow.Output A V.erg)

/-- A value return meets the function's interface postcondition. -/
def DoneValue (σ : World D) (v : ErgVal D V.erg) : Prop :=
  ∃ s, s.agrees A σ ∧ A.FreiOk σ ∧ s0.local s fr ∧ s0.progress s ∧ out.result A fr s v

/-- A reason return leaves no allocation owned by the activation. -/
def DoneReason (σ : World D) : Prop :=
  ∃ s, s.agrees A σ ∧ A.FreiOk σ ∧ s0.local s fr ∧ s0.progress s ∧ s.closed fr

/-- **The promise of a block outcome.** -/
def BPost (k c' : Context) {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Prop
  | .ok σ ρ => Holds A fr s0 c' σ ρ
  | .zurueck σ v => DoneValue A fr s0 out σ v
  | .why σ _ => DoneReason A fr s0 σ
  | .leave _ σ ρ => ∃ c, ExitsTo k c ∧ Holds A fr s0 c σ ρ
  | .next _ σ ρ => ∃ c, ExitsTo k c ∧ Holds A fr s0 c σ ρ
  | .logik _ => True
  | .hardware _ => True

/-- **The promise of an end-block outcome.** -/
def EPost (k : Context) {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → Prop
  | .zurueck σ v => DoneValue A fr s0 out σ v
  | .why σ _ => DoneReason A fr s0 σ
  | .leave _ σ ρ => ∃ c, ExitsTo k c ∧ Holds A fr s0 c σ ρ
  | .next _ σ ρ => ∃ c, ExitsTo k c ∧ Holds A fr s0 c σ ρ
  | .logik _ => True
  | .hardware _ => True

end Post

end Gabbro.Grammatik.ArenaOwnership.Body
