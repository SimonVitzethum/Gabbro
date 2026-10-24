import Grammatik.Bausteine.Arena.Ownership.Machine.Push
import Grammatik.Bausteine.Arena.Ownership.Machine.Exit
import Grammatik.Bausteine.Arena.Ownership.Body.Program
import Grammatik.Logik.Ruf.Maschine.RufMaschineG

/-! **Ownership on the whole machine.** One ledger agrees with the shared
memory and keeps its discipline against the stack depth of every thread.
In every thread the running activation is in a `Head` state, and every
suspended activation realises, over the ledger it sees, the context it
resumes from when its callee returns (`Resume`: the residue unchanged after
a plain call, the bound result in front of the rest after a binding call,
the `else` branch after a reason). -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

/-- **What a suspended caller resumes with**, by the residue it waits in: `k` is its loop context,
    `cs` its context after the call, `owner` whether the callee hands back an allocation. -/
inductive Resume (A : FreiForm D) (I : Interfaces A) (f : D.Fn) (k cs : Context) (owner : Bool) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D (vertragVon D f) l Γ Λ → Prop where
  | plain {l Γ Λ} (r : GRest D (vertragVon D f) l Γ Λ) (hr : OR A I (I f).output k (dropContextB cs owner) r) :
      Resume A I f k cs owner r
  | wartet {l Γ Λ Λ' τ} (rest : Block D (vertragVon D f) l (τ :: Γ) Λ Λ') (r : GRest D (vertragVon D f) l Γ Λ')
      (hr : OR A I (I f).output k (resultContextB cs owner) (.dann rest (.schrumpf r))) :
      Resume A I f k cs owner (.wartet rest r)
  | wartetSonst {l Γ Λ Λ' τ} (n : Nat) (err : Endblock D (vertragVon D f) l (.why n :: Γ) Λ)
      (rest : Block D (vertragVon D f) l (τ :: Γ) Λ Λ') (r : GRest D (vertragVon D f) l Γ Λ')
      (hr : OR A I (I f).output k (resultContextB cs owner) (.dann rest (.schrumpf r)))
      (he : OR A I (I f).output k (cs.bind none) (.dann err.alsBlock.2 (.abbruch (.schrumpf r)))) :
      Resume A I f k cs owner (.wartetSonst n err rest r)

/-- **A suspended activation `fr` of `f`**, waiting on a callee of `callee`, over the ledger it sees. -/
inductive Susp (A : FreiForm D) (I : Interfaces A) (fr : Frame) (s : State) (callee f : D.Fn) :
    (Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D f) l Γ Λ) → Prop where
  | mk {l Γ Λ k cs g} (ρ : Env D Γ) (r : GRest D (vertragVon D f) l Γ Λ) (hk : k.references.length ≤ Γ.length)
      (hf : FrameOk cs g (s.viewAt fr) fr ρ) (hres : Resume A I f k cs (Flow.Output.isOwner (I callee).output) r) :
      Susp A I fr s callee f ⟨l, Γ, Λ, ρ, r⟩

/-- The suspended activations of thread `t`, the innermost first, each waiting on the one above. -/
def StackOk (A : FreiForm D) (I : Interfaces A) (s : State) (t : Faden) : D.Fn → List (RufRahmenG D) → Prop
  | _, [] => True
  | callee, r :: rest => Susp A I ⟨t, rest.length⟩ s callee r.f r.rest ∧ StackOk A I s t r.f rest

/-- **One thread**: its running activation at the depth of its stack, its stack below. -/
def ThreadOk (A : FreiForm D) (I : Interfaces A) (s : State) (σ : World D) (t : Faden) (th : RufFadenG D) :
    Prop :=
  Head A I ⟨t, th.stapel.length⟩ s σ th.kopf.f th.kopf.rest ∧ StackOk A I s t th.kopf.f th.stapel

/-- The running depth of every thread. -/
def depthOf (M : RufMaschineG D) : Nat → Nat := fun t => (M.faeden t).stapel.length

/-- **Ownership on the machine `M`** for the arena `A` with interfaces `I`. -/
def OwnInv (A : FreiForm D) (I : Interfaces A) (M : RufMaschineG D) : Prop :=
  ∃ s : State, s.agrees A (M.speicher.welt []) ∧ A.FreiOk (M.speicher.welt []) ∧ s.Disciplined (depthOf M) ∧
    ∀ t, ThreadOk A I s (M.speicher.welt []) t (M.faeden t)

/-! ## The start -/

/-- **What the start owes the arena**: the list is well formed and no slot is live, and every start
    routine's interface precondition holds over the empty ledger (it is handed no allocation). -/
structure StartOwn (A : FreiForm D) (I : Interfaces A) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop where
  frei : A.FreiOk (sp.welt [])
  leer : ∀ i, ¬ A.Lebt (sp.welt []) i
  req : ∀ t, ((I (init t).1).contract A).requires ⟨t, 0⟩ State.empty (init t).2

theorem empty_disciplined (depth : Nat → Nat) : State.empty.Disciplined depth := by
  intro i c hc; cases hc

/-- **Ownership holds at the start.** -/
theorem ownInv_start {P : Programm D} {A : FreiForm D} {I : Interfaces A} (hc : Checked P A I)
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)} (hs : StartOwn A I sp init) :
    OwnInv A I (RufStartG P sp init) := by
  refine ⟨State.empty, ⟨State.empty_valid, fun i => ⟨fun h => absurd h (hs.leer i), fun ⟨_, h⟩ => by cases h⟩⟩,
    hs.frei, empty_disciplined _, fun t => ?_⟩
  have hreq := hs.req t
  simp only [ThreadOk, RufStartG]
  generalize init t = x at hreq
  obtain ⟨g, rho⟩ := x
  obtain ⟨gh, href, hr, hcomp⟩ := hreq
  exact ⟨.run rho _ (Nat.zero_le _) ⟨Flow.parameterContext_bounded _, href, hr, hcomp⟩ (.ende _ (hc g)), trivial⟩

end Gabbro.Grammatik.ArenaOwnership.Machine
