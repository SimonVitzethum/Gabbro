/-
  File:      stage0/Stage0/Senke/Bild/Rest.lean
  Subject:   The rest of a body behind the decomposed prefix (image theorem, piece T1, the end of the run).
             `BodyFrame.randIR_ende`: from ANY body boundary the image runs the rest of the body as its sequential
             outcome says (`lowEnd_ok` on the boundary's own premises): a return reaches the caller's return pc with
             the result after the ensures and owed-invariant checks, or stops with the code of the failed check
             (`RetZR`); a reason return returns the reason (`RetWhyR`); a logic or hardware outcome stops with its
             code (`Stops`, `logikCode`/`hwCode`). `BodyFrame.randIR_rueck`: at a boundary in front of a final
             `return e`, that outcome is the return of the value of `e` at the world after its reads. With
             `bild_ziel_seq` (whose last case is a corresponding boundary `Rand … ebe …`) this extends the image side
             to the end of the body. Machine G's side there: for the root (`stapel = []`) no `rueck` step exists,
             the root thread stays at its return residue, and the leg `StartEndeG` of `Ziel` at that machine says
             that `ensures` and the owed invariants hold there.
-/
module
public import Stage0.Senke.Bild.Korrespondenz
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## A binding at the head of a body (used by witnesses) -/

/-- The end block begins with a `let` binding. -/
def bindKopf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .bind .. => true
  | _ => false

/-- **A non-empty decomposed prefix from a decided head**: an end block that begins with a `let` binding IS that
    binding followed by its rest, and the binding alone is a decomposed prefix, for every frame, world and
    environment. -/
theorem zerlegung_bindKopf (B : BodyFrame D) (Agl : D.Lock → Prop) (Cg : D.Fn → Prop) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ} (h : bindKopf eb = true) (σ : World D)
    (ρ : Env D Γ) :
    ∃ (τ : Ty) (e : Expr D Γ Λ τ) (rest : Endblock D (vertragVon D B.f) l (τ :: Γ) Λ),
      eb = .bind e rest ∧
      Zerlegung B Agl Cg eb σ ρ rest (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by
  cases eb with
  | bind e rest =>
    exact ⟨_, e, rest, rfl, Zerlegung.bind (B := B) (Agl := Agl) (Cg := Cg) e rest rest σ _ ρ _
      (Zerlegung.halt (B := B) (Agl := Agl) (Cg := Cg) rest _ _)⟩
  | _ => simp [bindKopf] at h

variable [Kern]

/-- **The rest of the body from a boundary**: the image at a boundary of the end block `eb` runs it as `execEnd`
    says, with the targets of the enclosing loop behind the code `c` of `eb`. -/
theorem BodyFrame.randIR_ende {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ} {pc : Runner.W}
    {m : Runner.Mem} {σ : World D} {ρ : Env D Γ} (h : B.RandIR eb pc m σ ρ) :
    ∃ c : List II, Ret B.L B.P B.f B.σ0 B.ρ0 B.fp B.lo B.K B.pr B.rp B.cfp ⟨pc, B.fp⟩ m
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 B.ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 B.ex.2)
      (execEnd B.O B.passes B.R eb σ ρ) B.reserved B.sc := by
  obtain ⟨c, top, hl, hK, hs, hp, hlo, hu, hk, hWa, hpr, hH⟩ := h
  exact ⟨c, lowEnd_ok (O := B.O) (passes := B.passes) (R := B.R) (rp := B.rp) (cfp := B.cfp) (σ0 := B.σ0)
    (ρ0 := B.ρ0) (ex := B.ex) hB.spec hB.addr hB.lo0 hB.ens hB.scH eb hH c top hl hK hs hB.win m pc σ ρ hp hlo
    hu hk hWa hpr⟩

/-- **The final return**: at a boundary in front of `return e`, the image returns the value of `e` at the world after
    the reads of `e` — to the caller's return pc after the ensures and owed-invariant checks, or it stops with the code
    of the failed check (`Ret` of `.zurueck`, which is `RetZR` under the pending releases `B.sc`). -/
theorem BodyFrame.randIR_rueck {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {e : ErgExpr D Γ Λ (vertragVon D B.f).erg}
    {hΛ : Λ.Perm (vertragVon D B.f).ende} {pc : Runner.W} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : B.RandIR (l := l) (.ret e hΛ) pc m σ ρ) :
    ∃ c : List II, Ret B.L B.P B.f B.σ0 B.ρ0 B.fp B.lo B.K B.pr B.rp B.cfp ⟨pc, B.fp⟩ m
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 B.ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 B.ex.2) (l := l) (Γ := Γ)
      (EndAusgang.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) B.reserved B.sc :=
  BodyFrame.randIR_ende hB h

/-- **The rest of the body behind a corresponding boundary**: `randIR_ende` on the image side of `Rand`. -/
theorem rand_ende {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok) {thr : Faden}
    {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ} {pc : Runner.W}
    {m : Runner.Mem} {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : Rand B thr stapel rho s0 Agl eb pc m M σ ρ) :
    ∃ c : List II, Ret B.L B.P B.f B.σ0 B.ρ0 B.fp B.lo B.K B.pr B.rp B.cfp ⟨pc, B.fp⟩ m
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 B.ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 B.ex.2)
      (execEnd B.O B.passes B.R eb σ ρ) B.reserved B.sc :=
  BodyFrame.randIR_ende hB h.1

end Gabbro.Stage0.Senke.BildLauf
