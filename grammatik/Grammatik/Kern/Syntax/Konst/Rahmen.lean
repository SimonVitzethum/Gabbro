module

public import Grammatik.Kern.Syntax.Konst.Rein
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Ruf.RufLogik

@[expose] public section

namespace Gabbro.Grammatik

/-! ## Frame relations and expression congruence for const evaluation.

  Worlds of a closed const program agree on slots and globals everywhere:
  fields and globals do not exist. `WeltRahmen` records that agreement, and
  `constEvalGleich` shows pure evaluation only ever observes it (via the
  existing `eval_spurfrei`), over environments related pointwise by
  `EnvGleich`. The outcome relations below carry the same frame through
  whole runs; the executable congruence over them lives in `Kongruenz`. -/

/-- Two const worlds agree: same slots, same globals. Traces may differ. -/
@[expose] def WeltRahmen (c : ConstProgram) (σ₁ σ₂ : World c.D) : Prop :=
  σ₁.slots = σ₂.slots ∧ σ₁.globs = σ₂.globs

/-- Pointwise environment agreement over one context. -/
@[expose] inductive EnvGleich (c : ConstProgram) : {Γ : Ctx} → Env c.D Γ → Env c.D Γ → Prop where
  | nil : EnvGleich c .nil .nil
  | cons : v₁ = v₂ → EnvGleich c ρ₁ ρ₂ → EnvGleich c (.cons v₁ ρ₁) (.cons v₂ ρ₂)

theorem envGleichRefl (c : ConstProgram) {Γ : Ctx} (ρ : Env c.D Γ) : EnvGleich c ρ ρ := by
  induction ρ with
  | nil => exact .nil
  | cons v _ ih => exact .cons rfl ih

theorem envGleichGet (c : ConstProgram) {Γ : Ctx} {τ : Ty} {ρ₁ ρ₂ : Env c.D Γ} (h : EnvGleich c ρ₁ ρ₂) (x : Var Γ τ) : ρ₁.get x = ρ₂.get x := by
  cases h with
  | nil => cases x
  | cons heq hrest =>
    cases x with
    | here => simp only [Env.get]; exact heq
    | there y => simp only [Env.get]; exact envGleichGet c hrest y

theorem envGleichSet (c : ConstProgram) {Γ : Ctx} {τ : Ty} {ρ₁ ρ₂ : Env c.D Γ} (h : EnvGleich c ρ₁ ρ₂) (x : Var Γ τ) (v₁ v₂ : Wert c.D τ) (hv : v₁ = v₂) : EnvGleich c (ρ₁.set x v₁) (ρ₂.set x v₂) := by
  cases h with
  | nil => cases x
  | cons _ hrest =>
    cases x with
    | here => simp only [Env.set]; exact .cons hv hrest
    | there y => simp only [Env.set]; exact .cons rfl (envGleichSet c hrest y v₁ v₂ hv)

theorem envGleichTail (c : ConstProgram) {Γ : Ctx} {τ : Ty} {ρ₁ ρ₂ : Env c.D (τ :: Γ)} (h : EnvGleich c ρ₁ ρ₂) : EnvGleich c ρ₁.tail ρ₂.tail := by
  cases h with
  | cons _ hrest => simp only [Env.tail]; exact hrest

/-- Two statement outcomes agree: same shape, same values, framed worlds. -/
@[expose] inductive AusgangGleich (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Ausgang V l Γ → Prop where
  | ok : σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → EnvGleich c ρ₁ ρ₂ → AusgangGleich c (.ok σ₁ ρ₁) (.ok σ₂ ρ₂)
  | zurueck : σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → v₁ = v₂ → AusgangGleich c (.zurueck σ₁ v₁) (.zurueck σ₂ v₂)
  | why : σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → r₁ = r₂ → AusgangGleich c (.why σ₁ r₁) (.why σ₂ r₂)
  | leave : h₁ = h₂ → σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → EnvGleich c ρ₁ ρ₂ → AusgangGleich c (.leave h₁ σ₁ ρ₁) (.leave h₂ σ₂ ρ₂)
  | next : h₁ = h₂ → σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → EnvGleich c ρ₁ ρ₂ → AusgangGleich c (.next h₁ σ₁ ρ₁) (.next h₂ σ₂ ρ₂)
  | logik : e₁ = e₂ → AusgangGleich c (.logik e₁) (.logik e₂)
  | hardware : e₁ = e₂ → AusgangGleich c (.hardware e₁) (.hardware e₂)

/-- Two end-block outcomes agree: same shape, same values, framed worlds. -/
@[expose] inductive EndGleich (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → EndAusgang V l Γ → Prop where
  | zurueck : σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → v₁ = v₂ → EndGleich c (.zurueck σ₁ v₁) (.zurueck σ₂ v₂)
  | why : σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → r₁ = r₂ → EndGleich c (.why σ₁ r₁) (.why σ₂ r₂)
  | leave : h₁ = h₂ → σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → EnvGleich c ρ₁ ρ₂ → EndGleich c (.leave h₁ σ₁ ρ₁) (.leave h₂ σ₂ ρ₂)
  | next : h₁ = h₂ → σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → EnvGleich c ρ₁ ρ₂ → EndGleich c (.next h₁ σ₁ ρ₁) (.next h₂ σ₂ ρ₂)
  | logik : e₁ = e₂ → EndGleich c (.logik e₁) (.logik e₂)
  | hardware : e₁ = e₂ → EndGleich c (.hardware e₁) (.hardware e₂)

/-- Two call outcomes agree: same shape, same value, framed worlds. -/
@[expose] inductive RufGleich (c : ConstProgram) : {f : c.D.Fn} → RufAusgang f → RufAusgang f → Prop where
  | ok : σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → v₁ = v₂ → RufGleich c (.ok σ₁ v₁) (.ok σ₂ v₂)
  | logik : e₁ = e₂ → RufGleich c (.logik e₁) (.logik e₂)
  | hardware : e₁ = e₂ → RufGleich c (.hardware e₁) (.hardware e₂)
  | why : σ₁.slots = σ₂.slots → σ₁.globs = σ₂.globs → r₁ = r₂ → RufGleich c (.why σ₁ r₁) (.why σ₂ r₂)

/-- Every two const worlds agree on slots and globals: fields and globals
    do not exist, so both maps are vacuous. -/
theorem constWeltRahmenAlle (c : ConstProgram) (σ₁ σ₂ : World c.D) : WeltRahmen c σ₁ σ₂ := by
  constructor
  · funext t k fld
    exact (c.noFields t fld).elim
  · funext g
    exact (c.noGlobals g).elim

/-! ### Pure evaluation observes only the frame. -/

mutual

/-- Pure product tuples agree field by field. -/
theorem constEvalGleichProd (c : ConstProgram) {Γ : Ctx} {τs : List Ty} {e : Args c.D Γ [] τs} (hp : ConstArgs c e) (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ) (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂) : evalProd σ₁ e σ₁ ρ₁ = evalProd σ₂ e σ₂ ρ₂ := by
  match hp with
  | .nil => by simp only [evalProd]
  | .cons he hrest => by simp only [evalProd, constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichProd c hrest σ₁ σ₂ ρ₁ ρ₂ hW hρ]

theorem constEvalGleichExpr (c : ConstProgram) {Γ : Ctx} {τ : Ty} {e : Expr c.D Γ [] τ} (hp : ConstExpr c e) (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ) (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂) : eval σ₁ e σ₁ ρ₁ = eval σ₂ e σ₂ ρ₂ :=
  match hp with
  | .pureLit => by simp only [eval]
  | .pureTru => by simp only [eval]
  | .pureFls => by simp only [eval]
  | .pureVar => by simp only [eval]; exact envGleichGet c hρ _
  | .pureWiden ih => by simp only [eval, constEvalGleichExpr c ih σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureAdd ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureSub ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureNeg ha => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureMul ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureDiv ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureRem ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureSdiv ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureSrem ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureBand ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureBor ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureBxor ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureShl ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureShr ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureLt ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureLe ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureEq ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureAnd ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureOr ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureNot ha => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureNone => by simp only [eval]
  | .pureSome he => by simp only [eval, constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureIstSome he => by simp only [eval, constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureCase hpay => by simp only [eval, constEvalGleichPayload c hpay σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureWhy => by simp only [eval]
  | .pureForallSlots hbody => by
    have ih : ∀ k, eval σ₁ _ σ₁ (.cons k ρ₁) = eval σ₂ _ σ₂ (.cons k ρ₂) :=
      fun k => constEvalGleichExpr c hbody σ₁ σ₂ (.cons k ρ₁) (.cons k ρ₂) hW (.cons rfl hρ)
    simp only [eval, ih]
  | .pureExistsSlots hbody => by
    have ih : ∀ k, eval σ₁ _ σ₁ (.cons k ρ₁) = eval σ₂ _ σ₂ (.cons k ρ₂) :=
      fun k => constEvalGleichExpr c hbody σ₁ σ₂ (.cons k ρ₁) (.cons k ρ₂) hW (.cons rfl hρ)
    simp only [eval, ih]
  | .pureArrNil => by simp only [eval]
  | .pureArrCons ha hrest => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hrest σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureArrGet ha hi => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hi σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureArrSet ha hi hv => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hi σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hv σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureStrLit => by simp only [eval]
  | .pureStrLen hs => by simp only [eval, constEvalGleichExpr c hs σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureStrCat hs ht => by simp only [eval, constEvalGleichExpr c hs σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c ht σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureStrGet hs hi => by simp only [eval, constEvalGleichExpr c hs σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hi σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureStrEq hs ht => by simp only [eval, constEvalGleichExpr c hs σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c ht σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureStrLt hs ht => by simp only [eval, constEvalGleichExpr c hs σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c ht σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureStrWeit hs => by simp only [eval, constEvalGleichExpr c hs σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureWenn hc ha hb => by simp only [eval, constEvalGleichExpr c hc σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureEng he hfall => by simp only [eval, constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hfall σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureIntBuiltin1 ha => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureIntBuiltin2 ha hb => by simp only [eval, constEvalGleichExpr c ha σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c hb σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureCount hbody => by
    have ih : ∀ k, eval σ₁ _ σ₁ (.cons k ρ₁) = eval σ₂ _ σ₂ (.cons k ρ₂) :=
      fun k => constEvalGleichExpr c hbody σ₁ σ₂ (.cons k ρ₁) (.cons k ρ₂) hW (.cons rfl hρ)
    simp only [eval, ih]
  | .pureProd hargs => by simp only [eval, constEvalGleichProd c hargs σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureProdGet hv => by simp only [eval, constEvalGleichExpr c hv σ₁ σ₂ ρ₁ ρ₂ hW hρ]
  | .pureProdSet hv he => by simp only [eval, constEvalGleichExpr c hv σ₁ σ₂ ρ₁ ρ₂ hW hρ, constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ]

/-- Pure tag payloads agree: the empty payload is unit, a value payload
    evaluates its expression. -/
theorem constEvalGleichPayload (c : ConstProgram) {Γ : Ctx} {k : Option Ty} {e : NutzlastExpr c.D Γ [] k} (hp : ConstPayload c e) (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ) (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂) : evalNutz σ₁ e σ₁ ρ₁ = evalNutz σ₂ e σ₂ ρ₂ := by
  cases hp with
  | empty => simp only [evalNutz]
  | val he => simp only [evalNutz, constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ]
end

/-- Pure call arguments agree: evaluation is pointwise over the expressions,
    so environments that agree pointwise evaluate identically. -/
theorem constEvalGleichArgs (c : ConstProgram) {Γ : Ctx} {τs : List Ty} {e : Args c.D Γ [] τs} (hp : ConstArgs c e) (σ₁ σ₂ : World c.D) (ρ₁ ρ₂ : Env c.D Γ) (hW : WeltRahmen c σ₁ σ₂) (hρ : EnvGleich c ρ₁ ρ₂) : evalArgs σ₁ e σ₁ ρ₁ = evalArgs σ₂ e σ₂ ρ₂ := by
  induction hp with
  | nil => rfl
  | cons he _ ih => simp only [evalArgs, constEvalGleichExpr c he σ₁ σ₂ ρ₁ ρ₂ hW hρ, ih]
