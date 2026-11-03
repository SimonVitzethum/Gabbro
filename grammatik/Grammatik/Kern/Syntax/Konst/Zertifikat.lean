module

public import Grammatik.Kern.Syntax.Konst.Auswertung
public import Grammatik.Kern.Syntax.Konst.Kongruenz
public import Grammatik.Kern.Syntax.Konst.Rang
public import Grammatik.Logik.Ruf.RufTiefe

@[expose] public section

namespace Gabbro.Grammatik

/-! ## Soundness of checked const calls.

  `const_call_sound`: for every admissible, terminating program with a
  successful checked evaluation to `v`, every world, oracle, pass count and
  every depth at or above the certified bound, `rufAt` answers `.ok` with
  the same value, and the answer world keeps the input slots and globals
  (the design's frame condition: reads only append trace events). The proof
  goes by induction on the rank-free structural congruence (`constRufGleich`)
  plus depth stability (`rufAt_stabil_ab`); frame preservation is proved
  separately from `constWeltRahmenAlle`: a closed const program has no
  fields or globals, so every outcome world satisfies the frame. The
  termination rank is not consumed by the congruence itself; `n` fixes the
  certified depth bound. Uniqueness, depth stability and error
  correspondence follow separately below. -/

/-- Frame predicates over single outcomes: every world inside agrees with
    the entry world on slots and globals. -/
inductive AusgangErhaelt (c : ConstProgram) (σ : World c.D) : Ausgang V l Γ → Prop where
  | ok : σ'.slots = σ.slots → σ'.globs = σ.globs → AusgangErhaelt c σ (.ok σ' ρ')
  | zurueck : σ'.slots = σ.slots → σ'.globs = σ.globs → AusgangErhaelt c σ (.zurueck σ' v)
  | why : σ'.slots = σ.slots → σ'.globs = σ.globs → AusgangErhaelt c σ (.why σ' r)
  | leave : σ'.slots = σ.slots → σ'.globs = σ.globs → AusgangErhaelt c σ (.leave h σ' ρ')
  | next : σ'.slots = σ.slots → σ'.globs = σ.globs → AusgangErhaelt c σ (.next h σ' ρ')
  | logik (e : Logik c.D) : AusgangErhaelt c σ (.logik e)
  | hardware (e : Hardware c.D) : AusgangErhaelt c σ (.hardware e)

inductive EndErhaelt (c : ConstProgram) (σ : World c.D) : EndAusgang V l Γ → Prop where
  | zurueck : σ'.slots = σ.slots → σ'.globs = σ.globs → EndErhaelt c σ (.zurueck σ' v)
  | why : σ'.slots = σ.slots → σ'.globs = σ.globs → EndErhaelt c σ (.why σ' r)
  | leave : σ'.slots = σ.slots → σ'.globs = σ.globs → EndErhaelt c σ (.leave h σ' ρ')
  | next : σ'.slots = σ.slots → σ'.globs = σ.globs → EndErhaelt c σ (.next h σ' ρ')
  | logik (e : Logik c.D) : EndErhaelt c σ (.logik e)
  | hardware (e : Hardware c.D) : EndErhaelt c σ (.hardware e)

inductive RufErhaelt (c : ConstProgram) (σ : World c.D) : RufAusgang f → Prop where
  | ok : σ'.slots = σ.slots → σ'.globs = σ.globs → RufErhaelt c σ (.ok σ' v)
  | why : σ'.slots = σ.slots → σ'.globs = σ.globs → RufErhaelt c σ (.why σ' r)
  | logik (e : Logik c.D) : RufErhaelt c σ (.logik e)
  | hardware (e : Hardware c.D) : RufErhaelt c σ (.hardware e)

/-- Closed const worlds have the same data even when reads extend the trace.
    Prove the frame once for arbitrary outcomes, independently of execution. -/
private theorem ausgangErhaeltAlle (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    (σ : World c.D) (o : Ausgang V l Γ) : AusgangErhaelt c σ o := by
  cases o with
  | ok s _ => exact .ok (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | zurueck s _ => exact .zurueck (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | why s _ => exact .why (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | leave _ s _ => exact .leave (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | next _ s _ => exact .next (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | logik e => exact .logik e
  | hardware e => exact .hardware e

private theorem endErhaeltAlle (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    (σ : World c.D) (o : EndAusgang V l Γ) : EndErhaelt c σ o := by
  cases o with
  | zurueck s _ => exact .zurueck (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | why s _ => exact .why (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | leave _ s _ => exact .leave (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | next _ s _ => exact .next (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | logik e => exact .logik e
  | hardware e => exact .hardware e

private theorem rufErhaeltAlle (c : ConstProgram) {f : c.D.Fn}
    (σ : World c.D) (o : RufAusgang f) : RufErhaelt c σ o := by
  cases o with
  | ok s _ => exact .ok (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | why s _ => exact .why (constWeltRahmenAlle c s σ).1 (constWeltRahmenAlle c s σ).2
  | logik e => exact .logik e
  | hardware e => exact .hardware e

theorem constStmtErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Stmt c.D V l Γ [] []} (h : ConstStmt c body)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ : World c.D) (ρ : Env c.D Γ)
    (hR : ∀ (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g)),
      RufErhaelt c σ (R g σ ρ)) :
    AusgangErhaelt c σ (execStmt O p R body σ ρ) :=
  ausgangErhaeltAlle c σ _

theorem constBlockErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Block c.D V l Γ [] []} (h : ConstBlock c body)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ : World c.D) (ρ : Env c.D Γ)
    (hR : ∀ (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g)),
      RufErhaelt c σ (R g σ ρ)) :
    AusgangErhaelt c σ (execBlock O p R body σ ρ) :=
  ausgangErhaeltAlle c σ _

theorem constEndErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {body : Endblock c.D V l Γ []} (h : ConstEnd c body)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (σ : World c.D) (ρ : Env c.D Γ)
    (hR : ∀ (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g)),
      RufErhaelt c σ (R g σ ρ)) :
    EndErhaelt c σ (execEnd O p R body σ ρ) :=
  endErhaeltAlle c σ _

theorem constArmsErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {arms : Arms c.D V l Γ [] [] cs} (h : ConstArms c arms)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (v : Wert c.D (.sum cs)) (σ : World c.D) (ρ : Env c.D Γ)
    (hR : ∀ (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g)),
      RufErhaelt c σ (R g σ ρ)) :
    AusgangErhaelt c σ (execArms O p R arms v σ ρ) :=
  ausgangErhaeltAlle c σ _

theorem constReasonErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {arms : GrundArms c.D V l Γ [] [] n} (h : ConstReasonArms c arms)
    (O : Orakel c.D) (p : Nat)
    (R : ∀ g : c.D.Fn, World c.D → Env c.D (c.D.params g) → RufAusgang g)
    (v : Fin n) (σ : World c.D) (ρ : Env c.D Γ)
    (hR : ∀ (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g)),
      RufErhaelt c σ (R g σ ρ)) :
    AusgangErhaelt c σ (execGrund O p R arms v σ ρ) :=
  ausgangErhaeltAlle c σ _

/-- Shrinking preserves the single-run frame of a closed const world. -/
theorem schrumpfArmErhaelt (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {k : Option Ty} {o : Ausgang V l (ArmCtx Γ k)} {σ : World c.D}
    (h : AusgangErhaelt c σ o) : AusgangErhaelt c σ (o.schrumpfArm k) :=
  ausgangErhaeltAlle c σ _

/-- Const calls keep slots and globals independently of their control flow. -/
theorem constRufErhaelt (c : ConstProgram) (hadm : ConstAdmissible c) :
    ∀ (d : Nat) (g : c.D.Fn) (σ : World c.D) (ρ : Env c.D (c.D.params g))
      (O : Orakel c.D) (p : Nat),
      RufErhaelt c σ (rufAt c.P O p d g σ ρ) := by
  intro d g σ ρ O p
  exact rufErhaeltAlle c σ _

/-- Generic meaning theorem: a successful checked evaluation denotes the
    same value at every world, oracle, pass count and sufficient depth,
    with the design's frame condition. -/
theorem const_call_sound (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (cert : ConstCallCertificate c f args) (hadm : ConstAdmissible c) (n : Nat)
    (hterm : ConstTermination c n) :
    ∀ (σ : World c.D) (O : Orakel c.D) (passes depth : Nat),
      max cert.bound (n + 1) ≤ depth →
      ∃ σ', rufAt c.P O passes depth f σ args = RufAusgang.ok σ' cert.value ∧ σ'.slots = σ.slots ∧ σ'.globs = σ.globs := by
  have _ := hterm
  intro σ O passes depth hdepth
  have hok := cert.equation
  have hnab : ∀ g : c.D.Fn, rufAt c.P (constOrakel c) 0 cert.bound f (constWelt c) args ≠ RufAusgang.logik (.abstieg g) := by
    intro g hcon
    rw [hok] at hcon
    cases hcon
  have hmax : cert.bound + (max cert.bound (n + 1) - cert.bound) = max cert.bound (n + 1) :=
    Nat.add_sub_cancel' (Nat.le_max_left cert.bound (n + 1))
  have hcanon := rufAt_stabil_ab c.P (constOrakel c) 0 cert.bound f (constWelt c) args hnab (max cert.bound (n + 1) - cert.bound)
  rw [hmax] at hcanon
  rw [hok] at hcanon
  have hW := constWeltRahmenAlle c (constWelt c) σ
  have hrel := constRufGleich c hadm (max cert.bound (n + 1)) f (constWelt c) σ args (constOrakel c) O 0 passes hW
  rw [hcanon] at hrel
  cases harb : rufAt c.P O passes (max cert.bound (n + 1)) f σ args with
  | ok σ' v' =>
    have hnab' : ∀ g : c.D.Fn, rufAt c.P O passes (max cert.bound (n + 1)) f σ args ≠ RufAusgang.logik (.abstieg g) := by
      intro g hcon
      rw [harb] at hcon
      cases hcon
    have hstep : max cert.bound (n + 1) + (depth - max cert.bound (n + 1)) = depth :=
      Nat.add_sub_cancel' hdepth
    have hstab := rufAt_stabil_ab c.P O passes (max cert.bound (n + 1)) f σ args hnab' (depth - max cert.bound (n + 1))
    rw [hstep, harb] at hstab
    rw [harb] at hrel
    cases hrel with
    | ok _ _ hv' =>
      refine ⟨σ', ?_, (constWeltRahmenAlle c σ' σ).1, (constWeltRahmenAlle c σ' σ).2⟩
      rw [hstab, ← hv']
  | why _ _ =>
    rw [harb] at hrel
    cases hrel
  | logik _ =>
    rw [harb] at hrel
    cases hrel
  | hardware _ =>
    rw [harb] at hrel
    cases hrel

/-- Uniqueness: two certificates over one call denote one value. -/
theorem const_call_eindeutig (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (cert₁ cert₂ : ConstCallCertificate c f args) (hadm : ConstAdmissible c) (n : Nat)
    (hterm : ConstTermination c n) :
    cert₁.value = cert₂.value := by
  let depth := max (max cert₁.bound (n + 1)) (max cert₂.bound (n + 1))
  have hD₁ : max cert₁.bound (n + 1) ≤ depth := Nat.le_max_left _ _
  have hD₂ : max cert₂.bound (n + 1) ≤ depth := Nat.le_max_right _ _
  obtain ⟨s₁, e₁, _, _⟩ := const_call_sound c f args cert₁ hadm n hterm (constWelt c) (constOrakel c) 0 depth hD₁
  obtain ⟨s₂, e₂, _, _⟩ := const_call_sound c f args cert₂ hadm n hterm (constWelt c) (constOrakel c) 0 depth hD₂
  rw [e₁] at e₂
  exact (RufAusgang.ok.inj e₂).2

/-- Depth stability: past its bound the certified call no longer moves. -/
theorem const_call_stabil (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (cert : ConstCallCertificate c f args) :
    ∀ k : Nat, rufAt c.P (constOrakel c) 0 (cert.bound + k) f (constWelt c) args = rufAt c.P (constOrakel c) 0 cert.bound f (constWelt c) args := by
  intro k
  have hnab : ∀ g : c.D.Fn, rufAt c.P (constOrakel c) 0 cert.bound f (constWelt c) args ≠ RufAusgang.logik (.abstieg g) := by
    intro g hcon
    rw [cert.equation] at hcon
    cases hcon
  exact rufAt_stabil_ab c.P (constOrakel c) 0 cert.bound f (constWelt c) args hnab k

/-- Error correspondence, contract half: a failed requires or ensures maps
    to the matching `vorbedingung`/`nachbedingung` outcome, never to a value. -/
theorem const_call_fehlerVertrag (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat) (g : c.D.Fn)
    (haufwand : constArbeitsSchranke c f ≤ limit)
    (h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.logik (.vorbedingung g) ∨ rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.logik (.nachbedingung g)) :
    evalConstCall c f args limit = ConstCallResult.contract g := by
  rcases h with h | h <;>
  (unfold evalConstCall
   rw [if_pos haufwand]
   split <;> simp_all)

/-- Error correspondence, exhaustion half: exhausted fuel refuses with the
    used and allowed work. -/
theorem const_call_fehlerErschoepft (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat) (g : c.D.Fn)
    (haufwand : constArbeitsSchranke c f ≤ limit)
    (h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.logik (.abstieg g)) :
    evalConstCall c f args limit = ConstCallResult.exhausted (constArbeitsSchranke c f) limit := by
  unfold evalConstCall
  rw [if_pos haufwand]
  split <;> simp_all

/-- Error correspondence, limit half: work past the limit refuses before
    any reduction. -/
theorem const_call_fehlerLimit (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat)
    (hneg : ¬ constArbeitsSchranke c f ≤ limit) :
    evalConstCall c f args limit = ConstCallResult.exhausted (constArbeitsSchranke c f) limit := by
  simp only [evalConstCall, if_neg hneg]

/-- Error correspondence, range half: a range failure never denotes. -/
theorem const_call_fehlerBereich (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat)
    (haufwand : constArbeitsSchranke c f ≤ limit)
    (h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.logik .bereich) :
    evalConstCall c f args limit = ConstCallResult.range f := by
  unfold evalConstCall
  rw [if_pos haufwand]
  split <;> simp_all

/-- Error correspondence, dependency half: a hardware answer needed outside
    the closed program refuses as an unresolved dependency. -/
theorem const_call_fehlerHardware (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat) (e : Hardware c.D)
    (haufwand : constArbeitsSchranke c f ≤ limit)
    (h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.hardware e) :
    evalConstCall c f args limit = ConstCallResult.dependency f := by
  unfold evalConstCall
  rw [if_pos haufwand]
  split <;> simp_all

/-- Error correspondence, reason half: the absent reason channel refuses as
    an unresolved dependency. -/
theorem const_call_fehlerGrund (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (limit : Nat) (w : World c.D) (r : Fin (c.D.gruende f))
    (haufwand : constArbeitsSchranke c f ≤ limit)
    (h : rufAt c.P (constOrakel c) 0 (constTiefenSchranke c) f (constWelt c) args = RufAusgang.why w r) :
    evalConstCall c f args limit = ConstCallResult.dependency f := by
  unfold evalConstCall
  rw [if_pos haufwand]
  split <;> simp_all

end Gabbro.Grammatik
