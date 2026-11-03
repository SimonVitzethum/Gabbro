module

public import Grammatik.Kern.Syntax.Konst.Zertifikat
public import Grammatik.Kern.Syntax.Konst.Geschlossen
public import Grammatik.Kern.Syntax.Konst.Literal
public import Grammatik.Kern.Syntax.Konst.Zeuge

@[expose] public section

namespace Gabbro.Grammatik

/-! ## Certified call-site substitution inside closed const bodies.

  A call of an admitted const function with closed arguments is evaluated
  at compile time: the certified value (`ConstCallCertificate`,
  `evalConstCall`, `const_call_sound`) replaces the call by the literal of
  the SAME value (`ConstLit`, `constLit_exact`). Closed arguments evaluate
  independently of the environment (`geschlossen_args_eval`) and read no
  places (`geschlossen_args_orte`); the literal reads nothing either
  (`constLit_orte`). Hence with `World.lese` over the empty place list
  (`lese_leer` below) neither the argument evaluation nor the literal
  appends a runtime trace event.

  That is the precise trace/budget claim of this slice: the substitution
  preserves results and the world frame (slots and globals, as `EndGleich`;
  traces are explicitly excluded from the frame, see `WeltRahmen`), and the
  introduced literal itself contributes no trace event and no budget: its
  place list is empty, so `World.lese` is the identity, and the work bound
  (`constArbeitsSchranke`) is checked at compile time, never consumed at
  runtime. A const call therefore contributes no runtime trace/call-log
  entry and no budget *through this substitution*: the runtime program
  never calls the const function, whose declaration is dropped from the
  runtime unit (`fnItems`).

  Refusal boundary: statement calls (`Stmt.call`, `Block`/`Endblock`
  `cons` heads) are NOT substituted here. They would appear in a thread's
  call log, which `FolgeG` observes, and their removal could hide an
  ordering duty; likewise any timing duty `ZeitAb` would observe is kept
  refused. Only value-binding calls (`bindCall`) with a certified value
  and an exact literal are replaced, and every other const-call shape keeps
  the program refused rather than weakening a guarantee. The surface pass
  (`Parser/Elab/Konst/Ersetzung`) lifts this to source call sites and
  refuses open-argument calls there. -/

/-- Reading no places leaves the world unchanged. -/
theorem lese_leer (σ : World D) (Λ : List (Res D)) : σ.lese Λ [] = σ := by
  cases σ with
  | mk s g p => rfl

/-- Closed call arguments read nothing, so the pre-read is the identity. -/
theorem geschlossen_args_lese (c : ConstProgram) {Γ : Ctx} {τs : List Ty}
    {args : Args c.D Γ [] τs} (h : GeschlossenArgs c args)
    (σ : World c.D) (Λ : List (Res c.D)) : σ.lese Λ args.orte = σ := by
  rw [geschlossen_args_orte c h]
  exact lese_leer σ Λ

/-- A certified literal reads nothing, so its pre-read is the identity. -/
theorem constLit_lese (c : ConstProgram) {Γ : Ctx} {τ : Ty} {v : Wert c.D τ}
    {e : Expr c.D Γ [] τ} (h : ConstLit c v e)
    (σ : World c.D) (Λ : List (Res c.D)) : σ.lese Λ e.orte = σ := by
  rw [constLit_orte c h]
  exact lese_leer σ Λ

/-- Every call outcome agrees with itself. -/
theorem rufGleichRefl (c : ConstProgram) {f : c.D.Fn} (o : RufAusgang f) :
    RufGleich c o o := by
  cases o with
  | ok σ v => exact .ok rfl rfl rfl
  | why σ r => exact .why rfl rfl rfl
  | logik e => exact .logik rfl
  | hardware e => exact .hardware rfl

/-- Shrinking an agreed end outcome past one binder preserves agreement. -/
theorem schrumpfEndGleich (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {τ : Ty} {o₁ o₂ : EndAusgang V l (τ :: Γ)}
    (h : EndGleich c o₁ o₂) : EndGleich c o₁.schrumpf o₂.schrumpf := by
  cases h with
  | zurueck _ _ _ _ hS hG hv =>
    simp only [EndAusgang.schrumpf]
    exact EndGleich.zurueck hS hG hv
  | why _ _ _ _ hS hG hr =>
    simp only [EndAusgang.schrumpf]
    exact EndGleich.why hS hG hr
  | leave _ _ _ _ _ _ hEq hS hG hρ =>
    simp only [EndAusgang.schrumpf]
    exact EndGleich.leave hEq hS hG (envGleichTail c hρ)
  | next _ _ _ _ _ _ hEq hS hG hρ =>
    simp only [EndAusgang.schrumpf]
    exact EndGleich.next hEq hS hG (envGleichTail c hρ)
  | logik _ _ he =>
    simp only [EndAusgang.schrumpf]
    exact EndGleich.logik he
  | hardware _ _ he =>
    simp only [EndAusgang.schrumpf]
    exact EndGleich.hardware he

/-- Single replacement: a certified `bindCall` with closed arguments runs
    like binding the exact literal. The continuation is unchanged; the
    handler is the canonical `rufAt` at sufficient depth, so
    `const_call_sound` supplies the certified answer with its frame. -/
theorem const_bindCall_ersetzt_single
    (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {τ : Ty}
    {f : c.D.Fn} {args_syn : Args c.D Γ [] (c.D.params f)}
    {he : c.D.erg f = some τ}
    {hp : RufPasst c.D V (c.D.signatur f) []}
    {hr : c.D.gruende f = 0}
    {hnach : nach c.D f [] = []}
    {rest : Endblock c.D V l (τ :: Γ) (nach c.D f [])}
    {e_lit : Expr c.D Γ [] τ}
    (hgeschlossen : GeschlossenArgs c args_syn)
    (hrest : ConstEnd c (hnach ▸ rest))
    (hadm : ConstAdmissible c) (n : Nat) (hterm : ConstTermination c n)
    (σ : World c.D) (ρ : Env c.D Γ) (O : Orakel c.D) (passes depth : Nat)
    (cert : ConstCallCertificate c f (evalArgs σ args_syn σ ρ))
    (hlit : ConstLit c (ergWert he cert.value) e_lit)
    (hdepth : max cert.bound (n + 1) ≤ depth) :
    EndGleich c
      (execEnd O passes (rufAt c.P O passes depth)
        (Endblock.bindCall f args_syn he hp hr rest) σ ρ)
      (execEnd O passes (rufAt c.P O passes depth)
        (Endblock.bind e_lit (hnach ▸ rest)) σ ρ) := by
  have horte : args_syn.orte = [] := geschlossen_args_orte c hgeschlossen
  have horteLit : e_lit.orte = [] := constLit_orte c hlit
  have hlitEq : eval σ e_lit σ ρ = ergWert he cert.value :=
    constLit_exact c hlit σ ρ
  obtain ⟨σ', hcall, hS, hG⟩ :=
    const_call_sound c f (evalArgs σ args_syn σ ρ) cert hadm n hterm σ O passes depth hdepth
  have hW : WeltRahmen c σ' σ := ⟨hS, hG⟩
  have hρ : EnvGleich c
      (.cons (ergWert he cert.value) ρ) (.cons (eval σ e_lit σ ρ) ρ) :=
    .cons hlitEq.symm (envGleichRefl c ρ)
  have hagree : ∀ g (σ₁ σ₂ : World c.D) (ρ : Env c.D (c.D.params g)),
      WeltRahmen c σ₁ σ₂ →
        RufGleich c (rufAt c.P O passes depth g σ₁ ρ)
          (rufAt c.P O passes depth g σ₂ ρ) := by
    intro g σ₁ σ₂ ρ hW'
    exact constRufGleich c hadm depth g σ₁ σ₂ ρ O O passes passes hW'
  have hrel : EndGleich c
      (execEnd O passes (rufAt c.P O passes depth) (hnach ▸ rest) σ'
        (.cons (ergWert he cert.value) ρ))
      (execEnd O passes (rufAt c.P O passes depth) (hnach ▸ rest) σ
        (.cons (eval σ e_lit σ ρ) ρ)) :=
    constEndGleich c hrest O O passes passes
      (rufAt c.P O passes depth) (rufAt c.P O passes depth)
      σ' σ (.cons (ergWert he cert.value) ρ) (.cons (eval σ e_lit σ ρ) ρ)
      hW hρ hagree
  have hL : execEnd O passes (rufAt c.P O passes depth)
        (Endblock.bindCall f args_syn he hp hr rest) σ ρ =
      (execEnd O passes (rufAt c.P O passes depth) (hnach ▸ rest) σ'
        (.cons (ergWert he cert.value) ρ)).schrumpf := by
    cases hnach
    simp only [execEnd, horte, lese_leer, hcall]
  have hR : execEnd O passes (rufAt c.P O passes depth)
        (Endblock.bind e_lit (hnach ▸ rest)) σ ρ =
      (execEnd O passes (rufAt c.P O passes depth) (hnach ▸ rest) σ
        (.cons (eval σ e_lit σ ρ) ρ)).schrumpf := by
    simp only [execEnd, horteLit, lese_leer]
  rw [hL, hR]
  exact schrumpfEndGleich c hrel

/-! ### Context congruence and the refusal boundary.

  `bind` and `ite` contexts preserve `EndGleich` when their continuations
  do: the head expression is unchanged, so the branch taken and the bound
  value agree. In this slice the congruence is used once, inside
  `const_bindCall_ersetzt_single` via `schrumpfEndGleich` above: the
  continuation `rest` is unchanged, only its entry world moves along the
  certified frame. General statements (`cons` heads, including `Stmt.call`)
  have no substitution case here: a program needing them keeps its refusal
  instead of silently dropping a call-log entry `FolgeG` would observe,
  and likewise any timing duty `ZeitAb` would observe. The surface pass
  (`Parser/Elab/Konst/Ersetzung`) lifts single replacement to source call
  sites by structural recursion and refuses open-argument calls there. -/

/-- Reading nothing is witnessed on the canonical empty trace. -/
theorem lese_leer_zeuge :
    (constWelt ConstWitness.fixtureA).lese [] [] = constWelt ConstWitness.fixtureA := by
  cases (constWelt ConstWitness.fixtureA) with
  | mk s g p => rfl

end Gabbro.Grammatik
