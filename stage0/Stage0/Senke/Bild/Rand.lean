/-
  File:      stage0/Stage0/Senke/Bild/Rand.lean
  Subject:   Statement boundaries of a lowered function body (image theorem, piece T1), the image side.
             `BodyFrame` fixes what `lowEnd_ok` keeps for a whole body (layout, frame, code addresses, handler,
             entry snapshot, pending releases); `BodyFrame.Ok` its standing premises. `restAt` is the decoder from
             an instruction offset inside the code of an end block to the end block that remains there, by the
             same recursion as `lowEnd` (`.cons s rest`: the code of `s`, then the code of `rest`).
             `BodyFrame.RandIR eb pc m σ ρ` says that the image stands at the start of the code of the remaining
             end block `eb` with exactly the premises `lowEnd_ok` asks of such a start. `randIR_schritt`: from a
             boundary in front of a statement that ends normally, the image reaches the boundary behind it, by the
             statement's own simulation (`lowS_ok`) and the re-established premises (as in `endCons_case`).
             `randIR_bind`: the same across a `let` binding of the end block (as in `endBind_case`); the boundary
             behind it has one more variable in its context.
-/
module
public import Stage0.Senke.Anweisung.Satz.Teil5
public import Stage0.Senke.Anweisung.Faelle.Ende
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## The decoder -/

section Dekoder

variable {V : Vertrag D}

/-- **The decoder**: the end block that remains `n` instructions into the code of `eb` (lowered by `lowEnd` with the
    given parameters), if `n` is a statement boundary of the leading `.cons` chain of `eb`. Offset `0` is `eb`
    itself; inside `.cons s rest` an offset at or behind the end of the code of `s` continues in `rest`. -/
def restAt (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout) (ens : List II × Nat)
    (pr : List Nat) (ex : Int × Int) (reserved : Nat) (sc : List D.Lock) {l : Bool} :
    {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → Nat →
      Option (Σ Λ' : List (Res D), Endblock D V l Γ Λ')
  | _, Λ, eb, 0 => some ⟨Λ, eb⟩
  | _, _, .cons s rest, n + 1 =>
    match lowEnd (reserved := reserved) (sc := sc) passes A L layout ens pr ex rest with
    | none => none
    | some cr =>
      match lowS (reserved := reserved) (sc := sc) passes A L layout ens pr (exPlus ex cr.1.length) s with
      | none => none
      | some cs =>
        if cs.1.length ≤ n + 1 then restAt passes A L layout ens pr ex reserved sc rest (n + 1 - cs.1.length)
        else none
  | _, _, _, _ + 1 => none

theorem restAt_null (passes : Nat) (A : D.Fn → Nat) (L : Lay D) (layout : FrameLayout) (ens : List II × Nat)
    (pr : List Nat) (ex : Int × Int) (reserved : Nat) (sc : List D.Lock) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (eb : Endblock D V l Γ Λ) :
    restAt passes A L layout ens pr ex reserved sc eb 0 = some ⟨Λ, eb⟩ := by
  simp only [restAt]

/-- **The decoder follows the lowering**: behind the (nonempty) code of `s` the decoder of `.cons s rest` is the
    decoder of `rest`. -/
theorem restAt_cons {passes : Nat} {A : D.Fn → Nat} {L : Lay D} {layout : FrameLayout} {ens : List II × Nat}
    {pr : List Nat} {ex : Int × Int} {reserved : Nat} {sc : List D.Lock} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} {rest : Endblock D V l Γ Λ'} {cr cs : List II} {tr ts : Nat}
    (hr : lowEnd (reserved := reserved) (sc := sc) passes A L layout ens pr ex rest = some (cr, tr))
    (hs : lowS (reserved := reserved) (sc := sc) passes A L layout ens pr (exPlus ex cr.length) s = some (cs, ts))
    (hpos : 0 < cs.length) (n : Nat) :
    restAt passes A L layout ens pr ex reserved sc (.cons s rest) (cs.length + n) =
      restAt passes A L layout ens pr ex reserved sc rest n := by
  obtain ⟨j, hj⟩ : ∃ j, cs.length + n = j + 1 := ⟨cs.length + n - 1, by omega⟩
  have hle : cs.length ≤ j + 1 := by omega
  rw [hj]
  simp only [restAt, hr, hs, hle, ↓reduceIte]
  rw [show j + 1 - cs.length = n by omega]

end Dekoder

/-! ## The frame of one lowered body -/

/-- **The fixed data of one lowered function body**: what `lowEnd_ok` keeps from the first statement of the body of
    `f` to its last — the world layout `L`, the oracle and pass budget, the call handler `R` of the function
    simulations, the code addresses `A` and codes `C`, the frame at `fp` with `K` slots (`Ks` its own), the
    return target, the entry world and environment, the ensures code, the protected slots, the loop targets, the
    held locks `H` and the pending releases `sc`. -/
structure BodyFrame (D : Deklaration) where
  L : Lay D
  O : Orakel D
  passes : Nat
  R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g
  A : D.Fn → Nat
  C : D.Fn → List II
  dv : Runner.W
  cap : Nat
  P : Programm D
  f : D.Fn
  fp : Runner.W
  K : Nat
  Ks : Nat
  lo : Nat
  rp : Runner.W
  cfp : Runner.W
  σ0 : World D
  ρ0 : Env D (D.params f)
  cens : List II
  tens : Nat
  pr : List Nat
  ex : Int × Int
  H : List D.Lock
  sc : List D.Lock
  reserved : Nat

variable [Kern]

/-- The standing premises of `lowEnd_ok` for the frame: every function keeps its call protocol (`FunSpec`), the code
    addresses and the frame fit, the ensures code is the one of `f`, the pending releases are held. -/
structure BodyFrame.Ok (B : BodyFrame D) : Prop where
  spec : FunSpec B.L B.A B.C B.R B.dv B.cap
  addr : ∀ g, B.A g < 2 ^ 31
  lo0 : B.lo = (functionFrame B.P B.f).internalResult
  ens : lowPost B.L (functionFrame B.P B.f) B.P B.f (B.lo + returnWords (D.erg B.f) (D.gruende B.f)) =
    some (B.cens, B.tens)
  scH : ∀ M ∈ B.sc, M ∈ B.H
  win : WIn B.L B.fp B.Ks B.K

/-- **The image at a statement boundary** of the body: the remaining end block `eb` is lowered (`lowEnd`) to the code
    `c` at `pc`, and every premise `lowEnd_ok` asks of a start of `eb` holds in the memory `m`, with the environment
    `ρ` in the frame and the world `σ` in memory. -/
def BodyFrame.RandIR (B : BodyFrame D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (eb : Endblock D (vertragVon D B.f) l Γ Λ) (pc : Runner.W) (m : Runner.Mem) (σ : World D) (ρ : Env D Γ) :
    Prop :=
  ∃ (c : List II) (top : Nat),
    lowEnd (reserved := B.reserved) (sc := B.sc) B.passes B.A B.L (functionFrame B.P B.f) (B.cens, B.tens) B.pr
      B.ex eb = some (c, top) ∧
    top + B.cap ≤ B.Ks ∧ 16 * c.length < 2 ^ 31 ∧
    PreS B.L m pc B.fp B.K (frei Γ B.reserved) c ρ B.reserved ∧ B.lo ≤ frei Γ B.reserved ∧
    Umf B.L B.A B.C B.dv m B.fp B.Ks B.K B.H ∧ Kopf B.L B.f m B.fp B.K B.rp B.cfp B.ρ0 B.P B.σ0 ∧
    WeltAt m B.L σ ∧ (∀ j ∈ B.pr, j < frei Γ B.reserved) ∧ HeldIn B.H Λ (vertragVon D B.f).boden

/-- **One statement, the image side**: from the boundary in front of `s` in `.cons s rest`, when `s` ends normally in
    machine G's sequential semantics (`execStmt … = .ok σ1 ρ1`), the image runs the code of `s` (its lowering
    `cs`, decoded by `restAt_cons`) to the boundary behind it, changing only the frame from `lo` on, the world and
    the lock words (`AgreeW`), and there the premises of `rest` hold with the new world and environment. -/
theorem BodyFrame.randIR_schritt {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D (vertragVon D B.f) l Γ Λ Λ'}
    {rest : Endblock D (vertragVon D B.f) l Γ Λ'} {pc : Runner.W} {m : Runner.Mem} {σ σ1 : World D}
    {ρ ρ1 : Env D Γ} (h : B.RandIR (.cons s rest) pc m σ ρ)
    (hex : execStmt B.O B.passes B.R s σ ρ = .ok σ1 ρ1) :
    ∃ (cr cs : List II) (tr ts : Nat) (m1 : Runner.Mem),
      lowEnd (reserved := B.reserved) (sc := B.sc) B.passes B.A B.L (functionFrame B.P B.f) (B.cens, B.tens)
        B.pr B.ex rest = some (cr, tr) ∧
      lowS (reserved := B.reserved) (sc := B.sc) B.passes B.A B.L (functionFrame B.P B.f) (B.cens, B.tens)
        B.pr (exPlus B.ex cr.length) s = some (cs, ts) ∧
      Star ⟨pc, B.fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * cs.length), B.fp⟩ m1 ∧
      AgreeW B.L B.fp B.lo B.K m m1 ∧
      B.RandIR rest (pc + BitVec.ofNat 64 (16 * cs.length)) m1 σ1 ρ1 := by
  obtain ⟨c, top, hl, hK, hs, hp, hlo, hu, hk, hWa, hpr, hH⟩ := h
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs1, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  have hFB3 : FB = 4 := rfl
  have hFramePrefix := functionFrame_prefix B.P B.f
  have hlo0 := hB.lo0
  have ih := lowS_ok (O := B.O) (passes := B.passes) (R := B.R) (rp := B.rp) (cfp := B.cfp)
    (σ0 := B.σ0) (ρ0 := B.ρ0) (ex := exPlus B.ex cr.length) hB.spec hB.addr hB.lo0 hB.ens hB.scH s hH cs ts hs1
    (by omega) (by omega) hB.win m pc σ ρ hp.left (by omega) hlo hu hk hWa hpr
  rw [hex] at ih
  obtain ⟨m1, s1, a1, e1, hw1, _⟩ := ih
  have hf := codeFar_right (n := cs.length) (k := cr.length) (by simpa using hp.far)
  have hp1 : PreS B.L m1 (pc + BitVec.ofNat 64 (16 * cs.length)) B.fp B.K (frei Γ B.reserved) cr ρ1 B.reserved :=
    ⟨hp.ctx, hp.small, frameOK_agreeW hp.frame a1, codeAt_agreeWIn hB.win a1 (codeAt_right hp.code) hf, hf, e1,
      trivial, wstab_true _ _⟩
  exact ⟨cr, cs, tr, ts, m1, hr, hs1, s1, a1, cr, tr, hr, by omega, by omega, hp1, hlo,
    hu.agreeW hB.win a1 (by omega), hk.agreeW hB.win a1 (by omega), hw1, hpr, HeldIn.stmt s hH⟩


/-- **One binding, the image side**: from the boundary in front of `let x = e; rest`, the image runs the code of `e`
    (its lowering `ce`, which leaves the value in the next free slot of the frame) and stands at the boundary of
    `rest`, with the environment extended by the value of `e` and the world after the reads of `e`, as machine G's
    `endeBind` and `execEnd` take them. The steps are those of `endBind_case` up to its call of the rest. -/
theorem BodyFrame.randIR_bind {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Endblock D (vertragVon D B.f) l (τ :: Γ) Λ} {pc : Runner.W} {m : Runner.Mem} {σ : World D}
    {ρ : Env D Γ} (h : B.RandIR (.bind e rest) pc m σ ρ) :
    ∃ (ce : List II) (m1 : Runner.Mem),
      Star ⟨pc, B.fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * ce.length), B.fp⟩ m1 ∧
      AgreeW B.L B.fp B.lo B.K m m1 ∧
      B.RandIR rest (pc + BitVec.ofNat 64 (16 * ce.length)) m1 (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by
  obtain ⟨c, top, hl, hK, hs, hp, hlo, hu, hk, hWa, hpr, hH⟩ := h
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  have hFB3 : FB = 4 := rfl
  have hFramePrefix := functionFrame_prefix B.P B.f
  have hlo0 := hB.lo0
  have hW := hB.win
  have htop := lowE_top e _ _ _ he
  have hks := hW.ks
  have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, value⟩ :=
    lowE_ok (same := by intro _; rfl) (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) hW.lay e _ ce te he
      (by omega) m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hWa1 : WeltAt m1 B.L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have hf := codeFar_right (n := ce.length) (k := cr.length) (by simpa using hp.far)
  have hp1 : PreS B.L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) B.fp B.K (frei (τ :: Γ) B.reserved) cr
      (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) B.reserved :=
    ⟨by simp only [frei, contextWords_cons]; omega, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf,
      hf, envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) value, trivial, wstab_true _ _⟩
  have hlo1 : B.lo ≤ frei (τ :: Γ) B.reserved := by
    simp only [frei, contextWords_cons] at hlo ⊢; omega
  have hpr1 : ∀ j ∈ B.pr, j < frei (τ :: Γ) B.reserved := fun j hj => by
    have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega
  exact ⟨ce, m1, s1, agreeW_of (a1.mono hlo), cr, tr, hr, by omega, by omega, hp1, hlo1,
    hu.agree a1 hp.frame (by omega), hk.agree a1 hp.frame (by omega), hWa1, hpr1, hH⟩

end Gabbro.Stage0.Senke.BildLauf
