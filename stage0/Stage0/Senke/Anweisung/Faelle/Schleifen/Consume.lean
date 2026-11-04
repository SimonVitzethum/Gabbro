/- Current consuming semantics and its statement admission boundary. The old
   fixed-sweep equality is false after the C11 model change and is removed. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Traversal
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Lower
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Execution
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Selection
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Decrease
public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Consuming

variable {D : Deklaration} {V : Vertrag D}

/-- The canonical entry point, including read bookkeeping and the exact fuel.
    Selection is reevaluated after every completed body pass. The selected
    candidate is the second binder of the edge expression. -/
theorem consumeTraverse_exec (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int) (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R
      (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ Λ) σ ρ =
      verbrauchLauf t (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (verbrauchSel t member edge)
        (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n))
        bound ((D.count t).toNat + bound.toNat + 1) σ ρ := rfl

/-- The source entry always has fuel for its initial invariant/selection
    round, even for an empty index domain and a zero measure bound. Fuel
    exhaustion can occur only on a subsequent continuing round. -/
theorem consumeTraverse_initial_fuel (t : D.Tab) (bound : Int) :
    0 < (D.count t).toNat + bound.toNat + 1 := by
  omega

variable [Kern] {L : Lay D}

/-- The actual lowS image implements current-state consuming traversal. The
    canonical fuel induction composes both scans and every body outcome. -/
theorem consumeTraverse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f
      (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab}
    {member : Expr D (.index (D.count t) :: Γ) Λ .bool}
    {edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool}
    {inv : Expr D Γ Λ .bool} {bound : Int} {mass : Expr D Γ Λ (.int 0 bound)}
    {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0
      cens tens pr ex body reserved) →
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex
      (show Stmt D (vertragVon D f) l Γ Λ Λ from
        .consumeTraverse t member edge inv bound mass body) reserved := by
  intro ihBody c top emitted hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowS] at emitted
  obtain ⟨pairLow, pairRoom, counterFree, savedFree,
    ci, cm, ce, cw, hci, hcm, hce, hcw, hemit⟩ := Consuming.lower_actual emitted
  obtain ⟨cb, exits, hcb, hexits, assembled, hiTop, hmTop, heTop, hwTop,
    hbTop, counterTop, savedTop, scratchTop⟩ := Consuming.emit_actual hemit
  have gates := Consuming.emit_bounds hemit
  have indexWidth : valueWords (.index (D.count t)) = 1 :=
    integerWords_word (by omega) (by
      have countGate := gates.2.2.1
      simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at countGate
      omega)
  let x : Consuming.Image L P f reserved := {
    A := A, C := C, dv := dv, fp := fp, pc := pc, rp := rp, cfp := cfp,
    K := K, Ks := Ks, lo := lo, s := frei Γ reserved,
    counter := (counterPair reserved (counterDepthB body)).1,
    saved := (counterPair reserved (counterDepthB body)).2,
    fuel := (D.count t).toNat + bound.toNat + 1, table := t, bound := bound,
    invariant := ci.1, member := cm.1, edge := ce.1, measure := cw.1,
    body := cb.1, code := c, σ0 := σ0, ρ0 := ρ0, pr := pr,
    layout := hW, small := hp.small, abi := hlo0, low := hlo,
    controls := ⟨by simpa only [hlo0] using pairLow,
      by simp only [counterPair]; omega, pairRoom⟩,
    scratch := ⟨by simp only [frei]; omega, by omega⟩,
    kept := by
      intro j hj
      exact ⟨hpr j hj, fun eq => counterFree (eq ▸ hj), fun eq => savedFree (eq ▸ hj)⟩,
    bounds := gates, assembled := assembled, far := hp.far }
  let loop : Consuming.Loop x Γ Λ := {
    selector := {
      member := member, edge := edge, mt := cm.2, et := ce.2,
      memberCode := hcm, edgeCode := hce, memberTop := by omega, edgeTop := by omega,
      origin := rfl, indexWidth := indexWidth },
    inv := inv, mass := mass, it := ci.2, mt := cw.2,
    invCode := hci, massCode := hcw, invTop := by omega, massTop := by omega }
  have bodyCorrect : ∀ mem world env,
      x.Ready mem world env →
      Sim L P f σ0 ρ0 rp cfp fp lo K (x.s :: x.counter :: x.saved :: pr)
        ⟨x.addr 39, fp⟩ mem (x.addr 41) (x.addr 44) (x.addr 41)
        (execBlock O passes R body world env) reserved := by
    intro mem world env ready
    have pre := ready.pre 39 (frei (.index (D.count t) :: Γ) reserved) cb.1 (Nat.le_refl _) rfl
    have smallBody : 16 * cb.1.length < 2 ^ 31 := by consume_arith x
    have bodySim := ihBody (pr := x.s :: x.counter :: x.saved :: pr) (ex := exits)
      cb.1 cb.2 hcb (by omega) smallBody hW mem (x.addr 39) world env pre hlo
      (by simp only [frei, contextWords_cons, indexWidth]; have := hlo2; unfold frei at this; omega)
      ready.surround ready.head ready.world (by
        intro j hj
        simp only [List.mem_cons] at hj
        rcases hj with rfl | rfl | rfl | hj
        · simp only [frei, contextWords_cons, indexWidth]; change x.s < x.s + 1; omega
        · have := x.controls; have := x.scratch
          simp only [frei, contextWords_cons, indexWidth]; change x.counter < x.s + 1; omega
        · have := x.controls; have := x.scratch
          simp only [frei, contextWords_cons, indexWidth]; change x.saved < x.s + 1; omega
        · have := hpr j hj; simp only [frei, contextWords_cons, indexWidth] at *; omega)
    have exitsEq : exits = (16 * ((x.offset 44 : Int) - x.offset 41), 0) := by
      have eq := hexits
      change Consuming.targets x.fragment = some exits at eq
      simp [Consuming.targets, Consuming.Image.fragment, Consuming.pieces,
        Consuming.position, Consuming.Piece.width, Consuming.Image.offset, Consuming.width] at eq ⊢
      exact eq.symm
    exact bodySim.cast rfl (by consume_arith x)
      (by rw [exitsEq]; consume_arith x) (by rw [exitsEq]; consume_arith x)
  obtain ⟨m1, initialRun, initialFrame, initialPre, initialUmf, initialHead,
    initialWorld, initialKept, initialRead⟩ := Consuming.initialize assembled hW hp hu hk hWa
      (by rw [hlo0]) (by rw [hlo0]; exact pairLow)
      (by have := pairRoom; simp only [counterPair] at *; omega)
      (by have := hW.ks; omega) gates.1 (by
        intro j hj
        exact ⟨by have := hpr j hj; have := scratchTop; have := hW.ks; omega,
          fun eq => counterFree (eq ▸ hj)⟩)
  have entry : loop.Entry x.fuel m1 σ ρ :=
    ⟨⟨initialPre.frame, initialPre.code, initialPre.env, initialWorld, initialUmf, initialHead⟩,
      initialRead, Nat.le_refl _⟩
  have loopRun := loop.correct (l := l) (outerLeave := pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
    (outerNext := pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2)
    bodyCorrect x.fuel m1 σ ρ entry
  have headerAddress : pc + 16 = x.addr 2 := by consume_arith x
  rw [headerAddress] at initialRun
  have combined := Sim.prefix hlo initialRun initialFrame initialKept loopRun
  have exitAddress : x.addr 50 = pc + BitVec.ofNat 64 (16 * c.length) := by consume_arith x
  rw [exitAddress] at combined
  simpa only [consumeTraverse_exec, Consuming.Loop.invW, Consuming.Loop.sel,
    Consuming.Loop.massW, loop, x] using combined


end Gabbro.Stage0.Senke
