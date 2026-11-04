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

private theorem consume_position_label (target : Label) (before after : List Piece) (pc : Nat) :
    before.all (fun piece => match piece with
      | .label name => decide (name ≠ target)
      | _ => true) = true →
    position target (before ++ .label target :: after) pc = some (pc + width before) := by
  induction before generalizing pc with
  | nil => intro _; simp only [List.nil_append, position, ↓reduceIte, width, Nat.add_zero]
  | cons piece rest ih =>
    intro absent
    simp only [List.all_cons, Bool.and_eq_true] at absent
    cases piece with
    | code instructions =>
      simpa only [List.cons_append, position, width, Piece.width, Nat.add_assoc] using
        ih (pc + instructions.length) absent.2
    | label name =>
      have different : name ≠ target := of_decide_eq_true absent.1
      simpa only [List.cons_append, position, different, ↓reduceIte, width,
        Piece.width, Nat.add_zero, Nat.zero_add] using ih pc absent.2
    | jump destination =>
      simpa only [List.cons_append, position, width, Piece.width, Nat.add_assoc] using
        ih (pc + 1) absent.2
    | zero cell destination =>
      simpa only [List.cons_append, position, width, Piece.width, Nat.add_assoc] using
        ih (pc + 1) absent.2

private theorem consume_width_append (a b : List Piece) : width (a ++ b) = width a + width b := by
  induction a with
  | nil => simp only [List.nil_append, width, Nat.zero_add]
  | cons piece rest ih => simp only [List.cons_append, width, ih, Nat.add_assoc]

/-- Keep the initializer abstract while identifying the two-piece header prefix. -/
private theorem consume_header_width (fragment : List Piece) (first : List II)
    (rest : List Piece) (shape : fragment = .code first :: .label .header :: rest) :
    width (fragment.take 2) = first.length := by
  subst fragment
  simp only [List.take_succ_cons, List.take_zero, width, Piece.width, Nat.add_zero,
    Nat.zero_add]

variable [Kern] {L : Lay D}

section
variable {P : Programm D} {f : D.Fn} {reserved : Nat} (x : Consuming.Image L P f reserved)

private theorem consume_offset_step {i : Nat} {piece : Piece}
    (found : x.fragment[i]? = some piece) : x.offset (i + 1) = x.offset i + piece.width := by
  have inside : i < x.fragment.length := by
    by_cases hi : i < x.fragment.length
    · exact hi
    · have missing := List.getElem?_eq_none (l := x.fragment) (i := i) (by omega)
      cases (missing.symm.trans found)
  have element : x.fragment[i] = piece := by
    simpa only [List.getElem?_eq_getElem inside, Option.some.injEq] using found
  simp only [Consuming.Image.offset, List.take_succ_eq_append_getElem inside, element,
    consume_width_append, width, Nat.add_zero]

/-- The body is an actual slice of the accepted image, so it inherits its size gate. -/
private theorem consume_body_small : 16 * x.body.length < 2 ^ 31 := by
  have splitImage : x.fragment =
      x.fragment.take 39 ++ .code x.body :: x.fragment.drop 40 := rfl
  obtain ⟨leading, suffix, codeEq, _⟩ := assemble_block (x.fragment.take 39) x.body
    (x.fragment.drop 40) (code := x.code) (by rw [← splitImage]; exact x.assembled)
  have included : x.body.length ≤ x.code.length := by
    rw [codeEq]
    simp only [List.length_append]
    omega
  have small := assemble_size x.assembled
  omega

/-- Labels have zero width: body fallthrough is the actual after-body target. -/
private theorem consume_body_end :
    x.addr 39 + BitVec.ofNat 64 (16 * x.body.length) = x.addr 41 := by
  have bodyEnd := x.addr_next_code (i := 39) (block := x.body) rfl
  have afterLabel : x.addr 40 = x.addr 41 := rfl
  exact bodyEnd.trans afterLabel

private theorem consume_targets : targets x.fragment =
    some (16 * ((x.offset 44 : Int) - x.offset 41), 0) := by
  have afterSplit : x.fragment =
      x.fragment.take 40 ++ .label .afterBody :: x.fragment.drop 41 := rfl
  have afterPosition := consume_position_label .afterBody (x.fragment.take 40)
    (x.fragment.drop 41) 0 (by rfl)
  rw [← afterSplit] at afterPosition
  have afterLocated : position .afterBody x.fragment 0 = some (x.offset 41) := by
    have atLabel : position .afterBody x.fragment 0 = some (x.offset 40) := by
      simpa only [Nat.zero_add] using afterPosition
    have step := consume_offset_step x (i := 40) (piece := .label .afterBody) rfl
    simp only [Piece.width, Nat.add_zero] at step
    exact atLabel.trans (congrArg some step.symm)
  have leaveSplit : x.fragment =
      x.fragment.take 43 ++ .label .leaveBody :: x.fragment.drop 44 := rfl
  have leavePosition := consume_position_label .leaveBody (x.fragment.take 43)
    (x.fragment.drop 44) 0 (by rfl)
  rw [← leaveSplit] at leavePosition
  have leaveLocated : position .leaveBody x.fragment 0 = some (x.offset 44) := by
    have atLabel : position .leaveBody x.fragment 0 = some (x.offset 43) := by
      simpa only [Nat.zero_add] using leavePosition
    have step := consume_offset_step x (i := 43) (piece := .label .leaveBody) rfl
    simp only [Piece.width, Nat.add_zero] at step
    exact atLabel.trans (congrArg some step.symm)
  simp only [targets, afterLocated, leaveLocated, bind, Option.bind_some, pure]

private theorem consume_header_address : x.pc + 16 = x.addr 2 := by
  have initialWidth : x.offset 2 = (travCountC x.counter (x.fuel : Int)).length :=
    consume_header_width x.fragment (travCountC x.counter (x.fuel : Int))
      (x.fragment.drop 2) rfl
  have literal : lit32 (x.fuel : Int) = true := lit32_nat x.bounds.1
  have initial : (travCountC x.counter (x.fuel : Int)).length = 1 := by
    rw [travCountC_length]
    simp only [travCountSize, literal, ↓reduceIte]
  change x.pc + 16 = x.pc + BitVec.ofNat 64 (16 * x.offset 2)
  rw [initialWidth, initial]
  rfl

private theorem consume_exit_address :
    x.addr 50 = x.pc + BitVec.ofNat 64 (16 * x.code.length) := by
  have endWidth : x.offset 50 = width x.fragment := rfl
  have codeWidth : x.code.length = width x.fragment := assemble_length x.assembled
  change x.pc + BitVec.ofNat 64 (16 * x.offset 50) = _
  rw [endWidth, ← codeWidth]

end

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
    A := A
    C := C
    dv := dv
    fp := fp
    pc := pc
    rp := rp
    cfp := cfp
    K := K
    Ks := Ks
    lo := lo
    s := frei Γ reserved
    counter := (counterPair reserved (counterDepthB body)).1
    saved := (counterPair reserved (counterDepthB body)).2
    fuel := (D.count t).toNat + bound.toNat + 1
    table := t
    bound := bound
    invariant := ci.1
    member := cm.1
    edge := ce.1
    measure := cw.1
    body := cb.1
    code := c
    σ0 := σ0
    ρ0 := ρ0
    pr := pr
    layout := hW
    small := hp.small
    abi := hlo0
    low := hlo
    controls := ⟨by simpa only [hlo0] using pairLow,
      by simp only [counterPair]; omega, pairRoom⟩
    scratch := ⟨by simp only [frei]; omega, by omega⟩
    kept := by
      intro j hj
      exact ⟨hpr j hj, fun eq => counterFree (eq ▸ hj), fun eq => savedFree (eq ▸ hj)⟩
    bounds := gates
    assembled := assembled
    far := hp.far }
  let loop : Consuming.Loop x Γ Λ := {
    selector := {
      member := member
      edge := edge
      mt := cm.2
      et := ce.2
      memberCode := hcm
      edgeCode := hce
      memberTop := by change cm.2 ≤ Ks; omega
      edgeTop := by change ce.2 ≤ Ks; omega
      origin := rfl
      indexWidth := indexWidth }
    inv := inv
    mass := mass
    it := ci.2
    mt := cw.2
    invCode := hci
    massCode := hcw
    invTop := by change ci.2 ≤ Ks; omega
    massTop := by change cw.2 ≤ Ks; omega }
  have bodyCorrect : ∀ (mem : Runner.Mem) (world : World D)
      (env : Env D (.index (D.count t) :: Γ)),
      x.Ready mem world env →
      Sim L P f σ0 ρ0 rp cfp fp lo K (x.s :: x.counter :: x.saved :: pr)
        ⟨x.addr 39, fp⟩ mem (x.addr 41) (x.addr 44) (x.addr 41)
        (execBlock O passes R body world env) reserved := by
    intro mem world env ready
    have pre := ready.pre 39 (frei (.index (D.count t) :: Γ) reserved) cb.1 (Nat.le_refl _) rfl
    have smallBody : 16 * cb.1.length < 2 ^ 31 := consume_body_small x
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
      rw [consume_targets x] at eq
      exact (Option.some.inj eq).symm
    have bodyEnd : x.addr 39 + BitVec.ofNat 64 (16 * cb.1.length) = x.addr 41 :=
      consume_body_end x
    have leaveEnd : x.addr 39 + BitVec.ofNat 64 (16 * cb.1.length) +
        BitVec.ofInt 64 exits.1 = x.addr 44 := by
      rw [bodyEnd, exitsEq]
      change x.pc + BitVec.ofNat 64 (16 * x.offset 41) +
        BitVec.ofInt 64 (16 * ((x.offset 44 : Int) - x.offset 41)) =
        x.pc + BitVec.ofNat 64 (16 * x.offset 44)
      exact adr_eq x.pc (by omega)
    have nextEnd : x.addr 39 + BitVec.ofNat 64 (16 * cb.1.length) +
        BitVec.ofInt 64 exits.2 = x.addr 41 := by
      rw [bodyEnd, exitsEq]
      exact BitVec.add_zero _
    exact bodySim.cast rfl bodyEnd leaveEnd nextEnd
  obtain ⟨m1, initialRun, initialFrame, initialPre, initialUmf, initialHead,
    initialWorld, initialKept, initialRead⟩ := Consuming.«initialize» (lo := lo) (pr := pr)
      assembled hW hp hu hk hWa
      (by rw [hlo0]) (by rw [hlo0]; exact pairLow)
      (by have := pairRoom; simp only [counterPair] at *; omega)
      (by have := hW.ks; omega) gates.1 (by
        intro j hj
        exact ⟨by have := hpr j hj; have := scratchTop; have := hW.ks; omega,
          fun eq => counterFree (eq ▸ hj)⟩)
  have entry : loop.Entry x.fuel m1 σ ρ :=
    ⟨⟨initialPre.frame, initialPre.code, initialPre.env, initialWorld, initialUmf, initialHead⟩,
      initialRead, Nat.le_refl _⟩
  have loopRun := loop.correct (O := O) (passes := passes) (R := R) (body := body)
    (l := l) (outerLeave := pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
    (outerNext := pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2)
    bodyCorrect x.fuel m1 σ ρ entry
  have headerAddress : pc + 16 = x.addr 2 := consume_header_address x
  rw [headerAddress] at initialRun
  have combined := Sim.prefix hlo initialRun initialFrame initialKept loopRun
  have exitAddress : x.addr 50 = pc + BitVec.ofNat 64 (16 * c.length) := consume_exit_address x
  rw [exitAddress] at combined
  rw [consumeTraverse_exec]
  change Sim L P f x.σ0 x.ρ0 x.rp x.cfp fp lo K pr ⟨pc, fp⟩ m
    (pc + BitVec.ofNat 64 (16 * c.length))
    (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
    (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2)
    (verbrauchLauf (l := l) x.table (fun world env => execBlock O passes R body world env)
      loop.invW loop.sel loop.massW x.bound x.fuel σ ρ) reserved
  exact combined


end Gabbro.Stage0.Senke
