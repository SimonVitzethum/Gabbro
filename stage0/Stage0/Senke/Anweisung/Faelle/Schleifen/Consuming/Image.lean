/- Proof context for composing slices of one actual consuming image. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Selection
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Decrease
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}

/-- Only proof data: all instruction addresses refer to the assembled fragment. -/
structure Image (L : Lay D) (P : Programm D) (f : D.Fn) (reserved : Nat) where
  A : D.Fn → Nat
  C : D.Fn → List II
  dv : W
  fp : W
  pc : W
  rp : W
  cfp : W
  K : Nat
  Ks : Nat
  lo : Nat
  s : Nat
  counter : Nat
  saved : Nat
  fuel : Nat
  table : D.Tab
  bound : Int
  invariant : List II
  member : List II
  edge : List II
  measure : List II
  body : List II
  code : List II
  σ0 : World D
  ρ0 : Env D (D.params f)
  pr : List Nat
  layout : WIn L fp Ks K
  small : K < 2 ^ 31
  abi : lo = (functionFrame P f).internalResult
  low : FB ≤ lo
  controls : lo ≤ counter ∧ counter < saved ∧ saved < FB + reserved
  scratch : FB + reserved ≤ s ∧ s + 12 ≤ Ks
  kept : ∀ j ∈ pr, j < s ∧ j ≠ counter ∧ j ≠ saved
  bounds : fuel < 2 ^ 31 ∧ logikCode (D := D) .schleife < 2 ^ 31 ∧
    inW (D.count table) (D.count table) = true ∧ inW 0 bound = true
  assembled : assemble (pieces s counter saved fuel (logikCode (D := D) .schleife)
    (D.count table) bound invariant member edge measure body) = some code
  far : CodeFar pc code.length fp K

namespace Image
variable {reserved : Nat} (x : Image L P f reserved)

def fragment : List Piece := pieces x.s x.counter x.saved x.fuel
  (logikCode (D := D) .schleife) (D.count x.table) x.bound
  x.invariant x.member x.edge x.measure x.body

def offset (i : Nat) : Nat := width (x.fragment.take i)
def addr (i : Nat) : W := x.pc + BitVec.ofNat 64 (16 * x.offset i)
def read (m : Mem) (j : Nat) (v : W) : Prop :=
  m.rd64 (slot x.fp (BitVec.ofNat 64 j)) = some v

/-- A body may change the world and lexical variables; the surrounding ABI
    and the complete original code image remain available at every boundary. -/
structure Ready {Γ : Ctx} (m : Mem) (σ : World D) (ρ : Env D Γ) : Prop where
  frame : FrameOK m x.fp x.K
  code : CodeAt m x.pc x.code
  env : EnvAt L m x.fp ρ reserved
  world : WeltAt m L σ
  surround : Umf L x.A x.C x.dv m x.fp x.Ks x.K
  head : Kopf L f m x.fp x.K x.rp x.cfp x.ρ0 P x.σ0

variable {x} {Γ : Ctx} {m m' : Mem} {σ : World D} {ρ : Env D Γ}

theorem Ready.agree (h : x.Ready m σ ρ) {d : Nat}
    (a : Agree x.fp d x.K m m') (ctx : frei Γ reserved ≤ d)
    (abi : (functionFrame P f).internalResult ≤ d) (room : d ≤ x.K) :
    x.Ready m' σ ρ :=
  ⟨h.frame.agree a, h.code.agree a x.far, envAt_agree h.env a h.frame ctx room,
    weltAt_stab x.layout.lay x.layout.top m m' h.world (a.mono (Nat.zero_le _)),
    h.surround.agree a h.frame (by have := functionFrame_prefix P f; omega),
    h.head.agree a h.frame abi⟩

theorem Ready.body {Δ : Ctx} {τ : World D} {η : Env D Δ}
    (h : x.Ready m σ ρ) (a : AgreeW L x.fp x.lo x.K m m')
    (env : EnvAt L m' x.fp η reserved) (world : WeltAt m' L τ) :
    x.Ready m' τ η :=
  ⟨frameOK_agreeW h.frame a, codeAt_agreeWIn x.layout a h.code x.far,
    env, world, h.surround.agreeW x.layout a x.low,
    h.head.agreeW x.layout a (by rw [x.abi])⟩

theorem Ready.lese {Λ : List (Res D)} {sites : List (D.Tab ⊕ D.Glob)}
    (h : x.Ready m σ ρ) : x.Ready m (σ.lese Λ sites) ρ :=
  { h with world := h.world }

/-- Extract a resolved piece, together with its disjointness from the frame. -/
theorem Ready.slice (h : x.Ready m σ ρ) (i : Nat) (piece : Piece) (block : List II)
    (found : x.fragment[i]? = some piece)
    (resolved : resolve x.fragment (x.offset i) piece = some block) :
    CodeAt m (x.addr i) block ∧ CodeFar (x.addr i) block.length x.fp x.K := by
  have inside : i < x.fragment.length := by
    by_cases hi : i < x.fragment.length
    · exact hi
    · have missing := List.getElem?_eq_none (l := x.fragment) (i := i) (by omega)
      cases (missing.symm.trans found)
  have splitImage : x.fragment = x.fragment.take i ++ piece :: x.fragment.drop (i + 1) := by
    have eq := List.take_append_drop i x.fragment
    rw [List.drop_eq_getElem_cons inside] at eq
    have element : x.fragment[i] = piece := by simpa only [List.getElem?_eq_getElem inside,
      Option.some.injEq] using found
    simpa only [element] using eq.symm
  obtain ⟨leading, suffix, eq, len⟩ := assemble_piece (x.fragment.take i) piece
    (x.fragment.drop (i + 1)) (by rw [← splitImage]; exact x.assembled)
    (by rw [← splitImage]; exact resolved)
  constructor
  · apply codeAt_at (xs := leading) (zs := suffix)
    · simpa only [eq, List.append_assoc] using h.code
    · simp only [addr, offset, len]
  · have bound : leading.length + block.length ≤ x.code.length := by
      rw [eq]; simp only [List.length_append]; omega
    simpa only [addr, offset, len] using codeFar_at x.far bound

theorem Ready.pre (h : x.Ready m σ ρ) (i d : Nat) (block : List II)
    (ctx : frei Γ reserved ≤ d) (found : x.fragment[i]? = some (.code block)) :
    PreS L m (x.addr i) x.fp x.K d block ρ reserved := by
  have slice := h.slice i (.code block) block found rfl
  exact mkPreS ctx x.small h.frame slice.1 slice.2 h.env

/-- Repackage an ordinary expression/instruction simulation as a scan path. -/
theorem Ready.ok (h : x.Ready m σ ρ) {i j d : Nat} {block : List II} {Q : W → Prop}
    (run : Ok m (x.addr i) x.fp x.K d block Q)
    (endAt : x.addr i + BitVec.ofNat 64 (16 * block.length) = x.addr j)
    (ctx : frei Γ reserved ≤ d) (scratch : x.s ≤ d) (room : d ≤ x.K) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr i) (x.addr j) m
      (fun m' => x.Ready m' σ ρ ∧ Agree x.fp d x.K m m' ∧ ∃ v, x.read m' d v ∧ Q v) := by
  obtain ⟨m', run, a, v, read, value⟩ := run
  rw [endAt] at run
  have low : x.lo ≤ d := by have := x.controls; have := x.scratch; omega
  exact ⟨m', run, agreeW_of (a.mono low),
    keeps_of_agree a h.frame.room (by
      intro j hj
      have := x.controls; have := x.scratch
      simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj
      · omega
      · omega
      · have := x.kept j hj; omega) room,
    h.agree a ctx (by rw [← x.abi]; omega) room, a, v, read, value⟩

/-- A local jump resolves against the same image and preserves all memory. -/
theorem Ready.jump (h : x.Ready m σ ρ) (i j : Nat) (target : Label)
    (found : x.fragment[i]? = some (.jump target))
    (destination : position target x.fragment 0 = some (x.offset j))
    (originBound : x.offset i ≤ x.code.length) (targetBound : x.offset j ≤ x.code.length) :
    Star ⟨x.addr i, x.fp⟩ m ⟨x.addr j, x.fp⟩ m := by
  have code := (h.slice i (.jump target)
    [ci 18 (16 * ((x.offset j : Int) - x.offset i)) 0 0] found
    (by simp only [resolve, destination, bind, Option.bind_some, pure])).1
  have size := assemble_size x.assembled
  have run := jmp_go (fp := x.fp) code (lit_ok (by omega) (by omega))
  have address := adr_eq x.pc (x := x.offset i) (y := x.offset j)
    (J := 16 * ((x.offset j : Int) - x.offset i)) (by omega)
  simpa only [addr, address] using run

/-- Both outcomes of a resolved conditional branch. -/
theorem Ready.branch (h : x.Ready m σ ρ) (i j cell : Nat) (target : Label) (v : W)
    (found : x.fragment[i]? = some (.zero cell target))
    (destination : position target x.fragment 0 = some (x.offset j))
    (originBound : x.offset i ≤ x.code.length) (targetBound : x.offset j ≤ x.code.length)
    (cellBound : cell < x.K) (read : x.read m cell v)
    (next : x.addr i + 16 = x.addr (i + 1)) :
    Star ⟨x.addr i, x.fp⟩ m ⟨(if v = 0 then x.addr j else x.addr (i + 1)), x.fp⟩ m := by
  have code := (h.slice i (.zero cell target)
    [ci 19 cell (16 * ((x.offset j : Int) - x.offset i)) 0] found
    (by simp only [resolve, destination, bind, Option.bind_some, pure])).1
  change m.rd64 (slot x.fp (BitVec.ofNat 64 cell)) = some v at read
  by_cases zero : v = 0
  · simp only [zero, ↓reduceIte]
    have size := assemble_size x.assembled
    have run := brz_go code cellBound x.small (lit_ok (by omega) (by omega))
      (by simpa only [zero] using read)
    have address := adr_eq x.pc (x := x.offset i) (y := x.offset j)
      (J := 16 * ((x.offset j : Int) - x.offset i)) (by omega)
    simpa only [addr, address] using run
  · simp only [zero, ↓reduceIte]
    have run := brz_stay code cellBound x.small read zero
    change Star ⟨x.addr i, x.fp⟩ m ⟨x.addr i + 16, x.fp⟩ m at run
    rw [next] at run
    exact run

/-- An invariant or operand is evaluated in the specified read world. -/
theorem Ready.eval {Λ : List (Res D)} {τ : Ty} (h : x.Ready m σ ρ)
    {e : Expr D Γ Λ τ} {block : List II} {top : Nat} (i : Nat)
    (ctx : frei Γ reserved ≤ x.s + 4)
    (lowered : lowE (reserved := reserved) L e (x.s + 4) = some (block, top))
    (topBound : top ≤ x.Ks) (found : x.fragment[i]? = some (.code block))
    (compatible : WordCompatible τ) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr i) (x.addr (i + 1)) m
      (fun m' => x.Ready m' σ ρ ∧ Agree x.fp (x.s + 4) x.K m m' ∧ ∃ v, x.read m' (x.s + 4) v ∧ Enc L τ (eval σ e σ ρ) v) := by
  have pre := h.pre i (x.s + 4) block ctx found
  have preWorld := PreS.welt pre x.layout.ks h.world x.layout.lay x.layout.lo
  obtain ⟨mem, path, frame, value, read, encoded⟩ :=
    lowE_ok (same := by intro _; rfl) σ σ (fun _ h => h) x.layout.lay
    e (x.s + 4) block top lowered topBound m (x.addr i) ρ preWorld |>.word compatible
  have ok : Ok m (x.addr i) x.fp x.K (x.s + 4) block
      (Enc L τ (Gabbro.Grammatik.eval σ e σ ρ)) :=
    ⟨mem, path, Agree.widen frame x.layout.ks, value, read, encoded⟩
  apply h.ok ok
  · have inside : i < x.fragment.length := by
      apply Classical.byContradiction
      intro hn
      have missing := List.getElem?_eq_none (l := x.fragment) (i := i) (by omega)
      cases (missing.symm.trans found)
    have element : x.fragment[i] = .code block := by
      simpa only [List.getElem?_eq_getElem inside, Option.some.injEq] using found
    simp only [addr, offset, List.take_succ_eq_append_getElem inside, element]
    have widths : ∀ a b : List Piece, width (a ++ b) = width a + width b := by
      intro a b; induction a with
      | nil => simp only [List.nil_append, width, Nat.zero_add]
      | cons a as ih => simp only [List.cons_append, width, ih, Nat.add_assoc]
    rw [widths]
    simp only [width, Piece.width, Nat.add_zero, pc_add]
  · exact ctx
  · omega
  · have := x.scratch; have := x.layout.ks; omega

end Image
end Gabbro.Stage0.Senke.Consuming
