/-
  File:      Grammatik/CFormNested.lean
  Subject:   T4: correspondence of emitted reads of `[[T; n]; m]`.

  The emitter lowers `static mut M : [[u32; 4]; 3]` to `uint32_t M[3][4]`
  and `M[i][j]` to `M[i][j]` (lane 170). The model reads the same element
  as the flat slot `i * n + j` of a table with `count m * n`
  (`Verschachtelt.lean`: `nestIdx`, `eval_nestIdx`). This file states the
  C half with pinned numbers: the nested address is the flat address
  (`ev_idx_nested`), lifted through the load, so the emitted read denotes
  the model slot read at `flachIndex`.
-/
import Grammatik.Verschachtelt

namespace Gabbro.Grammatik

/-- The emitted read of `A[i][j]` on `T A[M][N]` with `es`-byte elements:
    `ld (idx (idx p ci M (N*es)) cj N es)`. -/
def nestedRead (p ci cj : CX) (M N es : Nat) (τ : CTy) : CX :=
  .ld (.idx (.idx p ci M (N * es)) cj N es) τ

/-- The flat read it denotes: element `ck = i * N + j` of `M * N`. -/
def flatRead (p ck : CX) (M N es : Nat) (τ : CTy) : CX :=
  .ld (.idx p ck (M * N) es) τ

/-- **C read correspondence for nested arrays `[[T; n]; m]`**: the emitted
    read `A[i][j]` (row `i` of `M`, `N * es` bytes a row, then element `j`)
    denotes the flat slot read at `i * N + j` of `M * N` elements -- the
    model's cell of `M[i][j]` (`eval_nestIdx`). Index bounds, layout
    offsets (`N * es`, `M * N`, `es`) and the element type `τ` are pinned
    as numbers in the two read shapes. -/
theorem cform_nested_read (L : CLayout) (orc : DevOrc) (fr : Nat)
    {p ci cj ck : CX} {st : CSt} {ρ : CLok} {q : CPtr} {i j : Int} (τ : CTy)
    (M N es : Nat) (hq : 0 ≤ q.off)
    (hp : ev L orc fr p st ρ = some (.ptr q, st))
    (hi : ev L orc fr ci st ρ = some (.int i, st))
    (hj : ev L orc fr cj st ρ = some (.int j, st))
    (hk : ev L orc fr ck st ρ = some (.int (flachIndex (N : Int) i j), st))
    (hi0 : 0 ≤ i) (hiM : i < (M : Int)) (hj0 : 0 ≤ j) (hjN : j < (N : Int)) :
    ev L orc fr (nestedRead p ci cj M N es τ) st ρ =
      ev L orc fr (flatRead p ck M N es τ) st ρ := by
  unfold nestedRead flatRead
  have haddr := ev_idx_nested L orc fr M N es hq hp hi hj hk hi0 hiM hj0 hjN
  show (match ev L orc fr (.idx (.idx p ci M (N * es)) cj N es) st ρ with
    | some (.ptr q', st1) => match bLoad L st1 q' τ with
      | some v => some (v, st1)
      | none => none
    | _ => none)
    = (match ev L orc fr (.idx p ck (M * N) es) st ρ with
    | some (.ptr q', st1) => match bLoad L st1 q' τ with
      | some v => some (v, st1)
      | none => none
    | _ => none)
  rw [haddr]

/-- Concrete layout, state, locals and oracle for the witness: global
    block 7 is a live `uint32_t M[3][4]` (`natLay 12 [uint32_t]`: twelve
    4-byte cells, 48 bytes), and every cell holds its own byte offset, so a
    loaded value names the address it was read from.
    (Review 2026-09-21, G01: the earlier witness used a layout with NO
    block, so both sides of its equation were `none`; fix lane F8 replaced
    it with this one, where the read succeeds.) -/
def nzL : CLayout := fun b =>
  match b with
  | .glob 7 => some { lay := natLay 12 [.int false .w32], kind := .plain, base := 0 }
  | _ => none
def nzSt : CSt := ⟨fun _ o => .int (o : Int), fun _ => true, []⟩
def nzRho : CLok := fun _ => .int 0
def nzOrc : DevOrc := fun _ _ _ => 0

/-- **Witness**: all premises of `cform_nested_read` hold jointly at
    `M = 3, N = 4, es = 4` (`uint32_t M[3][4]`, `M[1][2]`), and the read
    SUCCEEDS on both sides: the emitted nested read and the flat read of
    element `flachIndex 4 1 2 = 6` both load the cell at byte offset
    `1 * 16 + 2 * 4 = 24` (whose content is `24`, its own offset). The
    third conjunct is the defect probe: the transposed element `M[2][1]`
    loads offset 36, so the value really depends on the row stride. -/
theorem cform_nested_read_zeuge :
    ev nzL nzOrc 0 (nestedRead (.addr (.glob 7)) (.lit 1) (.lit 2) 3 4 4
        (.int false .w32)) nzSt nzRho
      = ev nzL nzOrc 0 (flatRead (.addr (.glob 7)) (.lit 6) 3 4 4
        (.int false .w32)) nzSt nzRho
    ∧ ev nzL nzOrc 0 (flatRead (.addr (.glob 7)) (.lit 6) 3 4 4
        (.int false .w32)) nzSt nzRho = some (.int 24, nzSt)
    ∧ ev nzL nzOrc 0 (nestedRead (.addr (.glob 7)) (.lit 2) (.lit 1) 3 4 4
        (.int false .w32)) nzSt nzRho = some (.int 36, nzSt)
    ∧ flachIndex (4 : Int) 1 2 = 6 := by
  refine ⟨?_, rfl, rfl, by decide⟩
  exact cform_nested_read nzL nzOrc 0 (p := .addr (.glob 7)) (ci := .lit 1)
    (cj := .lit 2) (ck := .lit 6) (st := nzSt) (ρ := nzRho) (q := ⟨.glob 7, 0⟩)
    (i := 1) (j := 2) (.int false .w32) 3 4 4
    (by decide) rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)

#print axioms cform_nested_read
#print axioms cform_nested_read_zeuge

end Gabbro.Grammatik

/- CUTS: what is not proved here.
   - The MODEL side of the read (`M[i][j]` as `Expr.slot` over `nestIdx`,
     `eval_nestIdx`) and the memory relation of a static C array (`corrW`
     for a `T a[M][N]` object) are not stated: this file proves the C
     ADDRESS equality through the load (`ev_idx_nested` lifted through
     `ld`). A flat-array read lemma for mutable statics does not exist
     yet (only `constTab_read` for `static const`), so the nested read
     inherits the pre-existing uncovered `expr:array-read` for its memory
     content -- the row stays uncovered until the flat static-array read
     has its lemma.
   - Deeper nesting `[[[T; K]; N]; M]` is the same flattening twice; not
     stated separately.
- NESTED-DEFECT: swapping the dimensions (`M * es` row stride instead of
   `N * es`) makes `cform_nested_read` unprovable: `ev_idx_nested` no
   longer applies and the `show`+`rw` step leaves the two different
   `ptrAdd` offsets on each side (measured by breaking the statement
   once; see MUSE-REPORT-205.md).
-/
