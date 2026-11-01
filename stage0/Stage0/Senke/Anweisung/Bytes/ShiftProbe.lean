/- A large one-word destination transition runs on real code, frame and table memory. -/
import Stage0.Senke.Anweisung.Bytes.Shift
import Grammatik.Parser.Elab.UebersetzeAllg
import Stage0.Senke.BildLese

namespace Gabbro.Stage0.Senke.ShiftProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def old : Int := 2 ^ 32 + 41
def target : Int := 2 ^ 32 + 42

def unit : UProg := {
  tabs := [{ name := "Cells", count := 2, cols := [("state", (0, target))] }]
  locks := []
  fns := [{ name := "main", params := [], kinds := [], res := none, held := [], puts := ["Cells"], gives := [], body := [], ret := .empty }]
}

/-- The generic model allows a declared transition between arbitrary integer states.
    Textual state declarations separately assign dense ordinals to their stage names. -/
def D : Deklaration := { declOf unit with
  erlaubt := fun _ _ a b => decide (a = old ∧ b = target) }
abbrev tab : D.Tab := ⟨0, by decide⟩
abbrev field : D.Feld tab := ⟨0, by decide⟩
abbrev entry : D.Fn := ⟨0, by decide⟩

instance : Subsingleton D.Tab := by change Subsingleton (Fin 1); infer_instance
instance (t : D.Tab) : Subsingleton (D.Feld t) := by
  have ht : t = tab := Subsingleton.elim _ _
  subst t
  change Subsingleton (Fin 1)
  infer_instance

def layout : Lay D where
  col _ _ := 8192
  ga g := Fin.elim0 g
  lo := 8192
  hi := 8208
  tor a := Fin.elim0 a
  byte _ := none

def world : World D where
  slots t k f := by
    have ht : t = tab := Subsingleton.elim _ _
    subst t
    have hf : f = field := Subsingleton.elim _ _
    subst f
    exact if k = 1 then ⟨old, by decide, by decide⟩ else ⟨0, by decide, by decide⟩
  globs g := Fin.elim0 g
  spur := []

def index : Expr D [] [] (.index 2) :=
  .widen (by decide) (by decide) (.lit 1)

def statement : Stmt D (vertragVon D entry) false [] [] [] :=
  .shift tab field rfl index old target (by decide) (by decide) (by decide)
    (by intro w hw; change w ∈ [] at hw; cases hw)

def program : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact .cons statement (.ret .empty (.refl []))

def lowered := lowS 1 (fun _ => 0) layout (⟨[], none, 0, 0, 0⟩ : FrameLayout) ([], 0) [3] (0, 0) statement
def code : List II := (lowered.getD ([], 0)).1
def top : Nat := (lowered.getD ([], 0)).2

def memory : Runner.Mem where
  b a := if a.toNat = 4120 then 77
    else if 8200 ≤ a.toNat ∧ a.toNat < 8208 then
      BitVec.ofNat 8 ((BitVec.ofInt 64 old).toNat / 256 ^ (a.toNat - 8200))
    else ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem cell_width : valueWords (D.typ tab field) = 1 := by decide +kernel

theorem layout_in : LayIn layout := by
  refine ⟨fun t f k hk => ?_, (fun g => Fin.elim0 g), by decide⟩
  have ht : t = tab := Subsingleton.elim _ _
  subst t
  have hf : f = field := Subsingleton.elim _ _
  subst f
  change (k : Int) < 2 at hk
  simp only [Lay.elem, layout, cell_width]
  omega

theorem layout_dis : LayDis layout := by
  have one : ∀ (t : D.Tab) (f : D.Feld t), valueWords (D.typ t f) = 1 := by
    intro t f
    have ht : t = tab := Subsingleton.elim _ _
    subst t
    have hf : f = field := Subsingleton.elim _ _
    subst f
    exact cell_width
  refine ⟨?_, ?_, ?_⟩
  · intro c c' hc hc' hne
    cases c with
    | glob g => exact Fin.elim0 g
    | elem t f k =>
      cases c' with
      | glob g => exact Fin.elim0 g
      | elem t' f' k' =>
        have ht : t = t' := Subsingleton.elim _ _
        subst t'
        have hf : f = f' := Subsingleton.elim _ _
        subst f'
        have hk : k ≠ k' := fun h => hne (by subst h; rfl)
        simp only [Zelle.adr, Zelle.bytes, Lay.elem, layout, one]
        omega
  · intro c c' hc hc' he
    cases c with
    | glob g => exact Fin.elim0 g
    | elem t f k =>
      cases c' with
      | glob g => exact Fin.elim0 g
      | elem t' f' k' =>
        have ht : t = t' := Subsingleton.elim _ _
        subst t'
        have hf : f = f' := Subsingleton.elim _ _
        subst f'
        simp only [Zelle.adr, Lay.elem, layout, one] at he
        have hk : k = k' := by omega
        subst k'
        rfl
  · intro c hc
    cases c with
    | glob g => exact Fin.elim0 g
    | elem t f k =>
      simp only [Zelle.adr, Lay.elem, layout, one]
      omega

theorem pre [Kern] : PreS layout memory 0 4096 64 4 code (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    ?_, ?_, ?_, trivial, wstab_true _ _⟩
  · apply codeAt_bytes code 0 (by decide +kernel)
    intro i hi
    have hs : (code.flatMap encII).length < 4120 := by decide +kernel
    refine ⟨rfl, rfl, ?_⟩
    simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      ite_eq_right (show i ≠ 4120 by omega),
      ite_eq_right (show ¬(8200 ≤ i ∧ i < 8208) by omega),
      List.getElem?_eq_getElem hi, Option.getD_some]
  · unfold CodeFar; decide +kernel
  · intro _ x; nomatch x

theorem world_at [Kern] : WeltAt memory layout world := by
  refine ⟨fun t f k hk => ?_, (fun g => Fin.elim0 g), fun _ _ _ => rfl⟩
  have ht : t = tab := Subsingleton.elim _ _
  subst t
  have hf : f = field := Subsingleton.elim _ _
  subst f
  change (k : Int) < 2 at hk
  have hcases : k = 0 ∨ k = 1 := by omega
  rcases hcases with rfl | rfl
  · exact ValueAt.ofCellWord (w := 0) cell_width (by decide +kernel) rfl
  · exact ValueAt.ofCellWord (w := BitVec.ofInt 64 old) cell_width (by decide +kernel) rfl

/-- All shift premises hold jointly. The old state is checked, a large target is
    stored in cell one, and both cell zero and the live frame sentinel survive. -/
theorem simulation_zeuge [Kern] (O : Orakel D)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    lit32 old = false ∧ lit32 target = false ∧ lowered = some (code, top) ∧ top ≤ 64 ∧
    PreS layout memory 0 4096 64 4 code (Env.nil : Env D []) ∧
    ∃ m', Star ⟨0, 4096⟩ memory ⟨0 + BitVec.ofNat 64 (16 * code.length), 4096⟩ m' ∧
      m'.rd64 8200 = some (BitVec.ofInt 64 target) ∧
      m'.rd64 8192 = some 0 ∧ m'.rd64 (slot 4096 3) = some 77 := by
  have emitted : lowered = some (code, top) := by decide +kernel
  have inside : WIn layout 4096 64 64 :=
    ⟨layout_in, layout_dis, by decide, by decide, by decide⟩
  have run := shift_ok (lo := 4) (P := program) (O := O) (R := R) (σ0 := world) (ρ0 := .nil)
    (rp := 0) (cfp := 0) (f := entry) (t := tab) (field := field)
    rfl index old target (by decide) (by decide) (by decide)
    (by intro w hw; change w ∈ [] at hw; cases hw)
    emitted (by decide +kernel) inside pre (by decide) world_at
    (by intro j hj
        have he : j = 3 := by simpa using hj
        subst j
        decide)
  change Reach layout 4096 4 64 [3] ⟨0, 4096⟩ memory
    (0 + BitVec.ofNat 64 (16 * code.length))
    ((world.lese [] [.inl tab]).schreibSlot tab [] 1 field
      (⟨target, by decide, by decide⟩ : Zahl 0 target)) .nil at run
  obtain ⟨m', steps, _, _, represented, kept⟩ := run
  obtain ⟨w1, read1, enc1⟩ := ValueAt.word (D.typ tab field) _ (wordCompatB_sound _ (by decide +kernel))
    (represented.1 tab field 1 (by decide))
  obtain ⟨w0, read0, enc0⟩ := ValueAt.word (D.typ tab field) _ (wordCompatB_sound _ (by decide +kernel))
    (represented.1 tab field 0 (by decide))
  rw [slot_zero] at read1 read0
  have value1 : w1 = BitVec.ofInt 64 target := by
    change w1 = BitVec.ofInt 64 target at enc1
    exact enc1
  have value0 : w0 = 0 := by
    change w0 = 0 at enc0
    exact enc0
  refine ⟨by decide, by decide, emitted, by decide +kernel, pre, m', steps, ?_, ?_, ?_⟩
  · simpa [value1, layout, Lay.elem, cell_width] using read1
  · simpa [value0, layout, Lay.elem, cell_width] using read0
  · exact (kept 3 (by simp)).trans (by decide +kernel)

end Gabbro.Stage0.Senke.ShiftProbe
