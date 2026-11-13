/-
  File:      stage0/Stage0/Senke/Sperre/Paar.lean
  Subject:   Where the parts of the lock code lie and what a jump between them does: a piece of code inside a larger
             one (`At.mid`, `At.of_eq`, `At.one`), its code and its distance from the frame (`At.codeAt`,
             `At.codeFar`), a `jmp` (`code_jmp`, `tgt_nat`), and the start state of the lock code (`ls_init`).
-/
module
public import Stage0.Senke.Sperre.Lauf
public import Stage0.Senke.Anweisung.Simulation
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem At.mid (xs ys zs : List II) : At (xs ++ ys ++ zs) xs.length ys := fun j hj => by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

theorem At.one {code : List II} {p : Nat} {x : II} (h : At code p [x]) : code[p]? = some x := by
  simpa using h.get (j := 0) rfl

theorem At.of_eq {code xs ys zs : List II} {p : Nat} (h : code = xs ++ ys ++ zs) (hp : p = xs.length) :
    At code p ys := by subst h hp; exact At.mid xs ys zs

theorem At.codeAt {m : Mem} {pc : W} {code xs : List II} {p : Nat} (hc : CodeAt m pc code) (h : At code p xs) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * p)) xs := fun k hk => by
  have e := h k hk
  rw [List.getElem?_eq_getElem hk] at e
  obtain ⟨hl, hx⟩ := List.getElem?_eq_some_iff.mp e
  have := hc (p + k) hl
  rw [hx, show pc + BitVec.ofNat 64 (16 * (p + k)) = pc + BitVec.ofNat 64 (16 * p) + BitVec.ofNat 64 (16 * k) by
    rw [pc_jump]] at this
  exact this

theorem At.codeFar {pc fp : W} {code xs : List II} {p K : Nat} (hf : CodeFar pc code.length fp K)
    (hl : p + xs.length ≤ code.length) : CodeFar (pc + BitVec.ofNat 64 (16 * p)) xs.length fp K := by
  obtain ⟨h1, h2, h3⟩ := hf
  have := pc.isLt
  have hx : (pc + BitVec.ofNat 64 (16 * p)).toNat = pc.toNat + 16 * p := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨by rw [hx]; omega, h2, by rw [hx]; omega⟩

theorem code_jmp {m : Mem} {pc fp : W} {code : List II} {i : Nat} {X : Int} (hc : CodeAt m pc code)
    (hi : code[i]? = some (ci 18 X 0 0)) (hX : lit32 X = true) :
    Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 X, fp⟩ m := by
  obtain ⟨hl, hx⟩ := List.getElem?_eq_some_iff.mp hi
  have hI := hc i hl
  rw [hx] at hI
  simp only [ci] at hI
  refine Star.one (run_step (t := ⟨_, fp⟩) hI (by decide) ?_)
  simp only [op]
  refine f1_run hI ?_
  rw [sx_lit hX]
  exact .next

theorem tgt_nat {p : W} {a b n : Nat} (h : a + 16 * n = b) :
    p + BitVec.ofNat 64 a + BitVec.ofInt 64 (16 * (n : Int)) = p + BitVec.ofNat 64 b := by
  have := tgt_eq (p := p) (x := 0) h
  simpa using this

section
variable {m0 : Mem} {pc fp : W} {s a : Nat} {code : List II} {o c w : W}

/-- The start state of the lock code: the scratch slots hold what they hold. -/
theorem ls_init (E : LE m0 pc fp s a code) (ho : m0.rd64 (BitVec.ofNat 64 a) = some o)
    (hc : m0.rd64 (BitVec.ofNat 64 (a + 8)) = some c) (hw : m0.rd64 (BitVec.ofNat 64 (a + 16)) = some w) :
    ∃ f, LS m0 m0 fp s a f o c w :=
  ⟨fun j => (m0.rd64 (slot fp (BitVec.ofNat 64 (s + j)))).getD 0, fun j hj => by
    simp only [Mem.rd64, E.frame.rd (s + j) (by omega), ite_true, Option.getD_some], ho, hc, hw,
    AgreeK.refl _ _ _ _⟩

end

end Gabbro.Stage0.Senke
