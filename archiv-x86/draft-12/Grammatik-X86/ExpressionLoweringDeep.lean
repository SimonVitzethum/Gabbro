/-
  File:      Grammatik/X86/ExpressionLoweringDeep.lean
  Subject:   Arbitrary-depth integer-expression-tree lowering to the pilot
             x86 machine, plus signed comparisons for branches.

  Generalises `Grammatik/X86/ExpressionLowering.lean` (`senkAtom`/`senkFrag`:
  atoms and one ADD/SUB level) to arbitrary-depth trees of `lit`/`var`/
  `weiter`/`add`/`sub`/`neg` over the 14 pilot `Befehl` forms
  (`Grammatik/X86/Typen.lean`), plus `lt`/`le`/`eq` comparisons lowered to
  `cmpReg64` with a `Bedingung` for `jumpIf32`. Reused, not refined or
  redefined: `Expr`/`eval` (`Grammatik.Syntax`/`Grammatik.Semantik`),
  `Codec.encode`, `Ausfuehrung.schritt`/`lauf`, `Wort.add64`/`sub64`/`xor64`/
  `bedingung`, `FlagBeweis.sint`/`sub64_sf_sint`/`sub64_of_iff`/
  `sub64_sint_eq_of_no_overflow`, and `ExpressionLowering`'s `EnvRepr`,
  `intWort_add`/`sub`/`sint`, `lauf_einzeln_gleich`/`lauf_anhang`,
  `laengeOk_encode`. No second IR, no new source interpreter.

  Register discipline: a single scratch STACK `frei` shared sequentially by
  sibling subtrees (the left subtree commits its final value to `dst` before
  the right subtree runs, so any register `frei` lent to the left subtree's
  own recursion is dead and safe for the right subtree to reuse). Each binary
  node peels exactly one register off the head of `frei` for the right
  operand and passes the tail to BOTH operands' recursion; an empty `frei` at
  a binary node refuses with `none` (no spilling -- an honest CUT, not a
  silent gap). `FrischListe` extends `Frisch` to a register list: no source
  variable lives in `dst` or anywhere in `frei`, `dst` is not itself in
  `frei`, and `frei` has no duplicate (so a nested peel can never collide
  with an outer one still live).
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.FlagBeweis
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ExpressionLowering

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-! ## 1. Register-list freshness. -/

/-- List register freshness: no source variable lives in `dst` or anywhere
    in `frei`; `dst` itself is not in `frei`; `frei` has no duplicate. The
    no-duplicate clause is what lets an outer peel (`tmp`) stay untouched by
    a nested peel out of the same tail `rest` on both sibling recursions. -/
def FrischListe {Γ : Ctx} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst : Register) (frei : List Register) : Prop :=
  (∀ (τ : Ty) (x : Var Γ τ), abb τ x ≠ dst ∧ abb τ x ∉ frei) ∧
  dst ∉ frei ∧ frei.Nodup

/-- The tail of a fresh list is fresh for the same `dst`. -/
theorem frischListe_tail {Γ : Ctx} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp : Register) (rest : List Register)
    (h : FrischListe abb dst (tmp :: rest)) : FrischListe abb dst rest := by
  obtain ⟨hvar, hdst, hnd⟩ := h
  refine ⟨fun τ x => ⟨(hvar τ x).1, ?_⟩, ?_, (List.nodup_cons.mp hnd).2⟩
  · intro hin
    exact (hvar τ x).2 (List.mem_cons_of_mem _ hin)
  · intro hin
    exact hdst (List.mem_cons_of_mem _ hin)

/-- The peeled head is fresh as a new destination, with the tail as its
    own scratch list: `tmp` plays the role of a new `dst`, `rest` of a new
    `frei`. -/
theorem frischListe_kopf {Γ : Ctx} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp : Register) (rest : List Register)
    (h : FrischListe abb dst (tmp :: rest)) : FrischListe abb tmp rest := by
  obtain ⟨hvar, _, hnd⟩ := h
  obtain ⟨htmp, hrest⟩ := List.nodup_cons.mp hnd
  refine ⟨?_, htmp, hrest⟩
  intro τ x
  have h2 := (hvar τ x).2
  rw [List.mem_cons, not_or] at h2
  exact h2

/-- `dst` and the peeled head differ (both read off one `FrischListe`). -/
theorem frischListe_dst_ne_tmp {Γ : Ctx} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp : Register) (rest : List Register)
    (h : FrischListe abb dst (tmp :: rest)) : dst ≠ tmp := by
  obtain ⟨_, hdst, _⟩ := h
  intro heq
  exact hdst (heq ▸ List.mem_cons_self)

/-! ## 2. Arbitrary-depth lowering.

    `lit`/`var` as in `senkAtom`; `weiter` is a pure re-reading of the same
    value (`Zahl.weiter` keeps `.n`, Semantik.lean `eval` equation `.weiter`)
    and costs no instruction; `add`/`sub` peel one scratch register for the
    right operand and recurse on BOTH operands into the tail (the register
    stack); `neg a` is lowered as `0 - a` (`xorReg64` zeroes a scratch
    register, `subReg64` subtracts the operand, the result is moved back
    into `dst`). Every other form, and an empty `frei` at a binary node,
    refuses with `none`. -/

/-- Arbitrary-depth integer-expression lowering over the shared scratch
    stack `frei`. Stated over a general `τ` (the established style: case
    analysis on the constructor substitutes the index, so no carrier
    projection ever gets stuck). -/
def senkTief {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst : Register) (frei : List Register) :
    Option (List Befehl) :=
  match e with
  | .lit n => some [.movImm64 dst (intWort n)]
  | .var x => some [.movReg64 dst (abb _ x)]
  | .weiter _ _ a => senkTief abb a dst frei
  | .add a b =>
    match frei with
    | [] => none
    | tmp :: rest =>
      match senkTief abb a dst rest, senkTief abb b tmp rest with
      | some pa, some pb => some (pa ++ pb ++ [Befehl.addReg64 dst tmp])
      | _, _ => none
  | .sub a b =>
    match frei with
    | [] => none
    | tmp :: rest =>
      match senkTief abb a dst rest, senkTief abb b tmp rest with
      | some pa, some pb => some (pa ++ pb ++ [Befehl.subReg64 dst tmp])
      | _, _ => none
  | .neg a =>
    match frei with
    | [] => none
    | tmp :: rest =>
      match senkTief abb a dst rest with
      | some pa => some (pa ++
          [Befehl.xorReg64 tmp tmp, Befehl.subReg64 tmp dst, Befehl.movReg64 dst tmp])
      | none => none
  | _ => none

/-- PLANTED REFUSAL: a three-deep nest lowers (register exhaustion is a
    SEPARATE poison probe below; this one shows depth itself is no longer a
    barrier). -/
theorem senkTief_tief_ok {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (dst r1 r2 r3 : Register) :
    senkTief abb
      (Expr.add (D := D) (Γ := Γ) (Λ := Λ)
        (Expr.add (Expr.lit 1) (Expr.lit 2)) (Expr.lit 3))
      dst [r1, r2, r3] =
      some [Befehl.movImm64 dst (intWort 1), Befehl.movImm64 r2 (intWort 2),
        Befehl.addReg64 dst r2, Befehl.movImm64 r1 (intWort 3),
        Befehl.addReg64 dst r1] := rfl

/-- PLANTED REFUSAL: multiplication is outside the lowered fragment at any
    depth. -/
theorem senkTief_verweigert_mul {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (dst : Register) (frei : List Register) :
    senkTief abb
      (Expr.mul (D := D) (Γ := Γ) (Λ := Λ) (Expr.lit 2) (Expr.lit 3))
      dst frei = none := by
  cases frei <;> rfl

/-- PLANTED REFUSAL: a register read via `slot` is outside the lowered
    fragment. -/
theorem senkTief_verweigert_slot {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ)
    (dst : Register) (frei : List Register) :
    senkTief abb (Expr.slot t f i hL) dst frei = none := by
  cases frei <;> rfl

/-- PLANTED REFUSAL: register exhaustion at a binary node with an empty
    scratch stack. -/
theorem senkTief_verweigert_erschoepft {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (dst : Register)
    (a b : Expr D Γ Λ (.int 0 0)) :
    senkTief abb (Expr.add a b) dst [] = none := rfl

/-! ## 3. Shape inversion: `IstTief`.

    `IstTief` mirrors `senkTief`'s six supported shapes, carrying the
    recursive sub-derivations on `add`/`sub`/`neg`'s operands as premises
    (not just a flat shape tag, as `IstFrag` is for the one-level fragment):
    inversion on a GENERAL `τ` never gets stuck (the file-wide pattern), and
    matching the resulting `IstTief` value afterwards is a clean, non-stuck
    structural induction with only six constructors -- no opaque carrier
    projection ever appears as an index. -/

inductive IstTief {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) :
    ∀ {τ : Ty}, Expr D Γ Λ τ → Register → List Register → List Befehl → Prop where
  | lit (n : Int) (dst : Register) (frei : List Register) :
      IstTief abb (Expr.lit n) dst frei [Befehl.movImm64 dst (intWort n)]
  | var {t : Ty} (x : Var Γ t) (dst : Register) (frei : List Register) :
      IstTief abb (Expr.var x) dst frei [Befehl.movReg64 dst (abb _ x)]
  | weiter {lo hi lo' hi' : Int} (h1 : lo' ≤ lo) (h2 : hi ≤ hi')
      (e : Expr D Γ Λ (.int lo hi)) (dst : Register) (frei : List Register) (p : List Befehl)
      (he : IstTief abb e dst frei p) :
      IstTief abb (Expr.weiter h1 h2 e) dst frei p
  | add {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
      (dst tmp : Register) (rest : List Register) (pa pb : List Befehl)
      (ha : IstTief abb a dst rest pa) (hb : IstTief abb b tmp rest pb) :
      IstTief abb (Expr.add a b) dst (tmp :: rest) (pa ++ pb ++ [Befehl.addReg64 dst tmp])
  | sub {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
      (dst tmp : Register) (rest : List Register) (pa pb : List Befehl)
      (ha : IstTief abb a dst rest pa) (hb : IstTief abb b tmp rest pb) :
      IstTief abb (Expr.sub a b) dst (tmp :: rest) (pa ++ pb ++ [Befehl.subReg64 dst tmp])
  | neg {lo hi : Int} (a : Expr D Γ Λ (.int lo hi))
      (dst tmp : Register) (rest : List Register) (pa : List Befehl)
      (ha : IstTief abb a dst rest pa) :
      IstTief abb (Expr.neg a) dst (tmp :: rest)
        (pa ++ [Befehl.xorReg64 tmp tmp, Befehl.subReg64 tmp dst, Befehl.movReg64 dst tmp])

/-- Every successful deep lowering is one of the six `IstTief` shapes, with
    the sub-derivations for `add`/`sub`/`neg` carried recursively. Proved
    over a GENERAL index (the established pattern: case analysis
    substitutes the constructor, so no opaque carrier projection ever gets
    stuck); the ~26 unsupported constructors close because `senkTief`
    reduces to `none` on them (`simp [senkTief]`). -/
theorem istTief_von_senkTief {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) :
    ∀ {τ : Ty} (e : Expr D Γ Λ τ) (dst : Register) (frei : List Register)
      (prog : List Befehl), senkTief abb e dst frei = some prog →
      IstTief abb e dst frei prog
  | _, .lit n, dst, frei, prog, h => by
      have hprog : prog = [Befehl.movImm64 dst (intWort n)] := Option.some_inj.mp h.symm
      subst hprog; exact .lit n dst frei
  | _, .var x, dst, frei, prog, h => by
      have hprog : prog = [Befehl.movReg64 dst (abb _ x)] := Option.some_inj.mp h.symm
      subst hprog; exact .var x dst frei
  | _, .weiter h1 h2 e, dst, frei, prog, h => by
      simp only [senkTief] at h
      exact .weiter h1 h2 e dst frei prog (istTief_von_senkTief abb e dst frei prog h)
  | _, .add a b, dst, frei, prog, h => by
      cases frei with
      | nil => simp [senkTief] at h
      | cons tmp rest =>
        cases h1 : senkTief abb a dst rest with
        | none => simp [senkTief, h1] at h
        | some pa =>
          cases h2 : senkTief abb b tmp rest with
          | none => simp [senkTief, h1, h2] at h
          | some pb =>
            simp only [senkTief, h1, h2] at h
            have hprog : prog = pa ++ pb ++ [Befehl.addReg64 dst tmp] :=
              Option.some_inj.mp h.symm
            subst hprog
            exact .add a b dst tmp rest pa pb (istTief_von_senkTief abb a dst rest pa h1)
              (istTief_von_senkTief abb b tmp rest pb h2)
  | _, .sub a b, dst, frei, prog, h => by
      cases frei with
      | nil => simp [senkTief] at h
      | cons tmp rest =>
        cases h1 : senkTief abb a dst rest with
        | none => simp [senkTief, h1] at h
        | some pa =>
          cases h2 : senkTief abb b tmp rest with
          | none => simp [senkTief, h1, h2] at h
          | some pb =>
            simp only [senkTief, h1, h2] at h
            have hprog : prog = pa ++ pb ++ [Befehl.subReg64 dst tmp] :=
              Option.some_inj.mp h.symm
            subst hprog
            exact .sub a b dst tmp rest pa pb (istTief_von_senkTief abb a dst rest pa h1)
              (istTief_von_senkTief abb b tmp rest pb h2)
  | _, .neg a, dst, frei, prog, h => by
      cases frei with
      | nil => simp [senkTief] at h
      | cons tmp rest =>
        cases h1 : senkTief abb a dst rest with
        | none => simp [senkTief, h1] at h
        | some pa =>
          simp only [senkTief, h1] at h
          have hprog : prog = pa ++
              [Befehl.xorReg64 tmp tmp, Befehl.subReg64 tmp dst, Befehl.movReg64 dst tmp] :=
            Option.some_inj.mp h.symm
          subst hprog
          exact .neg a dst tmp rest pa (istTief_von_senkTief abb a dst rest pa h1)
  | _, .wahr, _, _, _, h => by simp [senkTief] at h
  | _, .falsch, _, _, _, h => by simp [senkTief] at h
  | _, .glob _ _, _, _, _, h => by simp [senkTief] at h
  | _, .slot _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .durch _ _ _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .ptrOf _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .fnref _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .altGlob _ _, _, _, _, h => by simp [senkTief] at h
  | _, .altSlot _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .mul _ _, _, _, _, h => by simp [senkTief] at h
  | _, .div _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .rem _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .sdiv _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .srem _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .leseBytes _ _ _ _ _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .band _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .bor _ _ _ _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .bxor _ _ _ _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .shl _ _ _ _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .shr _ _ _ _ _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .lt _ _, _, _, _, h => by simp [senkTief] at h
  | _, .le _ _, _, _, _, h => by simp [senkTief] at h
  | _, .eq _ _, _, _, _, h => by simp [senkTief] at h
  | _, .fllt _ _, _, _, _, h => by simp [senkTief] at h
  | _, .flle _ _, _, _, _, h => by simp [senkTief] at h
  | _, .und _ _, _, _, _, h => by simp [senkTief] at h
  | _, .oder _ _, _, _, _, h => by simp [senkTief] at h
  | _, .nicht _, _, _, _, h => by simp [senkTief] at h
  | _, .none _, _, _, _, h => by simp [senkTief] at h
  | _, .some _, _, _, _, h => by simp [senkTief] at h
  | _, .istSome _, _, _, _, h => by simp [senkTief] at h
  | _, .fall _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .grund _ _, _, _, _, h => by simp [senkTief] at h
  | _, .forallSlots _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .existsSlots _ _ _, _, _, _, h => by simp [senkTief] at h
  | _, .reaches _ _ _ _ _ _, _, _, _, h => by simp [senkTief] at h


/-! ## 4. Small arithmetic facts the deep correctness proof needs. -/

/-- A self-xor word result is zero (the `neg` lowering's zeroing step). -/
theorem xor64_self_wert (x : Wort) : (xor64 x x).1 = 0 := by
  unfold xor64
  simp [BitVec.xor_self]

/-- `intWort` of the exact zero is the zero word. -/
theorem intWort_zero : intWort 0 = (0 : Wort) := by decide

/-! ## 5. Deep value correctness over `IstTief`.

    A clean structural induction over the six `IstTief` constructors (no
    opaque carrier index ever appears): the modular word of the exact
    source value lands in `dst`; memory is untouched; every register
    outside `dst :: frei` is kept; `rsp` is kept. The register-stack
    argument: the right operand's destination `tmp` and its own scratch
    `rest` are peeled from the head of `frei`, so both operand recursions
    share `rest` SEQUENTIALLY (the left operand fully commits to `dst`
    before the right operand starts, so anything the left operand's own
    recursion left behind in `rest` is dead weight the right operand is
    free to reuse) -- `FrischListe`'s `Nodup` clause is what keeps a nested
    peel from colliding with an outer one still alive. -/
theorem istTief_korrekt {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) :
    ∀ {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (dst : Register) (frei : List Register)
      (prog : List Befehl), IstTief abb e dst frei prog →
      ∀ (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand),
        FrischListe abb dst frei →
        (dst ≠ Register.rsp ∧ Register.rsp ∉ frei) →
        EnvRepr ρ s.register abb →
        ∃ s', lauf (prog.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) s = some s' ∧
          s'.register dst = intWort (eval σ₀ e σ ρ).n ∧
          s'.speicher = s.speicher ∧
          (∀ q, q ≠ dst → q ∉ frei → s'.register q = s.register q) ∧
          s'.register Register.rsp = s.register Register.rsp
  | _, _, _, _, _, _, @IstTief.lit _ _ _ abb n dst frei => fun ρ σ₀ σ s _ hrsp _ => by
      refine ⟨schrittRegister s (ripNach s.rip (encode (.movImm64 dst (intWort n))).length)
        s.flags dst (intWort n), ?_, ?_, rfl, ?_, ?_⟩
      · simp only [List.map_cons, List.map_nil, lauf_einzeln_gleich]
        exact schritt_movImm64 _ _ _ _ (laengeOk_encode _) rfl
      · exact regSet_gleich _ _ _
      · intro q hq _
        exact regSet_fremd s.register dst q (intWort n) hq
      · exact regSet_fremd s.register dst Register.rsp (intWort n) (Ne.symm hrsp.1)
  | _, _, _, _, _, _, @IstTief.var _ _ _ abb _ x dst frei => fun ρ σ₀ σ s _ hrsp hrenv => by
      have hx := hrenv _ _ x
      refine ⟨schrittRegister s
        (ripNach s.rip (encode (.movReg64 dst (abb _ x))).length)
        s.flags dst (s.register (abb _ x)), ?_, ?_, rfl, ?_, ?_⟩
      · simp only [List.map_cons, List.map_nil, lauf_einzeln_gleich]
        exact schritt_movReg64 _ _ _ _ (laengeOk_encode _) rfl
      · show regSet s.register dst (s.register (abb _ x)) dst =
          intWort (eval σ₀ (Expr.var x) σ ρ).n
        rw [regSet_gleich]; exact hx
      · intro q hq _
        exact regSet_fremd s.register dst q (s.register (abb _ x)) hq
      · exact regSet_fremd s.register dst Register.rsp (s.register (abb _ x)) (Ne.symm hrsp.1)
  | _, _, _, _, _, _, @IstTief.weiter _ _ _ abb _ _ _ _ h1 h2 e dst frei p he => fun ρ σ₀ σ s hfr hrsp hrenv => by
      obtain ⟨s', hrun, hval, hmem, hreg, hflrsp⟩ :=
        istTief_korrekt abb e dst frei p he ρ σ₀ σ s hfr hrsp hrenv
      exact ⟨s', hrun, hval, hmem, hreg, hflrsp⟩
  | _, _, _, _, _, _, @IstTief.add _ _ _ abb _ _ _ _ a b dst tmp rest pa pb ha hb => fun ρ σ₀ σ s hfr hrsp hrenv => by
      have hfrA := frischListe_tail abb dst tmp rest hfr
      have hfrB := frischListe_kopf abb dst tmp rest hfr
      have hdstTmp := frischListe_dst_ne_tmp abb dst tmp rest hfr
      have hrspRest : Register.rsp ∉ rest := fun hin => hrsp.2 (List.mem_cons_of_mem _ hin)
      have hrspTmp : tmp ≠ Register.rsp := by
        intro heq; exact hrsp.2 (heq ▸ List.mem_cons_self)
      obtain ⟨s1, hrun1, hval1, hmem1, hreg1, hrsp1⟩ :=
        istTief_korrekt abb a dst rest pa ha ρ σ₀ σ s hfrA ⟨hrsp.1, hrspRest⟩ hrenv
      have hrenv1 : EnvRepr ρ s1.register abb := by
        intro lo' hi' x
        have hx := hfr.1 _ x
        rw [hreg1 _ hx.1 (fun hin => hx.2 (List.mem_cons_of_mem _ hin))]
        exact hrenv lo' hi' x
      obtain ⟨s2, hrun2, hval2, hmem2, hreg2, hrsp2⟩ :=
        istTief_korrekt abb b tmp rest pb hb ρ σ₀ σ s1 hfrB ⟨hrspTmp, hrspRest⟩ hrenv1
      have hdst2 : s2.register dst = intWort (eval σ₀ a σ ρ).n := by
        rw [hreg2 dst (hdstTmp) (fun hin => hfr.2.1 (by
          rw [List.mem_cons]; exact Or.inr hin))]
        exact hval1
      have hlen : laengeOk (encode (Befehl.addReg64 dst tmp)).length = true := laengeOk_encode _
      have hadd := schritt_addReg64 ⟨Befehl.addReg64 dst tmp, (encode (Befehl.addReg64 dst tmp)).length⟩
        s2 dst tmp hlen rfl
      have hmap : ((pa ++ pb ++ [Befehl.addReg64 dst tmp]).map
          fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
          (pa.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          (pb.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          [⟨Befehl.addReg64 dst tmp, (encode (Befehl.addReg64 dst tmp)).length⟩] := by
        simp [List.map_append]
      refine ⟨schrittRegister s2 (ripNach s2.rip (encode (Befehl.addReg64 dst tmp)).length)
        (add64 (s2.register dst) (s2.register tmp)).2 dst
        (add64 (s2.register dst) (s2.register tmp)).1, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hmap]
        have h12 : lauf ((pa.map fun b => ⟨b, (encode b).length⟩) ++
            (pb.map fun b => ⟨b, (encode b).length⟩)) s = some s2 := by
          rw [lauf_anhang _ _ _ _ hrun1]; exact hrun2
        rw [lauf_anhang _ _ _ _ h12, lauf_einzeln_gleich]
        exact hadd
      · show regSet s2.register dst (add64 (s2.register dst) (s2.register tmp)).1 dst =
            intWort (eval σ₀ (Expr.add a b) σ ρ).n
        rw [regSet_gleich, hdst2, hval2]
        show intWort (eval σ₀ a σ ρ).n + intWort (eval σ₀ b σ ρ).n =
          intWort (eval σ₀ (Expr.add a b) σ ρ).n
        calc intWort (eval σ₀ a σ ρ).n + intWort (eval σ₀ b σ ρ).n
            = intWort ((eval σ₀ a σ ρ).n + (eval σ₀ b σ ρ).n) := intWort_add _ _
          _ = intWort (eval σ₀ (Expr.add a b) σ ρ).n := rfl
      · show s2.speicher = s.speicher
        rw [hmem2, hmem1]
      · intro q hqd hqf
        have hqtmp : q ≠ tmp := fun heq => hqf (heq ▸ List.mem_cons_self)
        have hqrest : q ∉ rest := fun hin => hqf (List.mem_cons_of_mem _ hin)
        show regSet s2.register dst (add64 (s2.register dst) (s2.register tmp)).1 q =
          s.register q
        rw [regSet_fremd _ _ _ _ hqd, hreg2 q hqtmp hqrest, hreg1 q hqd hqrest]
      · show regSet s2.register dst (add64 (s2.register dst) (s2.register tmp)).1
            Register.rsp = s.register Register.rsp
        rw [regSet_fremd _ _ _ _ (Ne.symm hrsp.1), hreg2 _ (Ne.symm hrspTmp) hrspRest,
          hreg1 _ (Ne.symm hrsp.1) hrspRest]
  | _, _, _, _, _, _, @IstTief.sub _ _ _ abb _ _ _ _ a b dst tmp rest pa pb ha hb => fun ρ σ₀ σ s hfr hrsp hrenv => by
      have hfrA := frischListe_tail abb dst tmp rest hfr
      have hfrB := frischListe_kopf abb dst tmp rest hfr
      have hdstTmp := frischListe_dst_ne_tmp abb dst tmp rest hfr
      have hrspRest : Register.rsp ∉ rest := fun hin => hrsp.2 (List.mem_cons_of_mem _ hin)
      have hrspTmp : tmp ≠ Register.rsp := by
        intro heq; exact hrsp.2 (heq ▸ List.mem_cons_self)
      obtain ⟨s1, hrun1, hval1, hmem1, hreg1, hrsp1⟩ :=
        istTief_korrekt abb a dst rest pa ha ρ σ₀ σ s hfrA ⟨hrsp.1, hrspRest⟩ hrenv
      have hrenv1 : EnvRepr ρ s1.register abb := by
        intro lo' hi' x
        have hx := hfr.1 _ x
        rw [hreg1 _ hx.1 (fun hin => hx.2 (List.mem_cons_of_mem _ hin))]
        exact hrenv lo' hi' x
      obtain ⟨s2, hrun2, hval2, hmem2, hreg2, hrsp2⟩ :=
        istTief_korrekt abb b tmp rest pb hb ρ σ₀ σ s1 hfrB ⟨hrspTmp, hrspRest⟩ hrenv1
      have hdst2 : s2.register dst = intWort (eval σ₀ a σ ρ).n := by
        rw [hreg2 dst (hdstTmp) (fun hin => hfr.2.1 (by
          rw [List.mem_cons]; exact Or.inr hin))]
        exact hval1
      have hlen : laengeOk (encode (Befehl.subReg64 dst tmp)).length = true := laengeOk_encode _
      have hsub := schritt_subReg64 ⟨Befehl.subReg64 dst tmp, (encode (Befehl.subReg64 dst tmp)).length⟩
        s2 dst tmp hlen rfl
      have hmap : ((pa ++ pb ++ [Befehl.subReg64 dst tmp]).map
          fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
          (pa.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          (pb.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          [⟨Befehl.subReg64 dst tmp, (encode (Befehl.subReg64 dst tmp)).length⟩] := by
        simp [List.map_append]
      refine ⟨schrittRegister s2 (ripNach s2.rip (encode (Befehl.subReg64 dst tmp)).length)
        (sub64 (s2.register dst) (s2.register tmp)).2 dst
        (sub64 (s2.register dst) (s2.register tmp)).1, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hmap]
        have h12 : lauf ((pa.map fun b => ⟨b, (encode b).length⟩) ++
            (pb.map fun b => ⟨b, (encode b).length⟩)) s = some s2 := by
          rw [lauf_anhang _ _ _ _ hrun1]; exact hrun2
        rw [lauf_anhang _ _ _ _ h12, lauf_einzeln_gleich]
        exact hsub
      · show regSet s2.register dst (sub64 (s2.register dst) (s2.register tmp)).1 dst =
            intWort (eval σ₀ (Expr.sub a b) σ ρ).n
        rw [regSet_gleich, hdst2, hval2]
        show intWort (eval σ₀ a σ ρ).n - intWort (eval σ₀ b σ ρ).n =
          intWort (eval σ₀ (Expr.sub a b) σ ρ).n
        calc intWort (eval σ₀ a σ ρ).n - intWort (eval σ₀ b σ ρ).n
            = intWort ((eval σ₀ a σ ρ).n - (eval σ₀ b σ ρ).n) := intWort_sub _ _
          _ = intWort (eval σ₀ (Expr.sub a b) σ ρ).n := rfl
      · show s2.speicher = s.speicher
        rw [hmem2, hmem1]
      · intro q hqd hqf
        have hqtmp : q ≠ tmp := fun heq => hqf (heq ▸ List.mem_cons_self)
        have hqrest : q ∉ rest := fun hin => hqf (List.mem_cons_of_mem _ hin)
        show regSet s2.register dst (sub64 (s2.register dst) (s2.register tmp)).1 q =
          s.register q
        rw [regSet_fremd _ _ _ _ hqd, hreg2 q hqtmp hqrest, hreg1 q hqd hqrest]
      · show regSet s2.register dst (sub64 (s2.register dst) (s2.register tmp)).1
            Register.rsp = s.register Register.rsp
        rw [regSet_fremd _ _ _ _ (Ne.symm hrsp.1), hreg2 _ (Ne.symm hrspTmp) hrspRest,
          hreg1 _ (Ne.symm hrsp.1) hrspRest]
  | _, _, _, _, _, _, @IstTief.neg _ _ _ abb _ _ a dst tmp rest pa ha => fun ρ σ₀ σ s hfr hrsp hrenv => by
      have hfrA := frischListe_tail abb dst tmp rest hfr
      have hdstTmp := frischListe_dst_ne_tmp abb dst tmp rest hfr
      have hrspRest : Register.rsp ∉ rest := fun hin => hrsp.2 (List.mem_cons_of_mem _ hin)
      have hrspTmp : tmp ≠ Register.rsp := by
        intro heq; exact hrsp.2 (heq ▸ List.mem_cons_self)
      obtain ⟨s1, hrun1, hval1, hmem1, hreg1, hrsp1⟩ :=
        istTief_korrekt abb a dst rest pa ha ρ σ₀ σ s hfrA ⟨hrsp.1, hrspRest⟩ hrenv
      -- Step 1: `xorReg64 tmp tmp` zeroes `tmp`, every other register kept.
      have hlenX : laengeOk (encode (Befehl.xorReg64 tmp tmp)).length = true := laengeOk_encode _
      obtain ⟨s2, hrunX, htmp2, hpres2, hmemX⟩ :
          ∃ s2, schritt ⟨Befehl.xorReg64 tmp tmp, (encode (Befehl.xorReg64 tmp tmp)).length⟩ s1
              = some s2 ∧
            s2.register tmp = 0 ∧ (∀ q, q ≠ tmp → s2.register q = s1.register q) ∧
            s2.speicher = s1.speicher := by
        refine ⟨schrittRegister s1 (ripNach s1.rip (encode (Befehl.xorReg64 tmp tmp)).length)
          (xor64 (s1.register tmp) (s1.register tmp)).2 tmp
          (xor64 (s1.register tmp) (s1.register tmp)).1,
          schritt_xorReg64 _ s1 tmp tmp hlenX rfl, ?_, ?_, rfl⟩
        · show regSet s1.register tmp (xor64 (s1.register tmp) (s1.register tmp)).1 tmp = 0
          rw [regSet_gleich]; exact xor64_self_wert _
        · intro q hq; exact regSet_fremd _ _ q _ hq
      have hdst2 : s2.register dst = intWort (eval σ₀ a σ ρ).n :=
        (hpres2 dst (hdstTmp)).trans hval1
      -- Step 2: `subReg64 tmp dst` computes `0 - a`; every register but `tmp` kept.
      have hlenS : laengeOk (encode (Befehl.subReg64 tmp dst)).length = true := laengeOk_encode _
      obtain ⟨s3, hrunS, htmp3, hpres3, hmemS⟩ :
          ∃ s3, schritt ⟨Befehl.subReg64 tmp dst, (encode (Befehl.subReg64 tmp dst)).length⟩ s2
              = some s3 ∧
            s3.register tmp = intWort (-(eval σ₀ a σ ρ).n) ∧
            (∀ q, q ≠ tmp → s3.register q = s2.register q) ∧ s3.speicher = s2.speicher := by
        refine ⟨schrittRegister s2 (ripNach s2.rip (encode (Befehl.subReg64 tmp dst)).length)
          (sub64 (s2.register tmp) (s2.register dst)).2 tmp
          (sub64 (s2.register tmp) (s2.register dst)).1,
          schritt_subReg64 _ s2 tmp dst hlenS rfl, ?_, ?_, rfl⟩
        · show regSet s2.register tmp (sub64 (s2.register tmp) (s2.register dst)).1 tmp =
              intWort (-(eval σ₀ a σ ρ).n)
          rw [regSet_gleich, htmp2, hdst2]
          show (0 : Wort) - intWort (eval σ₀ a σ ρ).n = intWort (-(eval σ₀ a σ ρ).n)
          rw [← intWort_zero, intWort_sub]
          exact congrArg intWort (by omega)
        · intro q hq; exact regSet_fremd _ _ q _ hq
      have hdst3 : s3.register dst = intWort (eval σ₀ a σ ρ).n :=
        (hpres3 dst hdstTmp).trans hdst2
      -- Step 3: `movReg64 dst tmp` commits the negated value; every register but `dst` kept.
      have hlenM : laengeOk (encode (Befehl.movReg64 dst tmp)).length = true := laengeOk_encode _
      obtain ⟨s4, hrunM, hval4, hpres4, hmemM⟩ :
          ∃ s4, schritt ⟨Befehl.movReg64 dst tmp, (encode (Befehl.movReg64 dst tmp)).length⟩ s3
              = some s4 ∧
            s4.register dst = intWort (eval σ₀ (Expr.neg a) σ ρ).n ∧
            (∀ q, q ≠ dst → s4.register q = s3.register q) ∧ s4.speicher = s3.speicher := by
        refine ⟨schrittRegister s3 (ripNach s3.rip (encode (Befehl.movReg64 dst tmp)).length)
          s3.flags dst (s3.register tmp),
          schritt_movReg64 _ s3 dst tmp hlenM rfl, ?_, ?_, rfl⟩
        · show regSet s3.register dst (s3.register tmp) dst =
              intWort (eval σ₀ (Expr.neg a) σ ρ).n
          rw [regSet_gleich, htmp3]; rfl
        · intro q hq; exact regSet_fremd _ _ q _ hq
      have hmapNeg : ((pa ++
          [Befehl.xorReg64 tmp tmp, Befehl.subReg64 tmp dst, Befehl.movReg64 dst tmp]).map
          fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
          (pa.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          [(⟨Befehl.xorReg64 tmp tmp, (encode (Befehl.xorReg64 tmp tmp)).length⟩ : Decodiert),
           ⟨Befehl.subReg64 tmp dst, (encode (Befehl.subReg64 tmp dst)).length⟩,
           ⟨Befehl.movReg64 dst tmp, (encode (Befehl.movReg64 dst tmp)).length⟩] := by
        simp [List.map_append]
      have htail : lauf
          [(⟨Befehl.xorReg64 tmp tmp, (encode (Befehl.xorReg64 tmp tmp)).length⟩ : Decodiert),
           ⟨Befehl.subReg64 tmp dst, (encode (Befehl.subReg64 tmp dst)).length⟩,
           ⟨Befehl.movReg64 dst tmp, (encode (Befehl.movReg64 dst tmp)).length⟩] s1 = some s4 := by
        simp only [lauf, hrunX, hrunS, hrunM]
      refine ⟨s4, ?_, hval4, ?_, ?_, ?_⟩
      · rw [hmapNeg, lauf_anhang _ _ _ _ hrun1]
        exact htail
      · rw [hmemM, hmemS, hmemX]; exact hmem1
      · intro q hqd hqf
        have hqtmp : q ≠ tmp := fun heq => hqf (heq ▸ List.mem_cons_self)
        have hqrest : q ∉ rest := fun hin => hqf (List.mem_cons_of_mem _ hin)
        rw [hpres4 q hqd, hpres3 q hqtmp, hpres2 q hqtmp]
        exact hreg1 q hqd hqrest
      · rw [hpres4 _ (Ne.symm hrsp.1), hpres3 _ (Ne.symm hrspTmp), hpres2 _ (Ne.symm hrspTmp)]
        exact hrsp1

/-! ## 6. Signed 64-bit overflow corollary.

    `Bereich64` is the honest side condition the task asks for: EVERY node
    of the tree, not only the leaves, has its TYPE range inside the signed
    64-bit window. It is computed from the expression's indices alone
    (never assumed): the window bound at this node, conjoined recursively
    with the same bound on every child. Matched over a general `τ` (no
    opaque carrier index), with a plain `match` on `t` for `var` since a
    source variable may carry any type -- only its `.int` instances
    constrain anything here. -/

/-- `-(2^63) ≤ lo` and `hi < 2^63`: the signed 64-bit window on a range. -/
def imBereich64 (lo hi : Int) : Prop := -(2 ^ 63 : Int) ≤ lo ∧ hi < 2 ^ 63

/-- Every node's own type range lies in the signed 64-bit window. -/
def Bereich64 {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} :
    ∀ {τ : Ty}, Expr D Γ Λ τ → Prop
  | _, .lit n => imBereich64 n n
  | .int lo hi, .var _x => imBereich64 lo hi
  | _, .var _ => True
  | _, .weiter (lo' := lo') (hi' := hi') _ _ e => imBereich64 lo' hi' ∧ Bereich64 e
  | _, .add (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b =>
    imBereich64 (l1 + l2) (h1 + h2) ∧ Bereich64 a ∧ Bereich64 b
  | _, .sub (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b =>
    imBereich64 (l1 - h2) (h1 - l2) ∧ Bereich64 a ∧ Bereich64 b
  | _, .neg (lo := lo) (hi := hi) a => imBereich64 (-hi) (-lo) ∧ Bereich64 a
  | _, _ => True

/-- The root's own window bound is exactly the top conjunct (or the whole
    fact, at a leaf) of `Bereich64`, read off through the six `IstTief`
    shapes -- the SAME non-stuck matching style as `istTief_korrekt`. -/
theorem bereich64_wurzel_tief {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) :
    ∀ {lo hi : Int} {e : Expr D Γ Λ (.int lo hi)} {dst : Register} {frei : List Register}
      {prog : List Befehl}, IstTief abb e dst frei prog → Bereich64 e → imBereich64 lo hi
  | _, _, _, _, _, _, @IstTief.lit _ _ _ abb n dst frei => fun h => h
  | _, _, _, _, _, _, @IstTief.var _ _ _ abb _ x dst frei => fun h => h
  | _, _, _, _, _, _, @IstTief.weiter _ _ _ abb _ _ _ _ h1 h2 e dst frei p _he => fun h => h.1
  | _, _, _, _, _, _, @IstTief.add _ _ _ abb _ _ _ _ a b dst tmp rest pa pb _ha _hb => fun h => h.1
  | _, _, _, _, _, _, @IstTief.sub _ _ _ abb _ _ _ _ a b dst tmp rest pa pb _ha _hb => fun h => h.1
  | _, _, _, _, _, _, @IstTief.neg _ _ _ abb _ _ a dst tmp rest pa _ha => fun h => h.1

/-- SIGNED 64-BIT CorrectNESS: under `Bereich64` (every subtree's type
    range inside the signed 64-bit window, a decidable side condition
    computed from the expression's indices alone), the modular word
    `istTief_korrekt` already proves `dst` holds is EXACTLY the source's
    signed reading -- the deep-tree generalisation of
    `ExpressionLowering.senkung_ohne_ueberlauf_add/sub`'s value conclusion.
    No architectural per-node overflow flag is tracked for the deep tree
    (an honest CUT; the one-level fragment's flag facts live where they
    were proved). -/
theorem istTief_ohne_ueberlauf {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (dst : Register) (frei : List Register) (prog : List Befehl)
    (hT : IstTief abb e dst frei prog) (hB : Bereich64 e)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hfr : FrischListe abb dst frei) (hrsp : dst ≠ Register.rsp ∧ Register.rsp ∉ frei)
    (hrenv : EnvRepr ρ s.register abb) :
    ∃ s', lauf (prog.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) s = some s' ∧
      sint (s'.register dst) = (eval σ₀ e σ ρ).n ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → q ∉ frei → s'.register q = s.register q) ∧
      s'.register Register.rsp = s.register Register.rsp := by
  obtain ⟨s', hrun, hval, hmem, hreg, hrsp'⟩ :=
    istTief_korrekt abb e dst frei prog hT ρ σ₀ σ s hfr hrsp hrenv
  obtain ⟨hroot1, hroot2⟩ := bereich64_wurzel_tief abb hT hB
  have hb1 := (eval σ₀ e σ ρ).lo_le
  have hb2 := (eval σ₀ e σ ρ).le_hi
  refine ⟨s', hrun, ?_, hmem, hreg, hrsp'⟩
  rw [hval]
  exact intWort_sint _ (by omega) (by omega)

/-! ## 7. Comparisons for branches: `lt`/`le`/`eq` lowered to `cmpReg64`.

    Same register-stack discipline as the binary arithmetic nodes: the
    head of `frei` becomes `tmp` for the right operand, the tail is the
    shared scratch pool for both (deep) operands. The comparison itself
    writes NO register (`cmpReg64` only sets flags and advances `rip`,
    `Ausfuehrung.schritt`'s own equation): the result is read off the
    flags with a `Bedingung` chosen by the source operator, for a later
    `jumpIf32` to test. -/

/-- Lower one comparison to lowered operands plus `cmpReg64`, returning the
    `Bedingung` a branch should test for "true". Every other boolean form,
    and an empty `frei`, refuses with `none`. -/
def senkVergleich {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst : Register) (frei : List Register) :
    Option (List Befehl × Bedingung) :=
  match e with
  | .lt a b =>
    match frei with
    | [] => none
    | tmp :: rest =>
      match senkTief abb a dst rest, senkTief abb b tmp rest with
      | some pa, some pb => some (pa ++ pb ++ [Befehl.cmpReg64 dst tmp], Bedingung.l)
      | _, _ => none
  | .le a b =>
    match frei with
    | [] => none
    | tmp :: rest =>
      match senkTief abb a dst rest, senkTief abb b tmp rest with
      | some pa, some pb => some (pa ++ pb ++ [Befehl.cmpReg64 dst tmp], Bedingung.le)
      | _, _ => none
  | .eq a b =>
    match frei with
    | [] => none
    | tmp :: rest =>
      match senkTief abb a dst rest, senkTief abb b tmp rest with
      | some pa, some pb => some (pa ++ pb ++ [Befehl.cmpReg64 dst tmp], Bedingung.e)
      | _, _ => none
  | _ => none

/-- PLANTED REFUSAL: `und`/boolean-and is outside the lowered comparisons. -/
theorem senkVergleich_verweigert_und {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (dst : Register) (frei : List Register) :
    senkVergleich abb (Expr.und (D := D) (Γ := Γ) (Λ := Λ) .wahr .wahr) dst frei = none := by
  cases frei <;> rfl

/-- Shape inversion: every successful comparison lowering is `lt`/`le`/`eq`
    over two DEEP-lowerable operands sharing the register stack, with
    `cmpReg64` and the matching `Bedingung`. General `τ`, the file-wide
    non-stuck pattern. -/
inductive IstVergleich {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) :
    ∀ {τ : Ty}, Expr D Γ Λ τ → Register → List Register → List Befehl → Bedingung → Prop where
  | lt {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
      (dst tmp : Register) (rest : List Register) (pa pb : List Befehl)
      (ha : IstTief abb a dst rest pa) (hb : IstTief abb b tmp rest pb) :
      IstVergleich abb (Expr.lt a b) dst (tmp :: rest)
        (pa ++ pb ++ [Befehl.cmpReg64 dst tmp]) Bedingung.l
  | le {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
      (dst tmp : Register) (rest : List Register) (pa pb : List Befehl)
      (ha : IstTief abb a dst rest pa) (hb : IstTief abb b tmp rest pb) :
      IstVergleich abb (Expr.le a b) dst (tmp :: rest)
        (pa ++ pb ++ [Befehl.cmpReg64 dst tmp]) Bedingung.le
  | eq {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
      (dst tmp : Register) (rest : List Register) (pa pb : List Befehl)
      (ha : IstTief abb a dst rest pa) (hb : IstTief abb b tmp rest pb) :
      IstVergleich abb (Expr.eq a b) dst (tmp :: rest)
        (pa ++ pb ++ [Befehl.cmpReg64 dst tmp]) Bedingung.e

/-- Every successful comparison lowering is one of the three `IstVergleich`
    shapes. Proved over a general `τ` (`e`'s index), closing the ~29
    unsupported constructors with `simp [senkVergleich]`. -/
theorem istVergleich_von_senkVergleich {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) :
    ∀ {τ : Ty} (e : Expr D Γ Λ τ) (dst : Register) (frei : List Register)
      (prog : List Befehl) (cond : Bedingung),
      senkVergleich abb e dst frei = some (prog, cond) →
      IstVergleich abb e dst frei prog cond
  | _, .lt a b, dst, frei, prog, cond, h => by
      cases frei with
      | nil => simp [senkVergleich] at h
      | cons tmp rest =>
        cases h1 : senkTief abb a dst rest with
        | none => simp [senkVergleich, h1] at h
        | some pa =>
          cases h2 : senkTief abb b tmp rest with
          | none => simp [senkVergleich, h1, h2] at h
          | some pb =>
            simp only [senkVergleich, h1, h2] at h
            have heq := Option.some_inj.mp h.symm
            injection heq with hprog hcond
            subst hprog; subst hcond
            exact .lt a b dst tmp rest pa pb (istTief_von_senkTief abb a dst rest pa h1)
              (istTief_von_senkTief abb b tmp rest pb h2)
  | _, .le a b, dst, frei, prog, cond, h => by
      cases frei with
      | nil => simp [senkVergleich] at h
      | cons tmp rest =>
        cases h1 : senkTief abb a dst rest with
        | none => simp [senkVergleich, h1] at h
        | some pa =>
          cases h2 : senkTief abb b tmp rest with
          | none => simp [senkVergleich, h1, h2] at h
          | some pb =>
            simp only [senkVergleich, h1, h2] at h
            have heq := Option.some_inj.mp h.symm
            injection heq with hprog hcond
            subst hprog; subst hcond
            exact .le a b dst tmp rest pa pb (istTief_von_senkTief abb a dst rest pa h1)
              (istTief_von_senkTief abb b tmp rest pb h2)
  | _, .eq a b, dst, frei, prog, cond, h => by
      cases frei with
      | nil => simp [senkVergleich] at h
      | cons tmp rest =>
        cases h1 : senkTief abb a dst rest with
        | none => simp [senkVergleich, h1] at h
        | some pa =>
          cases h2 : senkTief abb b tmp rest with
          | none => simp [senkVergleich, h1, h2] at h
          | some pb =>
            simp only [senkVergleich, h1, h2] at h
            have heq := Option.some_inj.mp h.symm
            injection heq with hprog hcond
            subst hprog; subst hcond
            exact .eq a b dst tmp rest pa pb (istTief_von_senkTief abb a dst rest pa h1)
              (istTief_von_senkTief abb b tmp rest pb h2)
  | _, .wahr, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .falsch, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .lit _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .var _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .glob _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .slot _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .durch _ _ _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .ptrOf _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .fnref _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .altGlob _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .altSlot _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .weiter _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .add _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .sub _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .neg _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .mul _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .div _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .rem _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .sdiv _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .srem _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .leseBytes _ _ _ _ _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .band _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .bor _ _ _ _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .bxor _ _ _ _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .shl _ _ _ _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .shr _ _ _ _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .fllt _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .flle _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .und _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .oder _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .nicht _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .none _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .some _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .istSome _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .fall _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .grund _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .forallSlots _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .existsSlots _ _ _, _, _, _, _, h => by simp [senkVergleich] at h
  | _, .reaches _ _ _ _ _ _, _, _, _, _, h => by simp [senkVergleich] at h

/-! ## 8. Comparison correctness: the condition code equals the source
    truth value, under the signed-64 range side condition.

    `VergleichBereich` packages the exact three facts the proof needs,
    read off the two operands' own types: both operands' `Bereich64` (so
    `intWort_sint` round-trips each one) and the DIFFERENCE range in the
    signed window (so `cmpReg64`'s architectural SUB never overflows --
    the same shape of premise as `ExpressionLowering.senkung_ohne_ueberlauf_sub`'s
    `hlo`/`hhi`). -/

/-- The side condition a comparison's correctness needs: both operands'
    `Bereich64`, plus their difference range inside the signed 64-bit
    window (so the architectural `cmpReg64` subtraction cannot overflow). -/
def VergleichBereich {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} :
    ∀ {τ : Ty}, Expr D Γ Λ τ → Prop
  | _, .lt (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b =>
    Bereich64 a ∧ Bereich64 b ∧ imBereich64 (l1 - h2) (h1 - l2)
  | _, .le (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b =>
    Bereich64 a ∧ Bereich64 b ∧ imBereich64 (l1 - h2) (h1 - l2)
  | _, .eq (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b =>
    Bereich64 a ∧ Bereich64 b ∧ imBereich64 (l1 - h2) (h1 - l2)
  | _, _ => True

/-- `(sub64 x y).2.zf` is architectural word equality: a direct group-law
    computation (`BitVec.sub_eq_iff_eq_add`, `BitVec.zero_add`), reused
    rather than a second equality test. -/
theorem sub64_zf_iff (x y : Wort) : (sub64 x y).2.zf = true ↔ x = y := by
  rw [sub64_zf]
  unfold zfTest
  rw [beq_iff_eq]
  constructor
  · intro h
    have h' := BitVec.sub_eq_iff_eq_add.mp h
    simpa using h'
  · intro h
    subst h
    exact BitVec.sub_self x

/-- The architectural SUB behind `cmpReg64` never overflows when both
    exact operand values lie in the signed 64-bit window AND their exact
    difference does too: the signed results are the exact operands and
    their exact difference (mirrors `senkung_ohne_ueberlauf_sub`'s proof,
    without building a result `Zahl`). -/
theorem cmp_kein_ueberlauf {l1 h1 l2 h2 : Int} (na nb : Int)
    (hna : l1 ≤ na) (hna' : na ≤ h1) (hnb : l2 ≤ nb) (hnb' : nb ≤ h2)
    (hBa : imBereich64 l1 h1) (hBb : imBereich64 l2 h2)
    (hdiff : imBereich64 (l1 - h2) (h1 - l2)) :
    (sub64 (intWort na) (intWort nb)).2.of = false ∧
    sint (intWort na) = na ∧ sint (intWort nb) = nb ∧
    sint (sub64 (intWort na) (intWort nb)).1 = na - nb := by
  obtain ⟨hBa1, hBa2⟩ := hBa
  obtain ⟨hBb1, hBb2⟩ := hBb
  obtain ⟨hd1, hd2⟩ := hdiff
  have hsa : sint (intWort na) = na := intWort_sint _ (by omega) (by omega)
  have hsb : sint (intWort nb) = nb := intWort_sint _ (by omega) (by omega)
  have hof : (sub64 (intWort na) (intWort nb)).2.of = false := by
    cases hofEq : (sub64 (intWort na) (intWort nb)).2.of with
    | true =>
      have hout := (sub64_of_iff _ _).mp hofEq
      rw [hsa, hsb] at hout
      omega
    | false => rfl
  refine ⟨hof, hsa, hsb, ?_⟩
  have hval := sub64_sint_eq_of_no_overflow (intWort na) (intWort nb) hof
  rw [hsa, hsb] at hval
  exact hval

/-- Comparison correctness: the lowered program runs, the chosen
    `Bedingung` read off the resulting flags equals the source truth
    value, memory is untouched, every register outside `dst :: frei` is
    kept, and `rsp` is kept. The register-stack argument is exactly
    `istTief_korrekt`'s (one scratch peel, shared sequentially); the two
    operands never write past `dst`/`tmp`, so the comparison reads exactly
    their committed values. -/
theorem istVergleich_korrekt {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) :
    ∀ {e : Expr D Γ Λ Ty.bool} {dst : Register} {frei : List Register}
      {prog : List Befehl} {cond : Bedingung},
      IstVergleich abb e dst frei prog cond → VergleichBereich e →
      ∀ (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand),
        FrischListe abb dst frei →
        (dst ≠ Register.rsp ∧ Register.rsp ∉ frei) →
        EnvRepr ρ s.register abb →
        ∃ s', lauf (prog.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) s = some s' ∧
          bedingung cond s'.flags = eval σ₀ e σ ρ ∧
          s'.speicher = s.speicher ∧
          (∀ q, q ≠ dst → q ∉ frei → s'.register q = s.register q) ∧
          s'.register Register.rsp = s.register Register.rsp
  | _, _, _, _, _, @IstVergleich.lt _ _ _ abb _ _ _ _ a b dst tmp rest pa pb ha hb =>
    fun hVB ρ σ₀ σ s hfr hrsp hrenv => by
      obtain ⟨hBa, hBb, hdiff⟩ := hVB
      have hfrA := frischListe_tail abb dst tmp rest hfr
      have hfrB := frischListe_kopf abb dst tmp rest hfr
      have hdstTmp := frischListe_dst_ne_tmp abb dst tmp rest hfr
      have hrspRest : Register.rsp ∉ rest := fun hin => hrsp.2 (List.mem_cons_of_mem _ hin)
      have hrspTmp : tmp ≠ Register.rsp := by
        intro heq; exact hrsp.2 (heq ▸ List.mem_cons_self)
      obtain ⟨s1, hrun1, hval1, hmem1, hreg1, hrsp1⟩ :=
        istTief_korrekt abb a dst rest pa ha ρ σ₀ σ s hfrA ⟨hrsp.1, hrspRest⟩ hrenv
      have hrenv1 : EnvRepr ρ s1.register abb := by
        intro lo' hi' x
        have hx := hfr.1 _ x
        rw [hreg1 _ hx.1 (fun hin => hx.2 (List.mem_cons_of_mem _ hin))]
        exact hrenv lo' hi' x
      obtain ⟨s2, hrun2, hval2, hmem2, hreg2, hrsp2⟩ :=
        istTief_korrekt abb b tmp rest pb hb ρ σ₀ σ s1 hfrB ⟨hrspTmp, hrspRest⟩ hrenv1
      have hdst2 : s2.register dst = intWort (eval σ₀ a σ ρ).n := by
        rw [hreg2 dst hdstTmp (fun hin => hfr.2.1 (by rw [List.mem_cons]; exact Or.inr hin))]
        exact hval1
      have hlen : laengeOk (encode (Befehl.cmpReg64 dst tmp)).length = true := laengeOk_encode _
      have hcmp := schritt_cmpReg64 ⟨Befehl.cmpReg64 dst tmp, (encode (Befehl.cmpReg64 dst tmp)).length⟩
        s2 dst tmp hlen rfl
      have hmap : ((pa ++ pb ++ [Befehl.cmpReg64 dst tmp]).map
          fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
          (pa.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          (pb.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          [⟨Befehl.cmpReg64 dst tmp, (encode (Befehl.cmpReg64 dst tmp)).length⟩] := by
        simp [List.map_append]
      obtain ⟨hBaRoot1, hBaRoot2⟩ := bereich64_wurzel_tief abb ha hBa
      obtain ⟨hBbRoot1, hBbRoot2⟩ := bereich64_wurzel_tief abb hb hBb
      obtain ⟨hof, hsa, hsb, hsd⟩ := cmp_kein_ueberlauf (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
        ⟨hBaRoot1, hBaRoot2⟩ ⟨hBbRoot1, hBbRoot2⟩ hdiff
      obtain ⟨s3, hrun3, hflag3, hreg3, hspeicher3⟩ :
          ∃ s3, schritt ⟨Befehl.cmpReg64 dst tmp, (encode (Befehl.cmpReg64 dst tmp)).length⟩ s2
              = some s3 ∧
            s3.flags = (sub64 (s2.register dst) (s2.register tmp)).2 ∧
            s3.register = s2.register ∧ s3.speicher = s2.speicher :=
        ⟨_, hcmp, rfl, rfl, rfl⟩
      refine ⟨s3, ?_, ?_, hspeicher3.trans (hmem2.trans hmem1), ?_, ?_⟩
      · rw [hmap]
        have h12 : lauf ((pa.map fun b => ⟨b, (encode b).length⟩) ++
            (pb.map fun b => ⟨b, (encode b).length⟩)) s = some s2 := by
          rw [lauf_anhang _ _ _ _ hrun1]; exact hrun2
        rw [lauf_anhang _ _ _ _ h12, lauf_einzeln_gleich]
        exact hrun3
      · rw [hflag3]
        show bedingung .l (sub64 (s2.register dst) (s2.register tmp)).2 = eval σ₀ (Expr.lt a b) σ ρ
        rw [hdst2, hval2, bedingung_l]
        have hsfof : ((sub64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2.sf != false) =
            decide ((eval σ₀ a σ ρ).n < (eval σ₀ b σ ρ).n) := by
          rw [sub64_sf_sint, hsd]
          rcases Int.lt_or_le (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n with hlt | hge
          · simp [show (eval σ₀ a σ ρ).n - (eval σ₀ b σ ρ).n < 0 from by omega, hlt]
          · simp [show ¬ (eval σ₀ a σ ρ).n - (eval σ₀ b σ ρ).n < 0 from by omega,
              show ¬ (eval σ₀ a σ ρ).n < (eval σ₀ b σ ρ).n from by omega]
        rw [hof]
        exact hsfof
      · intro q hqd hqf
        have hqtmp : q ≠ tmp := fun heq => hqf (heq ▸ List.mem_cons_self)
        have hqrest : q ∉ rest := fun hin => hqf (List.mem_cons_of_mem _ hin)
        show s3.register q = s.register q
        rw [hreg3, hreg2 q hqtmp hqrest, hreg1 q hqd hqrest]
      · show s3.register Register.rsp = s.register Register.rsp
        rw [hreg3, hreg2 _ (Ne.symm hrspTmp) hrspRest, hreg1 _ (Ne.symm hrsp.1) hrspRest]
  | _, _, _, _, _, @IstVergleich.le _ _ _ abb _ _ _ _ a b dst tmp rest pa pb ha hb =>
    fun hVB ρ σ₀ σ s hfr hrsp hrenv => by
      obtain ⟨hBa, hBb, hdiff⟩ := hVB
      have hfrA := frischListe_tail abb dst tmp rest hfr
      have hfrB := frischListe_kopf abb dst tmp rest hfr
      have hdstTmp := frischListe_dst_ne_tmp abb dst tmp rest hfr
      have hrspRest : Register.rsp ∉ rest := fun hin => hrsp.2 (List.mem_cons_of_mem _ hin)
      have hrspTmp : tmp ≠ Register.rsp := by
        intro heq; exact hrsp.2 (heq ▸ List.mem_cons_self)
      obtain ⟨s1, hrun1, hval1, hmem1, hreg1, hrsp1⟩ :=
        istTief_korrekt abb a dst rest pa ha ρ σ₀ σ s hfrA ⟨hrsp.1, hrspRest⟩ hrenv
      have hrenv1 : EnvRepr ρ s1.register abb := by
        intro lo' hi' x
        have hx := hfr.1 _ x
        rw [hreg1 _ hx.1 (fun hin => hx.2 (List.mem_cons_of_mem _ hin))]
        exact hrenv lo' hi' x
      obtain ⟨s2, hrun2, hval2, hmem2, hreg2, hrsp2⟩ :=
        istTief_korrekt abb b tmp rest pb hb ρ σ₀ σ s1 hfrB ⟨hrspTmp, hrspRest⟩ hrenv1
      have hdst2 : s2.register dst = intWort (eval σ₀ a σ ρ).n := by
        rw [hreg2 dst hdstTmp (fun hin => hfr.2.1 (by rw [List.mem_cons]; exact Or.inr hin))]
        exact hval1
      have hlen : laengeOk (encode (Befehl.cmpReg64 dst tmp)).length = true := laengeOk_encode _
      have hcmp := schritt_cmpReg64 ⟨Befehl.cmpReg64 dst tmp, (encode (Befehl.cmpReg64 dst tmp)).length⟩
        s2 dst tmp hlen rfl
      have hmap : ((pa ++ pb ++ [Befehl.cmpReg64 dst tmp]).map
          fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
          (pa.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          (pb.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          [⟨Befehl.cmpReg64 dst tmp, (encode (Befehl.cmpReg64 dst tmp)).length⟩] := by
        simp [List.map_append]
      obtain ⟨hBaRoot1, hBaRoot2⟩ := bereich64_wurzel_tief abb ha hBa
      obtain ⟨hBbRoot1, hBbRoot2⟩ := bereich64_wurzel_tief abb hb hBb
      obtain ⟨hof, hsa, hsb, hsd⟩ := cmp_kein_ueberlauf (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
        ⟨hBaRoot1, hBaRoot2⟩ ⟨hBbRoot1, hBbRoot2⟩ hdiff
      have hdstVal : s2.register dst = intWort (eval σ₀ a σ ρ).n := hdst2
      have hzf : (sub64 (s2.register dst) (s2.register tmp)).2.zf =
          decide ((eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n) := by
        rw [hdst2, hval2]
        rcases Decidable.em ((eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n) with heq | hne
        · rw [heq]
          simp [(sub64_zf_iff (intWort (eval σ₀ b σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).mpr rfl]
        · have hxney : intWort (eval σ₀ a σ ρ).n ≠ intWort (eval σ₀ b σ ρ).n := by
            intro hcontra
            apply hne
            have := congrArg sint hcontra
            rwa [hsa, hsb] at this
          rw [decide_eq_false hne]
          cases hz : (sub64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2.zf with
          | false => rfl
          | true => exact absurd ((sub64_zf_iff _ _).mp hz) hxney
      obtain ⟨s3, hrun3, hflag3, hreg3, hspeicher3⟩ :
          ∃ s3, schritt ⟨Befehl.cmpReg64 dst tmp, (encode (Befehl.cmpReg64 dst tmp)).length⟩ s2
              = some s3 ∧
            s3.flags = (sub64 (s2.register dst) (s2.register tmp)).2 ∧
            s3.register = s2.register ∧ s3.speicher = s2.speicher :=
        ⟨_, hcmp, rfl, rfl, rfl⟩
      refine ⟨s3, ?_, ?_, hspeicher3.trans (hmem2.trans hmem1), ?_, ?_⟩
      · rw [hmap]
        have h12 : lauf ((pa.map fun b => ⟨b, (encode b).length⟩) ++
            (pb.map fun b => ⟨b, (encode b).length⟩)) s = some s2 := by
          rw [lauf_anhang _ _ _ _ hrun1]; exact hrun2
        rw [lauf_anhang _ _ _ _ h12, lauf_einzeln_gleich]
        exact hrun3
      · rw [hflag3]
        show bedingung .le (sub64 (s2.register dst) (s2.register tmp)).2 = eval σ₀ (Expr.le a b) σ ρ
        rw [bedingung_le, hzf, hdst2, hval2]
        have hsfof : ((sub64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2.sf != false) =
            decide ((eval σ₀ a σ ρ).n < (eval σ₀ b σ ρ).n) := by
          rw [sub64_sf_sint, hsd]
          rcases Int.lt_or_le (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n with hlt | hge
          · simp [show (eval σ₀ a σ ρ).n - (eval σ₀ b σ ρ).n < 0 from by omega, hlt]
          · simp [show ¬ (eval σ₀ a σ ρ).n - (eval σ₀ b σ ρ).n < 0 from by omega,
              show ¬ (eval σ₀ a σ ρ).n < (eval σ₀ b σ ρ).n from by omega]
        rw [hof, hsfof]
        show (decide ((eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n) ||
          decide ((eval σ₀ a σ ρ).n < (eval σ₀ b σ ρ).n)) = decide ((eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n)
        rcases Decidable.em ((eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n) with heq | hne
        · simp [heq]
        · rcases Int.lt_or_le (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n with hlt | hge
          · simp [hne, hlt, show (eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n from by omega]
          · simp [hne, show ¬ (eval σ₀ a σ ρ).n < (eval σ₀ b σ ρ).n from by omega,
              show ¬ (eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n from by omega]
      · intro q hqd hqf
        have hqtmp : q ≠ tmp := fun heq => hqf (heq ▸ List.mem_cons_self)
        have hqrest : q ∉ rest := fun hin => hqf (List.mem_cons_of_mem _ hin)
        show s3.register q = s.register q
        rw [hreg3, hreg2 q hqtmp hqrest, hreg1 q hqd hqrest]
      · show s3.register Register.rsp = s.register Register.rsp
        rw [hreg3, hreg2 _ (Ne.symm hrspTmp) hrspRest, hreg1 _ (Ne.symm hrsp.1) hrspRest]
  | _, _, _, _, _, @IstVergleich.eq _ _ _ abb _ _ _ _ a b dst tmp rest pa pb ha hb =>
    fun hVB ρ σ₀ σ s hfr hrsp hrenv => by
      obtain ⟨hBa, hBb, hdiff⟩ := hVB
      have hfrA := frischListe_tail abb dst tmp rest hfr
      have hfrB := frischListe_kopf abb dst tmp rest hfr
      have hdstTmp := frischListe_dst_ne_tmp abb dst tmp rest hfr
      have hrspRest : Register.rsp ∉ rest := fun hin => hrsp.2 (List.mem_cons_of_mem _ hin)
      have hrspTmp : tmp ≠ Register.rsp := by
        intro heq; exact hrsp.2 (heq ▸ List.mem_cons_self)
      obtain ⟨s1, hrun1, hval1, hmem1, hreg1, hrsp1⟩ :=
        istTief_korrekt abb a dst rest pa ha ρ σ₀ σ s hfrA ⟨hrsp.1, hrspRest⟩ hrenv
      have hrenv1 : EnvRepr ρ s1.register abb := by
        intro lo' hi' x
        have hx := hfr.1 _ x
        rw [hreg1 _ hx.1 (fun hin => hx.2 (List.mem_cons_of_mem _ hin))]
        exact hrenv lo' hi' x
      obtain ⟨s2, hrun2, hval2, hmem2, hreg2, hrsp2⟩ :=
        istTief_korrekt abb b tmp rest pb hb ρ σ₀ σ s1 hfrB ⟨hrspTmp, hrspRest⟩ hrenv1
      have hdst2 : s2.register dst = intWort (eval σ₀ a σ ρ).n := by
        rw [hreg2 dst hdstTmp (fun hin => hfr.2.1 (by rw [List.mem_cons]; exact Or.inr hin))]
        exact hval1
      have hlen : laengeOk (encode (Befehl.cmpReg64 dst tmp)).length = true := laengeOk_encode _
      have hcmp := schritt_cmpReg64 ⟨Befehl.cmpReg64 dst tmp, (encode (Befehl.cmpReg64 dst tmp)).length⟩
        s2 dst tmp hlen rfl
      have hmap : ((pa ++ pb ++ [Befehl.cmpReg64 dst tmp]).map
          fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
          (pa.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          (pb.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
          [⟨Befehl.cmpReg64 dst tmp, (encode (Befehl.cmpReg64 dst tmp)).length⟩] := by
        simp [List.map_append]
      obtain ⟨hBaRoot1, hBaRoot2⟩ := bereich64_wurzel_tief abb ha hBa
      obtain ⟨hBbRoot1, hBbRoot2⟩ := bereich64_wurzel_tief abb hb hBb
      obtain ⟨hof, hsa, hsb, hsd⟩ := cmp_kein_ueberlauf (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
        ⟨hBaRoot1, hBaRoot2⟩ ⟨hBbRoot1, hBbRoot2⟩ hdiff
      obtain ⟨s3, hrun3, hflag3, hreg3, hspeicher3⟩ :
          ∃ s3, schritt ⟨Befehl.cmpReg64 dst tmp, (encode (Befehl.cmpReg64 dst tmp)).length⟩ s2
              = some s3 ∧
            s3.flags = (sub64 (s2.register dst) (s2.register tmp)).2 ∧
            s3.register = s2.register ∧ s3.speicher = s2.speicher :=
        ⟨_, hcmp, rfl, rfl, rfl⟩
      refine ⟨s3, ?_, ?_, hspeicher3.trans (hmem2.trans hmem1), ?_, ?_⟩
      · rw [hmap]
        have h12 : lauf ((pa.map fun b => ⟨b, (encode b).length⟩) ++
            (pb.map fun b => ⟨b, (encode b).length⟩)) s = some s2 := by
          rw [lauf_anhang _ _ _ _ hrun1]; exact hrun2
        rw [lauf_anhang _ _ _ _ h12, lauf_einzeln_gleich]
        exact hrun3
      · rw [hflag3]
        show bedingung .e (sub64 (s2.register dst) (s2.register tmp)).2 = eval σ₀ (Expr.eq a b) σ ρ
        rw [bedingung_e, hdst2, hval2]
        show (sub64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2.zf =
          decide ((eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n)
        rcases Decidable.em ((eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n) with heq | hne
        · rw [heq]
          simp [(sub64_zf_iff (intWort (eval σ₀ b σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).mpr rfl]
        · have hxney : intWort (eval σ₀ a σ ρ).n ≠ intWort (eval σ₀ b σ ρ).n := by
            intro hcontra
            apply hne
            have hc := congrArg sint hcontra
            rwa [hsa, hsb] at hc
          rw [decide_eq_false hne]
          cases hz : (sub64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2.zf with
          | false => rfl
          | true => exact absurd ((sub64_zf_iff _ _).mp hz) hxney
      · intro q hqd hqf
        have hqtmp : q ≠ tmp := fun heq => hqf (heq ▸ List.mem_cons_self)
        have hqrest : q ∉ rest := fun hin => hqf (List.mem_cons_of_mem _ hin)
        show s3.register q = s.register q
        rw [hreg3, hreg2 q hqtmp hqrest, hreg1 q hqd hqrest]
      · show s3.register Register.rsp = s.register Register.rsp
        rw [hreg3, hreg2 _ (Ne.symm hrspTmp) hrspRest, hreg1 _ (Ne.symm hrsp.1) hrspRest]

/- CUTS:
   Proved here, over the single source model (`Semantik.eval`) and the
   canonical pilot machine (`Codec.encode`, `Ausfuehrung.schritt`,
   `lauf`), generalising `ExpressionLowering.lean`'s one-level fragment
   to arbitrary depth:
   - `senkTief`: lowering of `lit`/`var`/`weiter`/`add`/`sub`/`neg` trees
     of any depth, over a shared register-stack scratch list; refuses
     (`none`) on every other source form AND on register exhaustion at a
     binary node (no spilling);
   - shape inversion (`IstTief`, `istTief_von_senkTief`) and value/memory/
     register/`rsp` correctness (`istTief_korrekt`) by a clean structural
     induction, with no opaque carrier projection ever appearing as an
     index (the file-wide non-stuck pattern: inversion over a general
     index, then matching the resulting six-constructor value);
   - the signed 64-bit overflow corollary (`Bereich64`, computed from the
     expression's own type indices; `istTief_ohne_ueberlauf`): under it,
     the register holds the EXACT signed source value, not only its
     modular reading;
   - `senkVergleich`/`IstVergleich`/`istVergleich_korrekt`: `lt`/`le`/`eq`
     lowered to `cmpReg64` plus a `Bedingung`, with the chosen condition
     code read off the resulting flags proved equal to the source Bool,
     under the same kind of signed-range side condition
     (`VergleichBereich`) applied to the architectural SUB behind `cmp`.

   NOT proved here, and not claimed:
   - No deeper source fragment: `mul`/`div`/`rem`/bitwise/float/memory/
     calls/control flow and every comparison but `lt`/`le`/`eq` refuse
     with `none` (honest boundary, not a silent gap).
   - No register spilling: an empty scratch list at a binary or
     comparison node refuses, even if the whole expression could fit in
     fewer registers with a smarter allocator.
   - No architectural per-node overflow-FLAG tracking through a deep
     tree: `istTief_ohne_ueberlauf` proves the final signed VALUE only
     (generalising the one-level fragment's value conclusion, not its
     flag conclusion). A later pass that needs an intermediate `add`/
     `sub` node's own `of`/`cf` must prove it locally from `istTief_korrekt`'s
     modular word, the same way `ExpressionLowering.senkung_ohne_ueberlauf_add/sub`
     already do for one level.
   - No branch instruction: `senkVergleich` stops at `cmpReg64` plus the
     chosen `Bedingung`; emitting and proving the following `jumpIf32`
     (reusing `schritt_jumpIf32_genommen/nicht`) is the next composition
     step, not done here.
   - No TSO bridge: runs are sequential `lauf` folds, as in
     `ExpressionLowering.lean`.
   - No whole-source or whole-binary theorem: these are expression/
     comparison fragments against the pilot machine, composed with (not
     replacing) the accepted source model and canonical executor.
-/

#print axioms senkTief_tief_ok
#print axioms istTief_von_senkTief
#print axioms istTief_korrekt
#print axioms bereich64_wurzel_tief
#print axioms istTief_ohne_ueberlauf
#print axioms istVergleich_von_senkVergleich
#print axioms istVergleich_korrekt

end Gabbro.Grammatik.X86
