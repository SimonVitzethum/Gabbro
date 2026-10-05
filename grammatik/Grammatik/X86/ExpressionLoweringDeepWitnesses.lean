/-
  File:      Grammatik/X86/ExpressionLoweringDeepWitnesses.lean
  Subject:   Joint witnesses and poison probes for the arbitrary-depth
             lowering (`ExpressionLoweringDeep.lean`).

  Reuses, never forks: `senkTief`/`IstTief`/`istTief_korrekt`/
  `istTief_ohne_ueberlauf`/`Bereich64`/`FrischListe` and
  `senkVergleich`/`IstVergleich`/`istVergleich_korrekt`/`VergleichBereich`
  from `ExpressionLoweringDeep.lean`; the witness declaration, context,
  environment and world (`ZeugeD`, `ZeugeCtx`, `ZeugeUmgebung`, `ZeugeWelt`,
  `ZeugeAbb`, `ZeugeStart`, `ZeugeSpeicher`) from `ExpressionLowering.lean`.
  No second source interpreter, no new register machine.

  Contents:
  - a depth-3 expression over the witness variable, lowered and run with
    its exact signed value checked (`zeuge_tief_lauf`, plus the joint
    `istTief_korrekt_zeuge`/`istTief_ohne_ueberlauf_zeuge`);
  - a comparison lowered and run both true and false
    (`istVergleich_korrekt_zeuge_wahr`/`_falsch`);
  - poison probes: register exhaustion at depth, `mul`/`div`/`slot`
    outside the fragment, an out-of-range comparison refused by the
    decidable `VergleichBereich` side condition, and a register-aliasing
    probe that shows `FrischListe` is load-bearing (dropping it gives a
    WRONG lowered value, not just an unprovable theorem).
-/
import Grammatik.X86.ExpressionLowering
import Grammatik.X86.ExpressionLoweringDeep

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-! ## 1. A depth-3 expression: `((x + 12) - 5) + 3`, `x = 30`. -/

/-- Depth-3 witness expression over the witness variable: three nested
    binary nodes (`add`, `sub`, `add`), the deepest leaf a variable. -/
def ZeugeTiefAusdruck : Expr ZeugeD ZeugeCtx [] (.int 10 110) :=
  .add (.sub (.add (.var .hier) (.lit 12)) (.lit 5)) (.lit 3)

/-- Scratch stack for the depth-3 witness: one register per nesting level. -/
def ZeugeTiefFrei : List Register := [Register.rcx, Register.rdx, Register.r8]

/-- The witness expression lowers to exactly this seven-instruction
    program: read `x`, add `12`, subtract `5`, add `3`, each level
    peeling its own scratch register off `ZeugeTiefFrei`. -/
theorem zeuge_tief_senkung :
    senkTief ZeugeAbb ZeugeTiefAusdruck Register.rax ZeugeTiefFrei =
      some [Befehl.movReg64 Register.rax Register.r10, Befehl.movImm64 Register.r8 (intWort 12),
        Befehl.addReg64 Register.rax Register.r8, Befehl.movImm64 Register.rdx (intWort 5),
        Befehl.subReg64 Register.rax Register.rdx, Befehl.movImm64 Register.rcx (intWort 3),
        Befehl.addReg64 Register.rax Register.rcx] := rfl

/-- The witness expression's source value: `((30 + 12) - 5) + 3 = 40`. -/
theorem zeuge_tief_auswertung :
    (eval ZeugeWelt ZeugeTiefAusdruck ZeugeWelt ZeugeUmgebung).n = 40 := rfl

/-- `FrischListe` holds: the witness variable lives in `r10`, disjoint
    from `rax` and the whole scratch stack. -/
theorem zeuge_tief_frisch : FrischListe ZeugeAbb Register.rax ZeugeTiefFrei := by
  refine ⟨fun τ x => ⟨?_, ?_⟩, by decide, by decide⟩
  · show Register.r10 ≠ Register.rax; decide
  · show Register.r10 ∉ ZeugeTiefFrei; decide

/-- The witness expression's range stays well inside the signed 64-bit
    window at every node (a direct `decide`, since `Bereich64` is built
    from `≤`/`<` on concrete `Int` literals). -/
theorem zeuge_tief_bereich : Bereich64 ZeugeTiefAusdruck := by
  show imBereich64 10 110 ∧
    ((imBereich64 7 107 ∧
      ((imBereich64 12 112 ∧ (imBereich64 0 100 ∧ imBereich64 12 12)) ∧
       imBereich64 5 5)) ∧
     imBereich64 3 3)
  unfold imBereich64
  decide

/-- Joint witness for `istTief_korrekt`: the depth-3 program, run from
    the witness start state, lands the modular word of `40` in `rax`,
    with memory, `rsp` and every register outside `rax :: ZeugeTiefFrei`
    kept. -/
theorem istTief_korrekt_zeuge :
    ∃ (prog : List Befehl) (hT : IstTief ZeugeAbb ZeugeTiefAusdruck Register.rax ZeugeTiefFrei prog) (s' : Zustand),
      lauf (prog.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ZeugeStart = some s' ∧
      s'.register Register.rax = intWort (eval ZeugeWelt ZeugeTiefAusdruck ZeugeWelt ZeugeUmgebung).n ∧
      s'.speicher = ZeugeStart.speicher ∧
      (∀ q, q ≠ Register.rax → q ∉ ZeugeTiefFrei → s'.register q = ZeugeStart.register q) ∧
      s'.register Register.rsp = ZeugeStart.register Register.rsp := by
  obtain ⟨prog, hsenk⟩ : ∃ prog, senkTief ZeugeAbb ZeugeTiefAusdruck Register.rax ZeugeTiefFrei = some prog :=
    ⟨_, zeuge_tief_senkung⟩
  have hT := istTief_von_senkTief ZeugeAbb ZeugeTiefAusdruck Register.rax ZeugeTiefFrei prog hsenk
  refine ⟨prog, hT, ?_⟩
  exact istTief_korrekt ZeugeAbb ZeugeTiefAusdruck Register.rax ZeugeTiefFrei prog hT
    ZeugeUmgebung ZeugeWelt ZeugeWelt ZeugeStart zeuge_tief_frisch (by decide) zeuge_umgebung

/-- Joint witness for `istTief_ohne_ueberlauf`: under `Bereich64`, the
    register holds the EXACT signed source value `40`, not only its
    modular reading. -/
theorem istTief_ohne_ueberlauf_zeuge :
    ∃ (prog : List Befehl) (hT : IstTief ZeugeAbb ZeugeTiefAusdruck Register.rax ZeugeTiefFrei prog) (s' : Zustand),
      lauf (prog.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ZeugeStart = some s' ∧
      sint (s'.register Register.rax) = 40 := by
  obtain ⟨prog, hsenk⟩ : ∃ prog, senkTief ZeugeAbb ZeugeTiefAusdruck Register.rax ZeugeTiefFrei = some prog :=
    ⟨_, zeuge_tief_senkung⟩
  have hT := istTief_von_senkTief ZeugeAbb ZeugeTiefAusdruck Register.rax ZeugeTiefFrei prog hsenk
  refine ⟨prog, hT, ?_⟩
  obtain ⟨s', hrun, hval, _, _, _⟩ :=
    istTief_ohne_ueberlauf ZeugeAbb ZeugeTiefAusdruck Register.rax ZeugeTiefFrei prog hT
      zeuge_tief_bereich ZeugeUmgebung ZeugeWelt ZeugeWelt ZeugeStart zeuge_tief_frisch (by decide)
      zeuge_umgebung
  refine ⟨s', hrun, ?_⟩
  rw [hval, zeuge_tief_auswertung]

/-- A direct, fully concrete check of the same run (no theorem applied):
    the seven-instruction program really does put `40` in `rax`. -/
theorem zeuge_tief_lauf :
    ∃ s', lauf (([Befehl.movReg64 Register.rax Register.r10, Befehl.movImm64 Register.r8 (intWort 12),
        Befehl.addReg64 Register.rax Register.r8, Befehl.movImm64 Register.rdx (intWort 5),
        Befehl.subReg64 Register.rax Register.rdx, Befehl.movImm64 Register.rcx (intWort 3),
        Befehl.addReg64 Register.rax Register.rcx]).map fun b => (⟨b, (encode b).length⟩ : Decodiert))
      ZeugeStart = some s' ∧ s'.register Register.rax = intWort 40 := by
  decide

/-! ## 2. A comparison, run both true and false. -/

/-- `x < 50`: true at `x = 30`. -/
def ZeugeVergleichWahr : Expr ZeugeD ZeugeCtx [] .bool := .lt (.var .hier) (.lit 50)

/-- `x < 20`: false at `x = 30`. -/
def ZeugeVergleichFalsch : Expr ZeugeD ZeugeCtx [] .bool := .lt (.var .hier) (.lit 20)

theorem zeuge_vergleich_wahr_senkung :
    senkVergleich ZeugeAbb ZeugeVergleichWahr Register.rax ZeugeTiefFrei =
      some ([Befehl.movReg64 Register.rax Register.r10, Befehl.movImm64 Register.rcx (intWort 50),
        Befehl.cmpReg64 Register.rax Register.rcx], Bedingung.l) := rfl

theorem zeuge_vergleich_falsch_senkung :
    senkVergleich ZeugeAbb ZeugeVergleichFalsch Register.rax ZeugeTiefFrei =
      some ([Befehl.movReg64 Register.rax Register.r10, Befehl.movImm64 Register.rcx (intWort 20),
        Befehl.cmpReg64 Register.rax Register.rcx], Bedingung.l) := rfl

theorem zeuge_vergleich_wahr_bereich : VergleichBereich ZeugeVergleichWahr := by
  show imBereich64 0 100 ∧ imBereich64 50 50 ∧ imBereich64 (0 - 50) (100 - 50)
  unfold imBereich64
  decide

theorem zeuge_vergleich_falsch_bereich : VergleichBereich ZeugeVergleichFalsch := by
  show imBereich64 0 100 ∧ imBereich64 20 20 ∧ imBereich64 (0 - 20) (100 - 20)
  unfold imBereich64
  decide

/-- Joint witness for `istVergleich_korrekt`, the TRUE side: `x < 50`
    lowers and runs, and the chosen condition code read off the
    resulting flags is `true`, matching the source comparison. -/
theorem istVergleich_korrekt_zeuge_wahr :
    ∃ (prog : List Befehl) (cond : Bedingung)
      (hT : IstVergleich ZeugeAbb ZeugeVergleichWahr Register.rax ZeugeTiefFrei prog cond) (s' : Zustand),
      lauf (prog.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ZeugeStart = some s' ∧
      bedingung cond s'.flags = true := by
  obtain ⟨prog, cond, hsenk⟩ :
      ∃ prog cond, senkVergleich ZeugeAbb ZeugeVergleichWahr Register.rax ZeugeTiefFrei =
        some (prog, cond) :=
    ⟨_, _, zeuge_vergleich_wahr_senkung⟩
  have hT := istVergleich_von_senkVergleich ZeugeAbb ZeugeVergleichWahr Register.rax ZeugeTiefFrei
    prog cond hsenk
  refine ⟨prog, cond, hT, ?_⟩
  obtain ⟨s', hrun, hval, _, _, _⟩ :=
    istVergleich_korrekt ZeugeAbb hT zeuge_vergleich_wahr_bereich
      ZeugeUmgebung ZeugeWelt ZeugeWelt ZeugeStart zeuge_tief_frisch (by decide) zeuge_umgebung
  refine ⟨s', hrun, ?_⟩
  rw [hval]
  rfl

/-- Joint witness for `istVergleich_korrekt`, the FALSE side: `x < 20`
    lowers and runs, and the chosen condition code is `false`. -/
theorem istVergleich_korrekt_zeuge_falsch :
    ∃ (prog : List Befehl) (cond : Bedingung)
      (hT : IstVergleich ZeugeAbb ZeugeVergleichFalsch Register.rax ZeugeTiefFrei prog cond) (s' : Zustand),
      lauf (prog.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ZeugeStart = some s' ∧
      bedingung cond s'.flags = false := by
  obtain ⟨prog, cond, hsenk⟩ :
      ∃ prog cond, senkVergleich ZeugeAbb ZeugeVergleichFalsch Register.rax ZeugeTiefFrei =
        some (prog, cond) :=
    ⟨_, _, zeuge_vergleich_falsch_senkung⟩
  have hT := istVergleich_von_senkVergleich ZeugeAbb ZeugeVergleichFalsch Register.rax ZeugeTiefFrei
    prog cond hsenk
  refine ⟨prog, cond, hT, ?_⟩
  obtain ⟨s', hrun, hval, _, _, _⟩ :=
    istVergleich_korrekt ZeugeAbb hT zeuge_vergleich_falsch_bereich
      ZeugeUmgebung ZeugeWelt ZeugeWelt ZeugeStart zeuge_tief_frisch (by decide) zeuge_umgebung
  refine ⟨s', hrun, ?_⟩
  rw [hval]
  rfl

/-! ## 3. Poison probes. -/

/-- PLANTED REFUSAL: register exhaustion at depth. The SAME depth-3
    expression as `zeuge_tief_senkung`, with only two scratch registers:
    the innermost `add` has none left once the two outer nodes have each
    peeled one, so the WHOLE lowering refuses -- depth, not just a single
    node, exhausts the stack. -/
theorem zeuge_tief_verweigert_erschoepft :
    senkTief ZeugeAbb ZeugeTiefAusdruck Register.rax [Register.rcx, Register.rdx] = none := rfl

/-- PLANTED REFUSAL: `mul` is outside the lowered fragment at any depth
    (already shown generically by `senkTief_verweigert_mul`; here with
    the witness variable as an operand). -/
theorem zeuge_verweigert_mul :
    senkTief ZeugeAbb (Expr.mul (D := ZeugeD) (Γ := ZeugeCtx) (Λ := []) (.var .hier) (.lit 2))
      Register.rax ZeugeTiefFrei = none := rfl

/-- PLANTED REFUSAL: `div` is outside the lowered fragment. -/
theorem zeuge_verweigert_div :
    senkTief ZeugeAbb
      (Expr.div (D := ZeugeD) (Γ := ZeugeCtx) (Λ := []) (by decide) (by decide)
        (Expr.lit 10) (Expr.lit 2))
      Register.rax ZeugeTiefFrei = none := rfl

/-- PLANTED REFUSAL: a table-field read (`slot`) is outside the lowered
    fragment (reusing the witness declaration's single table). -/
theorem zeuge_verweigert_slot :
    senkTief ZeugeAbb
      (Expr.slot (D := ZeugeD) (Γ := ZeugeCtx) (Λ := []) () ()
        (Expr.weiter (by decide) (by decide) (Expr.lit 0)) (fun w hw => nomatch hw))
      Register.rax ZeugeTiefFrei = none := rfl

/-- PLANTED REFUSAL: an out-of-range comparison. Both operands are
    individually inside the signed 64-bit window, but their DIFFERENCE
    is not (`2^62 - (-(2^62) - 100) = 2^63 + 100`): the decidable side
    condition `VergleichBereich` correctly refuses it, so
    `istVergleich_korrekt` cannot be invoked here. -/
theorem zeuge_verweigert_bereich :
    ¬ VergleichBereich (Expr.lt (D := ZeugeD) (Γ := ZeugeCtx) (Λ := [])
      (Expr.lit (2 ^ 62)) (Expr.lit (-(2 ^ 62) - 100))) := by
  show ¬ (imBereich64 (2 ^ 62) (2 ^ 62) ∧
    imBereich64 (-(2 ^ 62) - 100) (-(2 ^ 62) - 100) ∧
    imBereich64 (2 ^ 62 - (-(2 ^ 62) - 100)) (2 ^ 62 - (-(2 ^ 62) - 100)))
  unfold imBereich64
  decide

/-! ### Aliasing: `FrischListe` is load-bearing, not a convenience.

    Dropping it does not make `senkTief` refuse (it lowers just fine);
    it makes the lowering WRONG. The witness variable's register
    (`rdx`) is also the inner `add`'s own scratch register: by the time
    the variable is read, its register has already been overwritten by
    the left subtree's OWN computation. -/

/-- A register mapping that aliases the witness variable with a scratch
    register in `ZeugeTiefFrei` (an NON-fresh assignment, on purpose). -/
def ZeugeAbbAlias : ∀ (τ : Ty), Var ZeugeCtx τ → Register := fun _ _ => Register.rdx

/-- The aliased expression: `(1 + 2) + x` -- the left subtree `1 + 2` is
    itself a binary node that peels a scratch register before `x` is
    read on the right. -/
def ZeugeAliasAusdruck : Expr ZeugeD ZeugeCtx [] (.int 3 103) :=
  .add (.add (.lit 1) (.lit 2)) (.var .hier)

/-- `FrischListe` genuinely fails for this mapping: the witness
    variable's register (`rdx`) is itself in the scratch list. -/
theorem zeugeAlias_frischListe_verletzt :
    ¬ FrischListe ZeugeAbbAlias Register.rax [Register.rcx, Register.rdx] := by
  intro h
  exact (h.1 _ Var.hier).2 (by decide)

/-- A register file where `EnvRepr` still holds for this (non-fresh)
    mapping: `rdx` carries the witness variable's true value `30`. -/
def ZeugeRegAlias : Register → Wort := fun q => if q = Register.rdx then intWort 30 else 0

theorem zeugeAlias_envrepr : EnvRepr ZeugeUmgebung ZeugeRegAlias ZeugeAbbAlias := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

def ZeugeAliasStart : Zustand :=
  { register := ZeugeRegAlias, flags := witnessFlags, rip := BitVec.ofNat 64 0,
    speicher := ZeugeSpeicher }

/-- The aliased lowering (`senkTief` does NOT refuse -- it has no way to
    know the mapping is non-fresh). -/
theorem zeugeAlias_senkung :
    senkTief ZeugeAbbAlias ZeugeAliasAusdruck Register.rax [Register.rcx, Register.rdx] =
      some [Befehl.movImm64 Register.rax (intWort 1), Befehl.movImm64 Register.rdx (intWort 2),
        Befehl.addReg64 Register.rax Register.rdx, Befehl.movReg64 Register.rcx Register.rdx,
        Befehl.addReg64 Register.rax Register.rcx] := rfl

/-- The TRUE source value: `(1 + 2) + 30 = 33`. -/
theorem zeugeAlias_auswertung :
    (eval ZeugeWelt ZeugeAliasAusdruck ZeugeWelt ZeugeUmgebung).n = 33 := rfl

/-- POISON: with `EnvRepr` holding at the start but `FrischListe`
    violated, the lowered program runs (no refusal) but lands the WRONG
    value in `rax` -- the left subtree's own scratch write clobbers the
    variable's register before it is read on the right. This is exactly
    why `istTief_korrekt`/`istTief_ohne_ueberlauf` require `FrischListe`:
    without it, their conclusion is false, not merely unproved. -/
theorem zeugeAlias_korrektheit_bricht :
    ∃ s', lauf (([Befehl.movImm64 Register.rax (intWort 1), Befehl.movImm64 Register.rdx (intWort 2),
        Befehl.addReg64 Register.rax Register.rdx, Befehl.movReg64 Register.rcx Register.rdx,
        Befehl.addReg64 Register.rax Register.rcx]).map fun b => (⟨b, (encode b).length⟩ : Decodiert))
      ZeugeAliasStart = some s' ∧
      s'.register Register.rax ≠
        intWort (eval ZeugeWelt ZeugeAliasAusdruck ZeugeWelt ZeugeUmgebung).n := by
  decide

#print axioms istTief_korrekt_zeuge
#print axioms istTief_ohne_ueberlauf_zeuge
#print axioms istVergleich_korrekt_zeuge_wahr
#print axioms istVergleich_korrekt_zeuge_falsch
#print axioms zeuge_tief_lauf
#print axioms zeuge_tief_verweigert_erschoepft
#print axioms zeuge_verweigert_mul
#print axioms zeuge_verweigert_div
#print axioms zeuge_verweigert_slot
#print axioms zeuge_verweigert_bereich
#print axioms zeugeAlias_frischListe_verletzt
#print axioms zeugeAlias_korrektheit_bricht

/- CUTS:
   Proved here: a non-degenerate, jointly-instantiated witness for
   `istTief_korrekt`, `istTief_ohne_ueberlauf` and `istVergleich_korrekt`
   (depth-3 expression, a real `IstTief`/`IstVergleich` derivation,
   `FrischListe`, `EnvRepr`, and the actual run, all together, not just
   the conclusion alone); poison probes for register exhaustion AT DEPTH,
   `mul`/`div`/`slot` outside the fragment, an out-of-range comparison
   refused by the decidable `VergleichBereich`, and a register-aliasing
   probe that exhibits a WRONG lowered value (not just an unproved
   theorem) once `FrischListe` is dropped.
   NOT proved here: `le`/`eq` comparison run witnesses (the shape is
   identical to `lt`'s, proved in `ExpressionLoweringDeep.lean`'s own
   per-shape theorems, not re-witnessed per operator here); a poison
   probe for the register-stack `Nodup` clause specifically (the
   aliasing probe above already exercises the variable-disjointness
   clause of `FrischListe`, which is the one a real register allocator
   gets wrong first).
-/

end Gabbro.Grammatik.X86
