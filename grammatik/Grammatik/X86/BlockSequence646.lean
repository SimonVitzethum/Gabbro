/-
  File:      Grammatik/X86/BlockSequence646.lean
  Subject:   Direct typed two-assignment Block to fetched machine execution.

  Lane 646: extend the accepted single-assignment lowering
  (`SourceAssignmentLowering.senkAssign`, over `ExpressionLowering.senkFrag`
  and `SourceMemory.repOk`/`RepSlot`) to an ACTUAL typed source
  `Syntax.Block.cons` of TWO `Stmt.assignSlot` statements (no new list
  interpreter). The concatenated pilot sequence is generated from the
  syntax; finite target `lauf` execution and both source post-state
  representations are DERIVED, never assumed. Fetch stability of the code
  window across both data stores is derived from the accepted
  mapping/store frames (`CodeImmutability`, `ImageStoreFrame`), never from
  an assumed-unchanged premise. Full arbitrary-source closure stays OPEN.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.CodeImmutability
import Grammatik.X86.SourceMemory
import Grammatik.X86.ExpressionLowering
import Grammatik.X86.SourceAssignmentLowering
import Grammatik.X86.ImageStoreFrame

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Concatenated lowering of two admitted assignments: each value fragment
    lowered by `senkFrag` (599) followed by its slot store (628), each
    through its own dedicated base register at zero displacement. `none`
    is the explicit unsupported-expression refusal of either leg. -/
def senkSeq2 {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ1 τ2 : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e1 : Expr D Γ Λ τ1) (e2 : Expr D Γ Λ τ2)
    (dst tmp baseR1 baseR2 : Register) (disp1 disp2 : BitVec 32) :
    Option (List Befehl) :=
  match senkAssign abb e1 dst tmp baseR1 disp1,
        senkAssign abb e2 dst tmp baseR2 disp2 with
  | some p1, some p2 => some (p1 ++ p2)
  | _, _ => none

/-- Canonical bytes of a generated two-assignment sequence. -/
def seqBytes2 (prog : List Befehl) : List Byte :=
  (prog.map encode).flatten

/-- SHAPE: two successful assignment lowerings concatenate. -/
theorem senkSeq2_ok {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ1 τ2 : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e1 : Expr D Γ Λ τ1) (e2 : Expr D Γ Λ τ2)
    (dst tmp baseR1 baseR2 : Register) (disp1 disp2 : BitVec 32)
    (p1 p2 : List Befehl)
    (h1 : senkAssign abb e1 dst tmp baseR1 disp1 = some p1)
    (h2 : senkAssign abb e2 dst tmp baseR2 disp2 = some p2) :
    senkSeq2 abb e1 e2 dst tmp baseR1 baseR2 disp1 disp2 = some (p1 ++ p2) := by
  unfold senkSeq2
  rw [h1, h2]

/-- REFUSAL (first leg unsupported): a refused first assignment refuses
    the whole sequence, no partial bytes are generated. -/
theorem senkSeq2_verweigert_links {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ2 : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e2 : Expr D Γ Λ τ2)
    (dst tmp baseR1 baseR2 : Register) (disp1 disp2 : BitVec 32) :
    senkSeq2 abb
      (Expr.mul (Expr.lit (Γ := Γ) (Λ := Λ) 2) (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      e2 dst tmp baseR1 baseR2 disp1 disp2 = none := by
  unfold senkSeq2
  rw [senkAssign_verweigert_mul]

/-- REFUSAL (second leg unsupported): a refused second assignment refuses
    the whole sequence, even when the first leg lowers. -/
theorem senkSeq2_verweigert_rechts {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ1 : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e1 : Expr D Γ Λ τ1)
    (dst tmp baseR1 baseR2 : Register) (disp1 disp2 : BitVec 32) :
    senkSeq2 abb e1
      (Expr.mul (Expr.lit (Γ := Γ) (Λ := Λ) 2) (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst tmp baseR1 baseR2 disp1 disp2 = none := by
  unfold senkSeq2
  rw [senkAssign_verweigert_mul]
  cases senkAssign abb e1 dst tmp baseR1 disp1 <;> rfl

/-! ## 2. Source composition shape: two `assignSlot` as an actual `Block`.

    `Block.cons s1 (Block.cons s2 Block.nil)` with both statements
    preserving `Λ` is the two-assignment fragment. Only `.ok` chains are
    covered: any other source outcome short-circuits `execBlock` and no
    `.ok` conclusion is claimed for it (see the `uebergang` probe below). -/

/-- SOURCE CHAIN (`.ok` only): two chained `.ok` statement steps give the
    `.ok` block run over the actual `Block.cons` term. -/
theorem seq2_execBlock {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s1 s2 : Stmt D V l Γ Λ Λ)
    (σ σ' σ'' : World D) (ρ : Env D Γ)
    (h1 : execStmt O passes R s1 σ ρ = .ok σ' ρ)
    (h2 : execStmt O passes R s2 σ' ρ = .ok σ'' ρ) :
    execBlock O passes R (Block.cons s1 (Block.cons s2 Block.nil)) σ ρ =
      .ok σ'' ρ := by
  simp only [execBlock, h1, h2]

/-! ## 3. Main connection: generated two-store sequence.

    Supported fragment (explicit): two `Stmt.assignSlot` on one table,
    distinct fields, same row, each value in the `senkFrag` fragment
    (lit/var/one add/sub over atoms), each slot admitted by `repOk`
    (nonnegative range below `2 ^ 64`, width, region), zero displacement
    with one dedicated base register per slot.
    Register conditions: `Frisch` (no source variable in `dst`/`tmp`,
    `dst ≠ tmp`), neither working register is `rsp`, each base register
    differs from both working registers (else the expression run or the
    store clobbers the slot address).
    Target separation: `Disjunkt a1 a2` (the second word write must not
    cover the first slot) and `f1 ≠ f2` with `k1 = k2` on the source side.
    Map checks (code/data/no-wrap) belong to §4; the `lauf` run, both
    `RepSlot` facts with read-back, and the source `.ok` block equation
    are DERIVED here, never assumed. -/

/-- MAIN: two admitted assignments as one actual `Block` lower to the
    concatenated pilot sequence, and the finite target `lauf` run agrees
    with the source post-state on both slots, each with read-back. Every
    premise is used: `hOk` admits range/width/region, `hLese`/`hk`/`heval`
    name the evaluated index and value, `hExec` is the source step,
    `hsenk`/`hrenv`/`hFr`/`hrsp` drive the expression runs,
    `hBasis`/`hBaseR`/`hdisp`-free zero form/`ha` fix the slot addresses,
    `hTgt`/`hRd` give the target writes with read permission, `hDis`
    with `hk12`/`hf12` carries the first slot across the second write. -/
theorem seq2_korrekt {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (t : D.Tab) (f1 f2 : D.Feld t)
    (lo1 hi1 lo2 hi2 : Int)
    (hT1 : D.typ t f1 = .int lo1 hi1) (hT2 : D.typ t f2 = .int lo2 hi2)
    (base len off1 off2 : Nat)
    (hOk1 : repOk (D.typ t f1) base len off1 = true)
    (hOk2 : repOk (D.typ t f2) base len off2 = true)
    (i1 : Expr D Γ Λ (.index (D.count t)))
    (e1 : Expr D Γ Λ (.int lo1 hi1))
    (hw1 : V.schreibt t = true) (hL1 : darf D t Λ)
    (i2 : Expr D Γ Λ (.index (D.count t)))
    (e2 : Expr D Γ Λ (.int lo2 hi2))
    (hw2 : V.schreibt t = true) (hL2 : darf D t Λ)
    (σ : World D) (ρ : Env D Γ)
    (σL1 : World D)
    (hLese1 : σL1 = σ.lese Λ (i1.orte ++
      (cast (congrArg (Expr D Γ Λ) hT1.symm) e1).orte))
    (k1 : Int) (v1 : Zahl lo1 hi1)
    (hk1 : (eval σL1 i1 σL1 ρ).n = k1)
    (heval1 : (eval σL1 e1 σL1 ρ).n = v1.n)
    (σ' : World D)
    (hExec1 : execStmt O passes R
      (Stmt.assignSlot (l := l) t f1 i1
        (cast (congrArg (Expr D Γ Λ) hT1.symm) e1) hw1 hL1) σ ρ =
      .ok σ' ρ)
    (σL2 : World D)
    (hLese2 : σL2 = σ'.lese Λ (i2.orte ++
      (cast (congrArg (Expr D Γ Λ) hT2.symm) e2).orte))
    (k2 : Int) (v2 : Zahl lo2 hi2)
    (hk2 : (eval σL2 i2 σL2 ρ).n = k2)
    (heval2 : (eval σL2 e2 σL2 ρ).n = v2.n)
    (hk12 : k1 = k2) (hf12 : f1 ≠ f2)
    (σ'' : World D)
    (hExec2 : execStmt O passes R
      (Stmt.assignSlot (l := l) t f2 i2
        (cast (congrArg (Expr D Γ Λ) hT2.symm) e2) hw2 hL2) σ' ρ =
      .ok σ'' ρ)
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp baseR1 baseR2 : Register)
    (hFr : Frisch abb dst tmp)
    (hrsp : dst ≠ Register.rsp ∧ tmp ≠ Register.rsp)
    (hBasis1 : baseR1 ≠ dst ∧ baseR1 ≠ tmp)
    (hBasis2 : baseR2 ≠ dst ∧ baseR2 ≠ tmp)
    (s : Zustand) (m m1 m'' : Speicher)
    (hsMem : s.speicher = m)
    (hBaseR1 : s.register baseR1 = slotAddr base off1)
    (hBaseR2 : s.register baseR2 = slotAddr base off2)
    (a1 a2 : Adresse)
    (ha1 : a1 = slotAddr base off1) (ha2 : a2 = slotAddr base off2)
    (hTgt1 : write64 m a1 (zahlWort v1) = some m1)
    (hTgt2 : write64 m1 a2 (zahlWort v2) = some m'')
    (hRd1 : lesbar8 m a1 = true) (hRd2 : lesbar8 m1 a2 = true)
    (hDis : Disjunkt a1 a2)
    (prog1 prog2 : List Befehl)
    (hsenk1 : senkFrag abb e1 dst tmp = some prog1)
    (hsenk2 : senkFrag abb e2 dst tmp = some prog2)
    (hrenv : EnvRepr ρ s.register abb) :
    ∃ s'' : Zustand,
      lauf ((((prog1 ++ [Befehl.store64 baseR1 dst (BitVec.ofNat 32 0)]) ++
        (prog2 ++ [Befehl.store64 baseR2 dst (BitVec.ofNat 32 0)])).map
        fun b => (⟨b, (encode b).length⟩ : Decodiert))) s = some s'' ∧
      s''.register dst = intWort (eval σL2 e2 σL2 ρ).n ∧
      s''.speicher = m'' ∧
      RepSlot t k1 f1 lo1 hi1 hT1 a1 m'' σ'' ∧
      RepSlot t k2 f2 lo2 hi2 hT2 a2 m'' σ'' ∧
      (∃ w, read64 m'' a1 = some w ∧ wortZahl lo1 hi1 w = some v1) ∧
      (∃ w, read64 m'' a2 = some w ∧ wortZahl lo2 hi2 w = some v2) ∧
      execBlock O passes R
        (Block.cons
          (Stmt.assignSlot (l := l) t f1 i1
            (cast (congrArg (Expr D Γ Λ) hT1.symm) e1) hw1 hL1)
          (Block.cons
            (Stmt.assignSlot (l := l) t f2 i2
              (cast (congrArg (Expr D Γ Λ) hT2.symm) e2) hw2 hL2)
            Block.nil)) σ ρ = .ok σ'' ρ := by
  have hOkI1 : repOk (.int lo1 hi1) base len off1 = true := hT1 ▸ hOk1
  have hOkI2 : repOk (.int lo2 hi2) base len off2 = true := hT2 ▸ hOk2
  obtain ⟨hLo1, hHi1, -, -⟩ := repOk_klingt hOkI1
  obtain ⟨hLo2, hHi2, -, -⟩ := repOk_klingt hOkI2
  -- 1. First expression run (derived value, kept memory, kept registers).
  obtain ⟨mid1, hrunE1, hvalE1, hmemE1, hregsE1, _⟩ :=
    senkung_korrekt abb e1 dst tmp ρ σL1 σL1 s hFr hrsp hrenv prog1 hsenk1
  have hrenvMid1 : EnvRepr ρ mid1.register abb := by
    intro lo hi x
    have h1 := hFr.1 _ x
    rw [hregsE1 _ h1.1 h1.2]
    exact hrenv lo hi x
  have hbase1Mid1 : mid1.register baseR1 = slotAddr base off1 := by
    rw [hregsE1 baseR1 hBasis1.1 hBasis1.2, hBaseR1]
  have hbase2Mid1 : mid1.register baseR2 = slotAddr base off2 := by
    rw [hregsE1 baseR2 hBasis2.1 hBasis2.2, hBaseR2]
  have heff1 : effAddr mid1 baseR1 (BitVec.ofNat 32 0) = a1 := by
    rw [effAddr_null, hbase1Mid1, ha1]
  have hword1 : mid1.register dst = zahlWort v1 := by
    rw [hvalE1, heval1]
    exact intWort_zahlWort v1 hLo1 hHi1
  -- 2. First store step (registers kept by the record update).
  have hwr1 : write64 mid1.speicher (effAddr mid1 baseR1 (BitVec.ofNat 32 0))
      (mid1.register dst) = some m1 := by
    rw [hmemE1, hsMem, heff1, hword1]
    exact hTgt1
  have hlen1 : laengeOk
      (encode (Befehl.store64 baseR1 dst (BitVec.ofNat 32 0))).length = true :=
    laengeOk_encode _
  have hstore1 : schritt (⟨Befehl.store64 baseR1 dst (BitVec.ofNat 32 0), (encode (Befehl.store64 baseR1 dst (BitVec.ofNat 32 0))).length⟩ : Decodiert) mid1 = some ({ mid1 with speicher := m1, rip := ripNach mid1.rip (encode (Befehl.store64 baseR1 dst (BitVec.ofNat 32 0))).length }) :=
    schritt_store64_erfolg _ mid1 baseR1 dst _ m1 hlen1 rfl hwr1
  have hmapA : ((prog1 ++
      [Befehl.store64 baseR1 dst (BitVec.ofNat 32 0)]).map
      fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
      (prog1.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
      [⟨Befehl.store64 baseR1 dst (BitVec.ofNat 32 0),
        (encode (Befehl.store64 baseR1 dst (BitVec.ofNat 32 0))).length⟩] := by
    simp [List.map_append]
  have hrunA : ∃ s1' : Zustand,
      lauf ((prog1 ++ [Befehl.store64 baseR1 dst (BitVec.ofNat 32 0)]).map
        fun b => (⟨b, (encode b).length⟩ : Decodiert)) s = some s1' ∧
      s1'.speicher = m1 ∧
      EnvRepr ρ s1'.register abb ∧
      s1'.register baseR2 = slotAddr base off2 := by
    refine ⟨({ mid1 with speicher := m1, rip := ripNach mid1.rip (encode (Befehl.store64 baseR1 dst (BitVec.ofNat 32 0))).length }), ?_, ?_, ?_, ?_⟩
    · rw [hmapA, lauf_anhang _ _ _ _ hrunE1, lauf_einzeln_gleich]
      exact hstore1
    · rfl
    · intro lo hi x
      exact hrenvMid1 lo hi x
    · exact hbase2Mid1
  obtain ⟨s1', hrunA', hmemS1, hrenvS1, hbase2S1⟩ := hrunA
  -- 3. Second expression run from the post-store state.
  obtain ⟨mid2, hrunE2, hvalE2, hmemE2, hregsE2, _⟩ :=
    senkung_korrekt abb e2 dst tmp ρ σL2 σL2 s1' hFr hrsp hrenvS1 prog2 hsenk2
  have hbase2Mid2 : mid2.register baseR2 = slotAddr base off2 := by
    rw [hregsE2 baseR2 hBasis2.1 hBasis2.2]
    exact hbase2S1
  have heff2 : effAddr mid2 baseR2 (BitVec.ofNat 32 0) = a2 := by
    rw [effAddr_null, hbase2Mid2, ha2]
  have hword2 : mid2.register dst = zahlWort v2 := by
    rw [hvalE2, heval2]
    exact intWort_zahlWort v2 hLo2 hHi2
  -- 4. Second store step.
  have hwr2 : write64 mid2.speicher (effAddr mid2 baseR2 (BitVec.ofNat 32 0))
      (mid2.register dst) = some m'' := by
    have e : mid2.speicher = m1 := hmemE2.trans hmemS1
    rw [e, heff2, hword2]
    exact hTgt2
  have hlen2 : laengeOk
      (encode (Befehl.store64 baseR2 dst (BitVec.ofNat 32 0))).length = true :=
    laengeOk_encode _
  have hstore2 : schritt (⟨Befehl.store64 baseR2 dst (BitVec.ofNat 32 0), (encode (Befehl.store64 baseR2 dst (BitVec.ofNat 32 0))).length⟩ : Decodiert) mid2 = some ({ mid2 with speicher := m'', rip := ripNach mid2.rip (encode (Befehl.store64 baseR2 dst (BitVec.ofNat 32 0))).length }) :=
    schritt_store64_erfolg _ mid2 baseR2 dst _ m'' hlen2 rfl hwr2
  have hmapB : ((prog2 ++
      [Befehl.store64 baseR2 dst (BitVec.ofNat 32 0)]).map
      fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
      (prog2.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
      [⟨Befehl.store64 baseR2 dst (BitVec.ofNat 32 0),
        (encode (Befehl.store64 baseR2 dst (BitVec.ofNat 32 0))).length⟩] := by
    simp [List.map_append]
  have hrunB : ∃ s2' : Zustand,
      lauf ((prog2 ++ [Befehl.store64 baseR2 dst (BitVec.ofNat 32 0)]).map
        fun b => (⟨b, (encode b).length⟩ : Decodiert)) s1' = some s2' ∧
      s2'.speicher = m'' ∧
      s2'.register dst = intWort (eval σL2 e2 σL2 ρ).n := by
    refine ⟨({ mid2 with speicher := m'', rip := ripNach mid2.rip (encode (Befehl.store64 baseR2 dst (BitVec.ofNat 32 0))).length }), ?_, ?_, ?_⟩
    · rw [hmapB, lauf_anhang _ _ _ _ hrunE2, lauf_einzeln_gleich]
      exact hstore2
    · rfl
    · exact hvalE2
  obtain ⟨s2', hrunB', hmemS2, hvalDst⟩ := hrunB
  -- 5. The two generated runs compose over the concatenated sequence.
  have hmap : ((((prog1 ++ [Befehl.store64 baseR1 dst (BitVec.ofNat 32 0)]) ++
      (prog2 ++ [Befehl.store64 baseR2 dst (BitVec.ofNat 32 0)])).map
      fun b => (⟨b, (encode b).length⟩ : Decodiert))) =
      ((prog1 ++ [Befehl.store64 baseR1 dst (BitVec.ofNat 32 0)]).map
        fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
      ((prog2 ++ [Befehl.store64 baseR2 dst (BitVec.ofNat 32 0)]).map
        fun b => (⟨b, (encode b).length⟩ : Decodiert)) := by
    simp [List.map_append]
  have hrun : lauf ((((prog1 ++ [Befehl.store64 baseR1 dst (BitVec.ofNat 32 0)]) ++
      (prog2 ++ [Befehl.store64 baseR2 dst (BitVec.ofNat 32 0)])).map
      fun b => (⟨b, (encode b).length⟩ : Decodiert))) s = some s2' := by
    rw [hmap, lauf_anhang _ _ _ _ hrunA']
    exact hrunB'
  -- 6. Value links the source side consumes (transport, then name).
  have e1val : eval σL1 (cast (congrArg (Expr D Γ Λ) hT1.symm) e1) σL1 ρ =
      cast (congrArg (Wert D) hT1.symm) (eval σL1 e1 σL1 ρ) :=
    evalTrans σL1 hT1.symm e1 σL1 ρ
  have hcancel1 := paarCancel (D := D) (g := hT1) (eval σL1 e1 σL1 ρ)
  have hve1 : eval σL1 e1 σL1 ρ = v1 := by
    revert heval1
    obtain ⟨n, hlo, hhi⟩ := eval σL1 e1 σL1 ρ
    obtain ⟨m, glo, ghi⟩ := v1
    intro heval1
    have hnm : n = m := heval1
    subst hnm
    rfl
  have hv1 : (cast (congrArg (Wert D) hT1)
      (eval σL1 (cast (congrArg (Expr D Γ Λ) hT1.symm) e1) σL1 ρ) :
      Wert D (.int lo1 hi1)) = v1 := by
    rw [e1val, hcancel1]
    exact hve1
  have e2val : eval σL2 (cast (congrArg (Expr D Γ Λ) hT2.symm) e2) σL2 ρ =
      cast (congrArg (Wert D) hT2.symm) (eval σL2 e2 σL2 ρ) :=
    evalTrans σL2 hT2.symm e2 σL2 ρ
  have hcancel2 := paarCancel (D := D) (g := hT2) (eval σL2 e2 σL2 ρ)
  have hve2 : eval σL2 e2 σL2 ρ = v2 := by
    revert heval2
    obtain ⟨n, hlo, hhi⟩ := eval σL2 e2 σL2 ρ
    obtain ⟨m, glo, ghi⟩ := v2
    intro heval2
    have hnm : n = m := heval2
    subst hnm
    rfl
  have hv2 : (cast (congrArg (Wert D) hT2)
      (eval σL2 (cast (congrArg (Expr D Γ Λ) hT2.symm) e2) σL2 ρ) :
      Wert D (.int lo2 hi2)) = v2 := by
    rw [e2val, hcancel2]
    exact hve2
  -- 7. Both source world updates match (accepted 570 step, twice).
  have hRep1 := rep_schritt_bleibt O passes R t f1 lo1 hi1 hT1 base len off1
    hOk1 i1 (cast (congrArg (Expr D Γ Λ) hT1.symm) e1) hw1 hL1 σ ρ σL1
    hLese1 k1 v1 hk1 hv1 a1 m m1 σ' ρ hExec1 hTgt1 hRd1
  have hRep2 := rep_schritt_bleibt O passes R t f2 lo2 hi2 hT2 base len off2
    hOk2 i2 (cast (congrArg (Expr D Γ Λ) hT2.symm) e2) hw2 hL2 σ' ρ σL2
    hLese2 k2 v2 hk2 hv2 a2 m1 m'' σ'' ρ hExec2 hTgt2 hRd2
  -- 8. The source `.ok` block equation over the actual `Block` term.
  have hexec : execBlock O passes R
      (Block.cons
        (Stmt.assignSlot (l := l) t f1 i1
          (cast (congrArg (Expr D Γ Λ) hT1.symm) e1) hw1 hL1)
        (Block.cons
          (Stmt.assignSlot (l := l) t f2 i2
            (cast (congrArg (Expr D Γ Λ) hT2.symm) e2) hw2 hL2)
          Block.nil)) σ ρ = .ok σ'' ρ := by
    simp only [execBlock, hExec1, hExec2]
  -- 9. The first slot survives the second write (same row, other field,
  --    disjoint footprints): `lese` keeps slots, then the 570 frame.
  have hU2 : execStmt O passes R
      (Stmt.assignSlot (l := l) t f2 i2
        (cast (congrArg (Expr D Γ Λ) hT2.symm) e2) hw2 hL2) σ' ρ =
      .ok (σL2.schreibSlot t Λ (eval σL2 i2 σL2 ρ).n f2
        (eval σL2 (cast (congrArg (Expr D Γ Λ) hT2.symm) e2) σL2 ρ)) ρ := by
    have e : σ'.lese Λ (i2.orte ++
        (cast (congrArg (Expr D Γ Λ) hT2.symm) e2).orte) = σL2 := hLese2.symm
    simp only [execStmt, e, hk2]
  have hSrc2 : σ'' = σL2.schreibSlot t Λ k2 f2
      (eval σL2 (cast (congrArg (Expr D Γ Λ) hT2.symm) e2) σL2 ρ) := by
    rw [hU2] at hExec2
    cases hExec2
    rw [hk2]
  have hslots : ∀ (t' : D.Tab) (k' : Int) (f' : D.Feld t'),
      σL2.slots t' k' f' = σ'.slots t' k' f' := by
    intro t' k' f'
    rw [hLese2]
    rfl
  have hRep1L2 : RepSlot t k1 f1 lo1 hi1 hT1 a1 m1 σL2 := by
    have h := hRep1.1
    unfold RepSlot at h ⊢
    rw [hslots t k1 f1]
    exact h
  have hRep1fin : RepSlot t k1 f1 lo1 hi1 hT1 a1 m'' σ'' :=
    rep_fremd_feld σL2 t Λ k2 f2
      (eval σL2 (cast (congrArg (Expr D Γ Λ) hT2.symm) e2) σL2 ρ)
      k1 f1 lo1 hi1 hT1 hk12 hf12 σ'' hSrc2 a2 a1 m1 m'' (zahlWort v2)
      hRep1L2 hTgt2 (Disjunkt_symm a1 a2 hDis)
  have hread1 : ∃ w, read64 m'' a1 = some w ∧ wortZahl lo1 hi1 w = some v1 := by
    obtain ⟨w1, hrd1', hwz1⟩ := hRep1.2
    refine ⟨w1, ?_, hwz1⟩
    rw [read64_rahmen m1 m'' a2 a1 (zahlWort v2) hTgt2
      (Disjunkt_symm a1 a2 hDis)]
    exact hrd1'
  refine ⟨s2', hrun, hvalDst, hmemS2, hRep1fin, hRep2.1, hread1, hRep2.2, hexec⟩

/-! ## 4. Joint witness: one table, two fields, two memory-changing stores.

    One table with two `.int` fields (`false : 12 .. 112`,
    `true : 13 .. 113`), one parameterless function whose contract writes
    it, one integer variable `x = 30`. The actual source block writes
    `x + 12 = 42` to the first field and `x + 13 = 43` to the second
    (row 0): two reached source steps, each changing its slot. The target
    writes the two representation words to two disjoint 8-byte footprints
    in loaded image memory, changing at least two data bytes per slot.
    Fetched-byte execution (`laufBytes`) runs the generated bytes; forged
    bytes, aliasing footprints and unsupported expressions are refused. -/

/-- Witness signature: parameterless, no answer, writes the table. -/
def witSig646 : Signatur Unit Empty Empty Empty :=
  { params := [], erg := none, gruende := 0, haelt := [],
    schreibt := fun _ => true, gschreibt := fun g => (nomatch g),
    konsumiert := [], produziert := [], boden := none }

/-- Witness declaration: one table with two `.int` fields, one
    parameterless function whose contract writes it, nothing else. -/
def witD646 : Deklaration where
  Tab := Unit
  count := fun _ => 1
  Feld := fun _ => Bool
  typ := fun _ f => match f with
    | false => .int 12 112
    | true => .int 13 113
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => false
  ggeteilt := fun g => nomatch g
  Lock := Empty
  rang := fun L => nomatch L
  maskiert := fun L => nomatch L
  Marke := Empty
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => witSig646
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The witness contract: writes the table. -/
def witV646 : Vertrag witD646 :=
  { schreibt := fun _ => true
    gschreibt := fun g => nomatch g
    erg := none
    gruende := 0
    haelt := []
    produziert := []
    boden := none }

/-- The witness oracle: no axioms, registers or globals to answer. -/
def witO646 : Orakel witD646 where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- The witness callee table: every call succeeds without moving memory. -/
def witR646 : ∀ f : witD646.Fn, World witD646 →
    Env witD646 (witD646.params f) → RufAusgang f :=
  fun _ σ _ => .ok σ ()

/-- Witness context: one integer variable in `0 .. 100`. -/
def witCtx646 : Ctx := [.int 0 100]

/-- The witness indices: row 0 for both statements. -/
def witI646 : Expr witD646 witCtx646 [] (.index (witD646.count ())) :=
  Expr.lit 0

/-- First value: `x + 12` with `x = 30`, hence `42` in `12 .. 112`.
    The computed range is definitionally the first field type. -/
def witE1646 : Expr witD646 witCtx646 [] (.int 12 112) :=
  .add (.var .hier) (.lit 12)

/-- Second value: `x + 13` with `x = 30`, hence `43` in `13 .. 113`.
    The computed range is definitionally the second field type. -/
def witE2646 : Expr witD646 witCtx646 [] (.int 13 113) :=
  .add (.var .hier) (.lit 13)

/-- Witness environment: `x = 30`. -/
def witEnv646 : Env witD646 witCtx646 :=
  .cons ⟨30, by decide, by decide⟩ .nil

/-- The witness world: the slots hold 12 and 13, no trace yet. -/
def witSigma646 : World witD646 where
  slots := fun t _ f => by
    cases t
    cases f
    · exact ⟨12, by decide, by decide⟩
    · exact ⟨13, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

/-- The witness field types. -/
theorem witHT1646 : witD646.typ () false = .int 12 112 := rfl

theorem witHT2646 : witD646.typ () true = .int 13 113 := rfl

/-- The witness contract writes the table (both statements). -/
theorem witHw1646 : witV646.schreibt () = true := rfl

theorem witHw2646 : witV646.schreibt () = true := rfl

/-- The witness table needs no guards. -/
theorem witHL646 : darf witD646 () [] :=
  fun _ h => False.elim (List.not_mem_nil h)

/-- The witness values at the target: 42 and 43. -/
def witVal1646 : Zahl 12 112 := ⟨42, by decide, by decide⟩

def witVal2646 : Zahl 13 113 := ⟨43, by decide, by decide⟩

/-- The read worlds of the two witness runs (transported value places). -/
def witSL1646 : World witD646 :=
  witSigma646.lese []
    (witI646.orte ++
      (cast (congrArg (Expr witD646 witCtx646 []) witHT1646.symm)
        witE1646).orte)

/-- The witness index evaluates to row 0 (first leg). -/
theorem witHk1646 :
    (eval witSL1646 witI646 witSL1646 witEnv646).n = 0 :=
  rfl

/-- The first value evaluates to 42 in the single source model. -/
theorem witHeval1646 :
    (eval witSL1646 witE1646 witSL1646 witEnv646).n = witVal1646.n :=
  rfl

/-- Admission holds on both witness layouts (base `0x102000`, 16 bytes). -/
theorem witOk1646 : repOk (witD646.typ () false) 0x102000 16 0 = true := by
  rw [witHT1646]
  decide

theorem witOk2646 : repOk (witD646.typ () true) 0x102000 16 8 = true := by
  rw [witHT2646]
  decide

/-- Second-leg read world over any pre-world (evaluation of the pure
    value/index expressions never inspects the world). -/
def witSL2646 (σ : World witD646) : World witD646 :=
  σ.lese []
    (witI646.orte ++
      (cast (congrArg (Expr witD646 witCtx646 []) witHT2646.symm)
        witE2646).orte)

/-- The witness index evaluates to row 0 (second leg, any pre-world). -/
theorem witHk2646 (σ : World witD646) :
    (eval (witSL2646 σ) witI646 (witSL2646 σ) witEnv646).n = 0 :=
  rfl

/-- The second value evaluates to 43 (any pre-world). -/
theorem witHeval2646 (σ : World witD646) :
    (eval (witSL2646 σ) witE2646 (witSL2646 σ) witEnv646).n =
      witVal2646.n :=
  rfl

/-! ## 5. Witness target side: registers, generated bytes, loaded image.

    Two dedicated base registers (`rbx` for slot one at `0x102000`,
    `r12` for slot two at `0x102008`); the source variable lives in
    `r10`, the working registers are `rax`/`rcx`. The generated eight
    instructions live as file bytes of the executable code section of a
    checked image (`wohlgeformt .p48` decided); both data slots sit in
    its writable data section. -/

/-- Witness register assignment: the source variable lives in `r10`. -/
def witAbb646 : ∀ (τ : Ty), Var witCtx646 τ → Register :=
  fun _ _ => .r10

/-- Witness register file: `r10` holds the source value 30, `rbx` the
    first slot base `0x102000`, `r12` the second slot base `0x102008`,
    everything else zero. -/
def witReg646 : Register → Wort :=
  fun q => if q = Register.r10 then intWort 30
    else if q = Register.rbx then natAdresse 0x102000
    else if q = Register.r12 then natAdresse 0x102008
    else BitVec.ofNat 64 0

/-- Register freshness holds: no variable lives in `rax`/`rcx`. -/
theorem witFrisch646 : Frisch witAbb646 Register.rax Register.rcx := by
  refine ⟨fun τ x => ⟨?_, ?_⟩, by decide⟩
  · show Register.r10 ≠ Register.rax
    decide
  · show Register.r10 ≠ Register.rcx
    decide

/-- Neither working register is the stack pointer. -/
theorem witHRsp646 :
    Register.rax ≠ Register.rsp ∧ Register.rcx ≠ Register.rsp :=
  ⟨by decide, by decide⟩

/-- Both slot base registers differ from both working registers. -/
theorem witHBasis1646 :
    Register.rbx ≠ Register.rax ∧ Register.rbx ≠ Register.rcx :=
  ⟨by decide, by decide⟩

theorem witHBasis2646 :
    Register.r12 ≠ Register.rax ∧ Register.r12 ≠ Register.rcx :=
  ⟨by decide, by decide⟩

/-- The base registers hold the admitted slot addresses. -/
theorem witHBaseR1646 :
    witReg646 Register.rbx = slotAddr 0x102000 0 := by
  decide

theorem witHBaseR2646 :
    witReg646 Register.r12 = slotAddr 0x102000 8 := by
  decide

/-- Environment representation holds on the witness registers. -/
theorem witUmgebung646 :
    EnvRepr witEnv646 witReg646 witAbb646 := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

/-- The generated witness program: two lowered additions plus stores. -/
def witProg646 : List Befehl :=
  [Befehl.movReg64 Register.rax Register.r10,
   Befehl.movImm64 Register.rcx (intWort 12),
   Befehl.addReg64 Register.rax Register.rcx,
   Befehl.store64 Register.rbx Register.rax (BitVec.ofNat 32 0),
   Befehl.movReg64 Register.rax Register.r10,
   Befehl.movImm64 Register.rcx (intWort 13),
   Befehl.addReg64 Register.rax Register.rcx,
   Befehl.store64 Register.r12 Register.rax (BitVec.ofNat 32 0)]

/-- Witness program bytes from the canonical encodings. -/
def witBytes646 : List Byte := (witProg646.map encode).flatten

/-- The two value fragments lower to the expected pilot prefix/suffix. -/
theorem witSenk1646 :
    senkFrag witAbb646 witE1646 Register.rax Register.rcx =
      some [Befehl.movReg64 Register.rax Register.r10,
        Befehl.movImm64 Register.rcx (intWort 12),
        Befehl.addReg64 Register.rax Register.rcx] := rfl

theorem witSenk2646 :
    senkFrag witAbb646 witE2646 Register.rax Register.rcx =
      some [Befehl.movReg64 Register.rax Register.r10,
        Befehl.movImm64 Register.rcx (intWort 13),
        Befehl.addReg64 Register.rax Register.rcx] := rfl

/-- Each witness assignment lowers to its four-instruction leg. -/
theorem witSenkAssign1646 :
    senkAssign witAbb646 witE1646 Register.rax Register.rcx
      Register.rbx (BitVec.ofNat 32 0) =
      some [Befehl.movReg64 Register.rax Register.r10,
        Befehl.movImm64 Register.rcx (intWort 12),
        Befehl.addReg64 Register.rax Register.rcx,
        Befehl.store64 Register.rbx Register.rax (BitVec.ofNat 32 0)] :=
  senkAssign_ok witAbb646 witE1646 _ _ _ _ _ witSenk1646

theorem witSenkAssign2646 :
    senkAssign witAbb646 witE2646 Register.rax Register.rcx
      Register.r12 (BitVec.ofNat 32 0) =
      some [Befehl.movReg64 Register.rax Register.r10,
        Befehl.movImm64 Register.rcx (intWort 13),
        Befehl.addReg64 Register.rax Register.rcx,
        Befehl.store64 Register.r12 Register.rax (BitVec.ofNat 32 0)] :=
  senkAssign_ok witAbb646 witE2646 _ _ _ _ _ witSenk2646

/-- The full sequence lowering is exactly the witness program. -/
theorem witSenkSeq646 :
    senkSeq2 witAbb646 witE1646 witE2646 Register.rax Register.rcx
      Register.rbx Register.r12 (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) =
      some witProg646 := by
  unfold senkSeq2
  rw [witSenkAssign1646, witSenkAssign2646]
  rfl

/-- Witness file: generated program bytes then sixteen zero data bytes. -/
def witDatei646 : List Byte :=
  witBytes646 ++ List.replicate 16 (BitVec.ofNat 8 0)

/-- Witness code section: generated bytes, executable, never writable. -/
def witCode646 : Abschnitt :=
  { dateiOff := 0, dateiLen := witBytes646.length, vaddr := 0x1000,
    memLen := witBytes646.length, lesbar := false, schreibbar := false,
    ausfuehrbar := true, ausr := 4096 }

/-- Witness data section: sixteen writable bytes, never executable. -/
def witDaten646 : Abschnitt :=
  { dateiOff := witBytes646.length, dateiLen := 16, vaddr := 0x2000,
    memLen := 16, lesbar := true, schreibbar := true, ausfuehrbar := false,
    ausr := 4096 }

/-- Witness image: code plus data under checked base `0x100000`; the entry
    names the loaded sum, never base plus offset. -/
def witBild646 : Bild :=
  { datei := witDatei646
    abschnitte := [witCode646, witDaten646]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- ACCEPTANCE: the witness image validates under profile 48. -/
theorem witBild646_wohlgeformt :
    wohlgeformt .p48 witBild646 = true := by
  decide

/-- The witness code section is code-shaped. -/
theorem witCode646_code : istCodeAbschnitt witCode646 = true := by
  decide

/-- The witness data section is data-shaped. -/
theorem witDaten646_daten : istDatenAbschnitt witDaten646 = true := by
  decide

/-- The witness mapped virtual intervals are pairwise disjoint. -/
theorem witPaar646 :
    paarweise (virtReich 0x100000) witBild646.abschnitte = true := by
  decide

/-- The witness code and data regions differ as checked regions. -/
theorem witRegUngleich646 :
    abschnittAlsRegion 0x100000 witCode646 ≠
      abschnittAlsRegion 0x100000 witDaten646 := by
  decide

/-- Witness start state: loaded image, `rip` at the biased entry. -/
def witStart646 : Zustand :=
  bildZustand witBild646 0x100000 (BitVec.ofNat 64 0x101000) witReg646
    witnessFlags

/-- The witness start carries the canonically loaded memory. -/
theorem witStartMem646 :
    witStart646.speicher = geladen witBild646 0x100000 := rfl

/-- The witness slot addresses are the laid-out data addresses. -/
def witA1646 : Adresse := slotAddr 0x102000 0

def witA2646 : Adresse := slotAddr 0x102000 8

theorem witA1nat646 : witA1646.toNat = 0x102000 := by decide

theorem witA2nat646 : witA2646.toNat = 0x102008 := by decide

/-- TARGET SEPARATION: the two 8-byte slot footprints are disjoint. -/
theorem witDis646 : Disjunkt witA1646 witA2646 := by
  intro i j hi hj he
  have e1 : (addrOff witA1646 i).toNat = 0x102000 + i := by
    have h : witA1646.toNat + i < 2 ^ 64 := by
      rw [witA1nat646]
      omega
    rw [addrOff_nat witA1646 i h, witA1nat646]
  have e2 : (addrOff witA2646 j).toNat = 0x102008 + j := by
    have h : witA2646.toNat + j < 2 ^ 64 := by
      rw [witA2nat646]
      omega
    rw [addrOff_nat witA2646 j h, witA2nat646]
  have he2 := congrArg BitVec.toNat he
  rw [e1, e2] at he2
  omega

/-- The witness target memory after the first word write. -/
def witM1646 : Speicher :=
  { geladen witBild646 0x100000 with
    bytes := writeBytes (geladen witBild646 0x100000) witA1646
      (zahlWort witVal1646) }

/-- The first target word write succeeds on the loaded image. -/
theorem witTgt1646 :
    write64 (geladen witBild646 0x100000) witA1646
      (zahlWort witVal1646) = some witM1646 := by
  have hsch : schreibbar8 (geladen witBild646 0x100000) witA1646 = true := by
    decide
  unfold write64 witM1646
  rw [if_pos hsch]

/-- The witness target memory after the second word write. -/
def witM2646 : Speicher :=
  { witM1646 with
    bytes := writeBytes witM1646 witA2646 (zahlWort witVal2646) }

/-- The second target word write succeeds after the first. -/
theorem witTgt2646 :
    write64 witM1646 witA2646 (zahlWort witVal2646) = some witM2646 := by
  have hsch : schreibbar8 witM1646 witA2646 = true := by
    decide
  unfold write64 witM2646
  rw [if_pos hsch]

/-- Both witness slots are readable when written. -/
theorem witRd1646 : lesbar8 (geladen witBild646 0x100000) witA1646 = true := by
  decide

theorem witRd2646 : lesbar8 witM1646 witA2646 = true := by
  decide

/-- Explicit first post-world: slot `(0, false)` holds the evaluated
    first value, everything else from the read world. Closed term, so
    kernel reduction sees through it. -/
def witSigma1646 : World witD646 :=
  witSL1646.schreibSlot () [] 0 false
    (eval witSL1646
      (cast (congrArg (Expr witD646 witCtx646 []) witHT1646.symm)
        witE1646) witSL1646 witEnv646)

/-- Explicit second post-world: slot `(0, true)` holds the evaluated
    second value on top of the first post-world. -/
def witSigma2646 : World witD646 :=
  (witSL2646 witSigma1646).schreibSlot () [] 0 true
    (eval (witSL2646 witSigma1646)
      (cast (congrArg (Expr witD646 witCtx646 []) witHT2646.symm)
        witE2646) (witSL2646 witSigma1646) witEnv646)

/-- Both witness source steps are reached (each computes to `.ok`). -/
theorem witExec1646 :
    execStmt witO646 0 witR646
      (Stmt.assignSlot (l := false) () false witI646
        (cast (congrArg (Expr witD646 witCtx646 []) witHT1646.symm)
          witE1646) witHw1646 witHL646)
      witSigma646 witEnv646 = .ok witSigma1646 witEnv646 := by
  simp only [execStmt]
  rfl

theorem witExec2646 :
    execStmt witO646 0 witR646
      (Stmt.assignSlot (l := false) () true witI646
        (cast (congrArg (Expr witD646 witCtx646 []) witHT2646.symm)
          witE2646) witHw2646 witHL646)
      witSigma1646 witEnv646 = .ok witSigma2646 witEnv646 := by
  simp only [execStmt]
  rfl

/-- The two witness fields differ (same row, other field). -/
theorem witHf12646 : (false : Bool) ≠ true := by decide

/-- NON-DEGENERACY (writer): the witness function writes the table. -/
theorem witSchreibt646 :
    ∃ (f : witD646.Fn) (t : witD646.Tab),
      (witD646.signatur f).schreibt t = true :=
  ⟨(), (), rfl⟩

/-- NON-DEGENERACY (memory change): both data bytes change across the
    two target writes (from zero to the representation bytes). -/
theorem witBytesAendern1646 :
    witStart646.speicher.bytes witA1646 ≠
      witM2646.bytes witA1646 := by
  decide

theorem witBytesAendern2646 :
    witStart646.speicher.bytes witA2646 ≠
      witM2646.bytes witA2646 := by
  decide

/-- Source slots before: 12 and 13. -/
theorem witSlotVor1646 : (witSigma646.slots () 0 false).n = 12 := rfl

theorem witSlotVor2646 : (witSigma646.slots () 0 true).n = 13 := rfl

/-! ## 6. Fetched execution: the generated bytes run on real memory.

    Eight fetched byte steps (`byteschritt`, never a hand-fed `schritt`)
    from the loaded image state execute the concatenated lowering: `rax`
    holds the exact second source value 43 and both data cells hold the
    representation bytes 42 and 43 (zero before). A forged opcode byte
    admits no transition. -/

/-- FETCHED-VALUE witness: eight byte steps put the exact source value
    43 into `rax`. -/
theorem witBytesWert646 :
    ausgangReg Register.rax (laufBytes 8 witStart646) =
      some (intWort 43) := by
  decide

/-- MEMORY-CHANGING fetched run: the eight fetched byte steps store both
    representation bytes, observably changing each data cell from zero. -/
theorem witBytesSpeicher646 :
    ausgangByte (natAdresse 0x102000) (laufBytes 8 witStart646) =
      some (natByte 42) ∧
    ausgangByte (natAdresse 0x102008) (laufBytes 8 witStart646) =
      some (natByte 43) ∧
    witStart646.speicher.bytes (natAdresse 0x102000) = BitVec.ofNat 8 0 ∧
    witStart646.speicher.bytes (natAdresse 0x102008) = BitVec.ofNat 8 0 := by
  decide

/-- The fetched run observably changes memory (non-degenerate run). -/
theorem witLaufAendern646 :
    ∃ a : Adresse, ausgangByte a (laufBytes 8 witStart646) ≠
      some (witStart646.speicher.bytes a) := by
  refine ⟨natAdresse 0x102000, ?_⟩
  rw [witBytesSpeicher646.1, witBytesSpeicher646.2.2.1]
  decide

/-- Witness with the first executed opcode byte forged (`mov r64`
    prefix 72 becomes 74, which the canonical decoder refuses). -/
def witBytesFalsch646 : List Byte := witBytes646.set 0 (natByte 74)

def witBildFalsch646 : Bild := { witBild646 with datei := witBytesFalsch646 ++ List.replicate 16 (BitVec.ofNat 8 0) }

def witStartFalsch646 : Zustand :=
  bildZustand witBildFalsch646 0x100000 (BitVec.ofNat 64 0x101000) witReg646
    witnessFlags

/-- PLANTED FETCHED REFUSAL: forging the executed opcode byte admits no
    transition -- the changed byte governs the run. -/
theorem witByteFaelschung646 :
    ausgangRip (byteschritt witStartFalsch646) = none := by
  decide

/-- The forged byte refuses already at fetch-and-decode (not merely at
    the step): the canonical decoder admits no instruction there. -/
theorem witDecodeFaelschung646 :
    fetchDekodiert witStartFalsch646 = none := by
  decide

/-! ## 7. Joint witness for the main connection.

    Every premise of `seq2_korrekt` holds jointly on the witness
    declaration -- checked admission, writer contract, evaluated indices
    and values, two reached source steps moving the slots `12 -> 42`
    and `13 -> 43`, the generated lowered sequences with register
    freshness and slot bases, both target writes with read permission
    and disjoint footprints -- and so do all conclusions: the finite
    target run, both representations with read-back, the source `.ok`
    block equation, the slot changes, the changed target bytes, the
    fetched-byte run with value and memory observations, and the
    non-degeneracy (writer plus memory-changing run). -/
theorem seq2_korrekt_zeuge :
    ∃ (σ1' σ2' : World witD646) (mfin : Speicher) (sfin : Zustand),
      repOk (witD646.typ () false) 0x102000 16 0 = true ∧
      repOk (witD646.typ () true) 0x102000 16 8 = true ∧
      witV646.schreibt () = true ∧
      (eval witSL1646 witI646 witSL1646 witEnv646).n = 0 ∧
      (eval witSL1646 witE1646 witSL1646 witEnv646).n = witVal1646.n ∧
      execStmt witO646 0 witR646
        (Stmt.assignSlot (l := false) () false witI646
          (cast (congrArg (Expr witD646 witCtx646 []) witHT1646.symm)
            witE1646) witHw1646 witHL646)
        witSigma646 witEnv646 = .ok σ1' witEnv646 ∧
      (eval (witSL2646 σ1') witI646 (witSL2646 σ1') witEnv646).n = 0 ∧
      (eval (witSL2646 σ1') witE2646 (witSL2646 σ1') witEnv646).n =
        witVal2646.n ∧
      execStmt witO646 0 witR646
        (Stmt.assignSlot (l := false) () true witI646
          (cast (congrArg (Expr witD646 witCtx646 []) witHT2646.symm)
            witE2646) witHw2646 witHL646)
        σ1' witEnv646 = .ok σ2' witEnv646 ∧
      senkFrag witAbb646 witE1646 Register.rax Register.rcx =
        some [Befehl.movReg64 Register.rax Register.r10,
          Befehl.movImm64 Register.rcx (intWort 12),
          Befehl.addReg64 Register.rax Register.rcx] ∧
      senkFrag witAbb646 witE2646 Register.rax Register.rcx =
        some [Befehl.movReg64 Register.rax Register.r10,
          Befehl.movImm64 Register.rcx (intWort 13),
          Befehl.addReg64 Register.rax Register.rcx] ∧
      EnvRepr witEnv646 witStart646.register witAbb646 ∧
      Frisch witAbb646 Register.rax Register.rcx ∧
      (Register.rax ≠ Register.rsp ∧ Register.rcx ≠ Register.rsp) ∧
      (Register.rbx ≠ Register.rax ∧ Register.rbx ≠ Register.rcx) ∧
      (Register.r12 ≠ Register.rax ∧ Register.r12 ≠ Register.rcx) ∧
      witStart646.register Register.rbx = slotAddr 0x102000 0 ∧
      witStart646.register Register.r12 = slotAddr 0x102000 8 ∧
      witA1646 = slotAddr 0x102000 0 ∧
      witA2646 = slotAddr 0x102000 8 ∧
      write64 witStart646.speicher witA1646 (zahlWort witVal1646) =
        some witM1646 ∧
      write64 witM1646 witA2646 (zahlWort witVal2646) = some mfin ∧
      lesbar8 witStart646.speicher witA1646 = true ∧
      lesbar8 witM1646 witA2646 = true ∧
      Disjunkt witA1646 witA2646 ∧
      lauf ((witProg646.map
        fun b => (⟨b, (encode b).length⟩ : Decodiert))) witStart646 =
        some sfin ∧
      sfin.register Register.rax = intWort 43 ∧
      sfin.speicher = mfin ∧
      RepSlot () 0 false 12 112 witHT1646 witA1646 mfin σ2' ∧
      RepSlot () 0 true 13 113 witHT2646 witA2646 mfin σ2' ∧
      (∃ w, read64 mfin witA1646 = some w ∧
        wortZahl 12 112 w = some witVal1646) ∧
      (∃ w, read64 mfin witA2646 = some w ∧
        wortZahl 13 113 w = some witVal2646) ∧
      execBlock witO646 0 witR646
        (Block.cons
          (Stmt.assignSlot (l := false) () false witI646
            (cast (congrArg (Expr witD646 witCtx646 []) witHT1646.symm)
              witE1646) witHw1646 witHL646)
          (Block.cons
            (Stmt.assignSlot (l := false) () true witI646
              (cast (congrArg (Expr witD646 witCtx646 []) witHT2646.symm)
                witE2646) witHw2646 witHL646)
            Block.nil)) witSigma646 witEnv646 = .ok σ2' witEnv646 ∧
      (witSigma646.slots () 0 false).n = 12 ∧
      (σ2'.slots () 0 false).n = 42 ∧
      (witSigma646.slots () 0 true).n = 13 ∧
      (σ2'.slots () 0 true).n = 43 ∧
      witStart646.speicher.bytes witA1646 ≠ mfin.bytes witA1646 ∧
      witStart646.speicher.bytes witA2646 ≠ mfin.bytes witA2646 ∧
      ausgangReg Register.rax (laufBytes 8 witStart646) =
        some (intWort 43) ∧
      ausgangByte (natAdresse 0x102000) (laufBytes 8 witStart646) =
        some (natByte 42) ∧
      ausgangByte (natAdresse 0x102008) (laufBytes 8 witStart646) =
        some (natByte 43) ∧
      (∃ (f : witD646.Fn) (t : witD646.Tab),
        (witD646.signatur f).schreibt t = true) := by
  have hMain := seq2_korrekt witO646 0 witR646 () false true 12 112 13 113
    witHT1646 witHT2646 0x102000 16 0 8 witOk1646 witOk2646 witI646 witE1646
    witHw1646 witHL646 witI646 witE2646 witHw2646 witHL646 witSigma646
    witEnv646 witSL1646 rfl 0 witVal1646 witHk1646 witHeval1646 witSigma1646
    witExec1646 (witSL2646 witSigma1646) rfl 0 witVal2646
    (witHk2646 witSigma1646) (witHeval2646 witSigma1646) rfl witHf12646
    witSigma2646 witExec2646 witAbb646 Register.rax Register.rcx
    Register.rbx Register.r12 witFrisch646 witHRsp646 witHBasis1646
    witHBasis2646 witStart646 (geladen witBild646 0x100000) witM1646
    witM2646 witStartMem646 witHBaseR1646 witHBaseR2646 witA1646 witA2646
    rfl rfl witTgt1646 witTgt2646 witRd1646 witRd2646 witDis646
    [Befehl.movReg64 Register.rax Register.r10,
      Befehl.movImm64 Register.rcx (intWort 12),
      Befehl.addReg64 Register.rax Register.rcx]
    [Befehl.movReg64 Register.rax Register.r10,
      Befehl.movImm64 Register.rcx (intWort 13),
      Befehl.addReg64 Register.rax Register.rcx]
    witSenk1646 witSenk2646 witUmgebung646
  obtain ⟨sfin, hrun, hval, hmem, hRep1, hRep2, hread1, hread2, hexec⟩ := hMain
  have hSlotNach1 : (witSigma2646.slots () 0 false).n = 42 := rfl
  have hSlotNach2 : (witSigma2646.slots () 0 true).n = 43 := rfl
  have hRunFin : lauf ((witProg646.map
      fun b => (⟨b, (encode b).length⟩ : Decodiert))) witStart646 =
      some sfin := hrun
  have hValFin : sfin.register Register.rax = intWort 43 := hval
  refine ⟨witSigma1646, witSigma2646, witM2646, sfin, witOk1646, witOk2646,
    witHw1646, witHk1646, witHeval1646, witExec1646, witHk2646 witSigma1646,
    witHeval2646 witSigma1646, witExec2646, witSenk1646, witSenk2646,
    witUmgebung646, witFrisch646, witHRsp646, witHBasis1646, witHBasis2646,
    witHBaseR1646, witHBaseR2646, rfl, rfl, witTgt1646, witTgt2646, witRd1646,
    witRd2646, witDis646, hRunFin, hValFin, hmem, hRep1, hRep2, hread1,
    hread2, hexec, witSlotVor1646, hSlotNach1, witSlotVor2646, hSlotNach2,
    witBytesAendern1646, witBytesAendern2646, witBytesWert646,
    witBytesSpeicher646.1,     witBytesSpeicher646.2.1, witSchreibt646⟩

/-! ## 8. Fetch stability across both data stores.

    With the checked code/data mapping (pairwise `virtReich` verdict),
    section permission shapes (code executable/never-writable, data
    writable/never-executable) and explicit no-wrap bounds, both word
    writes preserve the fetched window, the decode outcome and every
    fetched code byte. Foreignness of each store is DERIVED from the
    mapping (`codeFremd_von_abbildung`), never assumed; the
    unchanged-memory facts come from the actual store frames. This is the
    composition API a future source validator consumes for its code-leg:
    run `seq2_korrekt` for data, `seq2_fetch` for code. -/

/-- FETCH STABILITY: two checked data stores preserve fetch, decode and
    every fetched code byte. Every premise is used: the stores through
    the derived foreignness and the actual frames, the mapping through
    both foreignness derivations, the section shapes through W^X. -/
theorem seq2_fetch (s : Zustand) (a1 a2 : Adresse) (w1 w2 : Wort)
    (m1 m'' : Speicher)
    (hTgt1 : write64 s.speicher a1 w1 = some m1)
    (hTgt2 : write64 m1 a2 w2 = some m'')
    (bild : Bild) (bias : Nat) (sc sd : Abschnitt)
    (hmc : sc ∈ bild.abschnitte) (hmd : sd ∈ bild.abschnitte)
    (hne : abschnittAlsRegion bias sc ≠ abschnittAlsRegion bias sd)
    (hpaar : paarweise (virtReich bias) bild.abschnitte = true)
    (hcode : istCodeAbschnitt sc = true)
    (hdat : istDatenAbschnitt sd = true)
    (hrip : ∀ j : Nat, j < fetchCap →
      abteilFinden bild.abschnitte bias (s.rip.toNat + j) = some sc)
    (hstore1 : ∀ q : Nat, q < 8 →
      abteilFinden bild.abschnitte bias (a1.toNat + q) = some sd)
    (hstore2 : ∀ q : Nat, q < 8 →
      abteilFinden bild.abschnitte bias (a2.toNat + q) = some sd)
    (hripNF : s.rip.toNat + fetchCap ≤ 2 ^ 64)
    (hANF1 : a1.toNat + 8 ≤ 2 ^ 64)
    (hANF2 : a2.toNat + 8 ≤ 2 ^ 64) :
    geholt { s with speicher := m'' } = geholt s ∧
    fetchDekodiert { s with speicher := m'' } = fetchDekodiert s ∧
    (∀ j : Nat, j < (geholt s).length →
      m''.bytes (addrOff s.rip j) = s.speicher.bytes (addrOff s.rip j)) ∧
    wxOk sc = true ∧ wxOk sd = true := by
  have hF1 : CodeFremd s a1 :=
    codeFremd_von_abbildung s a1 bild bias sc sd hmc hmd hne hpaar
      hrip hstore1 hripNF hANF1
  have hF2 : CodeFremd s a2 :=
    codeFremd_von_abbildung s a2 bild bias sc sd hmc hmd hne hpaar
      hrip hstore2 hripNF hANF2
  have hwx1 : wxOk sc = true := istCodeAbschnitt_wx sc hcode
  have hwx2 : wxOk sd = true := istDatenAbschnitt_wx sd hdat
  have g1 : geholt ({ s with speicher := m1 }) = geholt s :=
    geholt_nach_erlaubtem_schreiben s m1 a1 w1 hTgt1 hF1
  have g2 : geholt ({ s with speicher := m'' }) =
      geholt ({ s with speicher := m1 }) :=
    geholt_nach_erlaubtem_schreiben ({ s with speicher := m1 }) m'' a2 w2
      hTgt2 hF2
  have f1 : fetchDekodiert ({ s with speicher := m1 }) =
      fetchDekodiert s :=
    fetchDekodiert_nach_erlaubtem_schreiben s m1 a1 w1 hTgt1 hF1
  have f2 : fetchDekodiert ({ s with speicher := m'' }) =
      fetchDekodiert ({ s with speicher := m1 }) :=
    fetchDekodiert_nach_erlaubtem_schreiben ({ s with speicher := m1 }) m''
      a2 w2 hTgt2 hF2
  have c : ∀ j : Nat, j < (geholt s).length →
      m''.bytes (addrOff s.rip j) = s.speicher.bytes (addrOff s.rip j) := by
    intro j hj
    have hj' : j < (geholt ({ s with speicher := m1 })).length := by
      rw [g1]
      exact hj
    have h2 := codeBytes_nach_erlaubtem_schreiben ({ s with speicher := m1 })
      m'' a2 w2 j hTgt2 hF2 hj'
    have h1 := codeBytes_nach_erlaubtem_schreiben s m1 a1 w1 j hTgt1 hF1 hj
    exact h2.trans h1
  exact ⟨g2.trans g1, f2.trans f1, c, hwx1, hwx2⟩

/-- FETCH WITNESS: on the accepted witness image both generated stores
    preserve the fetched window, the decode outcome and every fetched
    code byte. The mapping verdicts, section shapes and lookups are all
    decided; foreignness itself is derived by `seq2_fetch`. -/
theorem witFetch646 :
    geholt ({ witStart646 with speicher := witM2646 }) =
      geholt witStart646 ∧
    fetchDekodiert ({ witStart646 with speicher := witM2646 }) =
      fetchDekodiert witStart646 ∧
    (∀ j : Nat, j < (geholt witStart646).length →
      witM2646.bytes (addrOff witStart646.rip j) =
        witStart646.speicher.bytes (addrOff witStart646.rip j)) := by
  have hT1 : write64 witStart646.speicher witA1646 (zahlWort witVal1646) =
      some witM1646 := witTgt1646
  have hT2 : write64 witM1646 witA2646 (zahlWort witVal2646) =
      some witM2646 := witTgt2646
  have hrip : ∀ j : Nat, j < fetchCap →
      abteilFinden witBild646.abschnitte 0x100000
        (witStart646.rip.toNat + j) = some witCode646 := by
    intro j hj
    have h15 : fetchCap = 15 := rfl
    have hj15 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨
        j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨
        j = 14 := by omega
    rcases hj15 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hmem : ∀ q : Nat, q < 8 →
      abteilFinden witBild646.abschnitte 0x100000
        (witA1646.toNat + q) = some witDaten646 ∧
      abteilFinden witBild646.abschnitte 0x100000
        (witA2646.toNat + q) = some witDaten646 := by
    intro q hq
    have hq8 : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨
        q = 7 := by omega
    rcases hq8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide⟩
  have h := seq2_fetch witStart646 witA1646 witA2646 (zahlWort witVal1646)
    (zahlWort witVal2646) witM1646 witM2646 hT1 hT2 witBild646 0x100000
    witCode646 witDaten646 (by decide) (by decide) witRegUngleich646
    witPaar646 witCode646_code witDaten646_daten hrip
    (fun q hq => (hmem q hq).1) (fun q hq => (hmem q hq).2) (by decide)
    (by decide) (by decide)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Joint witness for `senkSeq2_ok`: both legs lower on the witness
    declaration, which has a writing function and a memory-changing run. -/
theorem senkSeq2_ok_zeuge :
    ∃ (p1 p2 : List Befehl),
      senkAssign witAbb646 witE1646 Register.rax Register.rcx
        Register.rbx (BitVec.ofNat 32 0) = some p1 ∧
      senkAssign witAbb646 witE2646 Register.rax Register.rcx
        Register.r12 (BitVec.ofNat 32 0) = some p2 ∧
      (∃ (f : witD646.Fn) (t : witD646.Tab),
        (witD646.signatur f).schreibt t = true) ∧
      (∃ a : Adresse, ausgangByte a (laufBytes 8 witStart646) ≠
        some (witStart646.speicher.bytes a)) ∧
      senkSeq2 witAbb646 witE1646 witE2646 Register.rax Register.rcx
        Register.rbx Register.r12 (BitVec.ofNat 32 0)
        (BitVec.ofNat 32 0) = some (p1 ++ p2) := by
  refine ⟨[Befehl.movReg64 Register.rax Register.r10,
      Befehl.movImm64 Register.rcx (intWort 12),
      Befehl.addReg64 Register.rax Register.rcx,
      Befehl.store64 Register.rbx Register.rax (BitVec.ofNat 32 0)],
    [Befehl.movReg64 Register.rax Register.r10,
      Befehl.movImm64 Register.rcx (intWort 13),
      Befehl.addReg64 Register.rax Register.rcx,
      Befehl.store64 Register.r12 Register.rax (BitVec.ofNat 32 0)],
    witSenkAssign1646, witSenkAssign2646, witSchreibt646,
    witLaufAendern646, ?_⟩
  rw [witSenkSeq646]
  rfl

/-- Joint witness for `seq2_execBlock`: both source steps reach `.ok`
    on the witness declaration with its writer and memory-changing run. -/
theorem seq2_execBlock_zeuge :
    ∃ (σ1' σ2' : World witD646),
      execStmt witO646 0 witR646
        (Stmt.assignSlot (l := false) () false witI646
          (cast (congrArg (Expr witD646 witCtx646 []) witHT1646.symm)
            witE1646) witHw1646 witHL646)
        witSigma646 witEnv646 = .ok σ1' witEnv646 ∧
      execStmt witO646 0 witR646
        (Stmt.assignSlot (l := false) () true witI646
          (cast (congrArg (Expr witD646 witCtx646 []) witHT2646.symm)
            witE2646) witHw2646 witHL646)
        σ1' witEnv646 = .ok σ2' witEnv646 ∧
      (∃ (f : witD646.Fn) (t : witD646.Tab),
        (witD646.signatur f).schreibt t = true) ∧
      (∃ a : Adresse, ausgangByte a (laufBytes 8 witStart646) ≠
        some (witStart646.speicher.bytes a)) ∧
      execBlock witO646 0 witR646
        (Block.cons
          (Stmt.assignSlot (l := false) () false witI646
            (cast (congrArg (Expr witD646 witCtx646 []) witHT1646.symm)
              witE1646) witHw1646 witHL646)
          (Block.cons
            (Stmt.assignSlot (l := false) () true witI646
              (cast (congrArg (Expr witD646 witCtx646 []) witHT2646.symm)
                witE2646) witHw2646 witHL646)
            Block.nil)) witSigma646 witEnv646 =
        .ok σ2' witEnv646 := by
  refine ⟨witSigma1646, witSigma2646, witExec1646, witExec2646,
    witSchreibt646, witLaufAendern646, ?_⟩
  exact seq2_execBlock witO646 0 witR646 _ _ _ _ _ _ witExec1646 witExec2646

/-! ## 9. Planted refusals: alias, code store, range, stopped outcome.

    SM-UEBERLAPP (a footprint is never disjoint from itself, so the
    second write cannot cover the first slot); a store into the code
    footprint is refused by permission with memory unchanged by
    construction; a range starting below zero is refused by the checked
    admission; a stopped source block steps to `.leave`, never `.ok` --
    the `.ok` composition claims nothing about it. -/

/-- ALIAS IS NEVER FOREIGN: a footprint shares every byte with itself. -/
theorem witAlias646 : ¬ Disjunkt witA1646 witA1646 := by
  intro h
  have h0 := h 0 0 (by decide) (by decide)
  exact h0 rfl

/-- OVERLAP REFUSAL at region level: overlapping data extents share
    bytes, so the checked separation verdict refuses them. -/
theorem witRegionUeberlapp646 :
    regionDisjunkt
      (abschnittAlsRegion 0x100000 witDaten646)
      (abschnittAlsRegion 0x100000
        { witDaten646 with vaddr := 0x2008 }) = false := by
  decide

/-- PERMISSION REFUSAL: a store into the code footprint (eight bytes
    from `0x101000`, inside the executable section) is refused. -/
theorem witCodeWrite646 :
    write64 (geladen witBild646 0x100000) (BitVec.ofNat 64 0x101000)
      42 = none := by
  apply write64_verweigert _ _ _
  decide

/-- RANGE REFUSAL: a range starting below zero is refused by the checked
    admission (the modular word mapping would clip the negative part). -/
theorem witNegBereich646 :
    repOk (.int (-5) 100) 0x102000 16 0 = false := by
  decide

/-- STOPPED SOURCE OUTCOME: a block starting with `leave` steps to
    `.leave`, never `.ok` -- the `.ok` composition claims nothing
    about stopped runs. -/
theorem witLeave646 :
    execBlock witO646 0 witR646
      (Block.cons
        (Stmt.leave (D := witD646) (V := witV646) (l := true)
          (Γ := witCtx646) (Λ := ([] : List (Res witD646))) rfl)
        Block.nil)
      witSigma646 witEnv646 =
      .leave (l := true) rfl witSigma646 witEnv646 := rfl

/- CUTS:
    Proved here, over the ACTUAL accepted vocabulary (`Syntax.Block.cons`
    with two `Stmt.assignSlot`, `Semantik.execStmt`/`execBlock`,
    `senkFrag`/`senkAssign`, `repOk`/`RepSlot`/`rep_schritt_bleibt`,
    `lauf`/`schritt`, `geholt`/`fetchDekodiert`/`byteschritt`,
    `codeFremd_von_abbildung`, `geladen`/`wohlgeformt`):
    - concatenated lowering shape plus either-leg unsupported-expression
      refusals (`senkSeq2_ok`, `senkSeq2_verweigert_links/rechts`);
    - the source `.ok` chain over the actual two-assignment `Block` term
      (`seq2_execBlock`);
    - the main connection: two admitted assignments lower to the
      concatenated pilot sequence whose finite target `lauf` run agrees
      with the source post-state on both slots, each with read-back, plus
      the source `.ok` block equation -- all DERIVED, never assumed
      (`seq2_korrekt`);
    - fetch stability across both data stores from the checked
      code/data mapping with permission shapes and no-wrap bounds
      (`seq2_fetch`, the composition API for the code leg);
    - a joint non-degenerate witness: one table its function writes,
      two reached source steps (`12 -> 42`, `13 -> 43`), two derived
      target writes changing both data bytes, an 8-step fetched-byte run
      with value and memory observations, and planted alias/overlap/
      code-write/range/stopped-outcome/bad-byte refusals.
    NOT proved here, and not claimed:
    - No generic `laufBytes` induction for an ARBITRARY generated
      sequence: single steps agree by `kanonisch_schritt_ueberein`, the
      concrete witness bytes agree by `decide`; the lift to `∀ prog`
      stays OPEN.
    - Pilot integer fragment only: values in `senkFrag` (lit/var/one
      bounded add/sub over atoms), zero-displacement stores, one
      dedicated base register per slot, same row, distinct fields, one
      table. Sums, floats, bools, globals, pointers, calls, loops,
      locks, non-zero displacements and wider blocks are outside.
    - Only `.ok` chains: `.logik`/`.hardware`/`.zurueck`/`.leave`/`.next`
      short-circuit `execBlock` and no `.ok` conclusion is claimed for
      them (the `leave` probe documents the stopped shape).
    - No source correspondence for narrow stores: only the 8-byte legs
      carry `RepSlot`; 1/2/4-byte fetch preservation is target-only.
    - No concurrency claim: every step is sequential over one `Speicher`;
      per-access TSO/GX refinement stays with the TSO bridge.
    - No validator soundness: `valX86_sound` and the generic
      source-to-final-loaded-bytes closing theorem stay OPEN.
    - No hardware claim: everything runs over the model `Speicher`
      function, not silicon; only named hardware behaviour would be
      assumed, and none is assumed here.
    - No OS/loader claim: layout bases and the image mapping are checked
      premises about numbers; enforcement at runtime is user/binding
      logic with contracts, never granted here.
    - No int->ptr conversion: slot addresses are target-side
      `natAdresse` computations over accepted layout bases, never source
      values cast to pointers.
-/

#print axioms senkSeq2
#print axioms seqBytes2
#print axioms senkSeq2_ok
#print axioms senkSeq2_verweigert_links
#print axioms senkSeq2_verweigert_rechts
#print axioms seq2_execBlock
#print axioms seq2_korrekt
#print axioms seq2_korrekt_zeuge
#print axioms seq2_fetch
#print axioms witFetch646
#print axioms senkSeq2_ok_zeuge
#print axioms seq2_execBlock_zeuge
#print axioms witSenkSeq646
#print axioms witBild646_wohlgeformt
#print axioms witDis646
#print axioms witTgt1646
#print axioms witTgt2646
#print axioms witExec1646
#print axioms witExec2646
#print axioms witBytesWert646
#print axioms witBytesSpeicher646
#print axioms witLaufAendern646
#print axioms witByteFaelschung646
#print axioms witDecodeFaelschung646
#print axioms witAlias646
#print axioms witRegionUeberlapp646
#print axioms witCodeWrite646
#print axioms witNegBereich646
#print axioms witLeave646

end Gabbro.Grammatik.X86
