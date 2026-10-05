/-
  File:      Grammatik/X86/PipelineCallsBlock.lean
  Subject:   Pipeline calls, multi-statement callee bodies: the real
             `execBlock` correspondence for a callee body of exactly TWO
             straight-line slot assignments.

  Follow-up of lane 1189 (`PipelineCallsExec.lean`, single-assignment
  callee bodies only). Per-chunk runs reuse `einzelChunk_lauf`; target
  composition reuses lane 1195's run chain (`PipeBlock.KetteLauf`,
  `ketteLauf_lauf`). Lane 1211 (`PipelineChunkDerive`) is not merged,
  so chunk premises are DERIVED from the lowering, never assumed.
  Reuses `PipelineCalls` (`rufOk`, `calleeGerettet`), `Pipeline`
  (`validate`/`validate_sound`, `senkBlock_assign`, `lauf_zu_laufBytes`,
  `worldRep_store`) and the `pw`/`cw`/`rufWit` witnesses unchanged.
  No second machine, no second loader, no source claim beyond the
  proved two-assignment fragment.
-/
import Grammatik.X86.Pipeline.Kern.Pipeline
import Grammatik.X86.Pipeline.Aufrufe.PipelineCalls
import Grammatik.X86.Pipeline.Aufrufe.PipelineCallsExec
import Grammatik.X86.Pipeline.Kern.PipelineWitnesses
import Grammatik.X86.Pipeline.Ablauf.PipelineBlockInduct

namespace Gabbro.Grammatik.X86.PipelineCallsBlock

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineCalls
open Gabbro.Grammatik.X86.PipelineCallsExec
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeBlock
open Gabbro.Grammatik.X86.OptimizationRules

variable {D : Deklaration}

/-- The proved callee shape: exactly two slot assignments, then `nil`.
    Every other block form is refused, never guessed. -/
def istZweiZuweisung {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') : Bool :=
  match b with
  | .cons (.assignSlot _ _ _ _ _ _) (.cons (.assignSlot _ _ _ _ _ _) .nil) => true
  | _ => false

/-- THE CALL-BLOCK VALIDATOR: the caller frame is admitted (`rufOk`),
    the callee body has the proved two-assignment shape, and the
    candidate bytes are what the Lean pipeline recomputes from the
    source (no optimiser certificates, as in `rufExecOk`). -/
def rufBlockOk (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte) : Bool :=
  rufOk b r nArgs benutztRot && istZweiZuweisung body &&
    validate c L [] body bytes

/-- Unpacking the call-block validator: frame, shape, recomputed bytes. -/
theorem rufBlockOk_teile (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : rufBlockOk b r nArgs benutztRot c L body bytes = true) :
    rufOk b r nArgs benutztRot = true ∧ istZweiZuweisung body = true ∧
      validate c L [] body bytes = true := by
  unfold rufBlockOk at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- RED-ZONE USE REFUSAL: no call that uses the red zone is admitted. -/
theorem rufBlockOk_verweigert_rot (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte) :
    rufBlockOk b r nArgs true c L body bytes = false := by
  unfold rufBlockOk
  rw [pipeline_ruf_verweigert_rot]
  rfl

/-- SHAPE REFUSAL: a body that is not two assignments is refused loudly. -/
theorem rufBlockOk_verweigert_form (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : istZweiZuweisung body = false) :
    rufBlockOk b r nArgs benutztRot c L body bytes = false := by
  unfold rufBlockOk
  rw [h]
  cases rufOk b r nArgs benutztRot <;> rfl

/-- BYTE REFUSAL: candidate bytes the Lean pipeline does not recompute
    are refused loudly. -/
theorem rufBlockOk_verweigert_bytes (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : validate c L [] body bytes = false) :
    rufBlockOk b r nArgs benutztRot c L body bytes = false := by
  unfold rufBlockOk
  rw [h]
  cases rufOk b r nArgs benutztRot <;> cases istZweiZuweisung body <;> rfl

/-- CALLEE CORRECTNESS for two assignments (real source correspondence):
    for an admitted caller frame and validated callee bytes of TWO source
    assignments, the fetched byte run reaches the end of the code with the
    world of the REAL `execBlock` run represented, the environment
    represented, and every callee-saved register preserved. Per-chunk runs
    are DERIVED (`einzelChunk_lauf`, lane 1189); the target composition is
    lane 1195's run chain (`KetteLauf`, `ketteLauf_lauf`); the source
    outcome is inverted from the real `execBlock`. Every premise is
    consumed: `hval` for frame admission and recomputed bytes, `hsep`
    for the two stores, `hfremd` for callee-saved preservation, `hcode`
    and `hrip` for the fetch, `hW` and `hE` for the representation,
    `hsrc` for the source outcome. -/
theorem zweiRuf_korrekt (b : Belegung) (rh : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t1 : D.Tab) (f1 : D.Feld t1) (i1 : Expr D Γ Λ (.index (D.count t1)))
    (e1 : Expr D Γ Λ (D.typ t1 f1)) (hw1 : V.schreibt t1 = true) (hL1 : darf D t1 Λ)
    (t2 : D.Tab) (f2 : D.Feld t2) (i2 : Expr D Γ Λ (.index (D.count t2)))
    (e2 : Expr D Γ Λ (D.typ t2 f2)) (hw2 : V.schreibt t2 = true) (hL2 : darf D t2 Λ)
    (bytes : List Byte)
    (hval : rufBlockOk b rh nArgs benutztRot c L
      ((.cons (.assignSlot t1 f1 i1 e1 hw1 hL1)
        (.cons (.assignSlot t2 f2 i2 e2 hw2 hL2) .nil) : Block D V l Γ Λ Λ)) bytes = true)
    (hsep : LayoutSep L) (hfremd : calleeFremd c = true)
    (O : Orakel D) (passes : Nat)
    (R : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : CodeAt s.speicher (natAdresse c.codeBase) bytes)
    (hrip : s.rip = natAdresse c.codeBase)
    (hW : WorldRep L s.speicher σ) (hE : EnvRepr ρ s.register (abbOf c))
    (σ'' : World D) (ρ'' : Env D Γ)
    (hsrc : execBlock O passes R
      ((.cons (.assignSlot t1 f1 i1 e1 hw1 hL1)
        (.cons (.assignSlot t2 f2 i2 e2 hw2 hL2) .nil) : Block D V l Γ Λ Λ)) σ ρ =
      (.ok σ'' ρ'' : Ausgang V l Γ)) :
    rufOk b rh nArgs benutztRot = true ∧
    ∃ n s', laufBytes n s = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep L s'.speicher σ'' ∧ EnvRepr ρ'' s'.register (abbOf c) ∧
      (∀ q, q ∈ calleeGerettet → s'.register q = s.register q) := by
  have hruf : rufOk b rh nArgs benutztRot = true :=
    (rufBlockOk_teile b rh nArgs benutztRot c L _ _ hval).1
  have hval2 : validate c L []
      ((.cons (.assignSlot t1 f1 i1 e1 hw1 hL1)
        (.cons (.assignSlot t2 f2 i2 e2 hw2 hL2) .nil) : Block D V l Γ Λ Λ)) bytes = true :=
    (rufBlockOk_teile b rh nArgs benutztRot c L _ _ hval).2.2
  obtain ⟨prog, hc, hlow, hb, -, -⟩ := validate_sound c L [] _ bytes hval2
  rw [optimise_nil] at hlow
  rw [senkBlock_assign] at hlow
  cases hs1 : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t1 f1 i1 e1 hw1 hL1) with
  | none => rw [hs1] at hlow; cases hlow
  | some p1 =>
    rw [hs1] at hlow
    dsimp only at hlow
    cases hq1 : senkBlock c L (0 + (encodeAll p1).length)
        ((.cons (.assignSlot t2 f2 i2 e2 hw2 hL2) .nil : Block D V l Γ Λ Λ)) with
    | none => rw [hq1] at hlow; cases hlow
    | some q =>
      simp only [hq1, Option.map_some, Option.some.injEq] at hlow
      subst hlow
      rw [senkBlock_assign] at hq1
      cases hs2 : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t2 f2 i2 e2 hw2 hL2) with
      | none => rw [hs2] at hq1; cases hq1
      | some p2 =>
        rw [hs2] at hq1
        dsimp only at hq1
        have hnil : senkBlock c L (0 + (encodeAll p1).length + (encodeAll p2).length)
            (Block.nil : Block D V l Γ Λ Λ) = some [] := by simp [senkBlock]
        rw [hnil] at hq1
        simp only [Option.map_some, Option.some.injEq] at hq1
        subst hq1
        simp only [senkStmt] at hs1
        cases hk1 : constInt? i1 with
        | none => simp [hk1] at hs1
        | some k1 =>
          simp only [hk1] at hs1
          cases hA1 : L.loc t1 k1 f1 with
          | none => simp [hA1] at hs1
          | some A1 =>
            simp only [hA1] at hs1
            by_cases hok1 : repOk (D.typ t1 f1) A1 8 0 = true
            · rw [if_pos hok1] at hs1
              cases hv1 : senkWertT c e1 with
              | none => simp [hv1] at hs1
              | some pv1 =>
                simp only [hv1] at hs1
                simp only [Option.map_some, Option.some.injEq] at hs1
                subst hs1
                simp only [senkStmt] at hs2
                cases hk2 : constInt? i2 with
                | none => simp [hk2] at hs2
                | some k2 =>
                  simp only [hk2] at hs2
                  cases hA2 : L.loc t2 k2 f2 with
                  | none => simp [hA2] at hs2
                  | some A2 =>
                    simp only [hA2] at hs2
                    by_cases hok2 : repOk (D.typ t2 f2) A2 8 0 = true
                    · rw [if_pos hok2] at hs2
                      cases hv2 : senkWertT c e2 with
                      | none => simp [hv2] at hs2
                      | some pv2 =>
                        simp only [hv2] at hs2
                        simp only [Option.map_some, Option.some.injEq] at hs2
                        subst hs2
                        obtain ⟨lo1, hi1, hT1, hlo1, hhi1, -⟩ := repOk_int _ A1 hok1
                        obtain ⟨lo2, hi2, hT2, hlo2, hhi2, -⟩ := repOk_int _ A2 hok2
                        let σL1 := σ.lese Λ (i1.orte ++ e1.orte)
                        have hki1 : (eval σL1 i1 σL1 ρ).n = k1 := by
                          have hci := constInt?_sound i1 σL1 σL1 ρ k1 hk1
                          simpa [intOf] using hci
                        have hsrcEq1 : execBlock O passes R
                            ((.cons (.assignSlot t1 f1 i1 e1 hw1 hL1)
                              (.cons (.assignSlot t2 f2 i2 e2 hw2 hL2) .nil) :
                              Block D V l Γ Λ Λ)) σ ρ =
                            execBlock O passes R
                              ((.cons (.assignSlot t2 f2 i2 e2 hw2 hL2) .nil :
                                Block D V l Γ Λ Λ))
                              (σL1.schreibSlot t1 Λ k1 f1 (eval σL1 e1 σL1 ρ)) ρ := by
                          rw [← hki1]
                          rfl
                        rw [hsrcEq1] at hsrc
                        let σ1 := σL1.schreibSlot t1 Λ k1 f1 (eval σL1 e1 σL1 ρ)
                        let σL2 := σ1.lese Λ (i2.orte ++ e2.orte)
                        have hki2 : (eval σL2 i2 σL2 ρ).n = k2 := by
                          have hci := constInt?_sound i2 σL2 σL2 ρ k2 hk2
                          simpa [intOf] using hci
                        have hsrcEq2 : execBlock O passes R
                            ((.cons (.assignSlot t2 f2 i2 e2 hw2 hL2) .nil :
                              Block D V l Γ Λ Λ)) σ1 ρ =
                            execBlock O passes R (Block.nil : Block D V l Γ Λ Λ)
                              (σL2.schreibSlot t2 Λ k2 f2 (eval σL2 e2 σL2 ρ)) ρ := by
                          rw [← hki2]
                          rfl
                        rw [hsrcEq2] at hsrc
                        have hnilOk : execBlock O passes R (Block.nil : Block D V l Γ Λ Λ)
                            (σL2.schreibSlot t2 Λ k2 f2 (eval σL2 e2 σL2 ρ)) ρ =
                            (.ok (σL2.schreibSlot t2 Λ k2 f2 (eval σL2 e2 σL2 ρ)) ρ :
                              Ausgang V l Γ) := by simp [execBlock]
                        rw [hnilOk] at hsrc
                        cases hsrc
                        obtain ⟨-, -, hwrA1, -⟩ := hW t1 k1 f1 A1 hA1
                        obtain ⟨st1, hrun1, hw1t, hE1, hreg1⟩ :=
                          einzelChunk_lauf c hc e1 hT1 hlo1 hhi1 pv1 hv1 A1 ρ
                            σL1 σL1 s hE hwrA1
                        have hW1 : WorldRep L st1.speicher σ1 :=
                          worldRep_store L hsep s.speicher st1.speicher σL1 t1 k1 f1
                            A1 hA1 hW lo1 hi1 hT1 _ hw1t Λ
                        obtain ⟨-, -, hwrA2, -⟩ := hW1 t2 k2 f2 A2 hA2
                        obtain ⟨st2, hrun2, hw2t, hE2, hreg2⟩ :=
                          einzelChunk_lauf c hc e2 hT2 hlo2 hhi2 pv2 hv2 A2 ρ
                            σL2 σL2 st1 hE1 hwrA2
                        have hW2 : WorldRep L st2.speicher
                            (σL2.schreibSlot t2 Λ k2 f2 (eval σL2 e2 σL2 ρ)) :=
                          worldRep_store L hsep st1.speicher st2.speicher σL2 t2 k2 f2
                            A2 hA2 hW1 lo2 hi2 hT2 _ hw2t Λ
                        have d1 : lauf (decodiertZu (pv1 ++ [Befehl.movImm64 c.adr
                            (natAdresse A1),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)])) s =
                            some st1 := hrun1
                        have d2 : lauf (decodiertZu (pv2 ++ [Befehl.movImm64 c.adr
                            (natAdresse A2),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)])) st1 =
                            some st2 := hrun2
                        have hkette : KetteLauf [pv1 ++ [Befehl.movImm64 c.adr
                            (natAdresse A1),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)],
                            pv2 ++ [Befehl.movImm64 c.adr (natAdresse A2),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]] s st2 := by
                          refine KetteLauf.cons _ _ _ _ _ d1 (KetteLauf.cons _ _ _ _ _ d2
                            (KetteLauf.nil _))
                        have hrun0 := ketteLauf_lauf [pv1 ++ [Befehl.movImm64 c.adr
                            (natAdresse A1),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)],
                            pv2 ++ [Befehl.movImm64 c.adr (natAdresse A2),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]] s st2 hkette
                        simp only [List.flatten_cons, List.flatten_nil] at hrun0
                        have hrun : lauf (((pv1 ++ [Befehl.movImm64 c.adr (natAdresse A1),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]) ++
                            ((pv2 ++ [Befehl.movImm64 c.adr (natAdresse A2),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]) ++ [])).map
                            kanon) s = some st2 := hrun0
                        have hgp : ((pv1 ++ [Befehl.movImm64 c.adr (natAdresse A1),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]) ++
                            ((pv2 ++ [Befehl.movImm64 c.adr (natAdresse A2),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]) ++ [])).all
                            gerade = true := by
                          simp [List.all_append, senkWertT_gerade c e1 pv1 hv1,
                            senkWertT_gerade c e2 pv2 hv2, gerade]
                        obtain ⟨hb1, hr1, -, -, -⟩ := lauf_zu_laufBytes
                          (natAdresse c.codeBase) bytes
                          ((pv1 ++ [Befehl.movImm64 c.adr (natAdresse A1),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]) ++
                            ((pv2 ++ [Befehl.movImm64 c.adr (natAdresse A2),
                            Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]) ++ [])) [] []
                          s st2 hgp hrun hcode
                          (by simp [hb]) (by rw [hrip]; exact (addrOff_null _).symm)
                        refine ⟨hruf, _, st2, hb1, ?_, hW2, hE2, ?_⟩
                        · rw [hr1, hb, addrOff_natAdresse]
                          simp
                        · intro q hq
                          obtain ⟨hne1, hne2, hne3⟩ := calleeFremd_mem c hfremd q hq
                          rw [hreg2 q hne1 hne2 hne3]
                          exact hreg1 q hne1 hne2 hne3
                    · rw [if_neg hok2] at hs2; cases hs2
            · rw [if_neg hok1] at hs1; cases hs1

/-! ## Joint witness: two lowered assignments over concrete values. -/

/-- THE CALLEE BODY: `T[0].f = x + 5; T[1].f = x + 5;` -- two
    assignments, then `nil`. Both rows reuse the widened `x + 5`. -/
def bwBody : Block pwD pwV false pwCtx [] [] :=
  .cons (.assignSlot () () pwIdx0 pwWert0 pwHw pwHL)
    (.cons (.assignSlot () () pwIdx1 pwWert0 pwHw pwHL) .nil)

/-- THE CANDIDATE, written out as a producer would emit it: the `cwProg`
    chunk twice, storing to 8192 then to 8200. -/
def bwProg : List Befehl :=
  [ .movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx,
    .movImm64 .r11 (natAdresse 8192), .store64 .r11 .rax (BitVec.ofNat 32 0),
    .movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx,
    .movImm64 .r11 (natAdresse 8200), .store64 .r11 .rax (BitVec.ofNat 32 0) ]

def bwBytes : List Byte := encodeAll bwProg

/-- The body has the proved two-assignment shape. -/
theorem bw_zwei : istZweiZuweisung bwBody = true := rfl

/-- THE VALIDATOR ACCEPTS the joint call: admitted seven-argument frame,
    two-assignment shape, recomputed bytes -- by computation. -/
theorem bw_rufBlock : rufBlockOk rufWitBelegung rufWitRahmen 7 false cwCfg pwL
    bwBody bwBytes = true := by decide

/-- The memory: code at `[4096, 4096 + len)` (execute only), the two
    slots at `[8192, 8208)` holding 7 and 9 (read/write, never execute). -/
def bwMemBytes (a : Adresse) : Byte :=
  if 4096 ≤ a.toNat ∧ a.toNat < 4096 + bwBytes.length then bwBytes.getD (a.toNat - 4096) 0
  else if 8192 ≤ a.toNat ∧ a.toNat < 8200 then wortByte (BitVec.ofNat 64 7) (a.toNat - 8192)
  else if 8200 ≤ a.toNat ∧ a.toNat < 8208 then wortByte (BitVec.ofNat 64 9) (a.toNat - 8200)
  else 0

def bwCode (a : Adresse) : Bool := decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + bwBytes.length)

def bwDaten (a : Adresse) : Bool := decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

def bwMem : Speicher :=
  { bytes := bwMemBytes, lesbar := bwDaten, schreibbar := bwDaten, ausfuehrbar := bwCode }

/-- Registers: `x` in `r10`, everything else zero (reused `cwReg`). -/
def bwStart (x : Int) : Zustand :=
  { register := cwReg x, flags := witnessFlags, rip := natAdresse 4096, speicher := bwMem }

/-- The code fits far below the data: no wrap, no overlap. -/
theorem bw_laenge : 4096 + bwBytes.length < 2 ^ 64 := by decide

theorem bw_code : CodeAt bwMem (natAdresse 4096) bwBytes := by
  apply codeAt_von bwMem 4096 bwBytes bw_laenge
  intro a h1 h2
  have hlen : bwBytes.length ≤ 128 := by decide
  have hd : ¬ (8192 ≤ a.toNat ∧ a.toNat < 8208) := by omega
  simp only [bwMem, bwCode, bwDaten, bwMemBytes, decide_eq_true_eq, decide_eq_false_iff_not]
  exact ⟨⟨h1, h2⟩, hd, by rw [if_pos ⟨h1, h2⟩]⟩

theorem bw_worldRep : WorldRep pwL bwMem pwSigma := by
  intro t k f a h
  cases t; cases f
  simp only [pwL] at h
  by_cases e1 : k = 0
  · rw [if_pos e1] at h
    cases h
    subst e1
    refine ⟨by decide, by decide, by decide, fun lo hi hT => ?_⟩
    cases hT
    unfold RepSlot
    decide
  · rw [if_neg e1] at h
    by_cases e2 : k = 1
    · rw [if_pos e2] at h
      cases h
      subst e2
      refine ⟨by decide, by decide, by decide, fun lo hi hT => ?_⟩
      cases hT
      unfold RepSlot
      decide
    · rw [if_neg e2] at h; cases h

theorem bw_envRepr : EnvRepr pwEnv30 (bwStart 30).register (abbOf cwCfg) :=
  cw_envRepr

theorem bw_rip : (bwStart 30).rip = natAdresse cwCfg.codeBase := rfl

/-- `x = 30`: both stores happen, rows 0 and 1 become 35 --
    the REAL `execBlock` run, which changes memory. -/
theorem bw_quelle : ∃ σ' ρ', execBlock pwO 0 pwR bwBody pwSigma pwEnv30 = .ok σ' ρ' ∧
    (σ'.slots () 0 ()).n = 35 ∧ (σ'.slots () 1 ()).n = 35 :=
  ⟨_, _, rfl, rfl, rfl⟩

/-! ## Poison probes: every refusal fires on concrete data. -/

/-- A single assignment is not the proved two-assignment shape. -/
theorem bwProbe_form1 : istZweiZuweisung cwBody = false := rfl

/-- The empty block is not the proved shape. -/
theorem bwProbe_formNil :
    istZweiZuweisung (Block.nil : Block pwD pwV false pwCtx [] []) = false := rfl

/-- A block with a check is not two plain assignments. -/
theorem bwProbe_formPruef : istZweiZuweisung pwSrc = false := rfl

/-- A tampered candidate (one byte prepended) is not recomputed. -/
theorem bwProbe_bytes : validate cwCfg pwL [] bwBody (0 :: bwBytes) = false := by decide

/-- Planted refusal: the shape gate fires inside the joint validator. -/
theorem bwProbe_formRuf : rufBlockOk rufWitBelegung rufWitRahmen 7 false cwCfg pwL
    cwBody bwBytes = false :=
  rufBlockOk_verweigert_form _ _ _ _ _ _ _ _ bwProbe_form1

/-- Planted refusal: a call that uses the red zone is not admitted. -/
theorem bwProbe_rot : rufBlockOk rufWitBelegung rufWitRahmen 7 true cwCfg pwL
    bwBody bwBytes = false :=
  rufBlockOk_verweigert_rot _ _ _ _ _ _ _

/-- Planted refusal: tampered bytes are refused inside the joint validator. -/
theorem bwProbe_bytesRuf : rufBlockOk rufWitBelegung rufWitRahmen 7 false cwCfg pwL
    bwBody (0 :: bwBytes) = false :=
  rufBlockOk_verweigert_bytes _ _ _ _ _ _ _ _ bwProbe_bytes

/-- JOINT WITNESS for `zweiRuf_korrekt`: every premise holds jointly
    on concrete values -- the admitted seven-argument frame, the
    disjoint working registers, the validated two-assignment callee
    bytes, the code region, the represented world and environment, the
    reached source run (rows 0 and 1 turn from 7 and 9 to 35), the
    reached byte run with every callee-saved register preserved --
    beside the reached frame saves, whose result byte observably
    changes, and the reloaded argument word. The program is
    non-degenerate: `pwV` writes its table (`pwHw`), and both the
    source run and the frame saves change memory. -/
theorem zweiRuf_korrekt_zeuge :
    pwV.schreibt () = true ∧
    rufOk rufWitBelegung rufWitRahmen 7 false = true ∧
    calleeFremd cwCfg = true ∧
    rufBlockOk rufWitBelegung rufWitRahmen 7 false cwCfg pwL
      bwBody bwBytes = true ∧
    LayoutSep pwL ∧
    CodeAt (bwStart 30).speicher (natAdresse cwCfg.codeBase) bwBytes ∧
    (bwStart 30).rip = natAdresse cwCfg.codeBase ∧
    WorldRep pwL (bwStart 30).speicher pwSigma ∧
    EnvRepr pwEnv30 (bwStart 30).register (abbOf cwCfg) ∧
    (∃ σ' ρ', execBlock pwO 0 pwR bwBody pwSigma pwEnv30 = .ok σ' ρ' ∧
      (σ'.slots () 0 ()).n = 35 ∧ (σ'.slots () 1 ()).n = 35) ∧
    (∃ n s', laufBytes n (bwStart 30) = .weiter s' ∧
      s'.rip = natAdresse (cwCfg.codeBase + bwBytes.length) ∧
      (∀ q, q ∈ calleeGerettet → s'.register q = (bwStart 30).register q)) ∧
    speicherZeuge.bytes (rufWitRahmen.schlitzAddr 0) ≠
      rufWitM1.bytes (rufWitRahmen.schlitzAddr 0) ∧
    ladeWort rufWitM2 rufWitRahmen 7 = some 42 := by
  obtain ⟨σW, ρW, hok, h35a, h35b⟩ := bw_quelle
  obtain ⟨-, n, s', hrun, hripW, -, -, hcallee⟩ :=
    zweiRuf_korrekt rufWitBelegung rufWitRahmen 7 false cwCfg pwL
      () () pwIdx0 pwWert0 pwHw pwHL () () pwIdx1 pwWert0 pwHw pwHL bwBytes bw_rufBlock
      pw_layoutSep cw_fremd pwO 0 pwR pwSigma pwEnv30 (bwStart 30) bw_code bw_rip
      bw_worldRep bw_envRepr σW ρW hok
  exact ⟨pwHw, rufWit_ok, cw_fremd, bw_rufBlock, pw_layoutSep, bw_code, bw_rip,
    bw_worldRep, bw_envRepr, ⟨σW, ρW, hok, h35a, h35b⟩, ⟨n, s', hrun, hripW, hcallee⟩,
    rufWit_wechselt, rufWit_rundreise⟩

/- CUTS (exactly what is NOT proved here):
   Proved here (all over the REUSED canonical vocabulary and the accepted
   `Stapel`, `Pipeline`, `PipelineCalls`, `PipelineCallsExec` and
   `PipeBlock` theorems -- no new machine, no new decoder row, no second
   source interpreter):
   - the joint validator `rufBlockOk` (admitted caller frame `rufOk`,
     two-assignment shape `istZweiZuweisung`, recomputed bytes
     `validate` with no certificates) with its unpacking
     (`rufBlockOk_teile`);
   - red-zone, shape and byte refusals (`rufBlockOk_verweigert_rot`,
     `rufBlockOk_verweigert_form`, `rufBlockOk_verweigert_bytes`) with
     planted probes on every path (single assignment, empty block,
     checked block, red-zone use, tampered bytes);
   - callee correctness (`zweiRuf_korrekt`): from an admitted frame and
     validated bytes of TWO source assignments, the fetched byte run
     reaches the end of the code with the world of the REAL `execBlock`
     run represented, the environment represented, and every
     callee-saved register preserved. Per-chunk runs are DERIVED
     (`einzelChunk_lauf`: value code plus address materialisation plus
     store, keeping the environment and every register off the working
     set); the target composition is lane 1195's run chain
     (`KetteLauf`, `ketteLauf_lauf`); the source outcome is inverted
     from the real `execBlock` (constant indices via `constInt?_sound`,
     two `schreibSlot` steps). Lane 1211 (`PipelineChunkDerive`) is not
     merged; nothing here assumes its chunk premises.
   - a joint memory-changing witness (`zweiRuf_korrekt_zeuge`): the
     source run turns rows 0 and 1 from 7 and 9 to 35, the frame saves
     turn the result byte, the byte run preserves all six callee-saved
     registers.
   NOT proved here, and not claimed:
   - Only TWO straight-line slot assignments per callee body: longer
     blocks, `ite`, checks, loops, calls, gates, floats and everything
     else are REFUSED (`istZweiZuweisung`, `rufBlockOk_verweigert_form`,
     `bwProbe_form1`, `bwProbe_formNil`, `bwProbe_formPruef`), never
     guessed. Three-or-more-statement callee bodies stay OPEN.
   - No optimiser certificates: `rufBlockOk` fixes `certs = []`, since
     a certificate could rewrite the body away from the proved shape
     (`optimise_nil` pins the identity). Certified-optimised callee
     bodies stay OPEN.
   - No TSO/store-buffer/GX bridge: every fact is sequential over one
     canonical `Speicher`; the per-access target-to-W/GX simulation
     stays OPEN.
   - No callee-saved push/pop code is emitted or verified here;
     preservation holds because the proved chunks never touch a
     callee-saved register (`calleeFremd`), not because spills are
     modelled.
   - No silicon correspondence beyond the accepted producers; no
     loader, entry, relocation, cost or time claim.
-/

#print axioms istZweiZuweisung
#print axioms rufBlockOk
#print axioms rufBlockOk_teile
#print axioms rufBlockOk_verweigert_rot
#print axioms rufBlockOk_verweigert_form
#print axioms rufBlockOk_verweigert_bytes
#print axioms zweiRuf_korrekt
#print axioms bwBody
#print axioms bwProg
#print axioms bwBytes
#print axioms bw_zwei
#print axioms bw_rufBlock
#print axioms bwMemBytes
#print axioms bwMem
#print axioms bwStart
#print axioms bw_laenge
#print axioms bw_code
#print axioms bw_worldRep
#print axioms bw_envRepr
#print axioms bw_rip
#print axioms bw_quelle
#print axioms bwProbe_form1
#print axioms bwProbe_formNil
#print axioms bwProbe_formPruef
#print axioms bwProbe_bytes
#print axioms bwProbe_formRuf
#print axioms bwProbe_rot
#print axioms bwProbe_bytesRuf
#print axioms zweiRuf_korrekt_zeuge

end Gabbro.Grammatik.X86.PipelineCallsBlock
