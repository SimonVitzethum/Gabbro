/-
  File:      Grammatik/X86/PipelineCallsN.lean
  Subject:   Pipeline calls with three-or-more-statement callee bodies.

  Follow-up of `PipelineCallsExec` (single-assignment callee bodies):
  callee bodies that are chains of three or more `assignSlot` statements
  are lowered, validated and run, by induction on the body, with
  callee-saved preservation across the WHOLE body under the decided
  `calleeFremd` disjointness. Shorter bodies, non-assignment statements
  and everything else are REFUSED, never guessed.

  Reused, not duplicated: `Pipeline` (`senkBlock_assign`, `senkWertT`,
  `senkWertT_gerade`, `einzelChunk`-level `assignT_lauf` shape via
  `PipelineCallsExec.einzelChunk_lauf`, `worldRep_store`,
  `lauf_zu_laufBytes`, `validate_sound`, `repOk_int`, `constInt?_sound`),
  `PipelineCalls` (`rufOk`, `calleeGerettet`, `pipeline_ruf_verweigert_rot`,
  `rufWit*` frame witnesses), `PipelineCallsExec` (`rufExecOk_teile`
  shape, `calleeFremd`, `calleeFremd_mem`, `cwCfg`, `cw_fremd`,
  `cw_cfgOk`), `PipelineWitnesses` (`pwD`, `pwV`, `pwL`, `pwO`, `pwR`,
  `pwCtx`, `pwIdx0/1`, `pwWert0`, `pwHw/HL`, `pw_layoutSep`,
  `pw_cfgOk`-style facts), `PipelineBlockInduct` (`KetteLauf`,
  `ketteLauf_lauf`). No second machine, no second loader, no source
  claim beyond the proved fragment. Rust is out of scope.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineCalls
import Grammatik.X86.PipelineCallsExec
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineBlockInduct

namespace Gabbro.Grammatik.X86.PipelineCallsN

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineCalls
open Gabbro.Grammatik.X86.PipelineCallsExec
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeBlock
open Gabbro.Grammatik.X86.OptimizationRules

variable {D : Deklaration}

variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-! ## 1. Shape: all-assignment blocks of three or more statements.

    `istEinzelZuweisung` (one body, `PipelineCallsExec`) and the refused
    longer bodies are generalised here: `istAssignBlock` holds exactly
    when every statement is an `assignSlot`; `istDreiPlus` adds the
    three-statement floor. One- and two-statement bodies are refused HERE
    (they stay with the earlier validators); this validator covers three
    or more. -/

/-- A statement is a slot assignment (nothing else). -/
def istAssignStmt {Λ₁ Λ₂ : List (Res D)} (s : Stmt D V l Γ Λ₁ Λ₂) : Bool :=
  match s with
  | .assignSlot _ _ _ _ _ _ => true
  | _ => false

/-- A block is all slot assignments (nil counts as all-assignment). -/
def istAssignBlock {Λ₁ Λ₂ : List (Res D)} : Block D V l Γ Λ₁ Λ₂ → Bool
  | .nil => true
  | .cons s rest => istAssignStmt s && istAssignBlock rest
  | _ => false

/-- The number of `cons` statements of a block (`nil` is 0; any other
    non-`cons` form ends the count at 0, so only `cons` chains count). -/
def blockLaenge {Λ₁ Λ₂ : List (Res D)} : Block D V l Γ Λ₁ Λ₂ → Nat
  | .nil => 0
  | .cons _ rest => blockLaenge rest + 1
  | _ => 0

/-- THREE OR MORE: every statement an assignment, at least three of them. -/
def istDreiPlus {Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Bool :=
  istAssignBlock b && decide (3 ≤ blockLaenge b)

/-- THE CALL-N VALIDATOR: the caller frame is admitted (`rufOk`: layout
    fit, exact stack-arg count, six callee-save words, no red zone), the
    callee body has the proved three-or-more-assignment shape, and the
    candidate bytes are what the Lean pipeline recomputes from the source
    (`validate` with no optimiser certificates: a certificate could
    rewrite the body away from the proved shape). -/
def rufExecN (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (c : PipeCfg) (L : Layout D)
    {Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte) : Bool :=
  rufOk b r nArgs benutztRot && istDreiPlus body &&
    validate c L [] body bytes

/-- Unpacking the call-N validator: frame, shape and recomputed bytes.
    Every premise is used: each conjunct feeds one conclusion. -/
theorem rufExecN_teile (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (c : PipeCfg) (L : Layout D)
    {Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : rufExecN b r nArgs benutztRot c L body bytes = true) :
    rufOk b r nArgs benutztRot = true ∧ istDreiPlus body = true ∧
      validate c L [] body bytes = true := by
  unfold rufExecN at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## 2. Refusals: everything outside the three-or-more-assignment shape.

    Shorter bodies (nil, one, two statements -- the earlier validators'
    scope), non-assignment statements anywhere in the body, red-zone
    use and candidate bytes the Lean pipeline does not recompute are
    all refused loudly. -/

/-- SHAPE REFUSAL (non-assignment): a body containing a non-assignment
    statement is not the proved shape. -/
theorem istDreiPlus_verweigert_form {Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (h : istAssignBlock body = false) :
    istDreiPlus body = false := by
  unfold istDreiPlus
  rw [h, Bool.false_and]

/-- LENGTH REFUSAL (short body): fewer than three statements are not
    the proved shape (nil, one and two stay with the earlier validators). -/
theorem istDreiPlus_verweigert_kurz {Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (h : blockLaenge body < 3) :
    istDreiPlus body = false := by
  unfold istDreiPlus
  have hd : decide (3 ≤ blockLaenge body) = false :=
    (decide_eq_false_iff_not).mpr (by omega)
  rw [hd]
  cases istAssignBlock body <;> rfl

/-- RED-ZONE USE REFUSAL: no call that uses the red zone is admitted. -/
theorem rufExecN_verweigert_rot (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (c : PipeCfg) (L : Layout D)
    {Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte) :
    rufExecN b r nArgs true c L body bytes = false := by
  unfold rufExecN
  rw [pipeline_ruf_verweigert_rot]
  rfl

/-- SHAPE REFUSAL: a body that is not all assignments is refused loudly. -/
theorem rufExecN_verweigert_form (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (c : PipeCfg) (L : Layout D)
    {Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : istAssignBlock body = false) :
    rufExecN b r nArgs benutztRot c L body bytes = false := by
  unfold rufExecN
  have hd := istDreiPlus_verweigert_form body h
  rw [hd]
  cases rufOk b r nArgs benutztRot <;> cases validate c L [] body bytes <;> rfl

/-- LENGTH REFUSAL: a body of fewer than three statements is refused loudly. -/
theorem rufExecN_verweigert_kurz (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (c : PipeCfg) (L : Layout D)
    {Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : blockLaenge body < 3) :
    rufExecN b r nArgs benutztRot c L body bytes = false := by
  unfold rufExecN
  have hd := istDreiPlus_verweigert_kurz body h
  rw [hd]
  cases rufOk b r nArgs benutztRot <;> cases validate c L [] body bytes <;> rfl

/-- BYTE REFUSAL: candidate bytes the Lean pipeline does not recompute
    are refused loudly. -/
theorem rufExecN_verweigert_bytes (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (c : PipeCfg) (L : Layout D)
    {Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : validate c L [] body bytes = false) :
    rufExecN b r nArgs benutztRot c L body bytes = false := by
  unfold rufExecN
  rw [h]
  cases rufOk b r nArgs benutztRot <;> cases istDreiPlus body <;> rfl

/-! ## 3. Body induction: run, world, environment, callee-saved
    preservation and straight-line code across the whole body. -/

/-- Splitting the shape conjunction of a `cons` block (no casing:
    the `cons` equation of `istAssignBlock` rewrites under `simp`). -/
theorem istAssignBlock_cons_inv {Λ₂ Λ₃ : List (Res D)}
    (s : Stmt D V l Γ Λ₂ Λ₃) (rest : Block D V l Γ Λ₃ Λ')
    (h : istAssignBlock (.cons s rest) = true) :
    istAssignStmt s = true ∧ istAssignBlock rest = true := by
  simpa [istAssignBlock, Bool.and_eq_true] using h

/-- SINGLE-CHUNK RUN with callee-saved preservation: the reused
    single-chunk run (`einzelChunk_lauf`) never touches a working
    register outside `dst`/`adr`/`tmp :: frei`, so under the decided
    `calleeFremd` disjointness every callee-saved register survives the
    chunk. Every premise is consumed. -/
theorem assignChunkN_lauf (c : PipeCfg) (hc : cfgOk c = true)
    (hfremd : calleeFremd c = true)
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) {lo hi : Int} (hτ : τ = .int lo hi)
    (hlo : 0 ≤ lo) (hhi : hi < 2 ^ 64) (pv : List Befehl)
    (hp : senkWertT c e = some pv) (A : Nat)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hE : EnvRepr ρ s.register (abbOf c))
    (hwr : schreibbar8 s.speicher (natAdresse A) = true) :
    ∃ s', lauf ((pv ++ [Befehl.movImm64 c.adr (natAdresse A),
        Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]).map kanon) s = some s' ∧
      write64 s.speicher (natAdresse A)
        (zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi))) =
        some s'.speicher ∧
      EnvRepr ρ s'.register (abbOf c) ∧
      (∀ q, q ∈ calleeGerettet → s'.register q = s.register q) := by
  obtain ⟨s', hrun, hw, hE', hreg⟩ :=
    einzelChunk_lauf c hc e hτ hlo hhi pv hp A ρ σ₀ σ s hE hwr
  refine ⟨s', hrun, hw, hE', fun q hq => ?_⟩
  obtain ⟨hne1, hne2, hne3⟩ := calleeFremd_mem c hfremd q hq
  exact hreg q hne1 hne2 hne3

/-- BODY INDUCTION, fuel version (fuel is `sizeOf b`; the recursive
    call runs on the tail with strictly smaller size). `Block` is
    mutually inductive, so the `induction` tactic does not apply to it
    directly -- induction runs on the fuel and `cases` splits the block
    (the `rumpfBlock_total_aux` pattern, reused). -/
theorem assignBlockN_lauf_aux (c : PipeCfg) (hc : cfgOk c = true) (L : Layout D)
    (hsep : LayoutSep L) (hfremd : calleeFremd c = true)
    (O : Orakel D) (passes : Nat)
    (R : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (ρ : Env D Γ) (n : Nat) :
    ∀ (b : Block D V l Γ Λ Λ) (pos : Nat) (prog : List Befehl)
      (σ : World D) (st : Zustand) (σ' : World D) (ρ' : Env D Γ),
    sizeOf b ≤ n → istAssignBlock b = true →
    senkBlock c L pos b = some prog →
    WorldRep L st.speicher σ → EnvRepr ρ st.register (abbOf c) →
    execBlock O passes R b σ ρ = .ok σ' ρ' →
    ∃ s', lauf (prog.map kanon) st = some s' ∧
      WorldRep L s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf c) ∧
      (∀ q, q ∈ calleeGerettet → s'.register q = st.register q) ∧
      prog.all gerade = true := by
  induction n with
  | zero =>
    intro b pos prog σ st σ' ρ' hle hassign hlow hW hE hsrc
    cases b
    case nil =>
      simp only [senkBlock, Option.some.injEq] at hlow
      subst hlow
      simp only [execBlock] at hsrc
      cases hsrc
      exact ⟨st, by simp [lauf], hW, hE, fun _ _ => rfl, rfl⟩
    case cons s rest =>
      simp only [Block.cons.sizeOf_spec] at hle
      omega
    all_goals
      simp [istAssignBlock] at hassign
  | succ n ih =>
    intro b pos prog σ st σ' ρ' hle hassign hlow hW hE hsrc
    cases b
    case nil =>
      simp only [senkBlock, Option.some.injEq] at hlow
      subst hlow
      simp only [execBlock] at hsrc
      cases hsrc
      exact ⟨st, by simp [lauf], hW, hE, fun _ _ => rfl, rfl⟩
    case cons s rest =>
      have hle' : sizeOf rest ≤ n := by
        simp only [Block.cons.sizeOf_spec] at hle
        omega
      obtain ⟨h1, hrest⟩ := istAssignBlock_cons_inv s rest hassign
      cases s with
      | assignSlot t f i e hw hL =>
        rw [senkBlock_assign] at hlow
        cases hs : senkStmt c L (Stmt.assignSlot (V := V) t f i e hw hL) with
        | none =>
          rw [hs] at hlow
          cases hlow
        | some p =>
          rw [hs] at hlow
          dsimp only at hlow
          cases hq : senkBlock c L (pos + (encodeAll p).length) rest with
          | none =>
            simp [hq] at hlow
          | some q =>
            simp only [hq] at hlow
            simp only [Option.map_some, Option.some.injEq] at hlow
            subst hlow
            simp only [senkStmt] at hs
            cases hk : constInt? i with
            | none =>
              simp [hk] at hs
            | some k =>
              simp only [hk] at hs
              cases hA : L.loc t k f with
              | none =>
                simp [hA] at hs
              | some A =>
                simp only [hA] at hs
                by_cases hok : repOk (D.typ t f) A 8 0 = true
                · rw [if_pos hok] at hs
                  cases hv : senkWertT c e with
                  | none =>
                    simp [hv] at hs
                  | some pv =>
                    simp only [hv] at hs
                    simp only [Option.map_some, Option.some.injEq] at hs
                    subst hs
                    obtain ⟨lo, hi, hT, hlo, hhi, -⟩ := repOk_int _ A hok
                    let σL := σ.lese Λ (i.orte ++ e.orte)
                    have hki : (eval σL i σL ρ).n = k := by
                      have hci := constInt?_sound i σL σL ρ k hk
                      simpa [intOf] using hci
                    have hsrcEq : execBlock O passes R
                        (.cons (.assignSlot t f i e hw hL) rest) σ ρ =
                        execBlock O passes R rest
                          (σL.schreibSlot t Λ k f (eval σL e σL ρ)) ρ := by
                      rw [← hki]
                      rfl
                    rw [hsrcEq] at hsrc
                    obtain ⟨-, -, hwrA, -⟩ := hW t k f A hA
                    obtain ⟨s1, hrun1, hw1, hE1, hcallee1⟩ :=
                      assignChunkN_lauf c hc hfremd e hT hlo hhi pv hv A ρ σL σL st hE hwrA
                    have hW1 : WorldRep L s1.speicher
                        (σL.schreibSlot t Λ k f (eval σL e σL ρ)) :=
                      worldRep_store L hsep st.speicher s1.speicher σL t k f A hA hW lo hi hT
                        _ hw1 Λ
                    obtain ⟨s2, hrun2, hW2, hE2, hcallee2, hger2⟩ :=
                      ih rest _ q _ _ _ _ hle' hrest hq hW1 hE1 hsrc
                    have hrun : lauf (((pv ++ [Befehl.movImm64 c.adr (natAdresse A),
                        Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]) ++ q).map kanon)
                        st = some s2 := by
                      rw [List.map_append, lauf_anhang _ _ _ _ hrun1]
                      exact hrun2
                    have hcallee : ∀ q, q ∈ calleeGerettet →
                        s2.register q = st.register q := by
                      intro q hqmem
                      rw [hcallee2 q hqmem, hcallee1 q hqmem]
                    have hger : ((pv ++ [Befehl.movImm64 c.adr (natAdresse A),
                        Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]) ++ q).all gerade =
                        true := by
                      simp only [List.all_append, Bool.and_eq_true]
                      refine ⟨⟨senkWertT_gerade c e pv hv, ?_⟩, hger2⟩
                      simp [gerade]
                    exact ⟨s2, hrun, hW2, hE2, hcallee, hger⟩
                · rw [if_neg hok] at hs
                  cases hs
      | assignDurch p t ht f i e hw hL => simp [istAssignStmt] at h1
      | assignGlob g e hw hL => simp [istAssignStmt] at h1
      | schreibBytes t f hf n i hlo hhi e hw hL => simp [istAssignStmt] at h1
      | assignVar x e => simp [istAssignStmt] at h1
      | uebergang t f hτ i von nach hn he hw hL => simp [istAssignStmt] at h1
      | ite c t e => simp [istAssignStmt] at h1
      | onOption o p a => simp [istAssignStmt] at h1
      | onTag v arms => simp [istAssignStmt] at h1
      | onGrund r arms => simp [istAssignStmt] at h1
      | call f args hp hr => simp [istAssignStmt] at h1
      | callInd p args hp hr => simp [istAssignStmt] at h1
      | locks L0 hr body => simp [istAssignStmt] at h1
      | breaking i body => simp [istAssignStmt] at h1
      | traverse t inv body => simp [istAssignStmt] at h1
      | retry n bis body ueberlauf => simp [istAssignStmt] at h1
      | forever a inv body => simp [istAssignStmt] at h1
      | axiomCall a args h hw hg hd hgd => simp [istAssignStmt] at h1
      | regSchreib r hk e => simp [istAssignStmt] at h1
      | transition r hk m hm hl maske bits => simp [istAssignStmt] at h1
      | publish g e payload hp hw hL => simp [istAssignStmt] at h1
      | advances m a h hs => simp [istAssignStmt] at h1
      | retires m s0 h a => simp [istAssignStmt] at h1
      | ret e hΛ => simp [istAssignStmt] at h1
      | retGrund r hΛ => simp [istAssignStmt] at h1
      | leave h => simp [istAssignStmt] at h1
      | next h => simp [istAssignStmt] at h1
    all_goals
      simp [istAssignBlock] at hassign

/-- BODY INDUCTION (fuel-free): an all-assignment body with an accepted
    lowering runs to the world of the REAL `execBlock` run with the
    environment represented, every callee-saved register preserved
    across the whole body, and straight-line code. Fuel is `sizeOf b`.
    Every premise is consumed through the fuel version. -/
theorem assignBlockN_lauf (c : PipeCfg) (hc : cfgOk c = true) (L : Layout D)
    (hsep : LayoutSep L) (hfremd : calleeFremd c = true)
    (O : Orakel D) (passes : Nat)
    (R : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ) (pos : Nat) (prog : List Befehl)
    (σ : World D) (st : Zustand) (σ' : World D) (ρ' : Env D Γ) :
    istAssignBlock b = true →
    senkBlock c L pos b = some prog →
    WorldRep L st.speicher σ → EnvRepr ρ st.register (abbOf c) →
    execBlock O passes R b σ ρ = .ok σ' ρ' →
    ∃ s', lauf (prog.map kanon) st = some s' ∧
      WorldRep L s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf c) ∧
      (∀ q, q ∈ calleeGerettet → s'.register q = st.register q) ∧
      prog.all gerade = true := by
  intro hassign hlow hW hE hsrc
  exact assignBlockN_lauf_aux c hc L hsep hfremd O passes R ρ (sizeOf b) b pos prog σ st σ'
    ρ' (Nat.le_refl _) hassign hlow hW hE hsrc

/- CUTS (exactly what is NOT proved here):
   - Skeleton only: shape predicates, validator, induction, witness
     and refusals all stay OPEN in this skeleton commit.
-/

#print axioms rufOk
#print axioms calleeFremd

end Gabbro.Grammatik.X86.PipelineCallsN
