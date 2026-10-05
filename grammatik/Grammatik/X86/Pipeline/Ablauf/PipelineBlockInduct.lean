/-
  File:      Grammatik/X86/PipelineBlockInduct.lean
  Subject:   Block-size induction over multi-statement pipeline blocks
             (lane 1195).

  Follow-up of lanes 1165 (work transfer), 1189 (calls) and 1191
  (spills): all prove single shallow assignment chunks. Here the
  chunks compose: a run chain (`KetteLauf`) over the lowered chunks
  induces the run over the concatenated block, and source budget to
  target work is additive over the chunks through the admitted
  `pipeSummary` (1165). Deep trees beyond scratch, branches and
  loops stay refused with named refusal theorems. Reuses `senkStmt`,
  `senkBlock_assign`, `pipeSummary`/`pipeSummary_expand`,
  `decodiertZu`, `Deckung`, `laufKosten_anhang_erfolg`,
  `arbeit_decodiert`, `lauf_anhang` and the `pw` witnesses unchanged.
  No second IR, no second interpreter, no optimiser edit. Rust is
  out of scope.
-/
import Grammatik.X86.Pipeline.Kern.Pipeline
import Grammatik.X86.Pipeline.Kern.PipelineWitnesses
import Grammatik.X86.Pipeline.Ablauf.PipelineWork
import Grammatik.X86.Kosten.DerivedWorkBound
import Grammatik.X86.Kosten.BudgetExecution
import Grammatik.X86.Hw.Grundlage.HardwareAssumptions
import Grammatik.X86.Quelle.ExpressionLowering

namespace Gabbro.Grammatik.X86.PipeBlock

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipelineWork

/-! ## 1. Run chains over statement chunks.

    A run chain says: each lowered chunk runs from the state the
    previous chunk reached. Block-size induction is induction on
    this chain. -/

/-- A run chain over statement chunks. -/
inductive KetteLauf : List (List Befehl) → Zustand → Zustand → Prop where
  | nil (s : Zustand) : KetteLauf [] s s
  | cons (p : List Befehl) (rest : List (List Befehl)) (s s₁ s₂ : Zustand)
    (hhead : lauf (decodiertZu p) s = some s₁)
    (htail : KetteLauf rest s₁ s₂) : KetteLauf (p :: rest) s s₂

/-- Decoding distributes over chunk concatenation. -/
theorem decodiertZu_append (p q : List Befehl) :
    decodiertZu (p ++ q) = decodiertZu p ++ decodiertZu q := by
  simp [decodiertZu]

/-- CHAIN INDUCTION (runs): a run chain over the chunks is the run
    over the flattened block. Every premise is used: `hhead` feeds
    the head step through `lauf_anhang`, `htail` the induction. -/
theorem ketteLauf_lauf (chunks : List (List Befehl)) (s s' : Zustand)
    (h : KetteLauf chunks s s') :
    lauf (decodiertZu chunks.flatten) s = some s' := by
  induction h with
  | nil s =>
    simp [decodiertZu, lauf]
  | cons p rest s s₁ s₂ hhead _ ih =>
    rw [List.flatten_cons, decodiertZu_append, lauf_anhang _ _ _ _ hhead]
    exact ih

/-- CHAIN INDUCTION (work): retired work over the flattened block is
    the sum of the chunk works. -/
theorem ketteLaenge_sum (chunks : List (List Befehl)) :
    targetWork chunks.flatten = (chunks.map targetWork).sum := by
  unfold targetWork
  rw [List.length_flatten]

/-! ## 2. Budget additivity: source budget to target work over chunks.

    `Deckung` is DERIVED (1165), never a premise of the lowering. Two
    covered chunks concatenate to a covered block at the SUM budget:
    with the admitted summary's honest zero spill/fence counts
    (`pipeSummary_expand`) the bound is purely additive. -/

/-- COVER APPEND: two covered chunks concatenate at the sum budget.
    Every premise is used: `h1`/`h2` bound the two works, `hk` names
    the sum bound, and the work equation splits it. -/
theorem deckung_append_pipe (n m : Nat) (xs ys : List Decodiert)
    (h1 : Deckung pipeSummary n xs) (h2 : Deckung pipeSummary m ys) :
    Deckung pipeSummary (n + m) (xs ++ ys) := by
  intro k hk
  rw [pipeSummary_expand] at hk
  cases hk
  have a := h1 _ (pipeSummary_expand n)
  have b := h2 _ (pipeSummary_expand m)
  have hlen : targetWork ((xs ++ ys).map (fun d => d.befehl)) =
      targetWork (xs.map (fun d => d.befehl)) +
        targetWork (ys.map (fun d => d.befehl)) := by
    simp [targetWork]
  rw [hlen]
  omega

/-- BLOCK DECKUNG (induction over the chunk list): every chunk covered
    at budget 1 gives the flattened block covered at the chunk count.
    The empty block is covered at zero by computation. -/
theorem blockDeckung_eins (chunks : List (List Befehl))
    (h : ∀ c ∈ chunks, Deckung pipeSummary 1 (decodiertZu c)) :
    Deckung pipeSummary chunks.length (decodiertZu chunks.flatten) := by
  induction chunks with
  | nil =>
    exact deckung_leer pipeSummary 0 (pipeSummary_expand 0)
  | cons p rest ih =>
    have hhead : Deckung pipeSummary 1 (decodiertZu p) :=
      h p List.mem_cons_self
    have htail : Deckung pipeSummary rest.length (decodiertZu rest.flatten) :=
      ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have hcat := deckung_append_pipe 1 rest.length _ _ hhead htail
    simp only [List.flatten_cons, List.length_cons]
    rw [decodiertZu_append]
    have heq : 1 + rest.length = rest.length + 1 := Nat.add_comm _ _
    rwa [heq] at hcat

/-- TIME APPEND: named-time aggregation over concatenated chunks is
    the sum of the chunk times (reused `laufKosten_anhang_erfolg`). -/
theorem zeit_append_pipe (prof : HardwareProfil) (p q : List Befehl)
    (t1 t2 : Nat)
    (h1 : laufKosten prof (decodiertZu p) = some t1)
    (h2 : laufKosten prof (decodiertZu q) = some t2) :
    laufKosten prof (decodiertZu (p ++ q)) = some (t1 + t2) := by
  rw [decodiertZu_append]
  exact laufKosten_anhang_erfolg prof _ _ t1 t2 h1 h2

/-! ## 3. Two-chunk block correctness.

    Two lowered-correct assignment chunks compose: the source
    `execBlock` over the two-statement block reaches the second
    world's update, the target `lauf` over the concatenated chunks
    reaches the second state, and budget/work/time are additive.
    The per-step hardware bounds feed the transfer bound, so every
    premise is used. -/

variable {D : Deklaration} {V : Vertrag D}

/-- TWO-CHUNK BLOCK CORRECTNESS: source run, target run, coverage,
    time and work compose over a two-statement block. -/
theorem block_zwei_korrekt (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t1 : D.Tab) (f1 : D.Feld t1)
    (i1 : Expr D Γ Λ (.index (D.count t1)))
    (e1 : Expr D Γ Λ (D.typ t1 f1))
    (hw1 : V.schreibt t1 = true) (hL1 : darf D t1 Λ)
    (t2 : D.Tab) (f2 : D.Feld t2)
    (i2 : Expr D Γ Λ (.index (D.count t2)))
    (e2 : Expr D Γ Λ (D.typ t2 f2))
    (hw2 : V.schreibt t2 = true) (hL2 : darf D t2 Λ)
    (p1 p2 : List Befehl)
    (hlow1 : senkStmt c L
      (Stmt.assignSlot (V := V) (l := l) t1 f1 i1 e1 hw1 hL1) = some p1)
    (hlow2 : senkStmt c L
      (Stmt.assignSlot (V := V) (l := l) t2 f2 i2 e2 hw2 hL2) = some p2)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ σ₁ σ₂ : World D) (ρ : Env D Γ)
    (hsrc1 : execStmt O passes R
      (Stmt.assignSlot (V := V) (l := l) t1 f1 i1 e1 hw1 hL1) σ ρ = .ok σ₁ ρ)
    (hsrc2 : execStmt O passes R
      (Stmt.assignSlot (V := V) (l := l) t2 f2 i2 e2 hw2 hL2) σ₁ ρ = .ok σ₂ ρ)
    (st st₁ st₂ : Zustand)
    (hrun1 : lauf (decodiertZu p1) st = some st₁)
    (hrun2 : lauf (decodiertZu p2) st₁ = some st₂)
    (n1 n2 t1' t2' B : Nat) (prof : HardwareProfil)
    (hdeck1 : Deckung pipeSummary n1 (decodiertZu p1))
    (hdeck2 : Deckung pipeSummary n2 (decodiertZu p2))
    (hcost1 : laufKosten prof (decodiertZu p1) = some t1')
    (hcost2 : laufKosten prof (decodiertZu p2) = some t2')
    (hb1 : ∀ dd ∈ decodiertZu p1,
      ∃ cc, schrittKosten prof dd = some cc ∧ cc ≤ B)
    (hb2 : ∀ dd ∈ decodiertZu p2,
      ∃ cc, schrittKosten prof dd = some cc ∧ cc ≤ B)
    (pos : Nat) :
    execBlock O passes R
      (Block.cons (Stmt.assignSlot (V := V) (l := l) t1 f1 i1 e1 hw1 hL1)
        (Block.cons (Stmt.assignSlot (V := V) (l := l) t2 f2 i2 e2 hw2 hL2)
          Block.nil)) σ ρ = .ok σ₂ ρ
    ∧ lauf (decodiertZu (p1 ++ p2)) st = some st₂
    ∧ Deckung pipeSummary (n1 + n2) (decodiertZu (p1 ++ p2))
    ∧ laufKosten prof (decodiertZu (p1 ++ p2)) = some (t1' + t2')
    ∧ targetWork (p1 ++ p2) = targetWork p1 + targetWork p2
    ∧ senkBlock c L pos
        (Block.cons (Stmt.assignSlot (V := V) (l := l) t1 f1 i1 e1 hw1 hL1)
          (Block.cons (Stmt.assignSlot (V := V) (l := l) t2 f2 i2 e2 hw2 hL2)
            Block.nil)) = some (p1 ++ p2)
    ∧ ∀ k, expandBound pipeSummary (n1 + n2) = some k →
        (t1' + t2') ≤ B * k := by
  have hsrc : execBlock O passes R
      (Block.cons (Stmt.assignSlot (V := V) (l := l) t1 f1 i1 e1 hw1 hL1)
        (Block.cons (Stmt.assignSlot (V := V) (l := l) t2 f2 i2 e2 hw2 hL2)
          Block.nil)) σ ρ = .ok σ₂ ρ := by
    simp [execBlock, hsrc1, hsrc2]
  have hrun : lauf (decodiertZu (p1 ++ p2)) st = some st₂ := by
    rw [decodiertZu_append, lauf_anhang _ _ _ _ hrun1]
    exact hrun2
  have hdeck : Deckung pipeSummary (n1 + n2) (decodiertZu (p1 ++ p2)) := by
    rw [decodiertZu_append]
    exact deckung_append_pipe n1 n2 _ _ hdeck1 hdeck2
  have hcost := zeit_append_pipe prof p1 p2 t1' t2' hcost1 hcost2
  have hwork : targetWork (p1 ++ p2) = targetWork p1 + targetWork p2 := by
    simp [targetWork]
  have hlow : senkBlock c L pos
        (Block.cons (Stmt.assignSlot (V := V) (l := l) t1 f1 i1 e1 hw1 hL1)
          (Block.cons (Stmt.assignSlot (V := V) (l := l) t2 f2 i2 e2 hw2 hL2)
            Block.nil)) = some (p1 ++ p2) := by
    rw [senkBlock_assign c L _ _ _ _ _ _ _ pos, hlow1]
    simp only
    rw [senkBlock_assign c L _ _ _ _ _ _ _ _, hlow2]
    simp only
    have hnil : ∀ pos' : Nat,
        senkBlock c L pos' (Block.nil : Block D V l Γ Λ Λ) = some [] :=
      fun _ => rfl
    rw [hnil]
    simp
  have hball : ∀ dd ∈ decodiertZu (p1 ++ p2),
      ∃ cc, schrittKosten prof dd = some cc ∧ cc ≤ B := by
    rw [decodiertZu_append]
    intro dd hd
    rcases List.mem_append.mp hd with hm | hm
    · exact hb1 dd hm
    · exact hb2 dd hm
  have htime : ∀ k, expandBound pipeSummary (n1 + n2) = some k →
      (t1' + t2') ≤ B * k :=
    budgetAusfuehrung_transfer pipeSummary prof _ _ _ _ hcost hball hdeck
  exact ⟨hsrc, hrun, hdeck, hcost, hwork, hlow, htime⟩

/-! ## 4. Refusals: deep trees, branches, loops, binds.

    Unsupported shapes are REFUSED (`none`), never guessed. The deep
    refusal connects scratch exhaustion to the statement level: the
    same index, layout and admission that accept the shallow witness
    chunk refuse the deep tree, so the refusal is from depth alone. -/

/-- Deep value: two nested additions over literals (type `.int 6 6`).
    Needs a scratch register past `tmp`. -/
def tiefWert1195 {Γ : Ctx} {Λ : List (Res pwD)} : Expr pwD Γ Λ (.int 6 6) :=
  .add (.add (.lit 1) (.lit 2)) (.lit 3)

/-- The deep value widened to the witness field type. -/
def tiefWertFeld1195 : Expr pwD pwCtx [] (pwD.typ () ()) :=
  .weiter (by decide) (by decide) tiefWert1195

/-- DEEP-TREE REFUSAL (generic): with no scratch register past `tmp`
    (`frei = []`) the deep tree lowers to nothing. Reuses the accepted
    `senkTief_verweigert_tief`; both premises are used. -/
theorem block_verweigert_tief (c : PipeCfg) {Γ : Ctx} {Λ : List (Res pwD)}
    (hfrei : c.frei = []) :
    senkWertT c (tiefWert1195 (Γ := Γ) (Λ := Λ)) = none := by
  unfold senkWertT
  rw [hfrei]
  exact senkTief_verweigert_tief _ _ _

/-- DEEP-TREE REFUSAL (statement level): the witness layout admits the
    slot, yet the deep value gives no chunk -- refused, not guessed. -/
theorem block_verweigert_tief_stmt :
    senkStmt pwCfg pwL
      (Stmt.assignSlot (V := pwV) (l := false) () ()
        pwIdx0 tiefWertFeld1195 pwHw pwHL) = none := by
  decide

/-- BRANCH REFUSAL: `onOption` case analysis has no chunk lowering --
    the statement matches the catch-all, never a guessed sequence. -/
theorem block_verweigert_verzweigung (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Int}
    (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ')
    (a : Block D V l Γ Λ Λ') :
    senkStmt c L (Stmt.onOption o p a) = none :=
  rfl

/-- LOOP REFUSAL (block level): a `retry` head gives no block lowering,
    so no concatenated block is produced for it. -/
theorem block_verweigert_schleife (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (rest : Block D V l Γ Λ Λ') (pos : Nat) :
    senkBlock c L pos
      (Block.cons (Stmt.retry 5 Expr.wahr Block.nil Block.nil) rest) = none :=
  rfl

/-- BIND REFUSAL (block level): a `bind` block has no lowering in this
    fragment -- refused, not unfolded into the block. -/
theorem block_verweigert_bind (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (rest : Block D V l (τ :: Γ) Λ Λ')
    (pos : Nat) :
    senkBlock c L pos (Block.bind e rest) = none :=
  rfl

/-! ## 5. Poison probes: every refusal fires on concrete data. -/

/-- The widened deep value has no lowering on the witness configuration. -/
theorem gift_block_tief_wert :
    senkWertT pwCfg tiefWertFeld1195 = none := by
  decide

/-- A `retry` head gives no block lowering on witness data. -/
theorem gift_block_schleife :
    senkBlock pwCfg pwL 0
      (Block.cons
        (Stmt.retry (V := pwV) 5 (Expr.wahr : Expr pwD pwCtx [] .bool)
          (Block.nil : Block pwD pwV true pwCtx [] [])
          (Block.nil : Block pwD pwV false pwCtx [] []))
        (Block.nil : Block pwD pwV false pwCtx [] [])) = none :=
  rfl

/-- A `bind` block has no lowering on witness data. -/
theorem gift_block_bind :
    senkBlock pwCfg pwL 0
      (Block.bind (Expr.lit 1 : Expr pwD pwCtx [] (.int 1 1))
        (Block.nil : Block pwD pwV false ((.int 1 1) :: pwCtx) [] [])) =
      none :=
  rfl

/-- An `onOption` branch has no chunk lowering on witness data. -/
theorem gift_block_verzweigung :
    senkStmt pwCfg pwL
      (Stmt.onOption (V := pwV) (l := false)
        (Expr.none 0 : Expr pwD pwCtx [] (.opt 0))
        (Block.nil : Block pwD pwV false ((.index 0) :: pwCtx) [] [])
        (Block.nil : Block pwD pwV false pwCtx [] [])) = none :=
  rfl

/-! ## 6. Joint witnesses: one table, real runs.

    Every witness below shares the accepted pipeline package
    (`PipePaket`/`pipePaket_hold` from lane 1165): one table its
    contract writes, a source `execBlock` run moving the slots
    `7 -> 35` and `9 -> 6`, and a fetched-byte run observably
    changing memory. -/

/-- Joint witness for the deep-tree refusals. -/
theorem block_verweigert_tief_zeuge :
    senkWertT pwCfg tiefWertFeld1195 = none ∧
    senkStmt pwCfg pwL
      (Stmt.assignSlot (V := pwV) (l := false) () ()
        pwIdx0 tiefWertFeld1195 pwHw pwHL) = none ∧
    PipePaket :=
  ⟨gift_block_tief_wert, block_verweigert_tief_stmt, pipePaket_hold⟩

/-- Joint witness for the branch refusal. -/
theorem block_verweigert_verzweigung_zeuge :
    ∃ (o : Expr pwD pwCtx [] (.opt 0))
      (p : Block pwD pwV false ((.index 0) :: pwCtx) [] [])
      (a : Block pwD pwV false pwCtx [] []),
      senkStmt pwCfg pwL (Stmt.onOption o p a) = none ∧ PipePaket := by
  refine ⟨(Expr.none 0 : Expr pwD pwCtx [] (.opt 0)),
    (Block.nil : Block pwD pwV false ((.index 0) :: pwCtx) [] []),
    (Block.nil : Block pwD pwV false pwCtx [] []), ?_, pipePaket_hold⟩
  exact block_verweigert_verzweigung _ _ _ _ _

/-- Joint witness for the loop refusal. -/
theorem block_verweigert_schleife_zeuge :
    ∃ (rest : Block pwD pwV false pwCtx [] []),
      senkBlock pwCfg pwL 0
        (Block.cons (Stmt.retry 5 (Expr.wahr : Expr pwD pwCtx [] .bool)
          (Block.nil : Block pwD pwV true pwCtx [] [])
          (Block.nil : Block pwD pwV false pwCtx [] [])) rest) = none ∧
      PipePaket := by
  refine ⟨(Block.nil : Block pwD pwV false pwCtx [] []), ?_, pipePaket_hold⟩
  exact block_verweigert_schleife _ _ _ _

/-- Joint witness for the bind refusal. -/
theorem block_verweigert_bind_zeuge :
    ∃ (e : Expr pwD pwCtx [] (.int 1 1))
      (rest : Block pwD pwV false ((.int 1 1) :: pwCtx) [] []),
      senkBlock pwCfg pwL 0 (Block.bind e rest) = none ∧ PipePaket := by
  refine ⟨(Expr.lit 1 : Expr pwD pwCtx [] (.int 1 1)),
    (Block.nil : Block pwD pwV false ((.int 1 1) :: pwCtx) [] []),
    ?_, pipePaket_hold⟩
  exact block_verweigert_bind _ _ _ _ _

/-- Witness statement: the first witness assignment. The two-chunk
    block runs it twice in a row. -/
def witStmt1195 : Stmt pwD pwV false pwCtx [] [] :=
  Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0 pwWert0 pwHw pwHL

/-- JOINT WITNESS for `block_zwei_korrekt`: every premise holds jointly
    on the witness declaration -- one table its contract writes, two
    reached one-step source runs, two target chunk runs over the
    five-instruction chunk, derived coverage and named time `8` with
    per-step bound `3` on both chunks -- and so do all seven
    conclusions, with the fetched-byte run observably changing
    memory (`PipePaket`). -/
theorem block_zwei_korrekt_zeuge :
    ∃ (σ₁ σ₂ : World pwD) (st₁ st₂ : Zustand),
      senkStmt pwCfg pwL witStmt1195 = some (pwProg.take 5) ∧
      senkStmt pwCfg pwL witStmt1195 = some (pwProg.take 5) ∧
      execStmt pwO 0 pwR witStmt1195 pwSigma pwEnv30 = .ok σ₁ pwEnv30 ∧
      execStmt pwO 0 pwR witStmt1195 σ₁ pwEnv30 = .ok σ₂ pwEnv30 ∧
      lauf (decodiertZu (pwProg.take 5)) (pwStart 30) = some st₁ ∧
      lauf (decodiertZu (pwProg.take 5)) st₁ = some st₂ ∧
      Deckung pipeSummary 1 (decodiertZu (pwProg.take 5)) ∧
      Deckung pipeSummary 1 (decodiertZu (pwProg.take 5)) ∧
      laufKosten profilZeuge (decodiertZu (pwProg.take 5)) = some 8 ∧
      laufKosten profilZeuge (decodiertZu (pwProg.take 5)) = some 8 ∧
      (∀ dd ∈ decodiertZu (pwProg.take 5),
        ∃ cc, schrittKosten profilZeuge dd = some cc ∧ cc ≤ 3) ∧
      (∀ dd ∈ decodiertZu (pwProg.take 5),
        ∃ cc, schrittKosten profilZeuge dd = some cc ∧ cc ≤ 3) ∧
      execBlock pwO 0 pwR
        (Block.cons witStmt1195 (Block.cons witStmt1195 Block.nil))
        pwSigma pwEnv30 = .ok σ₂ pwEnv30 ∧
      lauf (decodiertZu ((pwProg.take 5) ++ (pwProg.take 5)))
        (pwStart 30) = some st₂ ∧
      Deckung pipeSummary (1 + 1)
        (decodiertZu ((pwProg.take 5) ++ (pwProg.take 5))) ∧
      laufKosten profilZeuge
        (decodiertZu ((pwProg.take 5) ++ (pwProg.take 5))) = some (8 + 8) ∧
      targetWork ((pwProg.take 5) ++ (pwProg.take 5)) =
        targetWork (pwProg.take 5) + targetWork (pwProg.take 5) ∧
      senkBlock pwCfg pwL 0
        (Block.cons witStmt1195 (Block.cons witStmt1195 Block.nil)) =
        some ((pwProg.take 5) ++ (pwProg.take 5)) ∧
      (∀ k, expandBound pipeSummary (1 + 1) = some k → (8 + 8) ≤ 3 * k) ∧
      PipePaket := by
  obtain ⟨σ₁, hsrc1⟩ : ∃ σ₁, execStmt pwO 0 pwR witStmt1195 pwSigma pwEnv30 =
      .ok σ₁ pwEnv30 := ⟨_, rfl⟩
  obtain ⟨σ₂, hsrc2⟩ : ∃ σ₂, execStmt pwO 0 pwR witStmt1195 σ₁ pwEnv30 =
      .ok σ₂ pwEnv30 := ⟨_, rfl⟩
  obtain ⟨st₁, st₂, hrun1, hrun2⟩ : ∃ st₁ st₂,
      lauf (decodiertZu (pwProg.take 5)) (pwStart 30) = some st₁ ∧
      lauf (decodiertZu (pwProg.take 5)) st₁ = some st₂ :=
    ⟨_, _, rfl, rfl⟩
  have hdeck : Deckung pipeSummary 1 (decodiertZu (pwProg.take 5)) :=
    deckung_pipeChunk pwCfg pwL false () () pwIdx0 pwWert0 pwHT0
      pwHw pwHL 1 _ _ pw_senkWert0 pwChunkCast (Nat.le_refl 1)
  have hmain := block_zwei_korrekt pwCfg pwL () () pwIdx0 pwWert0 pwHw pwHL
    () () pwIdx0 pwWert0 pwHw pwHL _ _ pwChunkWit pwChunkWit pwO 0 pwR
    _ _ _ _ hsrc1 hsrc2 _ _ _ hrun1 hrun2 1 1 8 8 3 profilZeuge
    hdeck hdeck kosten_chunkWit kosten_chunkWit hb_chunkWit hb_chunkWit 0
  exact ⟨σ₁, σ₂, st₁, st₂, pwChunkWit, pwChunkWit, hsrc1, hsrc2, hrun1,
    hrun2, hdeck, hdeck, kosten_chunkWit, kosten_chunkWit, hb_chunkWit,
    hb_chunkWit, hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1,
    hmain.2.2.2.2.1, hmain.2.2.2.2.2.1, hmain.2.2.2.2.2.2, pipePaket_hold⟩

/- CUTS:
    - Proved here (generic): decoding distribution over chunks
      (`decodiertZu_append`); run-chain induction to the flattened
      block run (`ketteLauf_lauf`) and work sum (`ketteLaenge_sum`);
      coverage append at the sum budget (`deckung_append_pipe`,
      honest zero spill/fence through `pipeSummary_expand`);
      block coverage by induction over the chunk list
      (`blockDeckung_eins`); time append (`zeit_append_pipe`,
      reused `laufKosten_anhang_erfolg`); two-chunk block
      correctness (`block_zwei_korrekt`: source `execBlock` run,
      target `lauf` run, coverage, time, work, the `senkBlock`
      lowering equation via reused `senkBlock_assign`, and the
      time-transfer bound through reused
      `budgetAusfuehrung_transfer`); four refusals (deep tree
      beyond scratch at value and statement level, `onOption`
      branch, `retry` loop head, `bind` block); four poison probes
      firing by computation; joint non-degenerate witnesses for
      every syntax-premise theorem (one table its contract writes;
      reached source steps; target chunk runs; fetched-byte run
      observably changing memory via reused `PipePaket`).
    - Reused, not duplicated: `senkStmt`, `senkBlock_assign`,
      `senkTief_verweigert_tief`, `pipeSummary`/`pipeSummary_expand`,
      `decodiertZu`, `Deckung`, `lauf_anhang`,
      `laufKosten_anhang_erfolg`, `arbeit_decodiert`,
      `budgetAusfuehrung_transfer`, and the whole `pw` witness
      package with its chunk/cost facts.
    - OPEN (per-chunk derivation): each chunk run premise
      (`hsrc`, `hrun`, `hdeck`) is ASSUMED here; deriving it from
      the lowering alone stays with `senkBlock_korrekt` /
      `pipeline_correct` (reused as black boxes, never
      re-proved). No WorldRep threading is claimed here beyond
      what the assumed runs carry.
    - OPEN (n-chunk source blocks): target/budget induction is over
      the chunk list; the dependent source `Block` chain beyond
      two `assignSlot` conses (mixed `Λ` threading, checks,
      branches) composes through `senkBlock_korrekt`, not here.
    - OPEN (entry/image): admission beyond the concatenated chunks
      (mapping, entry sequence, ABI duties, guards) composes
      through `PipelineImage`/`PipelineEntry`; no TSO/concurrency
      claim; named timing stays a hardware assumption; `forever`
      loops and calls hit the same catch-all arms (stated in
      prose, no theorem).
    - No second IR, no second interpreter, no optimiser edit, no
      weakened guarantee: unsupported shapes are refused, never
      guessed.
-/

#print axioms decodiertZu_append
#print axioms ketteLauf_lauf
#print axioms ketteLaenge_sum
#print axioms deckung_append_pipe
#print axioms blockDeckung_eins
#print axioms zeit_append_pipe
#print axioms block_zwei_korrekt
#print axioms tiefWert1195
#print axioms tiefWertFeld1195
#print axioms block_verweigert_tief
#print axioms block_verweigert_tief_stmt
#print axioms block_verweigert_verzweigung
#print axioms block_verweigert_schleife
#print axioms block_verweigert_bind
#print axioms gift_block_tief_wert
#print axioms gift_block_schleife
#print axioms gift_block_bind
#print axioms gift_block_verzweigung
#print axioms block_verweigert_tief_zeuge
#print axioms block_verweigert_verzweigung_zeuge
#print axioms block_verweigert_schleife_zeuge
#print axioms block_verweigert_bind_zeuge
#print axioms witStmt1195
#print axioms block_zwei_korrekt_zeuge

end Gabbro.Grammatik.X86.PipeBlock
