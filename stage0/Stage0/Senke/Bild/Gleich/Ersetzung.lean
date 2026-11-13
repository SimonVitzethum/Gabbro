/-
  File:      stage0/Stage0/Senke/Bild/Gleich/Ersetzung.lean
  Subject:   **Handler substitution up to read events** (package P1 of the closed calls of the image theorem). Two
             handlers related on `≈` worlds (`HandlerLG Er R₁ R₂`) under a read-blind oracle (`Leseblind O`) give,
             from `≈` worlds and the same environment, related runs of every statement, block and terminal block
             (`execStmt_lg`, `execBlock_lg`, `execEnd_lg`): the same outcome shape with `≈` worlds and equal values,
             unless the run under `R₁` fails early with a mark in `Er`. The proof is one mutual recursion over the
             grammar that hands each constructor to its case (`Faelle*.lean`) with the statement for its direct
             sub-terms (`*Kinder`).

             Corollaries: the body-running handler of the machine is read-blind (`rufRumpf_lg`), so a run that reads
             more before every call stays related (`rufRumpf_lese_vorn`); inversions of the outcome relations for
             the normal outcomes. The relation the image theorem needs between `rufAt` and `rufRumpf` (package P2)
             is `HandlerLG (fun _ => True) (rufAt P O passes n) (rufRumpf P O passes n)`; it is NOT proved here.
-/
module
public import Stage0.Senke.Bild.Gleich.FaelleStmt
public import Stage0.Senke.Bild.Gleich.FaelleBlock
public import Stage0.Senke.Bild.Gleich.FaelleEnde
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T1
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration} {O : Orakel D} {passes : Nat} {Er : Fehlermarke D → Prop}
  {R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {V : Vertrag D}

/-! ## 1. The mutual recursion over the grammar -/

mutual

theorem lg_stmt (hR : HandlerLG Er R₁ R₂) (hO : Leseblind O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → StmtLG O passes Er R₁ R₂ s
  | .ite c t e => stmt_lg hR hO (.ite c t e) (And.intro (lg_block hR hO t) (lg_block hR hO e))
  | .onOption o p a => stmt_lg hR hO (.onOption o p a) (And.intro (lg_block hR hO p) (lg_block hR hO a))
  | .onTag v arms => stmt_lg hR hO (.onTag v arms) (lg_arms hR hO arms)
  | .onWhy r arms => stmt_lg hR hO (.onWhy r arms) (lg_grund hR hO arms)
  | .locks L hr body => stmt_lg hR hO (.locks L hr body) (lg_block hR hO body)
  | .breaking i body => stmt_lg hR hO (.breaking i body) (lg_block hR hO body)
  | .traverse t inv body => stmt_lg hR hO (.traverse t inv body) (lg_block hR hO body)
  | .consumeTraverse t member edge inv bound mass body =>
      stmt_lg hR hO (.consumeTraverse t member edge inv bound mass body) (lg_block hR hO body)
  | .retry n bis body u => stmt_lg hR hO (.retry n bis body u) (And.intro (lg_block hR hO body) (lg_block hR hO u))
  | .forever a inv body => stmt_lg hR hO (.forever a inv body) (lg_block hR hO body)
  | .axiomCallElse e a args he hp hd hgd hr err =>
      stmt_lg hR hO (.axiomCallElse e a args he hp hd hgd hr err) (lg_ende hR hO err)
  | .callIndElse p args he hp hr err => stmt_lg hR hO (.callIndElse p args he hp hr err) (lg_ende hR hO err)
  | .assignSlot .. => stmt_lg hR hO _ (by exact True.intro)
  | .assignThru .. => stmt_lg hR hO _ (by exact True.intro)
  | .assignThruOwn .. => stmt_lg hR hO _ (by exact True.intro)
  | .assignSlotRef .. => stmt_lg hR hO _ (by exact True.intro)
  | .assignGlob .. => stmt_lg hR hO _ (by exact True.intro)
  | .putBytes .. => stmt_lg hR hO _ (by exact True.intro)
  | .assignVar .. => stmt_lg hR hO _ (by exact True.intro)
  | .shift .. => stmt_lg hR hO _ (by exact True.intro)
  | .call .. => stmt_lg hR hO _ (by exact True.intro)
  | .callInd .. => stmt_lg hR hO _ (by exact True.intro)
  | .axiomCall .. => stmt_lg hR hO _ (by exact True.intro)
  | .regWrite .. => stmt_lg hR hO _ (by exact True.intro)
  | .transition .. => stmt_lg hR hO _ (by exact True.intro)
  | .publish .. => stmt_lg hR hO _ (by exact True.intro)
  | .advances .. => stmt_lg hR hO _ (by exact True.intro)
  | .retires .. => stmt_lg hR hO _ (by exact True.intro)
  | .ret .. => stmt_lg hR hO _ (by exact True.intro)
  | .retWhy .. => stmt_lg hR hO _ (by exact True.intro)
  | .leave .. => stmt_lg hR hO _ (by exact True.intro)
  | .next .. => stmt_lg hR hO _ (by exact True.intro)
  | .retScoped .. => stmt_lg hR hO _ (by exact True.intro)
  | .retWhyScoped .. => stmt_lg hR hO _ (by exact True.intro)

theorem lg_block (hR : HandlerLG Er R₁ R₂) (hO : Leseblind O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → BlockLG O passes Er R₁ R₂ b
  | .nil => block_lg hR hO _ (by exact True.intro)
  | .cons s rest => block_lg hR hO (.cons s rest) (And.intro (lg_stmt hR hO s) (lg_block hR hO rest))
  | .bind e rest => block_lg hR hO (.bind e rest) (lg_block hR hO rest)
  | .bindCall f args he hp hr rest => block_lg hR hO (.bindCall f args he hp hr rest) (lg_block hR hO rest)
  | .bindCallInd p args he hp hr rest =>
      block_lg hR hO (.bindCallInd p args he hp hr rest) (lg_block hR hO rest)
  | .bindCallElse f args he hp hr err rest =>
      block_lg hR hO (.bindCallElse f args he hp hr err rest) (And.intro (lg_ende hR hO err) (lg_block hR hO rest))
  | .bindCallIndElse p args he hp hr err rest =>
      block_lg hR hO (.bindCallIndElse p args he hp hr err rest)
        (And.intro (lg_ende hR hO err) (lg_block hR hO rest))
  | .bindAxiom a args he hw hg hd hgd rest =>
      block_lg hR hO (.bindAxiom a args he hw hg hd hgd rest) (lg_block hR hO rest)
  | .bindAxiomElse a args he hr hw hg hd hgd err rest =>
      block_lg hR hO (.bindAxiomElse a args he hr hw hg hd hgd err rest)
        (And.intro (lg_ende hR hO err) (lg_block hR hO rest))
  | .bindAxiomOpt e a args he hp hd hgd rest =>
      block_lg hR hO (.bindAxiomOpt e a args he hp hd hgd rest) (lg_block hR hO rest)
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest =>
      block_lg hR hO (.bindAxiomOptElse e a args he hp hd hgd hr err rest)
        (And.intro (lg_ende hR hO err) (lg_block hR hO rest))
  | .regRead r hk rest => block_lg hR hO (.regRead r hk rest) (lg_block hR hO rest)
  | .regReadElse r hk zusage sonst rest =>
      block_lg hR hO (.regReadElse r hk zusage sonst rest) (And.intro (lg_ende hR hO sonst) (lg_block hR hO rest))
  | .awaits g pl hp hL ha rest => block_lg hR hO (.awaits g pl hp hL ha rest) (lg_block hR hO rest)
  | .exchange g neu hw hL rest => block_lg hR hO (.exchange g neu hw hL rest) (lg_block hR hO rest)
  | .narrow e lo' hi' sonst rest =>
      block_lg hR hO (.narrow e lo' hi' sonst rest) (And.intro (lg_ende hR hO sonst) (lg_block hR hO rest))
  | .narrowRequired e lo' hi' rest => block_lg hR hO (.narrowRequired e lo' hi' rest) (lg_block hR hO rest)
  | .check c sonst rest =>
      block_lg hR hO (.check c sonst rest) (And.intro (lg_ende hR hO sonst) (lg_block hR hO rest))
  | .float op a b lo hi rest => block_lg hR hO (.float op a b lo hi rest) (lg_block hR hO rest)
  | .floatLit q lo hi rest => block_lg hR hO (.floatLit q lo hi rest) (lg_block hR hO rest)
  | .floatOf e lo hi rest => block_lg hR hO (.floatOf e lo hi rest) (lg_block hR hO rest)
  | .floatNarrow e lo hi sonst rest =>
      block_lg hR hO (.floatNarrow e lo hi sonst rest) (And.intro (lg_ende hR hO sonst) (lg_block hR hO rest))

theorem lg_ende (hR : HandlerLG Er R₁ R₂) (hO : Leseblind O) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → EndeLG O passes Er R₁ R₂ b
  | .cons s rest => ende_lg hR hO (.cons s rest) (And.intro (lg_stmt hR hO s) (lg_ende hR hO rest))
  | .bind e rest => ende_lg hR hO (.bind e rest) (lg_ende hR hO rest)
  | .bindCall f args he hp hr rest => ende_lg hR hO (.bindCall f args he hp hr rest) (lg_ende hR hO rest)
  | .bindCallElse f args he hp hr err rest =>
      ende_lg hR hO (.bindCallElse f args he hp hr err rest) (And.intro (lg_ende hR hO err) (lg_ende hR hO rest))
  | .bindAxiom a args he hw hg hd hgd rest =>
      ende_lg hR hO (.bindAxiom a args he hw hg hd hgd rest) (lg_ende hR hO rest)
  | .bindAxiomElse a args he hr hw hg hd hgd err rest =>
      ende_lg hR hO (.bindAxiomElse a args he hr hw hg hd hgd err rest)
        (And.intro (lg_ende hR hO err) (lg_ende hR hO rest))
  | .regRead r hk rest => ende_lg hR hO (.regRead r hk rest) (lg_ende hR hO rest)
  | .regReadElse r hk zusage sonst rest =>
      ende_lg hR hO (.regReadElse r hk zusage sonst rest) (And.intro (lg_ende hR hO sonst) (lg_ende hR hO rest))
  | .awaits g pl hp hL ha rest => ende_lg hR hO (.awaits g pl hp hL ha rest) (lg_ende hR hO rest)
  | .bindCallInd p args he hp hr rest => ende_lg hR hO (.bindCallInd p args he hp hr rest) (lg_ende hR hO rest)
  | .narrow e lo' hi' sonst rest =>
      ende_lg hR hO (.narrow e lo' hi' sonst rest) (And.intro (lg_ende hR hO sonst) (lg_ende hR hO rest))
  | .exchange g neu hw hL rest => ende_lg hR hO (.exchange g neu hw hL rest) (lg_ende hR hO rest)
  | .ite c t e => ende_lg hR hO (.ite c t e) (And.intro (lg_ende hR hO t) (lg_ende hR hO e))
  | .narrowRequired e lo' hi' rest => ende_lg hR hO (.narrowRequired e lo' hi' rest) (lg_ende hR hO rest)
  | .bindAxiomOpt e a args he hp hd hgd rest =>
      ende_lg hR hO (.bindAxiomOpt e a args he hp hd hgd rest) (lg_ende hR hO rest)
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest =>
      ende_lg hR hO (.bindAxiomOptElse e a args he hp hd hgd hr err rest)
        (And.intro (lg_ende hR hO err) (lg_ende hR hO rest))
  | .bindCallIndElse p args he hp hr err rest =>
      ende_lg hR hO (.bindCallIndElse p args he hp hr err rest) (And.intro (lg_ende hR hO err) (lg_ende hR hO rest))
  | .float op a b lo hi rest => ende_lg hR hO (.float op a b lo hi rest) (lg_ende hR hO rest)
  | .floatLit q lo hi rest => ende_lg hR hO (.floatLit q lo hi rest) (lg_ende hR hO rest)
  | .floatOf e lo hi rest => ende_lg hR hO (.floatOf e lo hi rest) (lg_ende hR hO rest)
  | .floatNarrow e lo hi sonst rest =>
      ende_lg hR hO (.floatNarrow e lo hi sonst rest) (And.intro (lg_ende hR hO sonst) (lg_ende hR hO rest))
  | .ret .. => ende_lg hR hO _ (by exact True.intro)
  | .retWhy .. => ende_lg hR hO _ (by exact True.intro)
  | .leave .. => ende_lg hR hO _ (by exact True.intro)
  | .next .. => ende_lg hR hO _ (by exact True.intro)
  | .retScoped .. => ende_lg hR hO _ (by exact True.intro)
  | .retWhyScoped .. => ende_lg hR hO _ (by exact True.intro)

theorem lg_arms (hR : HandlerLG Er R₁ R₂) (hO : Leseblind O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} : (a : Arms D V l Γ Λ Λ' cs) → ArmsLG O passes Er R₁ R₂ a
  | .nil => arms_nil_lg
  | .cons b rest => arms_cons_lg (lg_block hR hO b) (lg_arms hR hO rest)

theorem lg_grund (hR : HandlerLG Er R₁ R₂) (hO : Leseblind O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : (a : GrundArms D V l Γ Λ Λ' n) → GrundLG O passes Er R₁ R₂ a
  | .nil => grund_nil_lg
  | .cons b rest => grund_cons_lg (lg_block hR hO b) (lg_grund hR hO rest)

end

/-! ## 2. The substitution theorems -/

/-- **Handler substitution, statements.** -/
theorem execStmt_lg (hR : HandlerLG Er R₁ R₂) (hO : Leseblind O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') {σ₁ σ₂ : World D} (h : WeltGleich σ₁ σ₂) (ρ : Env D Γ) :
    AusLG Er (execStmt O passes R₁ s σ₁ ρ) (execStmt O passes R₂ s σ₂ ρ) :=
  lg_stmt hR hO s σ₁ σ₂ ρ h

/-- **Handler substitution, blocks.** -/
theorem execBlock_lg (hR : HandlerLG Er R₁ R₂) (hO : Leseblind O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') {σ₁ σ₂ : World D} (h : WeltGleich σ₁ σ₂) (ρ : Env D Γ) :
    AusLG Er (execBlock O passes R₁ b σ₁ ρ) (execBlock O passes R₂ b σ₂ ρ) :=
  lg_block hR hO b σ₁ σ₂ ρ h

/-- **HANDLER SUBSTITUTION** (P1): under a read-blind oracle, a terminal block run from `≈` worlds under two
    handlers related on `≈` worlds ends in related outcomes -- the same shape, `≈` worlds, equal values and
    reasons -- unless the run under `R₁` fails early with a mark in `Er`. -/
theorem execEnd_lg (hR : HandlerLG Er R₁ R₂) (hO : Leseblind O) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D V l Γ Λ) {σ₁ σ₂ : World D} (h : WeltGleich σ₁ σ₂) (ρ : Env D Γ) :
    EndLG Er (execEnd O passes R₁ b σ₁ ρ) (execEnd O passes R₂ b σ₂ ρ) :=
  lg_ende hR hO b σ₁ σ₂ ρ h

/-! ## 3. Inversions of the normal outcomes -/

theorem EndLG.zurueck_inv {l : Bool} {Γ : Ctx} {σ : World D} {v : ErgVal D V.erg} {o : EndAusgang V l Γ}
    (h : EndLG Er (.zurueck σ v) o) : ∃ σ', o = .zurueck σ' v ∧ WeltGleich σ σ' := by
  cases h with
  | zurueck hw => exact ⟨_, rfl, hw⟩

theorem EndLG.why_inv {l : Bool} {Γ : Ctx} {σ : World D} {r : Fin V.gruende} {o : EndAusgang V l Γ}
    (h : EndLG Er (.why σ r) o) : ∃ σ', o = .why σ' r ∧ WeltGleich σ σ' := by
  cases h with
  | why hw => exact ⟨_, rfl, hw⟩

theorem RufLG.ok_inv {f : D.Fn} {σ : World D} {v : ErgVal D (D.erg f)} {a : RufAusgang f}
    (h : RufLG Er (.ok σ v) a) : ∃ σ', a = .ok σ' v ∧ WeltGleich σ σ' := by
  cases h with
  | ok hw => exact ⟨_, rfl, hw⟩

theorem RufLG.why_inv {f : D.Fn} {σ : World D} {r : Fin (D.gruende f)} {a : RufAusgang f}
    (h : RufLG Er (.why σ r) a) : ∃ σ', a = .why σ' r ∧ WeltGleich σ σ' := by
  cases h with
  | why hw => exact ⟨_, rfl, hw⟩

/-! ## 4. The body-running handler is read-blind -/

/-- **`rufRumpf` respects `≈`**: under a read-blind oracle, the body-running handler of machine G (`rufRumpf`) is
    related to itself on `≈` worlds at every depth, with no early failure. -/
theorem rufRumpf_lg {P : Programm D} (hO : Leseblind O) :
    ∀ n, HandlerLG Er (rufRumpf P O passes n) (rufRumpf P O passes n)
  | 0 => fun _ _ _ _ _ => .logik _
  | n + 1 => fun g σ σ' ρ h => by
      have he := execEnd_lg (passes := passes)
        (rufRumpf_lg (P := P) hO n) hO (P.rumpf g) h ρ
      simp only [rufRumpf]
      generalize execEnd O passes (rufRumpf P O passes n) (P.rumpf g) σ ρ = o₁ at he ⊢
      generalize execEnd O passes (rufRumpf P O passes n) (P.rumpf g) σ' ρ = o₂ at he ⊢
      cases he with
      | zurueck hw => exact .ok hw
      | why hw => exact .why hw
      | @leave hl _ _ _ _ => exact absurd hl (by decide)
      | @next hl _ _ _ _ => exact absurd hl (by decide)
      | logik e => exact .logik e
      | hardware e => exact .hardware e
      | frueh hE => exact .frueh hE
      | fruehH hE => exact .fruehH hE

/-- A run that reads more before every call stays related to the body-running run. -/
theorem rufRumpf_lese_vorn {P : Programm D} (hO : Leseblind O) (n : Nat) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) :
    HandlerLG Er (rufRumpf P O passes n) (fun g σ ρ => rufRumpf P O passes n g (σ.lese Λ os) ρ) :=
  (rufRumpf_lg hO n).lese_vorn Λ os

#print axioms execEnd_lg
#print axioms rufRumpf_lg

end Gabbro.Stage0.Senke.BildLauf
