/-
  File:      stage0/Stage0/Senke/Bild/Gleich/Ersetzung.lean
  Subject:   **Handler substitution up to read events** (package P1 of the closed calls of the image theorem). Two
             handlers related on `≈` worlds (`HandlerLG Er R₁ R₂`) under an oracle with read-blind register and
             visibility answers (`LeseblindRS O`) give, from `≈` worlds and the same environment, related runs of
             every statement, block and terminal block (`execStmt_lg`, `execBlock_lg`, `execEnd_lg`) that carries no
             foreign call (`axFrei`) -- or of every one, when the foreign answers are read-blind too (`LeseblindW`):
             the same outcome shape with `≈` worlds and equal values, unless the run under `R₁` fails early with a
             mark in `Er`. The proof is one mutual recursion over the grammar that hands each constructor to its case
             (`Faelle*.lean`) with the statement for its direct sub-terms (`*Kinder`); the alternative "no foreign
             call or read-blind foreign answers" descends with it.

             Corollaries: the body-running handler of the machine is read-blind (`rufRumpf_lg`, under the program
             premise `LeseblindP`), so a run that reads more before every call stays related (`rufRumpf_lese_vorn`);
             inversions of the outcome relations for the normal outcomes. The relation the image theorem needs
             between `rufAt` and `rufRumpf` (package P2) is `HandlerLG (fun _ => True) (rufAt P O passes n)
             (rufRumpf P O passes n)`; it is NOT proved here.
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

theorem lg_stmt (hR : HandlerLG Er R₁ R₂) (hO : LeseblindRS O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → (s.axFrei = true ∨ LeseblindW O) → StmtLG O passes Er R₁ R₂ s
  | .ite c t e, hX => stmt_lg hR hO (.ite c t e) hX
      (And.intro (lg_block hR hO t (frei_links (a := t.axFrei) (b := e.axFrei) hX))
        (lg_block hR hO e (frei_rechts (a := t.axFrei) (b := e.axFrei) hX)))
  | .onOption o p a, hX => stmt_lg hR hO (.onOption o p a) hX
      (And.intro (lg_block hR hO p (frei_links (a := p.axFrei) (b := a.axFrei) hX))
        (lg_block hR hO a (frei_rechts (a := p.axFrei) (b := a.axFrei) hX)))
  | .onTag v arms, hX => stmt_lg hR hO (.onTag v arms) hX (lg_arms hR hO arms hX)
  | .onWhy r arms, hX => stmt_lg hR hO (.onWhy r arms) hX (lg_grund hR hO arms hX)
  | .locks L hr body, hX => stmt_lg hR hO (.locks L hr body) hX (lg_block hR hO body hX)
  | .breaking i body, hX => stmt_lg hR hO (.breaking i body) hX (lg_block hR hO body hX)
  | .traverse t inv body, hX => stmt_lg hR hO (.traverse t inv body) hX (lg_block hR hO body hX)
  | .consumeTraverse t member edge inv bound mass body, hX =>
      stmt_lg hR hO (.consumeTraverse t member edge inv bound mass body) hX (lg_block hR hO body hX)
  | .retry n bis body u, hX => stmt_lg hR hO (.retry n bis body u) hX
      (And.intro (lg_block hR hO body (frei_links (a := body.axFrei) (b := u.axFrei) hX))
        (lg_block hR hO u (frei_rechts (a := body.axFrei) (b := u.axFrei) hX)))
  | .forever a inv body, hX => stmt_lg hR hO (.forever a inv body) hX (lg_block hR hO body hX)
  | .axiomCallElse e a args he hp hd hgd hr err, hX =>
      stmt_lg hR hO (.axiomCallElse e a args he hp hd hgd hr err) hX
        (lg_ende hR hO err (Or.inr (hX.resolve_left Bool.false_ne_true)))
  | .callIndElse p args he hp hr err, hX =>
      stmt_lg hR hO (.callIndElse p args he hp hr err) hX (lg_ende hR hO err hX)
  | .assignSlot .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .assignThru .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .assignThruOwn .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .assignSlotRef .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .assignGlob .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .putBytes .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .assignVar .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .shift .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .call .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .callInd .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .axiomCall .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .regWrite .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .transition .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .publish .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .advances .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .retires .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .ret .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .retWhy .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .leave .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .next .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .retScoped .., hX => stmt_lg hR hO _ hX (by exact True.intro)
  | .retWhyScoped .., hX => stmt_lg hR hO _ hX (by exact True.intro)

theorem lg_block (hR : HandlerLG Er R₁ R₂) (hO : LeseblindRS O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → (b.axFrei = true ∨ LeseblindW O) → BlockLG O passes Er R₁ R₂ b
  | .nil, hX => block_lg hR hO _ hX (by exact True.intro)
  | .cons s rest, hX => block_lg hR hO (.cons s rest) hX
      (And.intro (lg_stmt hR hO s (frei_links (a := s.axFrei) (b := rest.axFrei) hX))
        (lg_block hR hO rest (frei_rechts (a := s.axFrei) (b := rest.axFrei) hX)))
  | .bind e rest, hX => block_lg hR hO (.bind e rest) hX (lg_block hR hO rest hX)
  | .bindCall f args he hp hr rest, hX =>
      block_lg hR hO (.bindCall f args he hp hr rest) hX (lg_block hR hO rest hX)
  | .bindCallInd p args he hp hr rest, hX =>
      block_lg hR hO (.bindCallInd p args he hp hr rest) hX (lg_block hR hO rest hX)
  | .bindCallElse f args he hp hr err rest, hX =>
      block_lg hR hO (.bindCallElse f args he hp hr err rest) hX
        (And.intro (lg_ende hR hO err (frei_links (a := err.axFrei) (b := rest.axFrei) hX))
          (lg_block hR hO rest (frei_rechts (a := err.axFrei) (b := rest.axFrei) hX)))
  | .bindCallIndElse p args he hp hr err rest, hX =>
      block_lg hR hO (.bindCallIndElse p args he hp hr err rest) hX
        (And.intro (lg_ende hR hO err (frei_links (a := err.axFrei) (b := rest.axFrei) hX))
          (lg_block hR hO rest (frei_rechts (a := err.axFrei) (b := rest.axFrei) hX)))
  | .bindAxiom a args he hw hg hd hgd rest, hX =>
      block_lg hR hO (.bindAxiom a args he hw hg hd hgd rest) hX
        (lg_block hR hO rest (Or.inr (hX.resolve_left Bool.false_ne_true)))
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, hX =>
      block_lg hR hO (.bindAxiomElse a args he hr hw hg hd hgd err rest) hX
        (And.intro (lg_ende hR hO err (Or.inr (hX.resolve_left Bool.false_ne_true)))
          (lg_block hR hO rest (Or.inr (hX.resolve_left Bool.false_ne_true))))
  | .bindAxiomOpt e a args he hp hd hgd rest, hX =>
      block_lg hR hO (.bindAxiomOpt e a args he hp hd hgd rest) hX
        (lg_block hR hO rest (Or.inr (hX.resolve_left Bool.false_ne_true)))
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, hX =>
      block_lg hR hO (.bindAxiomOptElse e a args he hp hd hgd hr err rest) hX
        (And.intro (lg_ende hR hO err (Or.inr (hX.resolve_left Bool.false_ne_true)))
          (lg_block hR hO rest (Or.inr (hX.resolve_left Bool.false_ne_true))))
  | .regRead r hk rest, hX => block_lg hR hO (.regRead r hk rest) hX (lg_block hR hO rest hX)
  | .regReadElse r hk zusage sonst rest, hX =>
      block_lg hR hO (.regReadElse r hk zusage sonst rest) hX
        (And.intro (lg_ende hR hO sonst (frei_links (a := sonst.axFrei) (b := rest.axFrei) hX))
          (lg_block hR hO rest (frei_rechts (a := sonst.axFrei) (b := rest.axFrei) hX)))
  | .awaits g pl hp hL ha rest, hX => block_lg hR hO (.awaits g pl hp hL ha rest) hX (lg_block hR hO rest hX)
  | .exchange g neu hw hL rest, hX => block_lg hR hO (.exchange g neu hw hL rest) hX (lg_block hR hO rest hX)
  | .narrow e lo' hi' sonst rest, hX =>
      block_lg hR hO (.narrow e lo' hi' sonst rest) hX
        (And.intro (lg_ende hR hO sonst (frei_links (a := sonst.axFrei) (b := rest.axFrei) hX))
          (lg_block hR hO rest (frei_rechts (a := sonst.axFrei) (b := rest.axFrei) hX)))
  | .narrowRequired e lo' hi' rest, hX =>
      block_lg hR hO (.narrowRequired e lo' hi' rest) hX (lg_block hR hO rest hX)
  | .check c sonst rest, hX =>
      block_lg hR hO (.check c sonst rest) hX
        (And.intro (lg_ende hR hO sonst (frei_links (a := sonst.axFrei) (b := rest.axFrei) hX))
          (lg_block hR hO rest (frei_rechts (a := sonst.axFrei) (b := rest.axFrei) hX)))
  | .float op a b lo hi rest, hX => block_lg hR hO (.float op a b lo hi rest) hX (lg_block hR hO rest hX)
  | .floatLit q lo hi rest, hX => block_lg hR hO (.floatLit q lo hi rest) hX (lg_block hR hO rest hX)
  | .floatOf e lo hi rest, hX => block_lg hR hO (.floatOf e lo hi rest) hX (lg_block hR hO rest hX)
  | .floatNarrow e lo hi sonst rest, hX =>
      block_lg hR hO (.floatNarrow e lo hi sonst rest) hX
        (And.intro (lg_ende hR hO sonst (frei_links (a := sonst.axFrei) (b := rest.axFrei) hX))
          (lg_block hR hO rest (frei_rechts (a := sonst.axFrei) (b := rest.axFrei) hX)))

theorem lg_ende (hR : HandlerLG Er R₁ R₂) (hO : LeseblindRS O) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → (b.axFrei = true ∨ LeseblindW O) → EndeLG O passes Er R₁ R₂ b
  | .cons s rest, hX => ende_lg hR hO (.cons s rest) hX
      (And.intro (lg_stmt hR hO s (frei_links (a := s.axFrei) (b := rest.axFrei) hX))
        (lg_ende hR hO rest (frei_rechts (a := s.axFrei) (b := rest.axFrei) hX)))
  | .bind e rest, hX => ende_lg hR hO (.bind e rest) hX (lg_ende hR hO rest hX)
  | .bindCall f args he hp hr rest, hX =>
      ende_lg hR hO (.bindCall f args he hp hr rest) hX (lg_ende hR hO rest hX)
  | .bindCallElse f args he hp hr err rest, hX =>
      ende_lg hR hO (.bindCallElse f args he hp hr err rest) hX
        (And.intro (lg_ende hR hO err (frei_links (a := err.axFrei) (b := rest.axFrei) hX))
          (lg_ende hR hO rest (frei_rechts (a := err.axFrei) (b := rest.axFrei) hX)))
  | .bindAxiom a args he hw hg hd hgd rest, hX =>
      ende_lg hR hO (.bindAxiom a args he hw hg hd hgd rest) hX
        (lg_ende hR hO rest (Or.inr (hX.resolve_left Bool.false_ne_true)))
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, hX =>
      ende_lg hR hO (.bindAxiomElse a args he hr hw hg hd hgd err rest) hX
        (And.intro (lg_ende hR hO err (Or.inr (hX.resolve_left Bool.false_ne_true)))
          (lg_ende hR hO rest (Or.inr (hX.resolve_left Bool.false_ne_true))))
  | .regRead r hk rest, hX => ende_lg hR hO (.regRead r hk rest) hX (lg_ende hR hO rest hX)
  | .regReadElse r hk zusage sonst rest, hX =>
      ende_lg hR hO (.regReadElse r hk zusage sonst rest) hX
        (And.intro (lg_ende hR hO sonst (frei_links (a := sonst.axFrei) (b := rest.axFrei) hX))
          (lg_ende hR hO rest (frei_rechts (a := sonst.axFrei) (b := rest.axFrei) hX)))
  | .awaits g pl hp hL ha rest, hX => ende_lg hR hO (.awaits g pl hp hL ha rest) hX (lg_ende hR hO rest hX)
  | .bindCallInd p args he hp hr rest, hX =>
      ende_lg hR hO (.bindCallInd p args he hp hr rest) hX (lg_ende hR hO rest hX)
  | .narrow e lo' hi' sonst rest, hX =>
      ende_lg hR hO (.narrow e lo' hi' sonst rest) hX
        (And.intro (lg_ende hR hO sonst (frei_links (a := sonst.axFrei) (b := rest.axFrei) hX))
          (lg_ende hR hO rest (frei_rechts (a := sonst.axFrei) (b := rest.axFrei) hX)))
  | .exchange g neu hw hL rest, hX => ende_lg hR hO (.exchange g neu hw hL rest) hX (lg_ende hR hO rest hX)
  | .ite c t e, hX => ende_lg hR hO (.ite c t e) hX
      (And.intro (lg_ende hR hO t (frei_links (a := t.axFrei) (b := e.axFrei) hX))
        (lg_ende hR hO e (frei_rechts (a := t.axFrei) (b := e.axFrei) hX)))
  | .narrowRequired e lo' hi' rest, hX =>
      ende_lg hR hO (.narrowRequired e lo' hi' rest) hX (lg_ende hR hO rest hX)
  | .bindAxiomOpt e a args he hp hd hgd rest, hX =>
      ende_lg hR hO (.bindAxiomOpt e a args he hp hd hgd rest) hX
        (lg_ende hR hO rest (Or.inr (hX.resolve_left Bool.false_ne_true)))
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, hX =>
      ende_lg hR hO (.bindAxiomOptElse e a args he hp hd hgd hr err rest) hX
        (And.intro (lg_ende hR hO err (Or.inr (hX.resolve_left Bool.false_ne_true)))
          (lg_ende hR hO rest (Or.inr (hX.resolve_left Bool.false_ne_true))))
  | .bindCallIndElse p args he hp hr err rest, hX =>
      ende_lg hR hO (.bindCallIndElse p args he hp hr err rest) hX
        (And.intro (lg_ende hR hO err (frei_links (a := err.axFrei) (b := rest.axFrei) hX))
          (lg_ende hR hO rest (frei_rechts (a := err.axFrei) (b := rest.axFrei) hX)))
  | .float op a b lo hi rest, hX => ende_lg hR hO (.float op a b lo hi rest) hX (lg_ende hR hO rest hX)
  | .floatLit q lo hi rest, hX => ende_lg hR hO (.floatLit q lo hi rest) hX (lg_ende hR hO rest hX)
  | .floatOf e lo hi rest, hX => ende_lg hR hO (.floatOf e lo hi rest) hX (lg_ende hR hO rest hX)
  | .floatNarrow e lo hi sonst rest, hX =>
      ende_lg hR hO (.floatNarrow e lo hi sonst rest) hX
        (And.intro (lg_ende hR hO sonst (frei_links (a := sonst.axFrei) (b := rest.axFrei) hX))
          (lg_ende hR hO rest (frei_rechts (a := sonst.axFrei) (b := rest.axFrei) hX)))
  | .ret .., hX => ende_lg hR hO _ hX (by exact True.intro)
  | .retWhy .., hX => ende_lg hR hO _ hX (by exact True.intro)
  | .leave .., hX => ende_lg hR hO _ hX (by exact True.intro)
  | .next .., hX => ende_lg hR hO _ hX (by exact True.intro)
  | .retScoped .., hX => ende_lg hR hO _ hX (by exact True.intro)
  | .retWhyScoped .., hX => ende_lg hR hO _ hX (by exact True.intro)

theorem lg_arms (hR : HandlerLG Er R₁ R₂) (hO : LeseblindRS O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} : (a : Arms D V l Γ Λ Λ' cs) → (a.axFrei = true ∨ LeseblindW O) →
      ArmsLG O passes Er R₁ R₂ a
  | .nil, _ => arms_nil_lg
  | .cons b rest, hX => arms_cons_lg (lg_block hR hO b (frei_links (a := b.axFrei) (b := rest.axFrei) hX))
      (lg_arms hR hO rest (frei_rechts (a := b.axFrei) (b := rest.axFrei) hX))

theorem lg_grund (hR : HandlerLG Er R₁ R₂) (hO : LeseblindRS O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : (a : GrundArms D V l Γ Λ Λ' n) → (a.axFrei = true ∨ LeseblindW O) → GrundLG O passes Er R₁ R₂ a
  | .nil, _ => grund_nil_lg
  | .cons b rest, hX => grund_cons_lg (lg_block hR hO b (frei_links (a := b.axFrei) (b := rest.axFrei) hX))
      (lg_grund hR hO rest (frei_rechts (a := b.axFrei) (b := rest.axFrei) hX))

end

/-! ## 2. The substitution theorems -/

/-- **Handler substitution, statements.** -/
theorem execStmt_lg (hR : HandlerLG Er R₁ R₂) (hO : LeseblindRS O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (hX : s.axFrei = true ∨ LeseblindW O) {σ₁ σ₂ : World D} (h : WeltGleich σ₁ σ₂)
    (ρ : Env D Γ) : AusLG Er (execStmt O passes R₁ s σ₁ ρ) (execStmt O passes R₂ s σ₂ ρ) :=
  lg_stmt hR hO s hX σ₁ σ₂ ρ h

/-- **Handler substitution, blocks.** -/
theorem execBlock_lg (hR : HandlerLG Er R₁ R₂) (hO : LeseblindRS O) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (hX : b.axFrei = true ∨ LeseblindW O) {σ₁ σ₂ : World D} (h : WeltGleich σ₁ σ₂)
    (ρ : Env D Γ) : AusLG Er (execBlock O passes R₁ b σ₁ ρ) (execBlock O passes R₂ b σ₂ ρ) :=
  lg_block hR hO b hX σ₁ σ₂ ρ h

/-- **HANDLER SUBSTITUTION** (P1): under read-blind register and visibility answers, a terminal block without a
    foreign call (or any terminal block, when the foreign answers are read-blind too) run from `≈` worlds under two
    handlers related on `≈` worlds ends in related outcomes -- the same shape, `≈` worlds, equal values and
    reasons -- unless the run under `R₁` fails early with a mark in `Er`. -/
theorem execEnd_lg (hR : HandlerLG Er R₁ R₂) (hO : LeseblindRS O) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D V l Γ Λ) (hX : b.axFrei = true ∨ LeseblindW O) {σ₁ σ₂ : World D} (h : WeltGleich σ₁ σ₂)
    (ρ : Env D Γ) : EndLG Er (execEnd O passes R₁ b σ₁ ρ) (execEnd O passes R₂ b σ₂ ρ) :=
  lg_ende hR hO b hX σ₁ σ₂ ρ h

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

/-- **`rufRumpf` respects `≈`**: under the oracle premise of the program (`LeseblindP`), the body-running handler of
    machine G (`rufRumpf`) is related to itself on `≈` worlds at every depth, with no early failure. -/
theorem rufRumpf_lg {P : Programm D} (hO : LeseblindP P O) :
    ∀ n, HandlerLG Er (rufRumpf P O passes n) (rufRumpf P O passes n)
  | 0 => fun _ _ _ _ _ => .logik _
  | n + 1 => fun g σ σ' ρ h => by
      have he := execEnd_lg (passes := passes)
        (rufRumpf_lg (P := P) hO n) hO.rs (P.rumpf g) (hO.rumpf g) h ρ
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
theorem rufRumpf_lese_vorn {P : Programm D} (hO : LeseblindP P O) (n : Nat) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) :
    HandlerLG Er (rufRumpf P O passes n) (fun g σ ρ => rufRumpf P O passes n g (σ.lese Λ os) ρ) :=
  (rufRumpf_lg hO n).lese_vorn Λ os

#print axioms execEnd_lg
#print axioms rufRumpf_lg

end Gabbro.Stage0.Senke.BildLauf
