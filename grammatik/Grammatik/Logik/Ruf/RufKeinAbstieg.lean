/-
  File:      Grammatik/RufKeinAbstieg.lean
  Subject:   **A BODY RUN UNDER AN `abstieg`-FREE HANDLER NEVER ENDS IN AN
              `abstieg`** -- by mutual induction over statements, blocks, end
              blocks and both arm lists, carrying the call-depth admission
              (`rufeS`/`rufeB`/`rufeE`) as the hypothesis.

  The handler premise is admission-gated: `hR` is only needed for admitted
  callees, and `hZS` rules indirect calls out altogether (the depth
  discipline `rufTief` admits no indirect call, so the main depth theorem
  `RufKeinAbstiegTief.lean` applies this only to bodies without them).
  Every other `logik` outcome a body produces itself is a different
  constructor and falls to `cases`; transformers and loops fall to
  `RufKeinAbstiegSchleife.lean`. The shape mirrors the congruence induction
  (`HandlerKongruenz/Teil2Basis.lean`).
-/
module
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Fortschritt.KostenG.T1.Teil1
public import Grammatik.Logik.Ruf.RufKeinAbstiegSchleife
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}
variable (P : Programm D) (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool)
variable (hR : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (hh : D.Fn),
  Z g = true → R g σ ρ ≠ .logik (.abstieg hh))
variable (hZS : ∀ n, ZS n = false)
include hR hZS

mutual
/-- A statement run under an `abstieg`-free handler never ends in an `abstieg`. -/
theorem stmtKeinAbstieg : ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ)
    (hh : D.Fn), rufeS Z ZS EW s = true →
    execStmt O passes R s σ ρ ≠ .logik (.abstieg hh)
  | .assignSlot .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .assignThru .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .assignThruOwn .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .assignSlotRef .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .assignGlob .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .putBytes .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .assignVar .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .shift .., _, _, _, _ => by
      simp only [execStmt]
      split <;> (intro hc; cases hc)
  | .ite _ t e, σ, ρ, hh, h => by
      simp only [rufeS, Bool.and_eq_true] at h; simp only [execStmt]
      split
      · exact blockKeinAbstieg t _ _ hh h.1
      · exact blockKeinAbstieg e _ _ hh h.2
  | .onOption o p a, σ, ρ, hh, h => by
      simp only [rufeS, Bool.and_eq_true] at h; simp only [execStmt]
      cases he : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ with
      | none => dsimp only; exact blockKeinAbstieg a _ _ hh h.2
      | some k => dsimp only; exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg p _ _ hh h.1)
  | .onTag _ arms, σ, ρ, hh, h => by
      simp only [rufeS] at h; simp only [execStmt]
      exact armsKeinAbstieg arms _ _ _ hh h
  | .onWhy _ arms, σ, ρ, hh, h => by
      simp only [rufeS] at h; simp only [execStmt]
      exact grundArmsKeinAbstieg arms _ _ _ hh h
  | .call g args _ hr, σ, ρ, hh, h => by
      simp only [rufeS] at h; simp only [execStmt]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok _ _ => dsimp only; intro hc; cases hc
      | why _ r => dsimp only; exact fun _ => (keinGrund hr r : False).elim
      | logik e => dsimp only; exact fun hc => hR g _ _ hh h (hx.trans (by cases hc; rfl))
      | hardware _ => dsimp only; intro hc; cases hc
  | .callInd .., _, _, _, h => by
      -- `rufeS` of an indirect call is `ZS n`, and `hZS` makes it `false`.
      simp only [rufeS] at h
      rw [hZS] at h
      exact absurd h (by decide)
  | .callIndElse .., _, _, _, h => by
      -- `rufeS` is `ZS n && rufeE err`; its first conjunct is `false`.
      simp only [rufeS, Bool.and_eq_true] at h
      rw [hZS] at h
      exact absurd h.1 (by decide)
  | .locks L _ body, σ, ρ, hh, h => by
      simp only [rufeS] at h; simp only [execStmt]
      cases hx : execBlock O passes R body (σ.nimmt L) ρ with
      | ok _ _ => dsimp only; intro hc; cases hc
      | zurueck _ _ => dsimp only; intro hc; cases hc
      | why _ _ => dsimp only; intro hc; cases hc
      | leave _ _ _ => dsimp only; intro hc; cases hc
      | next _ _ _ => dsimp only; intro hc; cases hc
      | logik e => dsimp only; exact fun hc => blockKeinAbstieg body _ _ hh h (hx.trans (by cases hc; rfl))
      | hardware _ => dsimp only; intro hc; cases hc
  | .breaking _ body, σ, ρ, hh, h => by
      simp only [rufeS] at h; simp only [execStmt]
      exact blockKeinAbstieg body _ _ hh h
  | .traverse _ _ body, σ, ρ, hh, h => by
      simp only [rufeS] at h; simp only [execStmt]
      exact traverseKeinAbstieg _ _
        (fun σ ρ hh => blockKeinAbstieg body σ ρ hh h) _ _ _ hh
  | .consumeTraverse _ _ _ _ _ _ body, σ, ρ, hh, h => by
      simp only [rufeS] at h; simp only [execStmt]
      exact verbrauchKeinAbstieg _ _ _ _ _ _
        (fun σ ρ hh => blockKeinAbstieg body σ ρ hh h) _ _ _ hh
  | .retry n _ body ueber, σ, ρ, hh, h => by
      simp only [rufeS, Bool.and_eq_true] at h; simp only [execStmt]
      exact retryKeinAbstieg _ _ _
        (fun σ ρ hh => blockKeinAbstieg body σ ρ hh h.1)
        (fun σ ρ hh => blockKeinAbstieg ueber σ ρ hh h.2) _ _ _ hh
  | .forever a _ body, σ, ρ, hh, h => by
      simp only [rufeS, Bool.and_eq_true] at h; simp only [execStmt]
      exact foreverKeinAbstieg a _ _
        (fun σ ρ hh => blockKeinAbstieg body σ ρ hh h.2) _ _ _ hh
  | .axiomCall a args _ _ _ _ _, σ, ρ, hh, _ => by
      simp only [execStmt]
      cases ha : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk _ ov => cases ov <;> (intro hc; cases hc)
  | .axiomCallElse _ a args _ _ _ _ _ err, σ, ρ, hh, h => by
      simp only [rufeS] at h; simp only [execStmt]
      cases ha : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk _ ov =>
        rcases ov with _ | (v | r)
        · intro hc; cases hc
        · intro hc; cases hc
        · exact EndAusgang.zuAusgang_keinAbstieg
            (EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg err _ _ hh h))
  | .regWrite .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .transition .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .publish .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .advances .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .retires .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .ret .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .retWhy .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .leave _, _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .next _, _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .retScoped .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc
  | .retWhyScoped .., _, _, _, _ => by simp only [execStmt]; intro hc; cases hc

/-- A block run under an `abstieg`-free handler never ends in an `abstieg`. -/
theorem blockKeinAbstieg : ∀ (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ)
    (hh : D.Fn), rufeB Z ZS EW b = true →
    execBlock O passes R b σ ρ ≠ .logik (.abstieg hh)
  | .nil, _, _, _, _ => by simp only [execBlock]; intro hc; cases hc
  | .cons s rest, σ, ρ, hh, h => by
      simp only [rufeB, Bool.and_eq_true] at h; simp only [execBlock]
      cases hx : execStmt O passes R s σ ρ with
      | ok σ' ρ' => dsimp only; exact blockKeinAbstieg rest σ' ρ' hh h.2
      | zurueck _ _ => dsimp only; intro hc; cases hc
      | why _ _ => dsimp only; intro hc; cases hc
      | leave _ _ _ => dsimp only; intro hc; cases hc
      | next _ _ _ => dsimp only; intro hc; cases hc
      | logik e => dsimp only; exact fun hc => stmtKeinAbstieg s σ ρ hh h.1 (hx.trans (by cases hc; rfl))
      | hardware _ => dsimp only; intro hc; cases hc
  | .bind _ rest, σ, ρ, hh, h => by
      simp only [rufeB] at h; simp only [execBlock]
      exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h)
  | .bindCall g args _ _ hr rest, σ, ρ, hh, h => by
      simp only [rufeB, Bool.and_eq_true] at h; simp only [execBlock]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok σ' v =>
          dsimp only
          exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h.2)
      | why _ r => dsimp only; exact fun _ => (keinGrund hr r : False).elim
      | logik e => dsimp only; exact fun hc => hR g _ _ hh h.1 (hx.trans (by cases hc; rfl))
      | hardware _ => dsimp only; intro hc; cases hc
  | .bindCallInd .., _, _, _, h => by
      -- `rufeB` is `ZS n && rufeB rest`; its first conjunct is `false`.
      simp only [rufeB, Bool.and_eq_true] at h
      rw [hZS] at h
      exact absurd h.1 (by decide)
  | .bindCallElse g args _ _ _ err rest, σ, ρ, hh, h => by
      simp only [rufeB, Bool.and_eq_true] at h; simp only [execBlock]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok σ' v =>
          dsimp only
          exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h.2)
      | why _ r =>
          dsimp only
          exact EndAusgang.zuAusgang_keinAbstieg
            (EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg err _ _ hh h.1.2))
      | logik e => dsimp only; exact fun hc => hR g _ _ hh h.1.1 (hx.trans (by cases hc; rfl))
      | hardware _ => dsimp only; intro hc; cases hc
  | .bindCallIndElse .., _, _, _, h => by
      -- `rufeB` is `(ZS n && rufeE err) && rufeB rest`; `ZS n` is `false`.
      simp only [rufeB, Bool.and_eq_true] at h
      rw [hZS] at h
      exact absurd h.1.1 (by decide)
  -- The axiom arms follow `Block.kongruent` (HandlerKongruenz/Teil2Basis.lean):
  -- after `cases` on the answer pair the `match` stays stuck on the still open
  -- option, so no `dsimp` runs; after `cases` on the option the goal reduces by
  -- `whnf`, which `cases hc` and the unifier of `exact` both perform.
  | .bindAxiom a args _ _ _ _ _ rest, σ, ρ, hh, h => by
      simp only [rufeB] at h; simp only [execBlock]
      cases ha : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk _ ov =>
          cases ov with
          | none => intro hc; cases hc
          | some v => exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h)
  | .bindAxiomElse a args _ _ _ _ _ _ err rest, σ, ρ, hh, h => by
      simp only [rufeB, Bool.and_eq_true] at h; simp only [execBlock]
      cases ha : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk _ ov =>
        rcases ov with _ | (v | r)
        · intro hc; cases hc
        · exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h.2)
        · exact EndAusgang.zuAusgang_keinAbstieg
            (EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg err _ _ hh h.1))
  | .bindAxiomOpt e a args _ _ _ _ rest, σ, ρ, hh, h => by
      simp only [rufeB] at h; simp only [execBlock]
      cases ha : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk _ ov =>
        cases ov with
        | none => intro hc; cases hc
        | some v => exact Ausgang.weiterOpt_keinAbstieg e (blockKeinAbstieg rest _ _ hh h)
  | .bindAxiomOptElse e a args _ _ _ _ _ err rest, σ, ρ, hh, h => by
      simp only [rufeB, Bool.and_eq_true] at h; simp only [execBlock]
      cases ha : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk _ ov =>
        rcases ov with _ | (v | r)
        · intro hc; cases hc
        · exact Ausgang.weiterOpt_keinAbstieg e (blockKeinAbstieg rest _ _ hh h.2)
        · exact EndAusgang.zuAusgang_keinAbstieg
            (EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg err _ _ hh h.1))
  | .regRead r _ rest, σ, ρ, hh, h => by
      simp only [rufeB] at h; simp only [execBlock]
      cases he : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
      | none => dsimp only; intro hc; cases hc
      | some v =>
          dsimp only
          split
          · exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h)
          · intro hc; cases hc
  | .regReadElse r _ zusage sonst rest, σ, ρ, hh, h => by
      simp only [rufeB, Bool.and_eq_true] at h; simp only [execBlock]
      cases he : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
      | none => dsimp only; intro hc; cases hc
      | some v =>
          dsimp only
          split
          · exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h.2)
          · exact EndAusgang.zuAusgang_keinAbstieg (endKeinAbstieg sonst _ _ hh h.1)
  | .awaits _ _ _ _ _ rest, σ, ρ, hh, h => by
      simp only [rufeB] at h; simp only [execBlock]
      split
      · exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h)
      · intro hc; cases hc
  | .exchange _ _ _ _ rest, σ, ρ, hh, h => by
      simp only [rufeB] at h; simp only [execBlock]
      exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h)
  | .narrow _ _ _ sonst rest, σ, ρ, hh, h => by
      simp only [rufeB, Bool.and_eq_true] at h; simp only [execBlock]
      split
      · exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h.2)
      · exact EndAusgang.zuAusgang_keinAbstieg (endKeinAbstieg sonst _ _ hh h.1)
  | .narrowRequired _ _ _ rest, σ, ρ, hh, h => by
      simp only [rufeB] at h; simp only [execBlock]
      split
      · exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h)
      · intro hc; cases hc
  | .check _ sonst rest, σ, ρ, hh, h => by
      simp only [rufeB, Bool.and_eq_true] at h; simp only [execBlock]
      split
      · exact blockKeinAbstieg rest _ _ hh h.2
      · exact EndAusgang.zuAusgang_keinAbstieg (endKeinAbstieg sonst _ _ hh h.1)
  | .float op a b lo hi rest, σ, ρ, hh, h => by
      simp only [rufeB] at h; simp only [execBlock]
      cases hg : gleitPasst lo hi (gleitRechne op
          (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
          (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) with
      | none => dsimp only; intro hc; cases hc
      | some v => dsimp only; exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h)
  | .floatLit q lo hi rest, σ, ρ, hh, h => by
      simp only [rufeB] at h; simp only [execBlock]
      cases hg : gleitPasst lo hi (bruch q) with
      | none => dsimp only; intro hc; cases hc
      | some v => dsimp only; exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h)
  | .floatOf e lo hi rest, σ, ρ, hh, h => by
      simp only [rufeB] at h; simp only [execBlock]
      cases hg : gleitPasst lo hi (gleitAusInt
          (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) with
      | none => dsimp only; intro hc; cases hc
      | some v => dsimp only; exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h)
  | .floatNarrow e lo hi sonst rest, σ, ρ, hh, h => by
      simp only [rufeB, Bool.and_eq_true] at h; simp only [execBlock]
      cases hg : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x with
      | none => dsimp only; exact EndAusgang.zuAusgang_keinAbstieg (endKeinAbstieg sonst _ _ hh h.1)
      | some v => dsimp only; exact Ausgang.schrumpf_keinAbstieg (blockKeinAbstieg rest _ _ hh h.2)

/-- An end-block run under an `abstieg`-free handler never ends in an `abstieg`. -/
theorem endKeinAbstieg : ∀ (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hh : D.Fn), rufeE Z ZS EW e = true →
    execEnd O passes R e σ ρ ≠ .logik (.abstieg hh)
  | .ret .., _, _, _, _ => by simp only [execEnd]; intro hc; cases hc
  | .retWhy .., _, _, _, _ => by simp only [execEnd]; intro hc; cases hc
  | .leave _, _, _, _, _ => by simp only [execEnd]; intro hc; cases hc
  | .next _, _, _, _, _ => by simp only [execEnd]; intro hc; cases hc
  | .cons s rest, σ, ρ, hh, h => by
      simp only [rufeE, Bool.and_eq_true] at h; simp only [execEnd]
      cases hx : execStmt O passes R s σ ρ with
      | ok σ' ρ' => dsimp only; exact endKeinAbstieg rest σ' ρ' hh h.2
      | zurueck _ _ => dsimp only; intro hc; cases hc
      | why _ _ => dsimp only; intro hc; cases hc
      | leave _ _ _ => dsimp only; intro hc; cases hc
      | next _ _ _ => dsimp only; intro hc; cases hc
      | logik e => dsimp only; exact fun hc => stmtKeinAbstieg s σ ρ hh h.1 (hx.trans (by cases hc; rfl))
      | hardware _ => dsimp only; intro hc; cases hc
  | .bind _ rest, σ, ρ, hh, h => by
      simp only [rufeE] at h; simp only [execEnd]
      exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h)
  | .bindCall g args _ _ hr rest, σ, ρ, hh, h => by
      simp only [rufeE, Bool.and_eq_true] at h; simp only [execEnd]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok σ' v =>
          dsimp only
          exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h.2)
      | why _ r => dsimp only; exact fun _ => (keinGrund hr r : False).elim
      | logik e => dsimp only; exact fun hc => hR g _ _ hh h.1 (hx.trans (by cases hc; rfl))
      | hardware _ => dsimp only; intro hc; cases hc
  | .bindCallElse g args _ _ _ err rest, σ, ρ, hh, h => by
      simp only [rufeE, Bool.and_eq_true] at h; simp only [execEnd]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok σ' v =>
          dsimp only
          exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h.2)
      | why _ r =>
          dsimp only
          exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg err _ _ hh h.1.2)
      | logik e => dsimp only; exact fun hc => hR g _ _ hh h.1.1 (hx.trans (by cases hc; rfl))
      | hardware _ => dsimp only; intro hc; cases hc
  | .bindAxiom a args _ _ _ _ _ rest, σ, ρ, hh, h => by
      simp only [rufeE] at h; simp only [execEnd]
      cases ha : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk _ ov =>
        cases ov with
        | none => intro hc; cases hc
        | some v => exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h)
  | .bindAxiomElse a args _ _ _ _ _ _ err rest, σ, ρ, hh, h => by
      simp only [rufeE, Bool.and_eq_true] at h; simp only [execEnd]
      cases ha : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk _ ov =>
        rcases ov with _ | (v | r)
        · intro hc; cases hc
        · exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h.2)
        · exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg err _ _ hh h.1)
  | .bindAxiomOpt e a args _ _ _ _ rest, σ, ρ, hh, h => by
      simp only [rufeE] at h; simp only [execEnd]
      cases ha : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk _ ov =>
        cases ov with
        | none => intro hc; cases hc
        | some v => exact EndAusgang.weiterOpt_keinAbstieg e (endKeinAbstieg rest _ _ hh h)
  | .bindAxiomOptElse e a args _ _ _ _ _ err rest, σ, ρ, hh, h => by
      simp only [rufeE, Bool.and_eq_true] at h; simp only [execEnd]
      cases ha : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk _ ov =>
        rcases ov with _ | (v | r)
        · intro hc; cases hc
        · exact EndAusgang.weiterOpt_keinAbstieg e (endKeinAbstieg rest _ _ hh h.2)
        · exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg err _ _ hh h.1)
  | .regRead r _ rest, σ, ρ, hh, h => by
      simp only [rufeE] at h; simp only [execEnd]
      cases he : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
      | none => dsimp only; intro hc; cases hc
      | some v =>
          dsimp only
          split
          · exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h)
          · intro hc; cases hc
  | .regReadElse r _ zusage sonst rest, σ, ρ, hh, h => by
      simp only [rufeE, Bool.and_eq_true] at h; simp only [execEnd]
      cases he : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
      | none => dsimp only; intro hc; cases hc
      | some v =>
          dsimp only
          split
          · exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h.2)
          · exact endKeinAbstieg sonst _ _ hh h.1
  | .awaits _ _ _ _ _ rest, σ, ρ, hh, h => by
      simp only [rufeE] at h; simp only [execEnd]
      split
      · exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h)
      · intro hc; cases hc
  | .bindCallInd .., _, _, _, h => by
      -- `rufeE` is `ZS n && rufeE rest`; its first conjunct is `false`.
      simp only [rufeE, Bool.and_eq_true] at h
      rw [hZS] at h
      exact absurd h.1 (by decide)
  | .bindCallIndElse .., _, _, _, h => by
      -- `rufeE` is `(ZS n && rufeE err) && rufeE rest`; `ZS n` is `false`.
      simp only [rufeE, Bool.and_eq_true] at h
      rw [hZS] at h
      exact absurd h.1.1 (by decide)
  | .narrow _ _ _ sonst rest, σ, ρ, hh, h => by
      simp only [rufeE, Bool.and_eq_true] at h; simp only [execEnd]
      split
      · exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h.2)
      · exact endKeinAbstieg sonst _ _ hh h.1
  | .exchange _ _ _ _ rest, σ, ρ, hh, h => by
      simp only [rufeE] at h; simp only [execEnd]
      exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h)
  | .ite _ t e, σ, ρ, hh, h => by
      simp only [rufeE, Bool.and_eq_true] at h; simp only [execEnd]
      split
      · exact endKeinAbstieg t _ _ hh h.2
      · exact endKeinAbstieg e _ _ hh h.1
  | .retScoped .., _, _, _, _ => by simp only [execEnd]; intro hc; cases hc
  | .retWhyScoped .., _, _, _, _ => by simp only [execEnd]; intro hc; cases hc
  | .narrowRequired _ _ _ rest, σ, ρ, hh, h => by
      simp only [rufeE] at h; simp only [execEnd]
      split
      · exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h)
      · intro hc; cases hc
  | .float op a b lo hi rest, σ, ρ, hh, h => by
      simp only [rufeE] at h; simp only [execEnd]
      cases hg : gleitPasst lo hi (gleitRechne op
          (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
          (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) with
      | none => dsimp only; intro hc; cases hc
      | some v => dsimp only; exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h)
  | .floatLit q lo hi rest, σ, ρ, hh, h => by
      simp only [rufeE] at h; simp only [execEnd]
      cases hg : gleitPasst lo hi (bruch q) with
      | none => dsimp only; intro hc; cases hc
      | some v => dsimp only; exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h)
  | .floatOf e lo hi rest, σ, ρ, hh, h => by
      simp only [rufeE] at h; simp only [execEnd]
      cases hg : gleitPasst lo hi (gleitAusInt
          (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) with
      | none => dsimp only; intro hc; cases hc
      | some v => dsimp only; exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h)
  | .floatNarrow e lo hi sonst rest, σ, ρ, hh, h => by
      simp only [rufeE, Bool.and_eq_true] at h; simp only [execEnd]
      cases hg : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x with
      | none => dsimp only; exact endKeinAbstieg sonst _ _ hh h.1
      | some v => dsimp only; exact EndAusgang.schrumpf_keinAbstieg (endKeinAbstieg rest _ _ hh h.2)

/-- A case-arm run under an `abstieg`-free handler never ends in an `abstieg`. -/
theorem armsKeinAbstieg : ∀ (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
    (σ : World D) (ρ : Env D Γ) (hh : D.Fn), rufeArms Z ZS EW arms = true →
    execArms O passes R arms v σ ρ ≠ .logik (.abstieg hh)
  | .nil, ⟨⟨k, hk⟩, _⟩, _, _, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨⟨0, _⟩, _⟩, σ, ρ, hh, h => by
      simp only [rufeArms, Bool.and_eq_true] at h; simp only [execArms]
      exact Ausgang.schrumpfArm_keinAbstieg _ (blockKeinAbstieg b _ _ hh h.1)
  | .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, hh, h => by
      simp only [rufeArms, Bool.and_eq_true] at h; simp only [execArms]
      exact armsKeinAbstieg rest _ _ _ hh h.2

/-- A reason-arm run under an `abstieg`-free handler never ends in an `abstieg`. -/
theorem grundArmsKeinAbstieg : ∀ (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n)
    (σ : World D) (ρ : Env D Γ) (hh : D.Fn), rufeGArms Z ZS EW arms = true →
    execGrund O passes R arms r σ ρ ≠ .logik (.abstieg hh)
  | .nil, r, _, _, _, _ => r.elim0
  | .cons b _, ⟨0, _⟩, σ, ρ, hh, h => by
      simp only [rufeGArms, Bool.and_eq_true] at h; simp only [execGrund]
      exact blockKeinAbstieg b _ _ hh h.1
  | .cons _ rest, ⟨_ + 1, _⟩, σ, ρ, hh, h => by
      simp only [rufeGArms, Bool.and_eq_true] at h; simp only [execGrund]
      exact grundArmsKeinAbstieg rest _ _ _ hh h.2
end

end Gabbro.Grammatik
