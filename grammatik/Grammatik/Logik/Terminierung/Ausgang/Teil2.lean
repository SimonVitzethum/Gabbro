module
public import Grammatik.Logik.Terminierung.Ausgang.Verbrauch
import all Grammatik.Logik.Terminierung.Ausgang.Verbrauch

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}
section Semantik
variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)


mutual

theorem ohneAus_execStmt : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (eb dl : Bool),
    (befS eb true dl s).austritt = false → ∀ σ ρ, OhneAus eb (execStmt O passes R s σ ρ)
  | _, _, _, _, .assignSlot .., _, _, _, _, _ => trivial
  | _, _, _, _, .assignThru .., _, _, _, _, _ | _, _, _, _, .assignThruOwn .., _, _, _, _, _ | _, _, _, _, .assignSlotRef .., _, _, _, _, _ => trivial
  | _, _, _, _, .assignGlob .., _, _, _, _, _ => trivial
  | _, _, _, _, .putBytes .., _, _, _, _, _ => trivial
  | _, _, _, _, .assignVar .., _, _, _, _, _ => trivial
  | _, _, _, _, .shift .., _, _, _, σ, ρ => by simp only [execStmt]; split <;> trivial
  | _, _, _, _, .ite _ t e, eb, _, h, σ, ρ => by
      teile
      simp only [execStmt]
      split
      · exact ohneAus_execBlock t eb h.1 _ _
      · exact ohneAus_execBlock e eb h.2 _ _
  | _, _, _, _, .onOption _ p a, eb, _, h, σ, ρ => by
      teile
      simp only [execStmt]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock p eb h.1 _ _)
      · exact ohneAus_execBlock a eb h.2 _ _
  | _, _, _, _, .onTag _ arms, eb, _, h, σ, ρ => by
      teile
      exact ohneAus_execArms arms eb h _ _ _
  | _, _, _, _, .onWhy _ arms, eb, _, h, σ, ρ => by
      teile
      exact ohneAus_execGrund arms eb h _ _ _
  | _, _, _, _, .call _ _ _ hr, _, _, _, σ, ρ => by
      simp only [execStmt]
      split
      · trivial
      · rename_i r _; exact keinGrund hr r
      · trivial
      · trivial
  | _, _, _, _, .callInd _ _ _ hr, _, _, _, σ, ρ => by
      simp only [execStmt]
      split
      split
      · trivial
      · rename_i hf _ _ _ r _; exact keinGrundSig hf hr r
      · trivial
      · trivial
  | _, _, _, _, .callIndElse p args _ _ hr err, eb, _, h, σ, ρ => by
      teile
      simp only [execStmt, indSonst]
      split
      split
      · trivial
      · exact endOhneAus_zuAusgang (endOhneAus_schrumpf (ohneAus_execEnd err eb h.2 _ _))
      · trivial
      · trivial
  | _, _, _, _, .locks L _ body, eb, _, h, σ, ρ => by
      teile
      have hbody : OhneAus eb (execBlock O passes R body (σ.nimmt L) ρ) :=
        ohneAus_execBlock body eb h _ _
      simp only [execStmt]
      generalize execBlock O passes R body (σ.nimmt L) ρ = outcome at hbody ⊢
      cases outcome <;> exact hbody
  | _, _, _, _, .breaking _ body, eb, _, h, σ, ρ => by
      teile
      exact ohneAus_execBlock body eb h _ _
  | _, _, _, _, .traverse _ _ body, _, _, h, σ, ρ => by
      teile
      exact ohneAus_traverse _ _ (fun σ ρ => ohneAus_execBlock body false h σ ρ) _ _ _
  | _, _, _, _, .consumeTraverse t _ _ _ _ _ body, _, _, h, σ, ρ => by
      teile
      exact ohneAus_verbrauch t _ _ _ _ _ (fun σ ρ => ohneAus_execBlock body false h σ ρ) _ _ _
  | _, _, _, _, .retry n _ body ueber, eb, _, h, σ, ρ => by
      teile
      exact ohneAus_retry _ _ _ (fun σ ρ => ohneAus_execBlock body false h.1 σ ρ)
        (fun σ ρ => ohneAus_execBlock ueber eb h.2 σ ρ) n σ ρ
  | _, _, _, _, .forever a _ body, _, _, h, σ, ρ => by
      teile
      exact ohneAus_forever a _ _ (fun σ ρ => ohneAus_execBlock body true h.2 σ ρ) passes σ ρ
  | _, _, _, _, .axiomCall .., _, _, _, σ, ρ => by simp only [execStmt]; split <;> trivial
  | _, _, _, _, .axiomCallElse _ a args _ _ _ _ _ err, eb, _, h, σ, ρ => by
      have h2 : (befE eb true err).austritt = false := by simpa [befS] using h
      simp only [execStmt]
      split
      · trivial
      · exact endOhneAus_zuAusgang (endOhneAus_schrumpf (ohneAus_execEnd err eb h2 _ _))
      · trivial
  | _, _, _, _, .regWrite .., _, _, _, _, _ => trivial
  | _, _, _, _, .transition .., _, _, _, _, _ => trivial
  | _, _, _, _, .publish .., _, _, _, _, _ => trivial
  | _, _, _, _, .advances .., _, _, _, _, _ => trivial
  | _, _, _, _, .retires .., _, _, _, _, _ => trivial
  | _, _, _, _, .ret .., _, _, h, _, _ => by simp only [befS, Bool.true_eq_false] at h
  | _, _, _, _, .retWhy .., _, _, h, _, _ => by simp only [befS, Bool.true_eq_false] at h
  | _, _, _, _, .retScoped .., _, _, h, _, _ => by simp only [befS, Bool.true_eq_false] at h
  | _, _, _, _, .retWhyScoped .., _, _, h, _, _ => by simp only [befS, Bool.true_eq_false] at h
  | _, _, _, _, .leave _, _, _, h, _, _ => by simp only [befS] at h; exact h
  | _, _, _, _, .next _, _, _, _, _, _ => trivial

theorem ohneAus_execBlock : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (eb : Bool),
    (befB eb true b).austritt = false → ∀ σ ρ, OhneAus eb (execBlock O passes R b σ ρ)
  | _, _, _, _, .nil, _, _, _, _ => trivial
  | _, _, _, _, .cons s rest, eb, h, σ, ρ => by
      teile
      have hs := ohneAus_execStmt s eb _ h.1 σ ρ
      simp only [execBlock]
      split
      · exact ohneAus_execBlock rest eb h.2 _ _
      · exact hs
  | _, _, _, _, .bind _ rest, eb, h, σ, ρ => by
      teile
      exact ohneAus_schrumpf (ohneAus_execBlock rest eb h _ _)
  | _, _, _, _, .bindCall _ _ _ _ hr rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h.2 _ _)
      · rename_i r _; exact keinGrund hr r
      · trivial
      · trivial
  | _, _, _, _, .bindCallInd _ _ _ _ hr rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h.2 _ _)
      · rename_i hf _ _ _ r _; exact keinGrundSig hf hr r
      · trivial
      · trivial
  | _, _, _, _, .bindCallIndElse p args _ _ hr err rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock, indSonst]
      split
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h.2 _ _)
      · exact endOhneAus_zuAusgang (endOhneAus_schrumpf (ohneAus_execEnd err eb h.1.2 _ _))
      · trivial
      · trivial
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h.2 _ _)
      · exact endOhneAus_zuAusgang (endOhneAus_schrumpf (ohneAus_execEnd err eb h.1.2 _ _))
      · trivial
      · trivial
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h _ _)
      · trivial
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h.2 _ _)
      · exact endOhneAus_zuAusgang (endOhneAus_schrumpf (ohneAus_execEnd err eb h.1 _ _))
      · trivial
  | _, _, _, _, .bindAxiomOpt e a args he _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · have ihr := fun σ' ρ' => ohneAus_execBlock rest eb h σ' ρ'
        cases e with
        | none =>
            simp only [Ausgang.weiterOpt]
            exact ihr _ _
        | some τ =>
            simp only [Ausgang.weiterOpt]
            exact ohneAus_schrumpf (ihr _ _)
      · trivial
  | _, _, _, _, .bindAxiomOptElse e a args he _ _ _ _ err rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · have ihr := fun σ' ρ' => ohneAus_execBlock rest eb h.2 σ' ρ'
        cases e with
        | none =>
            simp only [Ausgang.weiterOpt]
            exact ihr _ _
        | some τ =>
            simp only [Ausgang.weiterOpt]
            exact ohneAus_schrumpf (ihr _ _)
      · exact endOhneAus_zuAusgang (endOhneAus_schrumpf (ohneAus_execEnd err eb h.1 _ _))
      · trivial
  | _, _, _, _, .regRead _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · split
        · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h _ _)
        · trivial
      · trivial
  | _, _, _, _, .regReadElse _ _ _ sonst rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · split
        · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h.2 _ _)
        · exact endOhneAus_zuAusgang (ohneAus_execEnd sonst eb h.1 _ _)
      · trivial
  | _, _, _, _, .awaits _ _ _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h _ _)
      · trivial
  | _, _, _, _, .exchange _ _ _ _ rest, eb, h, σ, ρ => by
      teile
      exact ohneAus_schrumpf (ohneAus_execBlock rest eb h _ _)
  | _, _, _, _, .narrow _ _ _ sonst rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h.2 _ _)
      · exact endOhneAus_zuAusgang (ohneAus_execEnd sonst eb h.1 _ _)
  | _, _, _, _, .narrowRequired _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h _ _)
      · trivial
  | _, _, _, _, .check _ sonst rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_execBlock rest eb h.2 _ _
      · exact endOhneAus_zuAusgang (ohneAus_execEnd sonst eb h.1 _ _)
  | _, _, _, _, .float _ _ _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h _ _)
      · trivial
  | _, _, _, _, .floatLit _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h _ _)
      · trivial
  | _, _, _, _, .floatOf _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h _ _)
      · trivial
  | _, _, _, _, .floatNarrow _ _ _ sonst rest, eb, h, σ, ρ => by
      teile
      simp only [execBlock]
      split
      · exact ohneAus_schrumpf (ohneAus_execBlock rest eb h.2 _ _)
      · exact endOhneAus_zuAusgang (ohneAus_execEnd sonst eb h.1 _ _)

theorem ohneAus_execEnd : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (eb : Bool),
    (befE eb true e).austritt = false → ∀ σ ρ, EndOhneAus eb (execEnd O passes R e σ ρ)
  | _, _, _, .ret .., _, h, _, _ => by simp only [befE, Bool.true_eq_false] at h
  | _, _, _, .retWhy .., _, h, _, _ => by simp only [befE, Bool.true_eq_false] at h
  | _, _, _, .retScoped .., _, h, _, _ => by simp only [befE, Bool.true_eq_false] at h
  | _, _, _, .retWhyScoped .., _, h, _, _ => by simp only [befE, Bool.true_eq_false] at h
  | _, _, _, .leave _, _, h, _, _ => by simp only [befE] at h; exact h
  | _, _, _, .next _, _, _, _, _ => trivial
  | _, _, _, .cons s rest, eb, h, σ, ρ => by
      teile
      have hs := ohneAus_execStmt s eb _ h.1 σ ρ
      simp only [execEnd]
      split
      · exact ohneAus_execEnd rest eb h.2 _ _
      all_goals (rename_i he; rw [he] at hs; exact hs)
  | _, _, _, .bind _ rest, eb, h, σ, ρ => by
      teile
      exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h _ _)
  | _, _, _, .bindCall _ _ _ _ hr rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h.2 _ _)
      · rename_i r _; exact keinGrund hr r
      · trivial
      · trivial
  | _, _, _, .bindCallElse _ _ _ _ _ err rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h.2 _ _)
      · exact endOhneAus_schrumpf (ohneAus_execEnd err eb h.1.2 _ _)
      · trivial
      · trivial
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h _ _)
      · trivial
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h.2 _ _)
      · exact endOhneAus_schrumpf (ohneAus_execEnd err eb h.1 _ _)
      · trivial
  | _, _, _, .bindAxiomOpt e a args he _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · have ihr := fun σ' ρ' => ohneAus_execEnd rest eb h σ' ρ'
        cases e with
        | none =>
            simp only [EndAusgang.weiterOpt]
            exact ihr _ _
        | some τ =>
            simp only [EndAusgang.weiterOpt]
            exact endOhneAus_schrumpf (ihr _ _)
      · trivial
  | _, _, _, .bindAxiomOptElse e a args he _ _ _ _ err rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · have ihr := fun σ' ρ' => ohneAus_execEnd rest eb h.2 σ' ρ'
        cases e with
        | none =>
            simp only [EndAusgang.weiterOpt]
            exact ihr _ _
        | some τ =>
            simp only [EndAusgang.weiterOpt]
            exact endOhneAus_schrumpf (ihr _ _)
      · exact endOhneAus_schrumpf (ohneAus_execEnd err eb h.1 _ _)
      · trivial
  | _, _, _, .regRead _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · split
        · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h _ _)
        · trivial
      · trivial
  | _, _, _, .regReadElse _ _ _ sonst rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · split
        · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h.2 _ _)
        · exact ohneAus_execEnd sonst eb h.1 _ _
      · trivial
  | _, _, _, .awaits _ _ _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h _ _)
      · trivial
  | _, _, _, .bindCallInd _ _ _ _ hr rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h.2 _ _)
      · rename_i hf _ _ _ r _; exact keinGrundSig hf hr r
      · trivial
      · trivial
  | _, _, _, .bindCallIndElse p args _ _ hr err rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd, indSonstE]
      split
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h.2 _ _)
      · exact endOhneAus_schrumpf (ohneAus_execEnd err eb h.1.2 _ _)
      · trivial
      · trivial
  | _, _, _, .narrow _ _ _ sonst rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h.2 _ _)
      · exact ohneAus_execEnd sonst eb h.1 _ _
  | _, _, _, .narrowRequired _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h _ _)
      · trivial
  | _, _, _, .exchange _ _ _ _ rest, eb, h, σ, ρ => by
      teile
      exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h _ _)
  | _, _, _, .ite _ t e, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact ohneAus_execEnd t eb h.2 _ _
      · exact ohneAus_execEnd e eb h.1 _ _

  | _, _, _, .float _ _ _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h _ _)
      · trivial
  | _, _, _, .floatLit _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h _ _)
      · trivial
  | _, _, _, .floatOf _ _ _ rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h _ _)
      · trivial
  | _, _, _, .floatNarrow _ _ _ sonst rest, eb, h, σ, ρ => by
      teile
      simp only [execEnd]
      split
      · exact endOhneAus_schrumpf (ohneAus_execEnd rest eb h.2 _ _)
      · exact (ohneAus_execEnd sonst eb h.1 _ _)
theorem ohneAus_execArms : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs) (eb : Bool), (befArms eb true arms).austritt = false →
      ∀ v σ ρ, OhneAus eb (execArms O passes R arms v σ ρ)
  | _, _, _, _, _, .nil, _, _, ⟨⟨k, hk⟩, _⟩, _, _ => absurd hk (Nat.not_lt_zero k)
  | _, _, _, _, _, .cons (c := c) b rest, eb, h, ⟨⟨0, _⟩, _⟩, σ, ρ => by
      teile
      exact ohneAus_schrumpfArm c (ohneAus_execBlock b eb h.1 _ _)
  | _, _, _, _, _, .cons b rest, eb, h, ⟨⟨i + 1, hi⟩, nutz⟩, σ, ρ => by
      teile
      exact ohneAus_execArms rest eb h.2 _ _ _

theorem ohneAus_execGrund : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (eb : Bool), (befGArms eb true arms).austritt = false →
      ∀ r σ ρ, OhneAus eb (execGrund O passes R arms r σ ρ)
  | _, _, _, _, _, .nil, _, _, ⟨k, hk⟩, _, _ => absurd hk (Nat.not_lt_zero k)
  | _, _, _, _, _, .cons b rest, eb, h, ⟨0, _⟩, σ, ρ => by
      teile
      exact ohneAus_execBlock b eb h.1 _ _
  | _, _, _, _, _, .cons b rest, eb, h, ⟨i + 1, hi⟩, σ, ρ => by
      teile
      exact ohneAus_execGrund rest eb h.2 _ _ _

end

/-- **THE LOOPS OF CLASS `umgebung` END ONLY BY THE ENVIRONMENT**: a `forever` loop whose body holds no exit -- no
    `leave` of this loop, no `return` (`(befB true true body).austritt = false`, the flag the class reads) -- ends,
    for every grant of passes, only at a logic or hardware stop: never normally, never by returning. -/
theorem forever_umgebung {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (h : (befB true true body).austritt = false) (σ : World D) (ρ : Env D Γ) :
    (∃ e, execStmt (l := l) O passes R (.forever a inv body) σ ρ = .logik e) ∨
      ∃ e, execStmt (l := l) O passes R (.forever a inv body) σ ρ = .hardware e :=
  foreverLauf_nur_umwelt a _ _ (fun σ ρ => ohneAus_execBlock O passes R body true h σ ρ) passes σ ρ

/-- **THE EXIT CONDITION OF CLASS `bedingt`**: a `forever` loop completes only through a pass that leaves, and
    returns only through a pass that returns. -/
theorem forever_bedingt {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (σ : World D) (ρ : Env D Γ) :
    (∀ σ' ρ', execStmt (l := l) O passes R (.forever a inv body) σ ρ = .ok σ' ρ' →
      ∃ σ1 ρ1, ∃ h : true = true, execBlock O passes R body σ1 ρ1 = .leave h σ' ρ') ∧
    (∀ σ' v, execStmt (l := l) O passes R (.forever a inv body) σ ρ = .zurueck σ' v →
      ∃ σ1 ρ1, execBlock O passes R body σ1 ρ1 = .zurueck σ' v) :=
  ⟨fun σ' ρ' h => foreverLauf_ok a _ _ passes σ ρ σ' ρ' h,
   fun σ' v h => foreverLauf_zurueck a _ _ passes σ ρ σ' v h⟩

end Semantik

end Gabbro.Grammatik
