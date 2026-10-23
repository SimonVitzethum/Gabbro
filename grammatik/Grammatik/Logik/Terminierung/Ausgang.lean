/-
  File:      Grammatik/Logik/Terminierung/Ausgang.lean
  Subject:   THE EXIT CONDITION OF A `forever` LOOP (2026-10-23): when a loop of class `umgebung` or `bedingt` ends.

  Whether a `forever` loop ever ends is the program's question (undecidable in general). What the model fixes is
  HOW it can end -- exactly:
  * `foreverLauf_ok`, `foreverLauf_zurueck`, `foreverLauf_why`: the loop completes only through a pass that ends in
    `leave`, and returns only through a pass that returns -- the condition C of class `bedingt`;
  * `foreverLauf_nur_umwelt`: a loop none of whose passes leaves or returns ends only at a logic or hardware stop --
    in particular at its `progress` assumption when the passes the environment grants are spent;
  * `ohneAus_execStmt` (syntax to semantics): a statement whose finding (`befS`, Klasse.lean) holds no exit -- no
    `leave` of the loop around it, no `return` inside a `forever` pass -- never yields one;
  * `forever_umgebung`: a `forever` loop whose body holds no exit (the loops of class `umgebung`) ends only at a
    logic or hardware stop: never normally, never by returning.
-/
import Grammatik.Logik.Terminierung.Klasse

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Outcomes without an exit -/

/-- The outcome is no exit: no return, no reason, and no `leave` where the innermost loop is the one asked about
    (`eb`). -/
def OhneAus {l : Bool} {Γ : Ctx} (eb : Bool) : Ausgang V l Γ → Prop
  | .zurueck .. => False
  | .why .. => False
  | .leave .. => eb = false
  | _ => True

/-- The same for an end outcome. -/
def EndOhneAus {l : Bool} {Γ : Ctx} (eb : Bool) : EndAusgang V l Γ → Prop
  | .zurueck .. => False
  | .why .. => False
  | .leave .. => eb = false
  | _ => True

theorem ohneAus_schrumpf {l : Bool} {Γ : Ctx} {τ : Ty} {eb : Bool} :
    ∀ {a : Ausgang V l (τ :: Γ)}, OhneAus eb a → OhneAus eb a.schrumpf
  | .ok .., h | .zurueck .., h | .why .., h | .leave .., h | .next .., h | .logik _, h | .hardware _, h => h

theorem ohneAus_schrumpfArm {l : Bool} {Γ : Ctx} {eb : Bool} :
    ∀ (c : Option (Int × Int)) {a : Ausgang V l (ArmCtx Γ c)}, OhneAus eb a → OhneAus eb (a.schrumpfArm c)
  | Option.none, _, h => h
  | Option.some (_, _), _, h => ohneAus_schrumpf h

theorem ohneAus_mapWelt {l : Bool} {Γ : Ctx} {eb : Bool} (f : World D → World D) :
    ∀ {a : Ausgang V l Γ}, OhneAus eb a → OhneAus eb (a.mapWelt f)
  | .ok .., h | .zurueck .., h | .why .., h | .leave .., h | .next .., h | .logik _, h | .hardware _, h => h

theorem endOhneAus_schrumpf {l : Bool} {Γ : Ctx} {τ : Ty} {eb : Bool} :
    ∀ {a : EndAusgang V l (τ :: Γ)}, EndOhneAus eb a → EndOhneAus eb a.schrumpf
  | .zurueck .., h | .why .., h | .leave .., h | .next .., h | .logik _, h | .hardware _, h => h

theorem endOhneAus_zuAusgang {l : Bool} {Γ : Ctx} {eb : Bool} :
    ∀ {a : EndAusgang V l Γ}, EndOhneAus eb a → OhneAus eb a.zuAusgang
  | .zurueck .., h | .why .., h | .leave .., h | .next .., h | .logik _, h | .hardware _, h => h

/-! ## 2. The loops -/

section Schleifen

variable {l : Bool} {Γ : Ctx}

/-- **A `forever` loop completes only through a pass that leaves.** -/
theorem foreverLauf_ok (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (σ' : World D) (ρ' : Env D Γ),
      foreverLauf (l := l) a schritt inv n σ ρ = .ok σ' ρ' →
      ∃ σ1 ρ1, ∃ h : true = true, schritt σ1 ρ1 = .leave h σ' ρ'
  | 0, _, _, _, _, h => by simp [foreverLauf] at h
  | n + 1, σ, ρ, σ', ρ', h => by
      unfold foreverLauf at h
      split at h
      · cases h
      · split at h
        · exact foreverLauf_ok a schritt inv n _ _ σ' ρ' h
        · exact foreverLauf_ok a schritt inv n _ _ σ' ρ' h
        · rename_i hh σ2 ρ2 he
          cases h
          exact ⟨_, _, hh, he⟩
        all_goals cases h

/-- **A `forever` loop returns only through a pass that returns.** -/
theorem foreverLauf_zurueck (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (σ' : World D) (v : ErgVal D V.erg),
      foreverLauf (l := l) a schritt inv n σ ρ = .zurueck σ' v → ∃ σ1 ρ1, schritt σ1 ρ1 = .zurueck σ' v
  | 0, _, _, _, _, h => by simp [foreverLauf] at h
  | n + 1, σ, ρ, σ', v, h => by
      unfold foreverLauf at h
      split at h
      · cases h
      · split at h
        · exact foreverLauf_zurueck a schritt inv n _ _ σ' v h
        · exact foreverLauf_zurueck a schritt inv n _ _ σ' v h
        · cases h
        · rename_i σ2 v2 he
          cases h
          exact ⟨_, _, he⟩
        all_goals cases h

/-- **A `forever` loop ends with a reason only through a pass that does.** -/
theorem foreverLauf_why (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (σ' : World D) (r : Fin V.gruende),
      foreverLauf (l := l) a schritt inv n σ ρ = .why σ' r → ∃ σ1 ρ1, schritt σ1 ρ1 = .why σ' r
  | 0, _, _, _, _, h => by simp [foreverLauf] at h
  | n + 1, σ, ρ, σ', r, h => by
      unfold foreverLauf at h
      split at h
      · cases h
      · split at h
        · exact foreverLauf_why a schritt inv n _ _ σ' r h
        · exact foreverLauf_why a schritt inv n _ _ σ' r h
        · cases h
        · cases h
        · rename_i σ2 r2 he
          cases h
          exact ⟨_, _, he⟩
        all_goals cases h

/-- **A loop without an exit ends only at a logic or hardware stop**: when every pass is free of `leave`, return and
    reason, the loop's outcome is a logic stop or a hardware stop -- at its `progress` assumption when the passes
    are spent. -/
theorem foreverLauf_nur_umwelt (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) (hs : ∀ σ ρ, OhneAus true (schritt σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      (∃ e, foreverLauf (l := l) a schritt inv n σ ρ = .logik e) ∨
        ∃ e, foreverLauf (l := l) a schritt inv n σ ρ = .hardware e
  | 0, _, _ => Or.inr ⟨_, rfl⟩
  | n + 1, σ, ρ => by
      unfold foreverLauf
      split
      · exact Or.inl ⟨_, rfl⟩
      · have h := hs (inv σ ρ).1 ρ
        split
        · exact foreverLauf_nur_umwelt a schritt inv hs n _ _
        · exact foreverLauf_nur_umwelt a schritt inv hs n _ _
        · rename_i he; rw [he] at h; exact absurd h (by simp [OhneAus])
        · rename_i he; rw [he] at h; exact absurd h (by simp [OhneAus])
        · rename_i he; rw [he] at h; exact absurd h (by simp [OhneAus])
        · exact Or.inl ⟨_, rfl⟩
        · exact Or.inr ⟨_, rfl⟩

theorem ohneAus_forever {eb : Bool} (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) (hs : ∀ σ ρ, OhneAus true (schritt σ ρ)) (n : Nat)
    (σ : World D) (ρ : Env D Γ) : OhneAus eb (foreverLauf (l := l) a schritt inv n σ ρ) := by
  rcases foreverLauf_nur_umwelt a schritt inv hs n σ ρ with ⟨e, he⟩ | ⟨e, he⟩ <;> rw [he] <;> trivial

theorem ohneAus_traverse {τ : Ty} {eb : Bool} (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) (hs : ∀ σ ρ, OhneAus false (schritt σ ρ)) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), OhneAus eb (traverseLauf (l := l) schritt inv ks σ ρ)
  | [], σ, ρ => by unfold traverseLauf; split <;> trivial
  | k :: ks, σ, ρ => by
      unfold traverseLauf
      split
      · trivial
      · have h := hs (inv σ ρ).1 (.cons k ρ)
        split
        · exact ohneAus_traverse schritt inv hs ks _ _
        · exact ohneAus_traverse schritt inv hs ks _ _
        · split <;> trivial
        · rename_i he; rw [he] at h; exact absurd h (by simp [OhneAus])
        · rename_i he; rw [he] at h; exact absurd h (by simp [OhneAus])
        · trivial
        · trivial

theorem ohneAus_retry {eb : Bool} (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueber : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, OhneAus false (schritt σ ρ)) (hu : ∀ σ ρ, OhneAus eb (ueber σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), OhneAus eb (retryLauf schritt bis ueber n σ ρ)
  | 0, σ, ρ => by unfold retryLauf; split; trivial; exact hu _ _
  | n + 1, σ, ρ => by
      unfold retryLauf
      split
      · trivial
      · have h := hs (bis σ ρ).1 ρ
        split
        · exact ohneAus_retry schritt bis ueber hs hu n _ _
        · exact ohneAus_retry schritt bis ueber hs hu n _ _
        · trivial
        · rename_i he; rw [he] at h; exact absurd h (by simp [OhneAus])
        · rename_i he; rw [he] at h; exact absurd h (by simp [OhneAus])
        · trivial
        · trivial

end Schleifen

/-! ## 3. Syntax to semantics: a statement without an exit yields none -/

theorem befund_und_austritt (a b : Befund D) : (a ++ b).austritt = (a.austritt || b.austritt) := rfl

section Semantik

variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

set_option hygiene false in
/-- Split a finding `a ++ b` with no exit into its parts. -/
macro "teile" : tactic => `(tactic| (simp only [befS, befB, befE, befArms, befGArms, befund_und_austritt,
  Bool.or_eq_false_iff] at h))

mutual

theorem ohneAus_execStmt : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (eb dl : Bool),
    (befS eb true dl s).austritt = false → ∀ σ ρ, OhneAus eb (execStmt O passes R s σ ρ)
  | _, _, _, _, .assignSlot .., _, _, _, _, _ => trivial
  | _, _, _, _, .assignThru .., _, _, _, _, _ => trivial
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
  | _, _, _, _, .locks _ _ body, eb, _, h, σ, ρ => by
      teile
      exact ohneAus_mapWelt _ (ohneAus_execBlock body eb h _ _)
  | _, _, _, _, .breaking _ body, eb, _, h, σ, ρ => by
      teile
      exact ohneAus_execBlock body eb h _ _
  | _, _, _, _, .traverse _ _ body, _, _, h, σ, ρ => by
      teile
      exact ohneAus_traverse _ _ (fun σ ρ => ohneAus_execBlock body false h σ ρ) _ _ _
  | _, _, _, _, .retry n _ body ueber, eb, _, h, σ, ρ => by
      teile
      exact ohneAus_retry _ _ _ (fun σ ρ => ohneAus_execBlock body false h.1 σ ρ)
        (fun σ ρ => ohneAus_execBlock ueber eb h.2 σ ρ) n σ ρ
  | _, _, _, _, .forever a _ body, _, _, h, σ, ρ => by
      teile
      exact ohneAus_forever a _ _ (fun σ ρ => ohneAus_execBlock body true h.2 σ ρ) passes σ ρ
  | _, _, _, _, .axiomCall .., _, _, _, σ, ρ => by simp only [execStmt]; split <;> trivial
  | _, _, _, _, .regWrite .., _, _, _, _, _ => trivial
  | _, _, _, _, .transition .., _, _, _, _, _ => trivial
  | _, _, _, _, .publish .., _, _, _, _, _ => trivial
  | _, _, _, _, .advances .., _, _, _, _, _ => trivial
  | _, _, _, _, .retires .., _, _, _, _, _ => trivial
  | _, _, _, _, .ret .., _, _, h, _, _ => by simp [befS] at h
  | _, _, _, _, .retWhy .., _, _, h, _, _ => by simp [befS] at h
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
  | _, _, _, .ret .., _, h, _, _ => by simp [befE] at h
  | _, _, _, .retWhy .., _, h, _, _ => by simp [befE] at h
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

theorem ohneAus_execArms : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
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
