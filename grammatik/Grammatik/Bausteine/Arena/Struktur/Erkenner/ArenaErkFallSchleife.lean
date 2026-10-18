/-
  File:      Grammatik/ArenaErkFallSchleife.lean
  Subject:   THE CASES OF THE RECOGNIZER'S SOUNDNESS PROOF, part 4: the loops (`forever`, `traverse`, `retry`).

  A loop is recognized when its body, started in the LOOP STATE `k0`, ends in a state at least as strong as `k0`. The
  proofs are the inductions the semantics asks for (`foreverLauf` on the fuel, `traverseLauf` on the list of indices,
  `retryLauf` on the bound), one pass at a time:

    * the body's outcome is `ok`: the loop state still holds, and the next pass starts from it;
    * the body returns or fails: the arena invariant holds there (`StrukturPost`);
    * the body leaves or goes `next`: impossible, a recognized body never produces either (`StrukturPost` is `False` there).

  `forever` never falls off (only a `leave` could end it), so every state is promised of its outcome; `traverse` falls off in
  `k0`; `retry` falls off in `k0` or leaves through the overflow block, which is recognized from `k0`.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkFallBaum

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

section Schleifen
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- A loop test only records a read: the world it hands on is the world it got, with one more read. -/
def LeseTest (invF : World D → Env D Γ → World D × Bool) : Prop :=
  ∀ σ ρ, ∃ (Λ0 : List (Res D)) (o : List (D.Tab ⊕ D.Glob)), (invF σ ρ).1 = σ.lese Λ0 o

theorem leseTest_inv (inv : Expr D Γ Λ .bool) :
    LeseTest (fun (σ : World D) (ρ : Env D Γ) => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) :=
  fun _ _ => ⟨Λ, inv.orte, rfl⟩

/-- **`forever`:** from the loop state, no pass ends in anything but a return, a failure, or the next pass. -/
theorem forever_post {k0 a1 : Abs} (an : D.Annahme) (invF : World D → Env D Γ → World D × Bool)
    (hinv : LeseTest invF) (body : Block D V true Γ Λ Λ)
    (hb : Folgt K O passes R k0 body a1) (hs : Abs.Schwacher k0 a1) (b : Abs) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), K.Ok σ → StrukturPasst K k0 σ ρ →
      StrukturPost K b (foreverLauf an (fun σ ρ => execBlock O passes R body σ ρ) invF n σ ρ : Ausgang V l Γ) := by
  intro n
  induction n with
  | zero => intro σ ρ _ _; simp only [foreverLauf]; trivial
  | succ n ih =>
    intro σ ρ hS hP
    obtain ⟨Λ0, o, hσ⟩ := hinv σ ρ
    simp only [foreverLauf]
    by_cases hi : (invF σ ρ).2 = false
    · rw [if_pos hi]; trivial
    · rw [if_neg hi, hσ]
      have hb1 := hb (σ.lese Λ0 o) ρ (Dekl.Ok.lese K Λ0 o hS) (StrukturPasst.lese K Λ0 o hP)
      rcases hx : execBlock O passes R body (σ.lese Λ0 o) ρ with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, r1⟩ |
        ⟨h1, σ1, ρ1⟩ | ⟨h1, σ1, ρ1⟩ | e1 | e1
      · rw [hx] at hb1
        exact ih σ1 ρ1 hb1.1 (StrukturPasst.schwacher K hs hb1.2)
      · rw [hx] at hb1; exact hb1
      · rw [hx] at hb1; exact hb1
      · rw [hx] at hb1; exact hb1.elim
      · rw [hx] at hb1; exact hb1.elim
      · trivial
      · trivial

theorem fall_forever {a a1 a' k0 : Abs} (an : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (rest : Block D V l Γ Λ Λ') (hin : Abs.Schwacher k0 a)
    (hb : Folgt K O passes R k0 body a1) (hs : Abs.Schwacher k0 a1) (ih : Folgt K O passes R a rest a') :
    Folgt K O passes R a (Block.cons (Stmt.forever an inv body) rest) a' := by
  intro σ ρ hS hP
  refine StrukturPost.cons_stmt K O passes R (a := a) ?_ ih
  exact forever_post O passes R K an _ (leseTest_inv inv) body hb hs a passes σ ρ hS (StrukturPasst.schwacher K hin hP)

/-- **`traverse`:** every pass keeps the loop state; the loop falls off in it. -/
theorem traverse_post {τ : Ty} {k0 a1 : Abs} (invF : World D → Env D Γ → World D × Bool) (hinv : LeseTest invF)
    (body : Block D V true (τ :: Γ) Λ Λ) (hb : Folgt K O passes R (k0.ext .offen) body a1)
    (hs : Abs.Schwacher k0 a1.tail) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), K.Ok σ → StrukturPasst K k0 σ ρ →
      StrukturPost K k0 (traverseLauf (fun σ ρ => execBlock O passes R body σ ρ) invF ks σ ρ : Ausgang V l Γ) := by
  intro ks
  induction ks with
  | nil =>
    intro σ ρ hS hP
    obtain ⟨Λ0, o, hσ⟩ := hinv σ ρ
    simp only [traverseLauf]
    by_cases hi : (invF σ ρ).2 = true
    · rw [if_pos hi, hσ]
      exact ⟨Dekl.Ok.lese K Λ0 o hS, StrukturPasst.lese K Λ0 o hP⟩
    · rw [if_neg hi]; trivial
  | cons k ks ih =>
    intro σ ρ hS hP
    obtain ⟨Λ0, o, hσ⟩ := hinv σ ρ
    simp only [traverseLauf]
    by_cases hi : (invF σ ρ).2 = false
    · rw [if_pos hi]; trivial
    · rw [if_neg hi, hσ]
      have hb1 := hb (σ.lese Λ0 o) (.cons k ρ) (Dekl.Ok.lese K Λ0 o hS)
        (StrukturPasst.ext_offen K (StrukturPasst.lese K Λ0 o hP))
      rcases hx : execBlock O passes R body (σ.lese Λ0 o) (.cons k ρ) with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, r1⟩ |
        ⟨h1, σ1, ρ1⟩ | ⟨h1, σ1, ρ1⟩ | e1 | e1
      · rw [hx] at hb1
        cases ρ1 with
        | cons k1 ρ2 =>
          exact ih σ1 ρ2 hb1.1 (StrukturPasst.schwacher K hs (StrukturPasst.tail K hb1.2))
      · rw [hx] at hb1; exact hb1
      · rw [hx] at hb1; exact hb1
      · rw [hx] at hb1; exact hb1.elim
      · rw [hx] at hb1; exact hb1.elim
      · trivial
      · trivial

theorem fall_traverse {a a1 a' k0 : Abs} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (Ty.index (D.count t) :: Γ) Λ Λ) (rest : Block D V l Γ Λ Λ')
    (hin : Abs.Schwacher k0 a) (hb : Folgt K O passes R (k0.ext .offen) body a1)
    (hs : Abs.Schwacher k0 a1.tail) (ih : Folgt K O passes R k0 rest a') :
    Folgt K O passes R a (Block.cons (Stmt.traverse t inv body) rest) a' := by
  intro σ ρ hS hP
  refine StrukturPost.cons_stmt K O passes R (a := k0) ?_ ih
  exact traverse_post O passes R K _ (leseTest_inv inv) body hb hs (alleIndizes (D.count t)) σ ρ hS
    (StrukturPasst.schwacher K hin hP)

/-- **`retry`:** every pass keeps the loop state; the loop falls off in it, or leaves through the overflow block. -/
theorem retry_post {k0 a1 au a3 : Abs} (bisF : World D → Env D Γ → World D × Bool) (hbis : LeseTest bisF)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ)
    (hb : Folgt K O passes R k0 body a1) (hs : Abs.Schwacher k0 a1) (hu : Folgt K O passes R k0 ueber au)
    (h3 : Abs.Schwacher a3 k0) (h4 : Abs.Schwacher a3 au) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), K.Ok σ → StrukturPasst K k0 σ ρ →
      StrukturPost K a3 (retryLauf (fun σ ρ => execBlock O passes R body σ ρ) bisF
        (fun σ ρ => execBlock O passes R ueber σ ρ) n σ ρ : Ausgang V l Γ) := by
  intro n
  induction n with
  | zero =>
    intro σ ρ hS hP
    obtain ⟨Λ0, o, hσ⟩ := hbis σ ρ
    simp only [retryLauf]
    by_cases hi : (bisF σ ρ).2 = true
    · rw [if_pos hi, hσ]
      exact ⟨Dekl.Ok.lese K Λ0 o hS, StrukturPasst.schwacher K h3 (StrukturPasst.lese K Λ0 o hP)⟩
    · rw [if_neg hi, hσ]
      exact StrukturPost.schwacher K h4 (hu _ ρ (Dekl.Ok.lese K Λ0 o hS) (StrukturPasst.lese K Λ0 o hP))
  | succ n ih =>
    intro σ ρ hS hP
    obtain ⟨Λ0, o, hσ⟩ := hbis σ ρ
    simp only [retryLauf]
    by_cases hi : (bisF σ ρ).2 = true
    · rw [if_pos hi, hσ]
      exact ⟨Dekl.Ok.lese K Λ0 o hS, StrukturPasst.schwacher K h3 (StrukturPasst.lese K Λ0 o hP)⟩
    · rw [if_neg hi, hσ]
      have hb1 := hb (σ.lese Λ0 o) ρ (Dekl.Ok.lese K Λ0 o hS) (StrukturPasst.lese K Λ0 o hP)
      rcases hx : execBlock O passes R body (σ.lese Λ0 o) ρ with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, r1⟩ |
        ⟨h1, σ1, ρ1⟩ | ⟨h1, σ1, ρ1⟩ | e1 | e1
      · rw [hx] at hb1
        exact ih σ1 ρ1 hb1.1 (StrukturPasst.schwacher K hs hb1.2)
      · rw [hx] at hb1; exact hb1
      · rw [hx] at hb1; exact hb1
      · rw [hx] at hb1; exact hb1.elim
      · rw [hx] at hb1; exact hb1.elim
      · trivial
      · trivial

theorem fall_retry {a a1 au a3 a' k0 : Abs} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (rest : Block D V l Γ Λ Λ')
    (hin : Abs.Schwacher k0 a) (hb : Folgt K O passes R k0 body a1) (hs : Abs.Schwacher k0 a1)
    (hu : Folgt K O passes R k0 ueber au) (h3 : Abs.Schwacher a3 k0) (h4 : Abs.Schwacher a3 au)
    (ih : Folgt K O passes R a3 rest a') :
    Folgt K O passes R a (Block.cons (Stmt.retry n bis body ueber) rest) a' := by
  intro σ ρ hS hP
  refine StrukturPost.cons_stmt K O passes R (a := a3) ?_ ih
  exact retry_post O passes R K _ (leseTest_inv bis) body ueber hb hs hu h3 h4 n σ ρ hS (StrukturPasst.schwacher K hin hP)

end Schleifen

end Gabbro.Grammatik
