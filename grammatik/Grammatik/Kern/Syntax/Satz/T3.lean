/- Part 3 of 5 of `Satz` (split by instrumente/teile/lean-teilen.py; the umbrella `Satz.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Satz.T2

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section Schleifen
variable {W : D.Tab → Bool} {G : D.Glob → Bool} {Λ : List (Res D)} {bo : Option Int}

theorem traverseLauf_gut (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → GutAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, HeldB bo Λ σ.haelt → Gut W G σ (inv σ ρ).1) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      GutAusgang W G σ (traverseLauf (l := l) schritt inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil =>
      intro σ ρ hh σ' h
      simp only [traverseLauf] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hi σ ρ hh
      · simp [Ausgang.welt] at h
  | cons k ks ih =>
      intro σ ρ hh σ' h
      simp only [traverseLauf] at h
      split at h
      · simp [Ausgang.welt] at h
      · have hinv := hi σ ρ hh
        have hstep := hs (inv σ ρ).1 (.cons k ρ) (hinv.heldB hh)
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1.tail (g1.heldB hh) σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1.tail (g1.heldB hh) σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          split at h <;> simp [Ausgang.welt] at h
          subst h; exact g1.trans (hi σ1 ρ1.tail (g1.heldB hh))
        · rename_i σ1 v hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp [Ausgang.welt] at h
        · simp [Ausgang.welt] at h

theorem retryLauf_gut (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → GutAusgang W G σ (schritt σ ρ))
    (hb : ∀ σ ρ, HeldB bo Λ σ.haelt → Gut W G σ (bis σ ρ).1)
    (hu : ∀ σ ρ, HeldB bo Λ σ.haelt → GutAusgang W G σ (ueberlauf σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      GutAusgang W G σ (retryLauf schritt bis ueberlauf n σ ρ) := by
  intro n
  induction n with
  | zero =>
      intro σ ρ hh σ' h
      simp only [retryLauf] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hb σ ρ hh
      · exact (hb σ ρ hh).trans (hu _ ρ ((hb σ ρ hh).heldB hh) σ' h)
  | succ n ih =>
      intro σ ρ hh σ' h
      simp only [retryLauf] at h
      split at h
      · simp [Ausgang.welt] at h; subst h; exact hb σ ρ hh
      · have hinv := hb σ ρ hh
        have hstep := hs (bis σ ρ).1 ρ (hinv.heldB hh)
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 (g1.heldB hh) σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 (g1.heldB hh) σ' h)
        · rename_i σ1 ρ1 hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 v hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp [Ausgang.welt] at h
        · simp [Ausgang.welt] at h

theorem foreverLauf_gut (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, HeldB bo Λ σ.haelt → GutAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, HeldB bo Λ σ.haelt → Gut W G σ (inv σ ρ).1) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), HeldB bo Λ σ.haelt →
      GutAusgang W G σ (foreverLauf (l := l) a schritt inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ _ σ' h; simp [foreverLauf, Ausgang.welt] at h
  | succ n ih =>
      intro σ ρ hh σ' h
      simp only [foreverLauf] at h
      split at h
      · simp [Ausgang.welt] at h
      · have hinv := hi σ ρ hh
        have hstep := hs (inv σ ρ).1 ρ (hinv.heldB hh)
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 (g1.heldB hh) σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 (g1.heldB hh) σ' h)
        · rename_i σ1 ρ1 hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 v hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp [Ausgang.welt] at h
        · simp [Ausgang.welt] at h

end Schleifen
/-! ### The lock floor of a body (held-set relaxation, 2026-09-13)

    `ueberBoden c`: every `locks L` in the syntax takes a lock of rank at
    least `c`. A function with floor `some c` (`Signatur.boden`) may run
    under extra locks of its caller of rank below `c` (`RufPasst.hx`); the
    Satz needs its body to take only locks at or above `c` (`StufenOk`), so
    that no `locks` inside the callee re-takes or undercuts a lock held by a
    caller it does not know of. Calls are not followed: the callee's own
    body is checked at its own floor. -/

section Boden

variable {V : Vertrag D}

mutual

def Stmt.ueberBoden {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : Int) :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.ueberBoden c && e.ueberBoden c
  | .onOption _ p a => p.ueberBoden c && a.ueberBoden c
  | .onTag _ arms => arms.ueberBoden c
  | .onWhy _ arms => arms.ueberBoden c
  | .locks L _ body => decide (c ≤ D.rang L) && body.ueberBoden c
  | .breaking _ body => body.ueberBoden c
  | .traverse _ _ body => body.ueberBoden c
  | .retry _ _ body ueber => body.ueberBoden c && ueber.ueberBoden c
  | .forever _ _ body => body.ueberBoden c
  | _ => true

def Block.ueberBoden {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : Int) :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.ueberBoden c && rest.ueberBoden c
  | .bind _ rest => rest.ueberBoden c
  | .bindCall _ _ _ _ _ rest => rest.ueberBoden c
  | .bindCallInd _ _ _ _ _ rest => rest.ueberBoden c
  | .bindCallElse _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.ueberBoden c
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c
  | .regRead _ _ rest => rest.ueberBoden c
  | .regReadElse _ _ _ sonst rest => sonst.ueberBoden c && rest.ueberBoden c
  | .awaits _ _ _ _ rest => rest.ueberBoden c
  | .exchange _ _ _ _ rest => rest.ueberBoden c
  | .narrow _ _ _ sonst rest => sonst.ueberBoden c && rest.ueberBoden c
  | .check _ sonst rest => sonst.ueberBoden c && rest.ueberBoden c
  | .float _ _ _ _ _ rest => rest.ueberBoden c
  | .floatLit _ _ _ rest => rest.ueberBoden c
  | .floatOf _ _ _ rest => rest.ueberBoden c
  | .floatNarrow _ _ _ sonst rest => sonst.ueberBoden c && rest.ueberBoden c

def Endblock.ueberBoden {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (c : Int) :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.ueberBoden c && rest.ueberBoden c
  | .bind _ rest => rest.ueberBoden c
  | .bindCall _ _ _ _ _ rest => rest.ueberBoden c
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.ueberBoden c
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c

def Arms.ueberBoden {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (c : Int) : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.ueberBoden c && rest.ueberBoden c

def GrundArms.ueberBoden {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} (c : Int) :
    GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.ueberBoden c && rest.ueberBoden c

end

/-- The syntax respects the floor `bo` (vacuous for `none`). -/
abbrev Stmt.BodenOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (bo : Option Int)
    (s : Stmt D V l Γ Λ Λ') : Prop := ∀ c, bo = some c → s.ueberBoden c = true
abbrev Block.BodenOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (bo : Option Int)
    (b : Block D V l Γ Λ Λ') : Prop := ∀ c, bo = some c → b.ueberBoden c = true
abbrev Endblock.BodenOk {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (bo : Option Int)
    (b : Endblock D V l Γ Λ) : Prop := ∀ c, bo = some c → b.ueberBoden c = true
abbrev Arms.BodenOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (bo : Option Int) (a : Arms D V l Γ Λ Λ' cs) : Prop := ∀ c, bo = some c → a.ueberBoden c = true
abbrev GrundArms.BodenOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (bo : Option Int) (a : GrundArms D V l Γ Λ Λ' n) : Prop := ∀ c, bo = some c → a.ueberBoden c = true

end Boden
/-- **The floors of a program are respected** (decidable per program): the
    body of every function with floor `some c` takes only locks of rank at
    least `c`. Trivial for a declaration without floors (`stufenOk_ohne`). -/
def StufenOk (P : Programm D) : Prop :=
  ∀ f c, (D.signatur f).boden = some c → (P.rumpf f).ueberBoden c = true

theorem stufenOk_ohne (P : Programm D) (h : ∀ f : D.Fn, (D.signatur f).boden = none) :
    StufenOk P := fun f c hc => by rw [h f] at hc; cases hc

set_option hygiene false in
/-- Floor bookkeeping: the floor premise of a sub-block from the enclosing one (`hbo`). -/
macro "boden_tac" : tactic => `(tactic|
  (intro c hc
   have hsc := hbo c hc
   simp only [Stmt.ueberBoden, Block.ueberBoden, Endblock.ueberBoden, Arms.ueberBoden,
     GrundArms.ueberBoden, Bool.and_eq_true, decide_eq_true_eq] at hsc
   first | exact hsc | exact hsc.1 | exact hsc.2 | exact hsc.2.1 | exact hsc.2.2 | exact hsc.1.1 | exact hsc.1.2))


end Gabbro.Grammatik
