import Grammatik.Code.Refine.Calls.Func

/-
  File:      Grammatik/Code/Refine/Closure.lean
  Subject:   TRACK L, PHASE L1 -- THE CLOSURE: every call of the program is refined, by induction on
             the recursion depth.

    * `fnOk_of_lowerFn` -- a module that holds the lowering of every function satisfies `FnOk`;
    * `rufAt_ok_inv` -- an `ok` answer of the source meaning of a call (`rufAt`, the body with its
      contract) comes from a `return` of the body, in a world that differs from the returned one
      only in the trace (which `Rep` does not see);
    * `lowerFn_callref` -- **for every depth `n`, the lowered functions refine `rufAt n`**: if the
      source meaning of a call of `f` is `ok σ' v`, the IR function of `f`, entered with the images
      of the arguments, returns the image of `v` and leaves a memory that represents `σ'` and keeps
      the caller's cells. The step from `n` to `n + 1` is `lowerFn_run` with the depth-`n` result as
      the meaning of the calls in the body -- the recursion of the program is closed by this
      induction, with no assumption about the callees beyond the module holding their lowerings.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Programm World Env Wert Ctx Res Vertrag Orakel ErgVal RufAusgang
  EndAusgang vertragVon rufAt Signatur execEnd)

variable {D : Deklaration}

theorem bindCode_supp {τ : GTy} {oe : Opd} {r : Nat} {c : List Instr × Nat × Nat}
    (h : bindCode τ oe r = some c) : supp τ = true := by
  unfold bindCode at h
  rcases hcm : cvtM τ oe r with _ | ⟨cm, om, r3⟩
  · simp only [hcm, reduceCtorEq] at h
  simp only [hcm] at h
  cases hbb : supp τ
  · simp only [hbb, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  · rfl

theorem prologue_supp : ∀ (ps : List GTy) (i r : Nat) {code : List Instr} {cenv0 : List Reg} {r' : Nat},
    prologue ps i r = some (code, cenv0, r') → ∀ τ ∈ ps, supp τ = true
  | [], _, _, _, _, _, _ => fun τ hτ => nomatch hτ
  | τ :: τs, i, r, code, cenv0, r', h => by
      simp only [prologue] at h
      rcases hp : prologue τs (i + 1) r with _ | ⟨c2, as, r1⟩
      · simp only [hp, reduceCtorEq] at h
      simp only [hp] at h
      rcases hb : bindCode τ (.reg i) r1 with _ | ⟨c, a, r2⟩
      · simp only [hb, reduceCtorEq] at h
      intro σ hσ
      rcases List.mem_cons.mp hσ with rfl | h'
      · exact bindCode_supp hb
      · exact prologue_supp τs (i + 1) r hp σ h'

/-- A module that holds the lowering of every function satisfies `FnOk`. -/
theorem fnOk_of_lowerFn (lay : Layout D) (P : Programm D) (M : Modl) (name : D.Fn → String)
    (hfun : ∀ f, ∃ func, lowerFn lay P f (name f) = some func ∧ M.funs[lay.fno f]? = some func) :
    FnOk lay M := by
  intro f
  obtain ⟨func, hlf, hM⟩ := hfun f
  unfold lowerFn at hlf
  rcases hp : prologue (D.params f) 0 (D.params f).length with _ | ⟨pc, cenv, r⟩
  · simp only [hp, reduceCtorEq] at hlf
  simp only [hp] at hlf
  rcases hl : lowerEnd lay cenv (0, 0) (P.rumpf f) 1 ⟨r, 2⟩ with _ | ⟨blks, s'⟩
  · simp only [hl, reduceCtorEq] at hlf
  simp only [hl, Option.some.injEq] at hlf
  subst hlf
  exact ⟨prologue_supp _ _ _ hp, _, ⟨0, [], pc, .jmp 1⟩, hM, rfl, rfl, rfl, rfl⟩

/-- `Rep` does not see the trace: a chain of reads leaves it as it was. -/
theorem rep_foldl_lese {lay : Layout D} {m : Mem} {α : Type} (l : List α) (g : α → List (Res D))
    (h : α → List (D.Tab ⊕ D.Glob)) :
    ∀ σ : World D, Rep lay (l.foldl (fun σ' i => σ'.lese (g i) (h i)) σ) m ↔ Rep lay σ m := by
  induction l with
  | nil => intro σ; exact Iff.rfl
  | cons a l ih => intro σ; exact ih (σ.lese (g a) (h a))

/-- An `ok` answer of the source meaning of a call comes from a `return` of the body. -/
theorem rufAt_ok_inv (P : Programm D) (O : Orakel D) (passes : Nat) (n : Nat) (f : D.Fn)
    (σ : World D) (ρ : Env D (D.params f)) (σ' : World D) (v : ErgVal D (D.erg f))
    (h : rufAt P O passes (n + 1) f σ ρ = RufAusgang.ok σ' v) :
    ∃ σ'', execEnd (V := vertragVon D f) O passes (rufAt P O passes n) (P.rumpf f)
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ = EndAusgang.zurueck σ'' v ∧
      ∀ (lay : Layout D) (m : Mem), Rep lay σ' m ↔ Rep lay σ'' m := by
  simp only [rufAt] at h
  split at h
  · cases h
  rename_i hreq
  split at h
  · rename_i σ'' v'' hx
    split at h
    · cases h
    rename_i hens
    split at h
    · cases h
    · injection h with h1 h2
      subst h1
      have h2' : v'' = v := h2
      subst h2'
      refine ⟨σ'', hx, fun lay m => ?_⟩
      rw [rep_foldl_lese]
      exact Iff.rfl
  all_goals first
    | exact absurd ‹false = true› (by decide)
    | (cases h; done)

/-- A `why` answer of the source meaning of a call comes from a `why` of the body. -/
theorem rufAt_why_inv (P : Programm D) (O : Orakel D) (passes : Nat) (n : Nat) (f : D.Fn)
    (σ : World D) (ρ : Env D (D.params f)) (σ' : World D) (r : Fin (D.gruende f))
    (h : rufAt P O passes (n + 1) f σ ρ = RufAusgang.why σ' r) :
    execEnd (V := vertragVon D f) O passes (rufAt P O passes n) (P.rumpf f)
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ = EndAusgang.why σ' r := by
  simp only [rufAt] at h
  split at h
  · cases h
  rename_i hreq
  split at h
  · rename_i σ'' v'' hx
    split at h
    · cases h
    rename_i hens
    split at h
    · cases h
    · cases h
  · rename_i σ'' r'' hx
    injection h with h1 h2
    subst h1
    have h2' : r'' = r := h2
    subst h2'
    exact hx
  all_goals first
    | exact absurd ‹false = true› (by decide)
    | (cases h; done)

/-- **The recursion is closed.** For every depth `n`, the lowered functions refine the source meaning
    of a call `rufAt n`: if `rufAt n f σ ρ = ok σ' v`, the IR function of `f`, entered with the images
    of the arguments, runs to a `ret` of the image of `v`, leaves a memory that represents `σ'`, and
    keeps the caller's memory (`Keep`); if it is `why σ' r`, it runs to a `ret` of the reason's word. The
    module is assumed to hold the lowering of every function and nothing else about the callees. -/
theorem lowerFn_callref (lay : Layout D) (hL : LayoutOk lay) (P : Programm D) (O : Orakel D)
    (passes : Nat) (M : Modl) (S : Sees) (name : D.Fn → String)
    (hfun : ∀ f, ∃ func, lowerFn lay P f (name f) = some func ∧ M.funs[lay.fno f]? = some func) :
    ∀ n, CallRef lay M S (rufAt P O passes n) := by
  have hFn := fnOk_of_lowerFn lay P M name hfun
  intro n
  induction n with
  | zero =>
      refine ⟨fun f σ ρ σ' v h => ?_, fun f σ ρ σ' r h => ?_⟩
      · simp only [rufAt, reduceCtorEq] at h
      · simp only [rufAt, reduceCtorEq] at h
  | succ n ih =>
      refine ⟨fun f σ ρ σ' v hok m rs ks dst hR hW hA => ?_, fun f σ ρ σ' r hwhy m rs ks dst hR hW hA => ?_⟩
      · obtain ⟨σ'', hex, hrep⟩ := rufAt_ok_inv P O passes n f σ ρ σ' v hok
        obtain ⟨func, hlf, hM⟩ := hfun f
        obtain ⟨m', f', hr, hf1, hf2, hret, hR', hW', hK⟩ := lowerFn_run lay hL P f (name f) func hlf M S
          (lay.fno f) hM O passes (rufAt P O passes n) hFn ih
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ m rs ks dst hR hW hA σ'' v hex
        exact ⟨m', f', hr, hf1, hf2, hret, (hrep lay m').2 hR', hW', hK⟩
      · have hex := rufAt_why_inv P O passes n f σ ρ σ' r hwhy
        obtain ⟨func, hlf, hM⟩ := hfun f
        exact lowerFn_run_why lay hL P f (name f) func hlf M S (lay.fno f) hM O passes (rufAt P O passes n)
          hFn ih (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ m rs ks dst
          hR hW hA σ' r hex

end Gabbro.Code.Lower
