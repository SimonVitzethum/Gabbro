/-
  File:      Grammatik/ArenaErkennerBeweis.lean
  Subject:   THE RECOGNIZER IS SOUND (PLAN-DYNAMISCH.md section 8a.1): every body `Erk` accepts keeps the arena
             invariant at EVERY exit, a body that falls off meets the abstract state it ends in, and no recognized body
             ends in a `leave` or a `next`.

    `erk_erhaelt`  -- `Erk K a b a'`, `K.Ok σ` and `StrukturPasst K a σ ρ` give `StrukturPost K a'` of the run of `b` from `(σ, ρ)`.
    `erk_koerper`  -- the corollary a function needs: a body that knows nothing at entry (every position `offen`).

  The proof is an induction on the derivation; each case is a theorem of `ArenaErkFallAlloc.lean` (allocator, guards,
  payload stores, branches), `ArenaErkFallListe.lean` (list moves), `ArenaErkFallBaum.lean` (tree moves) or
  `ArenaErkFallSchleife.lean` (loops), which apply the executed-form theorems with the side conditions discharged by the
  abstract state.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkFallSchleife

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

section Beweis
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D}

/-- **THE RECOGNIZER IS SOUND.** -/
theorem erk_erhaelt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a a' : Abs} {b : Block D V l Γ Λ Λ'}
    (h : Erk K a b a') : Folgt K O passes R a b a' := by
  induction h with
  | @nil l Γ Λ a => exact fall_nil O passes R K a
  | @push l Γ Λ Λ' a a' d hd x hwT hLT hwG hLG rest hx h ih =>
    exact fall_push O passes R K d hd x hwT hLT hwG hLG rest hx ih
  | @pop l Γ Λ Λ' a a'' d hd hwG hLG hLT voll rest hv h ih =>
    exact fall_pop O passes R K d hd hwG hLG hLT voll rest hv ih
  | @unlink l Γ Λ Λ' a a'' d hd p hwT hLT voll rest hp hv h ih =>
    exact fall_unlink O passes R K d hd p hwT hLT voll rest hp hv ih
  | @kopf l Γ Λ Λ' a a'' d hd hLG voll rest hv h ih =>
    exact fall_kopf O passes R K d hd hLG voll rest hv ih
  | @nach l Γ Λ Λ' a a'' d hd p hLT voll rest hp hv h ih =>
    exact fall_nach O passes R K d hd p hLT voll rest hp hv ih
  | @frisch l Γ Λ Λ' a a'' v hwT hLT hwG hLG voll rest hv h ih =>
    exact fall_frisch O passes R K v hwT hLT hwG hLG voll rest hv ih
  | @nimm l Γ Λ Λ' a a'' v hwT hLT hwK hLK voll rest hv h ih =>
    exact fall_nimm O passes R K v hwT hLT hwK hLK voll rest hv ih
  | @frei l Γ Λ Λ' a a' x hwT hLT hwK hLK rest hx h ih =>
    exact fall_frei O passes R K x hwT hLT hwK hLK rest hx ih
  | @wachs l Γ Λ Λ' a a'' n hn hwK hLK voll rest hv h ih =>
    exact fall_wachs O passes R K n hwK hLK voll rest hv ih
  | @pruefe l Γ Λ Λ' a a' c voll rest hv h ih =>
    exact fall_pruefe O passes R K c voll rest hv ih
  | @nutzlast l Γ Λ Λ' a a' i e hwT hLT rest h ih =>
    exact fall_nutzlast O passes R K i e hwT hLT rest ih
  | @ite l Γ Λ Λ1 Λ' a a1 a2 a3 a' c t e rest ht he h1 h2 h iht ihe ih =>
    exact fall_ite O passes R K c t e rest h1 h2 iht ihe ih
  | @wurzelEin l Γ Λ Λ' a a' b hb x hwT hLT hwG hLG voll rest hx hv h ih =>
    exact fall_wurzelEin O passes R K b hb x hwT hLT hwG hLG voll rest hx hv ih
  | @wurzelKopf l Γ Λ Λ' a a'' b hb hLG voll rest hv h ih =>
    exact fall_wurzelKopf O passes R K b hb hLG voll rest hv ih
  | @kind l Γ Λ Λ' a a'' b hb C hC p hLT voll rest hp hv h ih =>
    exact fall_kind O passes R K b hb C hC p hLT voll rest hp hv ih
  | @haengen l Γ Λ Λ' a a' b hb Cp Co hs p i hwT hLT voll rest hp hi hv h ih =>
    exact fall_haengen O passes R K b hb Cp Co hs p i hwT hLT voll rest hp hi hv ih
  | @abschneiden l Γ Λ Λ' a a'' b hb C hC p hwT hLT voll voll2 rest hp hv hv2 h ih =>
    exact fall_abschneiden O passes R K b hb C hC p hwT hLT voll voll2 rest hp hv hv2 ih
  | @wurzelAus l Γ Λ Λ' a a'' b hb hwG hLG hLT voll voll2 rest hv hv2 h ih =>
    exact fall_wurzelAus O passes R K b hb hwG hLG hLT voll voll2 rest hv hv2 ih
  | @forever l Γ Λ Λ' a a1 a' k0 an inv body rest hin hb hs h ihb ih =>
    exact fall_forever O passes R K an inv body rest hin ihb hs ih
  | @traverse l Γ Λ Λ' a a1 a' k0 t inv body rest hin hb hs h ihb ih =>
    exact fall_traverse O passes R K t inv body rest hin ihb hs ih
  | @retry l Γ Λ Λ' a a1 au a3 a' k0 n bis body ueber rest hin hb hs hu h3 h4 h ihb ihu ih =>
    exact fall_retry O passes R K n bis body ueber rest hin ihb hs ihu h3 h4 ih

/-- **A body that knows nothing at entry** (every position `offen`, as for parameters) keeps the arena invariant at
    every exit. -/
theorem erk_koerper {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a' : Abs} {b : Block D V l Γ Λ Λ'}
    (h : Erk K Abs.leer b a') (σ : World D) (ρ : Env D Γ) (hS : K.Ok σ) :
    StrukturPost K a' (execBlock O passes R b σ ρ) :=
  erk_erhaelt O passes R K h σ ρ hS
    ⟨fun _ hx => absurd hx (by simp [Abs.leer]), fun _ hx => absurd hx (by simp [Abs.leer]),
      fun _ hx => absurd hx (by simp [Abs.leer]), fun _ _ hx _ _ => absurd hx (by simp [Abs.leer])⟩

/-- **The same, for an outcome that is only named:** the run of the body is given as an equation, so that nothing has to be
    evaluated to state the promise (a long run is expensive to unfold by the elaborator). -/
theorem erk_koerper_lauf {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {a' : Abs} {b : Block D V l Γ Λ Λ'}
    (h : Erk K Abs.leer b a') (σ : World D) (ρ : Env D Γ) (hS : K.Ok σ) {o : Ausgang V l Γ}
    (ho : execBlock O passes R b σ ρ = o) : StrukturPost K a' o :=
  ho ▸ erk_koerper O passes R K h σ ρ hS

end Beweis

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.erk_erhaelt
#print axioms Gabbro.Grammatik.erk_koerper
#print axioms Gabbro.Grammatik.erk_koerper_lauf
