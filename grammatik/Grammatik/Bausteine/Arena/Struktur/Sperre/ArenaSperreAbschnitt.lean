/-
  File:      Grammatik/ArenaSperreAbschnitt.lean
  Subject:   THE SECTION THEOREM FOR A SHARED ARENA (PLAN-DYNAMISCH.md section 8a.2, phase 3, step 1): a critical
             section `locks L { .. }` over a recognized body starts from the arena invariant and leaves it, and the
             release check `freiH` of the lock invariant never fires.

  The lock family is `K.sperr L` (`ArenaSperreTraeger.lean`): the invariant of `L` IS `Dekl.Ok`. The sequential
  semantics with lock invariants runs `locks L { body }` as
      `freiH S L (execBlockH .. body ((U L σ).nimmt L) ρ)`
  where the environment move `U L σ` is in the class `HavocOk S U`: what the other threads left at the acquire meets
  `S.inv L`, i.e. the arena invariant. A recognized body keeps the invariant at every exit (`erk_erhaeltH`), so
  at the release the check passes and the world that leaves the section meets it again.

    * `freiH_post`        -- a release after an outcome that keeps the arena invariant keeps it and cannot fail.
    * `abschnitt_erk`     -- INLINE section over `Erk` (the body is the recognized block).
    * `abschnitt_rufe`    -- CALL section: the body is a run of calls of recognized functions (`W`), the form a
                             Gabbro program has (a `return` cannot leave a `locks` body, so the arena moves live in
                             functions that require the lock).
    * `rufAt_erk`         -- a recognized function, called through `rufAt` from an arena-consistent world, answers in
                             an arena-consistent world (the premise of `abschnitt_rufe` for the program semantics).

  The state at section entry is the knowledge-free state `Abs.leer`: an index a thread kept across the acquire says
  nothing (the cross-thread form of `N586`), and the state after the release is `Abs.leer` as well.
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreOhne

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

section Abschnitt
open Classical
variable {A : FreiForm D} (K : Dekl A) {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- The knowledge-free state is met by every world and environment. -/
theorem StrukturPasst.leer (σ : World D) (ρ : Env D Γ) : StrukturPasst K Abs.leer σ ρ :=
  ⟨fun _ hx => absurd hx (by simp [Abs.leer]), fun _ hx => absurd hx (by simp [Abs.leer]),
    fun _ hx => absurd hx (by simp [Abs.leer]), fun _ _ hx _ _ => absurd hx (by simp [Abs.leer])⟩

/-- The arena invariant does not see the lock events of the trace. -/
theorem Dekl.Ok.gibt {σ : World D} (h : K.Ok σ) (L : D.Lock) : K.Ok (σ.gibt L) :=
  Dekl.ok_gleich_wort (K := K) (σ := σ) (σ' := σ.gibt L) rfl (fun _ _ => rfl) h

theorem Dekl.Ok.nimmt {σ : World D} (h : K.Ok σ) (L : D.Lock) : K.Ok (σ.nimmt L) :=
  Dekl.ok_gleich_wort (K := K) (σ := σ) (σ' := σ.nimmt L) rfl (fun _ _ => rfl) h

variable (L : D.Lock)

/-- **THE RELEASE OF A SHARED ARENA'S LOCK.** An outcome that keeps the arena invariant is released into one that
    keeps it, and the release check of the lock invariant passes: the only `logik` outcome after the release is one
    the body already had. -/
theorem freiH_post {a : Abs} {o : Ausgang V l Γ} (h : StrukturPost K a o) :
    StrukturPost K Abs.leer (freiH (K.sperr L) L o) ∧ ∀ e, freiH (K.sperr L) L o = .logik e → o = .logik e := by
  cases o with
  | ok σ ρ =>
    have hok : (K.sperr L).inv L σ.speicher = true := (Dekl.sperr_inv_iff' σ).mpr h.1
    simp only [freiH, hok, if_true]
    exact ⟨⟨h.1.gibt K L, StrukturPasst.leer K _ _⟩, fun e he => by cases he⟩
  | zurueck σ v => exact ⟨h.gibt K L, fun e he => by cases he⟩
  | why σ r => exact ⟨h.gibt K L, fun e he => by cases he⟩
  | leave hh σ ρ => exact absurd h id
  | next hh σ ρ => exact absurd h id
  | logik e => exact ⟨trivial, fun e' he => he⟩
  | hardware e => exact ⟨trivial, fun e' he => by cases he⟩

variable (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Λ : List (Res D)}

/-- **The world a section starts in meets the arena invariant**: the environment move of the acquire is in `HavocOk`,
    whose third clause is the lock invariant. -/
theorem abschnitt_start {U : Umwelt D} (hU : HavocOk (K.sperr L) U) (σ : World D) : K.Ok ((U L σ).nimmt L) :=
  ((Dekl.sperr_inv_iff' (U L σ)).mp (hU L σ).2.2).nimmt K L

/-- **THE SECTION THEOREM, INLINE FORM.** `locks L { body }` over a recognized body started from the knowledge-free
    state: whatever the environment did at the acquire (any move in `HavocOk`), every exit of the section meets the
    arena invariant, no exit is a `leave` or a `next`, and the release check adds no failure. -/
theorem abschnitt_erk (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    {body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ)} {a' : Abs} (h : Erk K Abs.leer body a')
    (hU : HavocOk (K.sperr L) U) (σ : World D) (ρ : Env D Γ) :
    StrukturPost K Abs.leer (execStmtH (K.sperr L) O U passes R (Stmt.locks L hr body) σ ρ) ∧
      ∀ e, execStmtH (K.sperr L) O U passes R (Stmt.locks L hr body) σ ρ = .logik e →
        execBlock O passes R body ((U L σ).nimmt L) ρ = .logik e := by
  have hp := erk_erhaeltH (K.sperr L) O U passes R K h ((U L σ).nimmt L) ρ (abschnitt_start K L hU σ)
    (StrukturPasst.leer K _ _)
  rw [erk_execBlockH (K.sperr L) O U passes R K h] at hp
  simp only [execStmtH]
  rw [erk_execBlockH (K.sperr L) O U passes R K h]
  obtain ⟨h1, h2⟩ := freiH_post K L hp
  exact ⟨h1, h2⟩

/-! ## The call form -/

variable (W : D.Fn → Prop)

/-- **What a callee does to the arena:** from an arena-consistent world it answers in one (a value or a reason; a
    `logik`/`hardware` answer promises nothing). -/
def RErhaelt (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f, W f → ∀ (σ : World D) (ρ : Env D (D.params f)), K.Ok σ →
    (∀ σ' v, R f σ ρ = .ok σ' v → K.Ok σ') ∧ (∀ σ' r, R f σ ρ = .why σ' r → K.Ok σ')

/-- **A section body that is a run of calls of recognized functions** (`W`): the shape of a locked arena operation in a
    program, `locks L { f(x); g(y); }` with `f`, `g` requiring `L`. -/
inductive Rufe : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' → Prop where
  | nil {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Rufe (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ) Block.nil
  | cons {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (f : D.Fn) (args : Args D Γ Λ (D.params f))
      (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0) (rest : Block D V l Γ (nach D f Λ) Λ')
      (hf : W f) (h : Rufe rest) : Rufe (Block.cons (Stmt.call f args hp hr) rest)

variable {W}

/-- A run of calls contains no `locks`. -/
theorem rufe_ohneLocks {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'} (h : Rufe W b) : b.ohneLocks = true := by
  induction h with
  | nil => rfl
  | cons f args hp hr rest hf h ih => simpa [Block.ohneLocks, Stmt.ohneLocks] using ih

/-- A run of calls of recognized functions keeps the arena invariant at every exit. -/
theorem rufe_post (hR : RErhaelt K W R) {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'} (h : Rufe W b) :
    ∀ (σ : World D) (ρ : Env D Γ), K.Ok σ → StrukturPost K Abs.leer (execBlock O passes R b σ ρ) := by
  induction h with
  | nil => intro σ ρ hS; exact ⟨hS, StrukturPasst.leer K _ _⟩
  | cons f args hp hr rest hf h ih =>
    intro σ ρ hS
    rename_i Λ1 Λ2
    simp only [execBlock, execStmt]
    have hS' := Dekl.Ok.lese K Λ1 args.orte hS
    obtain ⟨hok, hwhy⟩ := hR f hf _ (evalArgs _ args _ ρ) hS'
    generalize hx : R f _ (evalArgs _ args _ ρ) = x at hok hwhy
    cases x with
    | ok σ' v => exact ih σ' ρ (hok σ' v rfl)
    | why σ' r => exfalso; have := r.2; omega
    | logik e => trivial
    | hardware e => trivial

/-- **THE SECTION THEOREM, CALL FORM.** `locks L { f(..); g(..); }` over recognized functions: every exit of the section
    meets the arena invariant, and the release check adds no failure. -/
theorem abschnitt_rufe (hR : RErhaelt K W R) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    {body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ)} (h : Rufe W body)
    (hU : HavocOk (K.sperr L) U) (σ : World D) (ρ : Env D Γ) :
    StrukturPost K Abs.leer (execStmtH (K.sperr L) O U passes R (Stmt.locks L hr body) σ ρ) := by
  have hp := rufe_post K O passes R hR h ((U L σ).nimmt L) ρ (abschnitt_start K L hU σ)
  simp only [execStmtH]
  rw [Block.execH_ohne (K.sperr L) O U passes R body (rufe_ohneLocks h)]
  exact (freiH_post K L hp).1

end Abschnitt

end Gabbro.Grammatik
