/-
  File:      Grammatik/ArenaSperreInv.lean
  Subject:   THE WRITER OBLIGATION OF AN ARENA INVARIANT (PLAN-DYNAMIC.md section 8a.3, D2 and D3), proved against the
             PROPOSED meaning of an invariant name -- `Spec.lean` is not touched.

  D2 proposes that a declared arena is one more invariant NAME whose meaning is `Dekl.Ok` instead of the evaluation of an
  expression. Here that meaning is `InvHaeltD2 arena P i σ` (`arena i = some ⟨A, K⟩` ↦ `K.Ok σ`, otherwise `InvHaelt`),
  with the twins `InvAmRueckD2` (the owed invariants at a return) and `InvGutSD2` (the body obligation over `execEndH`, the
  exact shape of `InvGutS`).

    * `invGutSD2_arena` -- D3: if every owed arena invariant of `f` has a recognizer derivation `ErkE K Abs.leer (P.rumpf f)`,
      the arena is whole at entry, and the user's own obligation covers the other invariants, then `InvGutSD2` holds.
      The user does not prove anything about an arena invariant; the derivation is the proof, and it is a Prop that Lean's
      kernel checks.
    * `invGutSD2_ohne` -- a function that owes no invariant owes nothing new (as `invGutS_ohne`).

  The entry premise (`hein`) is NOT free: where the arena is known to be whole at the ENTRY of a writer is the lock
  invariant at the acquire (`abschnitt_start`) for a shared arena, and the start memory plus `invRuhe` for a per-thread one.
  It is stated as a premise on purpose and listed among the open items of 8a.3.
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreRuf

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

/-- **The arena declarations of a program** (proposal D1): the invariant names whose meaning is a structure invariant. -/
abbrev ArenaTafel (D : Deklaration) := D.Inv → Option (Σ A : FreiForm D, Dekl A)

/-- **The proposed meaning of an invariant name (D2).** -/
def InvHaeltD2 (arena : ArenaTafel D) (P : Programm D) (i : D.Inv) (σ : World D) : Prop :=
  match arena i with
  | none => InvHaelt P i σ
  | some s => s.2.Ok σ

/-- Every invariant `f` owes holds in `σ`, with the proposed meaning. -/
def InvAmRueckD2 (arena : ArenaTafel D) (P : Programm D) (f : D.Fn) (σ : World D) : Prop :=
  ∀ i ∈ D.invs, schuldet f i = true → InvHaeltD2 arena P i σ

/-- **`InvGutS` with an arbitrary meaning of the invariant names**: from `requires f`, a normal return of the body over
    `execEndH` satisfies `Mean i` for every invariant `f` owes. (`Mean := InvHaelt P` is `InvGutS`.) -/
def InvGutSM (Mean : D.Inv → World D → Prop) (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
    (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ (σ' : World D) (v : ErgVal D (D.erg f)),
          execEndH (V := vertragVon D f) S O' U passes R (P.rumpf f) σ ρ = EndAusgang.zurueck σ' v →
            ∀ i ∈ D.invs, schuldet f i = true → Mean i σ'

/-- `InvGutS` is `InvGutSM` at the present meaning. -/
theorem invGutS_iff_M (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (f : D.Fn) :
    InvGutS P passes Q S f ↔ InvGutSM (InvHaelt P) P passes Q S f :=
  Iff.rfl

/-- `InvGutS` of the proposed meaning. -/
abbrev InvGutSD2 (arena : ArenaTafel D) (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (f : D.Fn) :
    Prop :=
  InvGutSM (InvHaeltD2 arena P) P passes Q S f

/-- **The writer obligation of an arena invariant is the recognizer** (D3). The non-arena invariants keep the user's
    obligation (`hrest`); for an arena invariant owed by `f` the body is recognized (`hrec`) and the arena is whole at
    entry (`hein`), and the body returns in an arena-consistent world (`erkE_koerperH`, over `execEndH`). -/
theorem invGutSD2_arena (arena : ArenaTafel D) (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
    (f : D.Fn)
    (hrec : ∀ i ∈ D.invs, schuldet f i = true → ∀ s, arena i = some s → ErkE s.2 Abs.leer (P.rumpf f))
    (hein : ∀ i ∈ D.invs, schuldet f i = true → ∀ s, arena i = some s →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ → s.2.Ok σ)
    (hrest : InvGutSM (fun i σ => arena i = none → InvHaelt P i σ) P passes Q S f) :
    InvGutSD2 arena P passes Q S f := by
  intro O' hRO hRL hQ U hU R hRR hRV σ ρ hreq σ' v hexec i hi hs
  unfold InvHaeltD2
  cases ha : arena i with
  | none => exact hrest O' hRO hRL hQ U hU R hRR hRV σ ρ hreq σ' v hexec i hi hs ha
  | some s =>
    have hpost := erkE_koerperH S O' U passes R s.2 (hrec i hi hs s ha) σ ρ (hein i hi hs s ha σ ρ hreq) Abs.leer
    rw [hexec] at hpost
    exact hpost

/-- A function that owes no invariant owes nothing new, with the proposed meaning too. -/
theorem invGutSD2_ohne {arena : ArenaTafel D} {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
    {f : D.Fn} (h : ∀ i ∈ D.invs, schuldet f i = false) : InvGutSD2 arena P passes Q S f := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i hi hs
  rw [h i hi] at hs
  cases hs

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.invGutSD2_arena
