/-
  Lane-21 audit probe 5: unused premises and unused-equation patterns.

  Claim under test (pattern (b)):
  (1) `PCSchritt.leaf` carries `hΛa : Λa = Λ`, but `pcSchritt_gen`,
      `pcSchritt_eigen`, and `pcSchritt_fremd` all bind it as `_hΛa` and
      never use it: the counter/footprint identity is dead for projection
      and for the counter laws. Demonstrated: the same proofs go through
      with `hΛa` replaced by `True`.
  (2) Same for `hmark`/`hcar` in the projection and counter laws
      (`_hmark`, `_hcar` in `pcSchritt_gen`).
  (3) `genInv_gibt` takes `_hhaelt : L ∈ offen (M.spuren f)` (underscore:
      explicitly unused) — releasing needs no held-proof for the invariant.
-/
import Grammatik.Maschine

open Gabbro.Grammatik

variable {D : Deklaration}

/-- (1) `hΛa` is dead for the projection: variant with `True` instead. -/
theorem audit21_pcSchritt_gen_without_hLa
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M _M' : GenMaschine D) (pc _pc' : PCStand) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ M.spuren f)
    (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (_hpc : (prog f)[pc f]? = some (PCAtom.leaf Λa cs))
    (_dead : True)
    (_hmark : ∀ e ∈ neu, ∀ (m : D.Marke) (st : Nat),
      Res.marke m st ∈ e.lambda → m ∈ PCAtom.marks (PCAtom.leaf Λa cs))
    (_hcar : ∀ e ∈ neu, ∀ o, e.traeger = some o →
      o ∈ PCAtom.carriers (PCAtom.leaf Λa cs)) :
    GenSchritt P O passes M f
      ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
       M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩ :=
  GenSchritt.blatt M f V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein_nimmt

/-- (3) `gibt` preserves consistency without the held-proof: the `_hhaelt`
    premise of `genInv_gibt` is unused (it is underscore-bound in-file). -/
theorem audit21_gibt_konsistent_without_held
    (M : GenMaschine D) (f : Faden) (L : D.Lock)
    (hM : GenInv M) (f' : Faden) :
    Konsistent (genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f') := by
  by_cases hf : f' = f
  · subst f'
    rw [genUpdate_self]
    exact konsistent_cons trivial (hM.konsistent f)
  · rw [genUpdate_noteq _ _ _ hf]
    exact hM.konsistent f'

/-
CUTS:
- (1) demonstrates the dead-premise shape for `pcSchritt_gen`'s use of the
  leaf constructor; the analogous `_hmark`/`_hcar` cases are visible in-file
  (bound with underscore at lines 1389, 1408, 1419) and not separately
  re-proved here.
- "Unused" is relative to these consumers: `hΛa` IS used at line 2304
  (`zaehler_zeigt_atom` rewrite) and `hmark`/`hcar` ARE used in
  `pcSchritt_markInv`/`pcSchritt_carrierInv`. The audit point is that the
  projection and counter laws — the theorems that make PC steps behave like
  machine steps — do not need them, so a PC step can advance on a footprint
  that matches nothing.
-/
#print axioms audit21_pcSchritt_gen_without_hLa
#print axioms audit21_gibt_konsistent_without_held
