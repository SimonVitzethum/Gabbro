/-
  File:      Grammatik/ArenaSperreWachs.lean
  Subject:   `grow` AS A LOCKED COMMIT (PLAN-DYNAMISCH.md section 8a.2): the commit is ONE store, to the committed word
             `komm`, and the arena invariant does not read `komm` -- so the commit never exposes a broken arena, with or
             without the lock; what the lock adds is that the commit cannot interleave with the multi-store moves of
             another thread (alloc, link, free), whose intermediate states DO break the invariant.

    * `lesGlobs_ne_komm`  -- no word the structures read is the committed word.
    * `grow_atomar`       -- the world after a commit: the arena invariant holds iff it held before, every liveness is as
                             before, the counter is as before, and the committed word moved to `komSt + n`.
    * `grow_gesperrt`     -- the same inside a section: the executed `grow` is an `Erk` form (`wachs`), so
                             `abschnitt_erk` applies to every locked body that contains one.
    * `komm_wachstum`     -- the commit never shrinks the committed word (`0 ≤ n`; the surface demands `n ≥ 1`).

  What this does NOT say (named in 8a.3): the recognizer's alloc forms (`frisch`, from the counter) are guarded by the
  static bound `hi`, not by `komSt`; `Block.dynAlloc` (guard `stand < komSt`) is not a recognized form. So "every live slot
  is committed storage" (`stand ≤ komSt`) is not part of the lock invariant: it is a statement about the `dynAlloc` form
  and `grow` (here), not about every recognized body.
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreMaschine

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

section Wachs
variable {A : FreiForm D} {K : Dekl A}

/-- **No word the structures read is the committed word.** -/
theorem Dekl.lesGlobs_ne_komm {g : D.Glob} (h : g ∈ K.lesGlobs) : g ≠ A.komm := by
  rcases Dekl.mem_lesGlobs.mp h with rfl | rfl | ⟨d, -, rfl⟩ | ⟨b, -, rfl⟩
  · exact Ne.symm A.hzwei
  · exact A.hk2
  · exact d.G.h3
  · exact b.Wz.h3

/-- **A commit does not touch what the arena invariant reads.** -/
theorem grow_ok_iff (n : Int) (Λ : List (Res D)) (σ : World D) (h0 : 0 ≤ A.komSt σ + n)
    (h : A.komSt σ + n ≤ D.count A.tab) :
    K.Ok (nachGrow A.toDynForm n Λ σ h0 h) ↔ K.Ok σ :=
  Dekl.ok_gleich_wort_iff (K := K) (σ := σ) (σ' := nachGrow A.toDynForm n Λ σ h0 h)
    (by rw [(nachGrow_rahmen A.toDynForm n Λ σ h0 h).2])
    (fun g hg => (nachGrow_rahmen A.toDynForm n Λ σ h0 h).1 g (Dekl.lesGlobs_ne_komm hg))

/-- **The commit is atomic for every observer of the arena:** the arena invariant holds after it iff before, every
    liveness is as before, the counter is as before, and the committed word is `komSt + n`. There is no state between
    "not grown" and "grown" that breaks anything the structures read. -/
theorem grow_atomar (n : Int) (Λ : List (Res D)) (σ : World D) (h0 : 0 ≤ A.komSt σ + n)
    (h : A.komSt σ + n ≤ D.count A.tab) :
    (K.Ok (nachGrow A.toDynForm n Λ σ h0 h) ↔ K.Ok σ) ∧
    (∀ j, A.Lebt (nachGrow A.toDynForm n Λ σ h0 h) j ↔ A.Lebt σ j) ∧
    A.stand (nachGrow A.toDynForm n Λ σ h0 h) = A.stand σ ∧
    A.komSt (nachGrow A.toDynForm n Λ σ h0 h) = A.komSt σ + n := by
  obtain ⟨hg, hs⟩ := nachGrow_rahmen A.toDynForm n Λ σ h0 h
  have hk : A.kopfSt (nachGrow A.toDynForm n Λ σ h0 h) = A.kopfSt σ :=
    congrArg (fun w => (Wert.umTyp A.hkopf w).n) (hg A.kopf A.hk2)
  have hn : ∀ j, A.naechst (nachGrow A.toDynForm n Λ σ h0 h) j = A.naechst σ j := fun j => by
    simp only [FreiForm.naechst, hs]
  have hz : A.stand (nachGrow A.toDynForm n Λ σ h0 h) = A.stand σ :=
    congrArg (fun w => (Wert.umTyp A.hz w).n) (hg A.zaehl (Ne.symm A.hzwei))
  exact ⟨grow_ok_iff n Λ σ h0 h, A.lebt_gleich hk hn hz, hz, by
    rw [nachGrow, DynForm.komSt_schreibGlob, komSt_hin_her A.toDynForm _ h0 h]⟩

/-- The commit never shrinks the committed word. -/
theorem komm_wachstum (n : Int) (Λ : List (Res D)) (σ : World D) (h0 : 0 ≤ A.komSt σ + n)
    (h : A.komSt σ + n ≤ D.count A.tab) (hn : 0 ≤ n) :
    A.komSt σ ≤ A.komSt (nachGrow A.toDynForm n Λ σ h0 h) :=
  dynCommit_monoton A.toDynForm n Λ σ h0 h hn

/-- **`grow` as a locked commit.** A section whose body is `grow A by n else voll; rest` with a recognized `rest`: every exit
    meets the arena invariant. (The `grow` is the recognizer's `wachs` form; the section theorem does the rest.) -/
theorem grow_gesperrt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock) (O : Orakel D)
    (U : Umwelt D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L) (n : Int) (hwK : V.gschreibt A.komm = true)
    (hLK : gdarf D A.komm (Res.held L :: Λ)) (voll : Endblock D V l Γ (Res.held L :: Λ))
    (rest : Block D V l (Ty.int 0 (D.count A.tab) :: Γ) (Res.held L :: Λ) (Res.held L :: Λ)) {a'' : Abs}
    (hn : 0 ≤ n) (hv : Rein voll) (h : Erk K (Abs.leer.ext .offen) rest a'') (hU : HavocOk (K.sperr L) U) (σ : World D)
    (ρ : Env D Γ) :
    StrukturPost K Abs.leer
      (execStmtH (K.sperr L) O U passes R
        (Stmt.locks L hr (Block.dynGrowB A.toDynForm n hwK hLK voll rest)) σ ρ) :=
  (abschnitt_erk K L O U passes R hr (Erk.wachs n hn hwK hLK voll rest hv h) hU σ ρ).1

end Wachs

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.grow_atomar
#print axioms Gabbro.Grammatik.grow_gesperrt
