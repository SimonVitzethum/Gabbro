/- The shared epilogue preserves the saved result, parameters and entry snapshots. -/
module
public import Stage0.Senke.Rueckkehr.Invariant
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}
set_option maxHeartbeats 2000000

/-- This contract is threaded unchanged through the ordinary block simulation. -/
theorem lowPost_ok (P : Programm D) (f : D.Fn) (σ0 σ : World D)
    (ρ : Env D (D.params f)) (v : ErgVal D (D.erg f))
    {fp : Runner.W} {K d : Nat} {code : List II} {top : Nat}
    (lower : lowPost L (functionFrame P f) P f d = some (code, top)) (fits : top ≤ K)
    (above : FB ≤ d) (layout : LayIn L) (separated : fp.toNat + 8 * K ≤ L.lo)
    (m : Runner.Mem) (pc : Runner.W)
    (pre : PreS L m pc fp K d code (ergEnv (D.erg f) v ρ) (functionFrame P f).ensReserved)
    (world : WeltAt m L σ)
    (saved : EntrySnapshots.At L σ0 m fp (oldCells (P.ensures f)) FB) :
    if returnFault P f σ0 σ ρ v ≠ 0 then Stops ⟨pc, fp⟩ m (returnFault P f σ0 σ ρ v)
    else ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
      Agree fp d K m m' := by
  simp only [lowPost, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lower
  obtain ⟨⟨ce, te⟩, he, ⟨ci, ti⟩, hi, rfl, rfl⟩ := lower
  have scratch := lowInvs_scratch L P f d D.invs ci ti hi
  let post := σ.lese (vertragVon D f).ende (P.ensures f).orte
  have postEq : σ.lese (vertragVon D f).ende (P.ensures f).orte = post := rfl
  have postAt : WeltAt m L post := world
  have exprPre := PreS.welt pre.left (Nat.le_refl K) postAt layout separated
  obtain ⟨m1, run, changed, b, read, encoded⟩ :=
    lowEns_ok (functionFrame P f) σ0 post (fun _ h => h) layout (P.ensures f)
      d ce te he (by omega) m pc _ exprPre saved rfl |>.word trivial
  have next := pre.next changed (Nat.le_refl _) (by omega)
  have frame1 := pre.frame.agree changed
  have guardFar := codeFar_left (by rw [← List.length_append]; exact next.far)
  simp only [Enc] at encoded
  by_cases failure : wahr? (eval σ0 (P.ensures f) post (ergEnv (D.erg f) v ρ)) = false
  · have fault : returnFault P f σ0 σ ρ v = 102 := by simp only [returnFault, postEq, failure, ite_true]
    rw [fault, if_pos (by decide)]
    have zero : b = 0 := by simpa only [failure, Bool.false_eq_true, ↓reduceIte] using encoded
    exact Stops.prefix run (guard_stop (codeAt_left next.code) guardFar frame1
      (by omega) (by omega) pre.small (by decide) (by simpa only [zero] using read))
  · have success : wahr? (eval σ0 (P.ensures f) post (ergEnv (D.erg f) v ρ)) = true := by
      cases h : wahr? (eval σ0 (P.ensures f) post (ergEnv (D.erg f) v ρ)) <;> simp_all
    have one : b = 1 := by simpa only [success, ite_true] using encoded
    have guardRun := guard_pass (codeAt_left next.code) (by omega) read (by rw [one]; decide)
    have restPre : PreS L m1 _ fp K d ci (Env.nil : Env D []) :=
      ⟨by simpa only [frei, contextWords_nil, Nat.add_zero] using above, next.small, next.frame,
        codeAt_right next.code, codeFar_tail (a := guardC d 102 d) next.far,
        (fun _ x => nomatch x), trivial, wstab_true _ _⟩
    have finalAt := owedWorld_at P f post m1
      (exprPre.wstab m m1 postAt (changed.mono (Nat.zero_le _)))
    have result := lowInvs_ok P f (owedWorld P f post) above layout separated
      D.invs ci ti hi (by omega) m1 _ restPre finalAt
    simp only [returnFault, postEq, if_neg failure]
    unfold owedFailure
    split at result
    · next bad =>
      rw [if_pos bad, if_pos (by decide)]
      exact Stops.prefix (run.trans guardRun) result
    · next good =>
      rw [if_neg good, if_neg (by simp)]
      obtain ⟨m2, run2, changed2⟩ := result
      refine ⟨m2, ?_, changed.trans changed2⟩
      simpa only [List.append_assoc, List.length_append, pc_add, Nat.add_assoc]
        using run.trans (guardRun.trans run2)

end Gabbro.Stage0.Senke
