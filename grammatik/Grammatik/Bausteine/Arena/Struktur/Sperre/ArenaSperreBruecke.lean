/-
  File:      Grammatik/ArenaSperreBruecke.lean
  Subject:   THE BRIDGE FROM MACHINE G TO THE RECOGNIZER (PLAN-DYNAMISCH.md section 8a.3, premise 2): a writer's frame, run
             by the small steps of one thread of the call machine, returns an arena-consistent memory.

  `rufG_adaequat_ruf` (RufAdaequatRufG/T8) says: a body in the covered fragment (`EndR`), started at a thread's world,
  is realised by steps of that thread exactly as `execEnd O passes (rufRumpf ..)` computes it -- the return world IS the
  memory the machine holds after the frame is popped. The recognizer talks about `execEnd` (`erkE_koerper`, any handler),
  so the two meet at `execEnd`: the machine's memory after the return meets the arena invariant when the world at entry did.

  The premise PAIR is what an accepted unit supplies for a writer `b`: coverage `EndR` (the checker's fragment, the Bool
  `programmImFragmentG`) and the recognizer derivation `ErkE K Abs.leer b` (the exporter's certificate). A body is covered
  and recognized only when loop-free (`EndR` has no guard inside a loop body); a recognized loop body is a statement about
  `execEnd` only (`erkE_koerper`), and its machine correspondence is named open in 8a.3.
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreAbschnitt
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

/-- **A recognized, covered writer returns an arena-consistent memory in the machine.** From a thread of the call machine
    whose world meets the arena invariant at the entry of the writer's body, the steps of the thread reach a machine whose
    frame is popped with the return value, whose shared memory is the return world's -- and meets the arena invariant. -/
theorem erkE_maschine {A' : FreiForm D} (K : Dekl A') (P : Programm D) (O : Orakel D) (passes n : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (spur : List (Ereignis D)) (log : List (RufEreignisF D)) {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (b : Endblock D (vertragVon D fn) false Γ Λ)
    (A : D.Lock → Prop) (hb : EndR A (Tief P A n) b) (hE : ErkE K Abs.leer b)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (hnw : caller.wartend = false) (hΛ : HeldGenau Λ (offen spur))
    (hfrei : ∀ L, A L → RufFreiG M f L) (hOk : K.Ok (M.weltVon f))
    (σ' : World D) (v : ErgVal D (vertragVon D fn).erg)
    (hexec : execEnd O passes (rufRumpf P O passes n) b (M.weltVon f) ρ = .zurueck σ' v) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: (ext ++ log)⟩ ∧
      M'.speicher = σ'.speicher ∧ (∀ g, g ≠ f → M'.faeden g = M.faeden g) ∧ K.Ok (M'.speicher.welt []) := by
  obtain ⟨M', ext, hl, hf, hsp, hfr⟩ := rufG_adaequat_ruf P O passes n M f fn rho s0 caller rst spur log ρ b A hb hM hnw
    hΛ hfrei σ' v hexec
  have hpost := erkE_koerper O passes (rufRumpf P O passes n) K hE (M.weltVon f) ρ hOk Abs.leer
  rw [hexec] at hpost
  refine ⟨M', ext, hl, hf, hsp, hfr, ?_⟩
  rw [hsp]
  exact (Dekl.ok_spur σ' []).mpr hpost

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.erkE_maschine
