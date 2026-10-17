/- Part 6 of 6 of `RufUmkehrRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufUmkehrRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T5

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The bind witness up to its waiting state, as a run up to the first pop:
    `endeEntf`, `dannIteWahr`, `dannBindCall`. -/
theorem t4B_wartet_ueber :
    ∃ M3 : RufMaschineG t4D, RufLaufUeber t4P t4O 0 0 0 (t4M t4B t4BRumpf) M3 ∧
      ∃ caller : RufRahmenG t4D, (M3.faeden 0).stapel = [caller, t4Unten] ∧
        caller.f = t4B ∧ caller.wartend = true ∧ (M3.faeden 0).kopf.f = t4G := by
  have hZ0 : ZustandG (t4M t4B t4BRumpf) 0 [t4Unten] t4B Env.nil (t4Sp.welt []) []
      (Env.nil : Env t4D []) (.ende t4BRumpf) ((t4M t4B t4BRumpf).weltVon 0) := ⟨rfl, rfl⟩
  obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := t4P) (O := t4O) (passes := 0) hZ0.1
    (.ite .tru t4BindBlock .nil) (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil)
    Env.nil rfl rfl
  obtain ⟨M2, hs2, hZ2⟩ := w_iteWahr (P := t4P) (O := t4O) (passes := 0) hZ1.1
    .tru t4BindBlock .nil .nil
    (.ende (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil)) Env.nil rfl rfl
    (fun L => nomatch L)
  obtain ⟨M3, hs3, hZ3⟩ := w_bindCall (P := t4P) (O := t4O) (passes := 0) hZ2.1
    t4G .nil rfl (t4Hp t4B) rfl (.cons (.assignSlot () () t4Idx1x (.var .here) rfl t4Darf) .nil)
    (.dann .nil (.ende (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil))) Env.nil
    rfl (fun L => nomatch L)
  have h0 : 0 < ((t4M t4B t4BRumpf).faeden 0).stapel.length := Nat.zero_lt_succ _
  have h1 : 0 < (M1.faeden 0).stapel.length := by rw [hZ1.1]; exact Nat.zero_lt_succ _
  have h2 : 0 < (M2.faeden 0).stapel.length := by rw [hZ2.1]; exact Nat.zero_lt_succ _
  refine ⟨M3, RufLaufUeber.schritt h0 hs1 (RufLaufUeber.schritt h1 hs2
    (RufLaufUeber.schritt h2 hs3 (RufLaufUeber.refl M3))), _, by rw [hZ3.1], rfl, rfl,
    by rw [hZ3.1]⟩

/-- **AGREEMENT on the bind witness, both halves** (the former finding
    `befund_wartet`). From the state in which the caller of `t4B` WAITS
    below the callee, along every run of the thread up to the first pop of
    the caller's frame: no head of any thread waits (the verbatim pops can
    no longer restore the waiting caller), and if the run pops the
    caller's frame, the logged return value is the sequential one, `9`. -/
theorem wartet_einig_voll :
    (∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧ (show Zahl 0 100 from v).n = 9) ∧
    ∃ M3 : RufMaschineG t4D, RufLaufUeber t4P t4O 0 0 0 (t4M t4B t4BRumpf) M3 ∧
      (∃ caller : RufRahmenG t4D, (M3.faeden 0).stapel = [caller, t4Unten] ∧
        caller.f = t4B ∧ caller.wartend = true) ∧
      ∀ M' : RufMaschineG t4D, RufLaufUeber t4P t4O 0 0 0 M3 M' →
        (∀ g, (M'.faeden g).kopf.wartend = false) ∧
        ((M'.faeden 0).stapel.length ≤ 0 →
          ∃ (v : ErgVal t4D (t4D.erg t4B)) (s1 : World t4D) (ext : List (RufEreignisF t4D)),
            (M'.faeden 0).log = RufEreignisF.rueck t4B Env.nil v (t4Sp.welt []) s1 :: ext ∧
            (show Zahl 0 100 from v).n = 9) := by
  obtain ⟨σ0, v0, hex0, h50, h30, h90⟩ := t4B_exec
  refine ⟨⟨σ0, v0, hex0, h90⟩, ?_⟩
  obtain ⟨M3, hu3, caller, hst, hf, hw, _⟩ := t4B_wartet_ueber
  refine ⟨M3, hu3, ⟨caller, hst, hf, hw⟩, ?_⟩
  intro M' hu'
  refine ⟨fun g => (rufLaufG_sauber (hu3.trans hu').lauf (t4M_sauber t4B t4BRumpf) g).kopf_wartend,
    ?_⟩
  intro hpop
  obtain ⟨v1, s1, ext, σ1, hlog, hex1, _⟩ := rufG_adaequat_ruf_umkehr t4P t4O 0 1
    (t4M t4B t4BRumpf) 0 t4B Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4BRumpf
    (fun _ => False) (t4BRumpf_K _) t4BRumpf_kOk rfl M' (hu3.trans hu') hpop
  cases hex0.symm.trans hex1
  exact ⟨v0, s1, ext ++ [], hlog, h90⟩

/-! ## CUTS:
  What is proved: the converse with calls (`rufG_adaequat_ruf_umkehr`) --
  for a frame whose body is covered at depth `n` by the fragment of the
  converse, every run of its thread up to the first pop of the frame
  logs the value the sequential semantics with the
  body-running handler `rufRumpf n` returns, in a world with the logged
  memory. Proved through a pending call chain invariant (`InvK`: the top
  frame's result meets the demand `Anspruch` of the frames below it) that
  every step keeps (`invK_schritt`, from the one-frame step lemma
  `schrittErhaltK`: stay / pop / push), and the trace-insensitivity of the
  sequential semantics with calls (`rufRumpf_SG`, by depth). Joint witness
  on the bind program (`rufG_adaequat_ruf_umkehr_zeuge`), and the full
  agreement on the former deadlock finding (`wartet_einig_voll`).
  What is NOT proved:

  - The fragment of the converse (`kOk`) excludes loops (`traverse`,
    `retry`, `forever`), `leave`/`next`, the error channel (`retGrund`,
    `let … else`), indirect calls, axioms and the oracle forms (`regLies`,
    `regLiesElse`, `awaits`). The frame semantics `semK` gives the loop
    shims and waiting residues no meaning (`sonst`); following a loop
    would need its residues (`trav`/`wieder`/`ewig` and their `Rest`
    shims) in `semK` with `traverseLauf`/`retryLauf`/`foreverLauf` as their
    meaning, and the error channel a second demand (`grund`) in
    `Anspruch`. The oracle forms stay out for the reason of the G converse:
    the oracle sees the whole world, trace included (the bare lock steps
    that changed the trace are gone since 2026-09-13, but a run from a
    world with a different trace still meets a trace-reading oracle).
  - The run is cut at the FIRST pop of the frame (`RufLaufUeber`): after
    the pop the caller may call `fn` again, and a later `rueck fn …` belongs
    to another frame. `rufLaufG_erster` finds the first pop on any run.
  - The depth `n` is any depth at which the body is covered (`TiefK`); the
    statement is about THAT `n` (a deeper `n` covers the same body and
    gives the same result, by determinism of the witness, not proved in
    general).
  - As in the G converse, `s1` agrees with the sequential world in memory,
    not in trace.
-/

#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_umkehr
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_umkehr_zeuge
#print axioms Gabbro.Grammatik.wartet_einig_voll
#print axioms Gabbro.Grammatik.invK_schritt
#print axioms Gabbro.Grammatik.schrittErhaltK
#print axioms Gabbro.Grammatik.rufRumpf_SG
#print axioms Gabbro.Grammatik.rufLaufG_erster


end Gabbro.Grammatik
