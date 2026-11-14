/-
  File:      stage0/Stage0/Senke/Bild/Rek/Emitted.lean
  Subject:   **The image theorem with boundaries inside a callee** (package P4 of the closed calls of the image
             theorem, part 5).
             * `Emitted.bild_anfang_codes`: `Emitted.bild_anfang` that also names the image facts every prologue
               needs (`BildCodes` of the frame's codes `C` and call capacity `Lm`) and bounds the image's call depth
               (`depth < 2 ^ 64`, from the stack band); the proof is that of `Emitted.bild_anfang` with the code facts
               of `BildLage.code` kept.
             * `Emitted.bild_ziel_rek`: `Emitted.bild_ziel_tief` for a decomposed prefix of `main`'s body that ends in
               front of a plain call `g(xs); rest`, which ends normally, with the callee's own decomposed prefix
               (callees admitted one level down, `Tief P Agl j`, no call premise). Every memory-only prefix of the
               image run from the loader's first instruction is in front of `main`'s first boundary, inside a
               decomposed step of `main`'s prefix, between the boundary in front of the call and the callee's first
               body boundary (corresponding to the caller's machine there), or INSIDE THE CALLEE: inside a
               decomposed step of the callee's body or behind its prefix, corresponding to a machine `thr` reaches,
               with every leg of `Ziel` (`ImRumpf`). The callee's boundaries are boundaries of the callee's frame at
               depth `j` (`depth - 1 = j + 1`), with `main`'s frame waiting on the thread's stack.
             At a boundary of the callee in front of a further call, `bild_ziel_rek` (`Rek/Lauf.lean`) applies again
             with the callee's frame as the caller's: the descent iterates to every depth the image has.
-/
module
public import Stage0.Senke.Bild.Rek.Lauf
public import Stage0.Senke.Bild.Ruf.EmittedZielL
@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildLauf Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {src : String} {K : Nat} {options : Profil.Options}

/-- **T2 with the image's codes**: `Emitted.bild_anfang`, and the codes `C` and call capacity `Lm` of the frame are
    those of the laid-out image (`BildCodes`), whose call depth is below `2 ^ 64`. -/
theorem Emitted.bild_anfang_codes [Kern] (output : Emitted src K options) (hr : output.compiled.unit.roots = [])
    (hg : output.compiled.unit.gestartet = []) (O : Orakel (declOf output.compiled.unit))
    [TorOK output.image.Y O] [SichtOK O] {m : Runner.Mem}
    (loaded : BytesAt m Runner.Prog.IMG output.bytes)
    (hreq : ReqAmEintritt output.compiled.program output.compiled.main
      (Senke.initialWorld output.compiled.unit output.initialValid) output.args) :
    ∃ (C : (declOf output.compiled.unit).Fn → List II) (Lm : Nat) (ens : List II × Nat) (rp pc : Runner.W)
      (mR : Runner.Mem),
      Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ m
        ⟨pc, slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB)⟩ mR ∧
      (output.rahmen O C Lm rp ens).Ok ∧
      (output.rahmen O C Lm rp ens).RandIR (output.compiled.program.rumpf output.compiled.main) pc mR
        (Senke.initialWorld output.compiled.unit output.initialValid) output.args ∧
      BildCodes output.image.Y output.compiled.program output.image.passes output.image.A C Lm ∧
      output.image.depth < 2 ^ 64 := by
  have hst : output.starts = [] := output.starts_leer hr hg
  have hb := output.emission
  rw [show output.startPlan.starts (Senke.initialWorld output.compiled.unit output.initialValid) = [] from hst]
    at hb
  obtain ⟨world, _, sync, _, made, _, _, startup, _⟩ :=
    bild_initialized_loaded_u output.initialValid hb output.funktionen_voll loaded
  obtain ⟨cs, body, sp, h, code, _, args, rootArgs⟩ := bild_lage hb output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync output.compiled.unit output.tor base)
  have startup' : BytesAt m codeBase (output.image.code.flatMap encII ++
      ((startStackBytes output.image.Ks (FB + FB) (output.image.args :: output.image.rootArgs)).getD [] ++ [])) := by
    simpa only [made, Option.getD_some, List.append_nil] using startup
  rw [code, args, rootArgs] at startup'
  obtain ⟨c1, c2, _, _, _⟩ := h.code startup'
  have hfit := h.hfit
  have hdep : output.image.depth < 2 ^ 64 := by
    have hylo := h.hylo
    have hyhi := h.hyhi
    have hyord := h.hyord
    have hd := h.hdepth
    have hdiv := Nat.div_le_self (output.image.Ks - FB) (maxTop cs)
    simp only [List.map_nil, List.length_nil, Nat.zero_add, Nat.mul_one] at hylo
    simp only [depthOf] at hd
    omega
  obtain ⟨ens, rp, pc, mR, run, ok, rand⟩ := BildLauf.bild_anfang (O := O) h startup'
    (fun τ x => Senke.mainEnv_valid output.image.Y _ output.args output.pointers τ x) world
    (by simpa only [Nat.mul_zero, Nat.add_zero] using sync 0 (Nat.zero_le _)) hreq
  exact ⟨_, _, ens, rp, pc, mR, run, ok, rand,
    ⟨h.hfa, c1, fun g => by have := (c2 g).2; dsimp only at this ⊢; omega,
      fun g => by have := (c2 g).2; dsimp only at this ⊢; omega⟩, hdep⟩

/-- **THE IMAGE THEOREM WITH BOUNDARIES INSIDE A CALLEE (one thread).** `Emitted.bild_ziel_tief` for a decomposed
    prefix of `main`'s body that ends in front of a plain call `g(xs); rest` which ends normally under the image's
    handler, and the callee's own decomposed prefix (callees admitted at depth `j`, `depth - 1 = j + 1`). Every
    memory-only prefix of the image's run from the loader's first instruction is
    (i) in front of `main`'s first body boundary (the start machine satisfies `Ziel`), or
    (ii) inside a decomposed step of `main`'s prefix, corresponding to a reachable machine with `Ziel`, or
    (iii) behind `main`'s prefix and in front of the callee's first body boundary, the boundary in front of the call
         corresponding to a reachable machine with `Ziel`, or
    (iv) inside the callee: inside a decomposed step of its body, or behind its prefix, corresponding (in the callee's
         frame at depth `j`, `main`'s frame waiting below) to a reachable machine at which every leg of `Ziel`
         holds. -/
theorem Emitted.bild_ziel_rek [Kern] (output : Emitted src K options)
    (hZ : OldSource.zertifizierbar output.compiled.unit = true) (hr : output.compiled.unit.roots = [])
    (hg : output.compiled.unit.gestartet = []) (hAt : ∀ g, (declOf output.compiled.unit).atomar g = false)
    {r : (declOf output.compiled.unit).Fn}
    {ρr : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params r)}
    (hRuhig : Ruhig output.compiled.program output.fsA.1 r)
    (hreqr : ReqAmEintritt output.compiled.program r (output.sp0.welt []) ρr)
    {Q : AxEns (declOf output.compiled.unit)} (hN : NutzerPflichtA (output.einheit Q))
    {O : Orakel (declOf output.compiled.unit)} (hH : HardwareAnnahmen O Q)
    [TorOK output.image.Y O] [SichtOK O] {m : Runner.Mem}
    (loaded : BytesAt m Runner.Prog.IMG output.bytes)
    {thr : Faden} {Agl : (declOf output.compiled.unit).Lock → Prop} {j : Nat}
    (hj : output.image.depth - 1 = j + 1)
    {Γe : Ctx} {Λe : List (Res (declOf output.compiled.unit))} {g : (declOf output.compiled.unit).Fn}
    {xs : Args (declOf output.compiled.unit) Γe Λe ((declOf output.compiled.unit).params g)}
    {hp : RufPasst (declOf output.compiled.unit)
      (vertragVon (declOf output.compiled.unit) output.compiled.main)
      ((declOf output.compiled.unit).signatur g) Λe}
    {hrg : (declOf output.compiled.unit).gruende g = 0}
    {rest : Endblock (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) output.compiled.main)
      false Γe (nach (declOf output.compiled.unit) g Λe)}
    {σe σ1 : World (declOf output.compiled.unit)} {ρe ρ1 : Env (declOf output.compiled.unit) Γe}
    (hk : Zerlegung (output.zRahmen O) Agl (Tief output.compiled.program Agl (output.image.depth - 1))
      (output.compiled.program.rumpf output.compiled.main) (output.sp0.welt []) output.args
      (.cons (.call g xs hp hrg) rest) σe ρe)
    (hex : execStmt O output.image.passes (rufAt output.compiled.program O output.image.passes
      (output.image.depth - 1))
      (.call g xs hp hrg : Stmt (declOf output.compiled.unit)
        (vertragVon (declOf output.compiled.unit) output.compiled.main) false Γe Λe
        (nach (declOf output.compiled.unit) g Λe)) σe ρe = .ok σ1 ρ1)
    {ΓeC : Ctx} {ΛeC : List (Res (declOf output.compiled.unit))}
    {ebeC : Endblock (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) g) false ΓeC ΛeC}
    {σeC : World (declOf output.compiled.unit)} {ρeC : Env (declOf output.compiled.unit) ΓeC}
    (hkC : Zerlegung (rufZRahmen output.image.Y O output.image.passes output.compiled.program output.image.A j g
        (rufWelt output.compiled.program g σe Λe xs) (rufEnv g σe Λe xs ρe)) Agl
      (Tief output.compiled.program Agl j) (output.compiled.program.rumpf g)
      (rufWelt output.compiled.program g σe Λe xs) (rufEnv g σe Λe xs ρe) ebeC σeC ρeC) :
    ∃ (C : (declOf output.compiled.unit).Fn → List II) (Lm : Nat) (ens : List II × Nat) (rp pcB : Runner.W)
      (mB : Runner.Mem),
      Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ m
        ⟨pcB, slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB)⟩ mB ∧
      ∀ {n : Nat} {t : Runner.IR.T} {m' : Runner.Mem},
        StarM n ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ m t m' →
        (Star t m' ⟨pcB, slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB)⟩ mB ∧
          Ziel output.compiled.program (output.einheit Q).S O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))) ∨
        (∃ M', KorrespondenzL (output.rahmen O C Lm rp ens) thr [] output.args (output.sp0.welt []) Agl false
            t m' M' ∧
          RufErreichbarG output.compiled.program O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) M' ∧
          Ziel output.compiled.program (output.einheit Q).S O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) M') ∨
        (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG (declOf output.compiled.unit)),
          RandL (output.rahmen O C Lm rp ens) thr [] output.args (output.sp0.welt []) Agl
            (.cons (.call g xs hp hrg) rest) pce me Me σe ρe ∧
          RufErreichbarG output.compiled.program O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) Me ∧
          Ziel output.compiled.program (output.einheit Q).S O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) Me ∧
          (∃ k, StarM k ⟨pce, slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB)⟩ me t m') ∧
          ∃ (pcI fpc : Runner.W) (mI : Runner.Mem),
            Star ⟨pce, slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB)⟩ me ⟨pcI, fpc⟩ mI ∧
            Star t m' ⟨pcI, fpc⟩ mI) ∨
        (∃ (fpc rpc : Runner.W) (Kc Ksc : Nat) (ensc : List II × Nat) (σm : World (declOf output.compiled.unit)),
          ImRumpf (rumpfRahmen output.image.Y O output.image.passes output.compiled.program output.image.A C Lm j g
              fpc Kc Ksc rpc (slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB))
              (rufWelt output.compiled.program g σe Λe xs) (rufEnv g σe Λe xs ρe) [] ensc)
            thr [rufRahmenNach output.args (output.sp0.welt []) ρe rest] (rufEnv g σe Λe xs ρe) σm Agl
            ebeC σeC ρeC
            (fun M' => RufErreichbarG output.compiled.program O output.image.passes
                (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))
                M' ∧
              Ziel output.compiled.program (output.einheit Q).S O output.image.passes
                (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))
                M')
            t m') := by
  -- (a′): the compiler's acceptance, the checker's soundness, no shared atomic
  have hA0 := output.akzeptiertSpec Q hZ hr hg hAt hH.2.2.2
  -- (b): the logic without the rely, and the start duty of `main`
  have hL : LogikPflicht output.compiled.program (output.einheit Q).S Q := logikPflicht_of_A hN.logik
  have hmain : output.compiled.main ∈ (output.einheit Q).ws := by
    show output.compiled.main ∈ [output.compiled.main]
    exact List.mem_cons_self
  have hreq : ReqAmEintritt output.compiled.program output.compiled.main (output.sp0.welt []) output.args :=
    hN.start.req ⟨output.compiled.main, output.args⟩ (List.mem_append_left _ List.mem_cons_self)
  have hhaelt : (declOf output.compiled.unit).haelt output.compiled.main = [] := (hA0.wurzeln _ hmain).1
  -- (d′): the start the image realises
  have hZ' : StartZulaessig output.compiled.program (output.einheit Q).S output.fsA.1 (output.einheit Q).ws
      output.sp0 (bildInit thr output.compiled.main output.args r ρr) :=
    startZulaessig_bild hmain hRuhig hreq hreqr hN.start.sperren
  -- T2 with the image's codes: the run to the first body boundary
  obtain ⟨C, Lm, ens, rp, pcB, mB, run0, hOk, hRand, hcodes, hdep⟩ := output.bild_anfang_codes hr hg O loaded hreq
  refine ⟨C, Lm, ens, rp, pcB, mB, run0, ?_⟩
  intro n t m' hrun
  have hSt : StartEntspricht (output.rahmen O C Lm rp ens) output.sp0
      (bildInit thr output.compiled.main output.args r ρr) thr output.args Agl pcB mB (output.sp0.welt []) :=
    ⟨hRand, randG_start output.compiled.program output.sp0 Agl (bildInit_gleich rfl) hhaelt
      (bildInit_frei hRuhig.1)⟩
  have hk' : Zerlegung (output.rahmen O C Lm rp ens) Agl
      (Tief output.compiled.program Agl (output.image.depth - 1))
      (output.compiled.program.rumpf output.compiled.main) (output.sp0.welt []) output.args
      (.cons (.call g xs hp hrg) rest) σe ρe :=
    zerlegung_rahmen hk
  have hRuf := rufOk_gleich_tief (P := output.compiled.program) (passes := output.image.passes)
    (leseblindP_alle _ O) thr Agl (output.image.depth - 1)
  rcases hrun.weiche run0 with hvor | ⟨k, hnach⟩
  · exact Or.inl ⟨hvor, ziel_aus output.compiled.program (output.einheit Q).S Q output.fsA output.lsA
      (output.einheit Q).ws hA0 hL O hH output.image.passes output.sp0 _ hZ' _ RufErreichbarG.start⟩
  · rcases bild_ziel_startL (fs := output.fsA) (ls := output.lsA) hOk hA0 hL hH hZ'
        hRuf hk' hSt hnach with h1 | ⟨pce, me, Me, hRe, hre, hze, k2, hk2⟩
    · exact Or.inr (Or.inl h1)
    · obtain ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, M1, σm, sI, _, _, _, hinner⟩ :=
        BildLauf.bild_ziel_rek (fs := output.fsA) hcodes output.lsA hA0 hL hH hZ' hj
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hdep) hOk hre hRe hex
          (rufOk_gleich_tief (P := output.compiled.program) (passes := output.image.passes)
            (leseblindP_alle _ O) thr Agl j) hkC
      rcases hk2.weiche sI with hvor2 | ⟨k3, hnach2⟩
      · exact Or.inr (Or.inr (Or.inl ⟨pce, me, Me, hRe, hre, hze, ⟨k2, hk2⟩, pcI, fpc, mI, sI, hvor2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨fpc, rpc, Kc, Ksc, ensc, σm, hinner hnach2⟩))

#print axioms Emitted.bild_anfang_codes
#print axioms Emitted.bild_ziel_rek

end Gabbro.Stage0
