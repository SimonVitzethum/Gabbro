/-
  File:      stage0/Stage0/Senke/Bild/Rek/EmittedRueck.lean
  Subject:   **The image theorem along a whole call, recursion included** (package P5 of the closed calls of the image
             theorem, part 4). `Emitted.bild_ziel_aufruf` is `Emitted.bild_ziel_rek` (P4) with
             * the call taken IN AND OUT: `main`'s decomposed prefix runs to the boundary in front of a plain call
               `g(xs); rest` and CONTINUES behind it (`hkR`, a decomposed prefix of `rest` from the world behind the
               call), and the call's window is refined completely (`bild_ziel_fenster`): in front of the callee's
               first body boundary, inside the callee's decomposed steps, and in the return window from the callee's
               last boundary to `main`'s boundary behind the call;
             * recursion admitted: callees are admitted by `TiefAlle` (`Rek/Alle.lean`) at the image's handler depth
               `depth - 1 = j + 1`, which every program whose bodies are in the call fragment satisfies
               (`tiefAlle_frag`) -- self- and mutually recursive bodies included; the depth bound is the image's own
               (`depth < 2 ^ 64`, `Emitted.bild_anfang_codes`).
             Every memory-only prefix of the image's run from the loader's first instruction is classified, and every
             machine named is reachable with every leg of `Ziel`.
-/
module
public import Stage0.Senke.Bild.Rek.Fenster
public import Stage0.Senke.Bild.Rek.Emitted
@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildLauf Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {src : String} {K : Nat} {options : Profil.Options}

/-- **THE IMAGE THEOREM ALONG A WHOLE CALL, RECURSION INCLUDED (one thread).** For a decomposed prefix of `main`'s
    body to the boundary in front of a plain call `g(xs); rest` that ends normally under the image's handler, the callee
    admitted at the handler depth (`TiefAlle`, recursion included), the callee's own decomposed prefix (callees one level
    down), and a decomposed prefix of `rest` from the world behind the call, every memory-only prefix of the image's
    run from the loader's first instruction is
    (i) in front of `main`'s first body boundary (the start machine satisfies `Ziel`), or
    (ii) inside a decomposed step of `main`'s prefix in front of the call, or
    (iii) behind it and in front of the callee's first body boundary (the boundary in front of the call corresponds), or
    (iv) inside a decomposed step of the callee's body (callee frame at depth `j`, `main`'s frame waiting below), or
    (v) in the call's return window (`ImRueck`): between the callee's boundary behind its prefix and `main`'s boundary
        behind the call, both corresponding, the second reached from the first, or
    (vi) behind the call: inside a decomposed step of `rest`'s prefix, or behind it (`ImRumpf` of `main`'s frame);
    every machine named is reachable and satisfies every leg of `Ziel`. -/
theorem Emitted.bild_ziel_aufruf [Kern] (output : Emitted src K options)
    (hZ : OldSource.zertifizierbar output.compiled.unit = true) (hr : output.compiled.unit.roots = [])
    (hg : output.compiled.unit.gestartet = []) (hAt : ∀ g, (declOf output.compiled.unit).atomar g = false)
    {r : (declOf output.compiled.unit).Fn}
    {ρr : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params r)}
    (hRuhig : Ruhig output.compiled.program output.fsA.1 r)
    (hreqr : ReqAmEintritt output.compiled.program r (output.sp0.welt []) ρr)
    {Q : AxEns (declOf output.compiled.unit)} (hN : NutzerPflichtA (output.einheit Q))
    {O : Orakel (declOf output.compiled.unit)} (hH : HardwareAnnahmen O Q)
    [TorOK output.image.Y O] [SichtOK O] [LeseblindOK O] {m : Runner.Mem}
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
    (hk : Zerlegung (output.zRahmen O) Agl (TiefAlle output.compiled.program Agl (output.image.depth - 1))
      (output.compiled.program.rumpf output.compiled.main) (output.sp0.welt []) output.args
      (.cons (.call g xs hp hrg) rest) σe ρe)
    (hex : execStmt O output.image.passes (rufAt output.compiled.program O output.image.passes
      (output.image.depth - 1))
      (.call g xs hp hrg : Stmt (declOf output.compiled.unit)
        (vertragVon (declOf output.compiled.unit) output.compiled.main) false Γe Λe
        (nach (declOf output.compiled.unit) g Λe)) σe ρe = .ok σ1 ρ1)
    (hgT : TiefAlle output.compiled.program Agl (output.image.depth - 1) g)
    {ΓeC : Ctx} {ΛeC : List (Res (declOf output.compiled.unit))}
    {ebeC : Endblock (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) g) false ΓeC ΛeC}
    {σeC : World (declOf output.compiled.unit)} {ρeC : Env (declOf output.compiled.unit) ΓeC}
    (hkC : Zerlegung (rufZRahmen output.image.Y O output.image.passes output.compiled.program output.image.A j g
        (rufWelt output.compiled.program g σe Λe xs) (rufEnv g σe Λe xs ρe)) Agl
      (TiefAlle output.compiled.program Agl j) (output.compiled.program.rumpf g)
      (rufWelt output.compiled.program g σe Λe xs) (rufEnv g σe Λe xs ρe) ebeC σeC ρeC)
    {ΓeR : Ctx} {ΛeR : List (Res (declOf output.compiled.unit))}
    {ebeR : Endblock (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) output.compiled.main)
      false ΓeR ΛeR}
    {σeR : World (declOf output.compiled.unit)} {ρeR : Env (declOf output.compiled.unit) ΓeR}
    (hkR : Zerlegung (output.zRahmen O) Agl (TiefAlle output.compiled.program Agl (output.image.depth - 1))
      rest σ1 ρ1 ebeR σeR ρeR) :
    ∃ (C : (declOf output.compiled.unit).Fn → List II) (Lm : Nat) (ens : List II × Nat) (rp pcB : Runner.W)
      (mB : Runner.Mem),
      Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ m
        ⟨pcB, slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB)⟩ mB ∧
      ∀ {n : Nat} {t : Runner.IR.T} {m' : Runner.Mem},
        StarM n ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ m t m' →
        -- (i)
        (Star t m' ⟨pcB, slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB)⟩ mB ∧
          Ziel output.compiled.program (output.einheit Q).S O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))) ∨
        -- (ii)
        (∃ M', KorrespondenzL (output.rahmen O C Lm rp ens) thr [] output.args (output.sp0.welt []) Agl false
            t m' M' ∧
          RufErreichbarG output.compiled.program O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) M' ∧
          Ziel output.compiled.program (output.einheit Q).S O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) M') ∨
        -- (iii)
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
        -- (iv)
        (∃ (fpc rpc : Runner.W) (Kc Ksc : Nat) (ensc : List II × Nat) (σm : World (declOf output.compiled.unit))
            (M' : RufMaschineG (declOf output.compiled.unit)),
          KorrespondenzL (rumpfRahmen output.image.Y O output.image.passes output.compiled.program output.image.A C Lm
              j g fpc Kc Ksc rpc (slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB))
              (rufWelt output.compiled.program g σe Λe xs) (rufEnv g σe Λe xs ρe) [] ensc)
            thr [rufRahmenNach output.args (output.sp0.welt []) ρe rest] (rufEnv g σe Λe xs ρe) σm Agl false t m'
            M' ∧
          RufErreichbarG output.compiled.program O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) M' ∧
          Ziel output.compiled.program (output.einheit Q).S O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) M') ∨
        -- (v)
        (∃ (fpc rpc : Runner.W) (Kc Ksc : Nat) (ensc : List II × Nat) (σm : World (declOf output.compiled.unit))
            (pcN : Runner.W) (mN : Runner.Mem),
          ImRueck (output.rahmen O C Lm rp ens)
            (rumpfRahmen output.image.Y O output.image.passes output.compiled.program output.image.A C Lm
              j g fpc Kc Ksc rpc (slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB))
              (rufWelt output.compiled.program g σe Λe xs) (rufEnv g σe Λe xs ρe) [] ensc)
            thr [] output.args (output.sp0.welt []) Agl rest pcN mN σ1 ρ1
            [rufRahmenNach output.args (output.sp0.welt []) ρe rest] (rufEnv g σe Λe xs ρe) σm ebeC σeC ρeC
            (fun M' => RufErreichbarG output.compiled.program O output.image.passes
                (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))
                M' ∧
              Ziel output.compiled.program (output.einheit Q).S O output.image.passes
                (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))
                M')
            t m') ∨
        -- (vi)
        ImRumpf (output.rahmen O C Lm rp ens) thr [] output.args (output.sp0.welt []) Agl ebeR σeR ρeR
          (fun M' => RufErreichbarG output.compiled.program O output.image.passes
              (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))
              M' ∧
            Ziel output.compiled.program (output.einheit Q).S O output.image.passes
              (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))
              M')
          t m' := by
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
      (TiefAlle output.compiled.program Agl (output.image.depth - 1))
      (output.compiled.program.rumpf output.compiled.main) (output.sp0.welt []) output.args
      (.cons (.call g xs hp hrg) rest) σe ρe :=
    zerlegung_rahmen hk
  have hkR' : Zerlegung (output.rahmen O C Lm rp ens) Agl
      (TiefAlle output.compiled.program Agl (output.image.depth - 1)) rest σ1 ρ1 ebeR σeR ρeR :=
    zerlegung_rahmen hkR
  have hRuf := rufOk_gleich_tiefAlle (P := output.compiled.program) (passes := output.image.passes)
    (leseblind_von O) thr Agl (output.image.depth - 1)
  rcases hrun.weiche run0 with hvor | ⟨k, hnach⟩
  · exact Or.inl ⟨hvor, ziel_aus output.compiled.program (output.einheit Q).S Q output.fsA output.lsA
      (output.einheit Q).ws hA0 hL O hH output.image.passes output.sp0 _ hZ' _ RufErreichbarG.start⟩
  · rcases bild_ziel_startL (fs := output.fsA) (ls := output.lsA) hOk hA0 hL hH hZ'
        hRuf hk' hSt hnach with h1 | ⟨pce, me, Me, hRe, hre, hze, k2, hk2⟩
    · exact Or.inr (Or.inl h1)
    · -- the call's window, in and out
      obtain ⟨n1, m1, M2, fpc, rpc, Kc, Ksc, ensc, pcI, mI, σm, sB, hRB, hr2, _, sI, hwin⟩ :=
        bild_ziel_fenster (fs := output.fsA) hcodes output.lsA hA0 hL hH hZ' hj
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hdep) hOk hre hRe hex
          hgT hkC
      rcases hk2.weiche sB with hvorB | ⟨k3, hnachB⟩
      · -- inside the call
        rcases hwin hk2 hvorB with hvorI | ⟨M', hK, hr', hz'⟩ | hrue
        · exact Or.inr (Or.inr (Or.inl ⟨pce, me, Me, hRe, hre, hze, ⟨k2, hk2⟩, pcI, fpc, mI, sI, hvorI⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨fpc, rpc, Kc, Ksc, ensc, σm, M', hK, hr', hz'⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨fpc, rpc, Kc, Ksc, ensc, σm, _, _, hrue⟩))))
      · -- behind the call: `rest`'s decomposed prefix from the boundary behind the call
        rcases bild_ziel_seqL (ls := output.lsA) hOk hA0 hL hH hZ' hRuf hkR' hr2 hRB hnachB with
          ⟨M', hK, hr', hz'⟩ | ⟨pce', me', Me', hRe', hre', hze', k', hk'⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨M', hK, hr', hz'⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨pce', me', Me', hRe', ⟨hre', hze'⟩, k', hk'⟩)))))

#print axioms Emitted.bild_ziel_aufruf

end Gabbro.Stage0
