/-
  File:      stage0/Stage0/Senke/Bild/Ruf/EmittedZielL.lean
  Subject:   **The image theorem on the emitted image, with calls** (package P3 of the closed calls of the image
             theorem, part 4: the (ii) of `EmittedZiel`). `Emitted.bild_ziel` (`Bild/EmittedZiel.lean`) admits calls
             only under the call obligation `RufOk` for the image's handler `rufAt`, which holds only for the empty
             callee set: `rufAt` reads the contracts into the trace and machine G does not (`befund_vertrag`).
             `Emitted.bild_ziel_ruf` takes the obligation up to read events (`RufOkGleich`); the named oracle
             property (`LeseblindOK`) comes from the hardware assumptions (`leseblindOK_hardware`); it concludes with
             the correspondence up to read events (`KorrespondenzL`, `RandL`). `Emitted.bild_ziel_tief` discharges the
             obligation: every callee admitted at the image's call depth (`Tief P Agl (depth - 1)`: its body
             is in the call fragment with callees admitted one level down) may be called in the decomposed prefix,
             with no call premise left
             (`rufOk_gleich_tief`). A call is ONE decomposed step: image states inside the callee correspond to the
             machine at the caller's boundary in front of the call (recursion into the callee's boundaries is P4).
             The exact `Emitted.bild_ziel` stays.
-/
module
public import Stage0.Senke.Bild.Ruf.ZielL
public import Stage0.Senke.Bild.EmittedZiel
@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildLauf Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {src : String} {K : Nat} {options : Profil.Options}

/-- **The goal legs on what the emitted image runs through, with calls (one thread).** `Emitted.bild_ziel` with the
    call obligation up to read events (`hRuf : RufOkGleich …` for the image's handler `rufAt (depth - 1)`); the
    named oracle property comes from the hardware assumptions (`leseblindOK_hardware`). Every memory-only prefix of the
    image's run from the loader's first instruction is in front of `main`'s first body boundary (the start machine
    satisfies every leg of `Ziel`), or inside a decomposed step -- a statement, a `let` binding, or a call of an
    admitted callee -- corresponding (machine G up to read events) to a machine `thr` reaches at which every leg of
    `Ziel` holds, or behind the decomposed prefix, whose end boundary corresponds to such a machine. -/
theorem Emitted.bild_ziel_ruf [Kern] (output : Emitted src K options)
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
    {thr : Faden} {Agl : (declOf output.compiled.unit).Lock → Prop}
    {Γe : Ctx} {Λe : List (Res (declOf output.compiled.unit))}
    {ebe : Endblock (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) output.compiled.main)
      false Γe Λe}
    {σe : World (declOf output.compiled.unit)}
    {ρe : Env (declOf output.compiled.unit) Γe}
    {Cg : (declOf output.compiled.unit).Fn → Prop}
    (hRuf : RufOkGleich output.compiled.program O output.image.passes thr Agl
      (rufAt output.compiled.program O output.image.passes (output.image.depth - 1)) Cg)
    (hk : Zerlegung (output.zRahmen O) Agl Cg
      (output.compiled.program.rumpf output.compiled.main) (output.sp0.welt []) output.args ebe σe ρe) :
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
          RandL (output.rahmen O C Lm rp ens) thr [] output.args (output.sp0.welt []) Agl ebe pce me Me σe ρe ∧
          RufErreichbarG output.compiled.program O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) Me ∧
          Ziel output.compiled.program (output.einheit Q).S O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) Me ∧
          ∃ k, StarM k ⟨pce, slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB)⟩ me t m') := by
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
  -- T2: the run to the first body boundary
  obtain ⟨C, Lm, ens, rp, pcB, mB, run0, hOk, hRand⟩ := output.bild_anfang hr hg O loaded hreq
  refine ⟨C, Lm, ens, rp, pcB, mB, run0, ?_⟩
  intro n t m' hrun
  have hSt : StartEntspricht (output.rahmen O C Lm rp ens) output.sp0
      (bildInit thr output.compiled.main output.args r ρr) thr output.args Agl pcB mB (output.sp0.welt []) :=
    ⟨hRand, randG_start output.compiled.program output.sp0 Agl (bildInit_gleich rfl) hhaelt
      (bildInit_frei hRuhig.1)⟩
  have hk' : Zerlegung (output.rahmen O C Lm rp ens) Agl Cg
      (output.compiled.program.rumpf output.compiled.main) (output.sp0.welt []) output.args ebe σe ρe :=
    zerlegung_rahmen hk
  rcases hrun.weiche run0 with hvor | ⟨k, hnach⟩
  · exact Or.inl ⟨hvor, ziel_aus output.compiled.program (output.einheit Q).S Q output.fsA output.lsA
      (output.einheit Q).ws hA0 hL O hH output.image.passes output.sp0 _ hZ' _ RufErreichbarG.start⟩
  · rcases bild_ziel_startL (fs := output.fsA) (ls := output.lsA) hOk hA0 hL hH hZ'
        hRuf hk' hSt hnach with h1 | h2
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)

/-- **THE IMAGE THEOREM WITH CALLS, NO CALL PREMISE.** `Emitted.bild_ziel_ruf` for the callees admitted at the
    image's call depth (`Tief P Agl (depth - 1)`), whose call obligation up to read events is proved
    (`rufOk_gleich_tief`): the decomposed prefix of `main`'s body may call every such callee. The handler relation
    for ALL callees needs read-blindness of the oracle, which every oracle has (`leseblindP_alle`): the theorem
    covers programs WITH foreign calls (raw syscalls), with no premise on the oracle beyond (c). -/
theorem Emitted.bild_ziel_tief [Kern] (output : Emitted src K options)
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
    {thr : Faden} {Agl : (declOf output.compiled.unit).Lock → Prop}
    {Γe : Ctx} {Λe : List (Res (declOf output.compiled.unit))}
    {ebe : Endblock (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) output.compiled.main)
      false Γe Λe}
    {σe : World (declOf output.compiled.unit)}
    {ρe : Env (declOf output.compiled.unit) Γe}
    (hk : Zerlegung (output.zRahmen O) Agl (Tief output.compiled.program Agl (output.image.depth - 1))
      (output.compiled.program.rumpf output.compiled.main) (output.sp0.welt []) output.args ebe σe ρe) :
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
          RandL (output.rahmen O C Lm rp ens) thr [] output.args (output.sp0.welt []) Agl ebe pce me Me σe ρe ∧
          RufErreichbarG output.compiled.program O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) Me ∧
          Ziel output.compiled.program (output.einheit Q).S O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) Me ∧
          ∃ k, StarM k ⟨pce, slot (BitVec.ofNat 64 output.image.fp0) (BitVec.ofNat 64 FB)⟩ me t m') :=
  output.bild_ziel_ruf hZ hr hg hAt hRuhig hreqr hN hH loaded
    (rufOk_gleich_tief (P := output.compiled.program) (leseblindP_alle _ O) thr Agl
      (output.image.depth - 1)) hk

#print axioms Emitted.bild_ziel_ruf
#print axioms Emitted.bild_ziel_tief

end Gabbro.Stage0
