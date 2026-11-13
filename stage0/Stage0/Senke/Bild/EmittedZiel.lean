/-
  File:      stage0/Stage0/Senke/Bild/EmittedZiel.lean
  Subject:   **The image theorem on the emitted image** (T1 instantiated by T2, one thread). For what Stage 0 emits
             from a certifiable unit without roots and without `atomic` globals, under (b) and (c) as `gabbro_ziel`
             states them, every memory-only prefix of the image's run from the loader's first instruction is either
             still in front of the first body boundary of `main` (where machine G is at its start machine, at which
             every leg of `Ziel` holds), or lies inside or behind the decomposed prefix of `main`'s body, where it
             corresponds to a machine G reaches by the steps of `main`'s thread and at which every leg of `Ziel`
             holds. Premise (a′) of `bild_ziel_start` is derived from the compiler's acceptance, (d′) from the user's
             start duty; machine G runs `P` (not `P.mitRuhe`), so every other thread starts an idle function `r` of
             `P` (`startZulaessig_bild`): that idle start is a premise. Calls of admitted callees are decomposed
             steps under the named call obligation `RufOk` for the image's handler (see `Emitted.bild_ziel`).
-/
module
public import Stage0.Senke.Bild.Emitted
@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildLauf Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {src : String} {K : Nat} {options : Profil.Options}

/-- The complete function list of the unit. -/
abbrev Emitted.fsA (output : Emitted src K options) : Aufzaehlung (declOf output.compiled.unit).Fn :=
  ⟨List.finRange output.compiled.unit.fns.length, List.mem_finRange⟩

/-- The complete lock list of the unit. -/
abbrev Emitted.lsA (output : Emitted src K options) : Aufzaehlung (declOf output.compiled.unit).Lock :=
  ⟨List.finRange output.compiled.unit.locks.length, List.mem_finRange⟩

/-- The complete carrier list of the unit. -/
abbrev Emitted.csA (output : Emitted src K options) :
    Aufzaehlung ((declOf output.compiled.unit).Tab ⊕ (declOf output.compiled.unit).Glob) :=
  ⟨(List.finRange output.compiled.unit.tabs.length).map Sum.inl ++
      (List.finRange output.compiled.unit.globs.length).map Sum.inr, fun c => by
    cases c with
    | inl t => exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange t))
    | inr g => exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange g))⟩

/-- **(a′) on the emitted image**: the checker's facts without the rely, for the judged unit of the image. -/
theorem Emitted.akzeptiertSpec (output : Emitted src K options) (Q : AxEns (declOf output.compiled.unit))
    (hZ : OldSource.zertifizierbar output.compiled.unit = true) (hr : output.compiled.unit.roots = [])
    (hg : output.compiled.unit.gestartet = []) (hAt : ∀ g, (declOf output.compiled.unit).atomar g = false)
    (hw : RootNativeFloat.Hardware) :
    AkzeptiertSpec (output.einheit Q).P (output.einheit Q).S output.fsA.1 (output.einheit Q).ws
      (output.einheit Q).akku := by
  have hacc : akzeptiertX_pruefer.akzeptiert (output.einheit Q) output.fsA.1 output.lsA.1 output.csA.1 = true :=
    (output.goal_checker_main Q output.sp0 hZ hr hg).1
  exact akzeptiertSpec_of_X (akzeptiertX_pruefer.korrekt (output.einheit Q) output.fsA output.lsA output.csA
    hw hacc).1 (keinGeteiltV hAt)

/-- **The goal legs on what the emitted image runs through (one thread).** Let the image be what Stage 0 emits from
    a certifiable unit (`zertifizierbar`) without declared and run-time roots and without `atomic` globals; let the
    user's logic (b) hold for its judged unit and the hardware assumptions (c) for the oracle `O`; let every thread
    but `thr` start an idle function `r` of the program with its `requires` true; let the image's gates and
    visibility meet `O` and the payload be loaded; let the callees `Cg` keep the call obligation `RufOk` for the
    handler of the image's frame (`rufAt` at depth `depth - 1`); and let `main`'s body begin with a decomposed
    prefix (`Zerlegung … Cg …`, ending at `ebe`). Then there is a run from the loader's first instruction to the
    first body boundary of `main`, and every memory-only prefix of the image's run from there is
    * in front of that boundary, and the start machine satisfies every leg of `Ziel`; or
    * inside a decomposed step (a statement or a `let` binding), corresponding to a machine `thr` reaches, at
      which every leg of `Ziel` holds; or
    * behind the decomposed prefix, whose end boundary corresponds to such a machine.
    The machine is `RufStartG P sp init` with `sp` the canonical initial memory (the judged unit's `sp0`) and
    `init = bildInit thr main output.args r ρr`.

    **Calls.** A call statement of an admitted callee is ONE decomposed step: its image side is the big-step
    `call_ok` inside `lowS_ok`, its machine side the callee's whole run to its pop (`RufOk`). Image states INSIDE the
    callee therefore correspond (`Korrespondenz`) to the machine at the caller's boundary in front of the call; the
    theorem gives `Ziel` at the caller's boundaries and at those machines, not at boundaries of the callee's body.
    With `Cg := fun _ => False` and `rufOk_leer` this is the call-free statement of before. `RufOk` is proved for
    the BODY-running handler (`rufOk_tief` over `rufRumpf` and `Tief`), not for `rufAt`: `rufAt` reads the places
    of `requires`, `ensures` and the owed invariants into the trace, machine G does not (`befund_vertrag`), so the
    final worlds of the two differ in their traces even when every contract holds. What would discharge `hRuf`:
    (i) `rufAt n g σ ρ = .ok σ' v → ∃ σ'', rufRumpf n g σ ρ = .ok σ'' v ∧ σ''` equal to `σ'` up to read events,
    by induction over the depth with a handler-substitution lemma for `execEnd`; and (ii) a version of `RufOk`
    (and of `Rand`) whose world equality is taken up to read events. Neither exists yet.

    **The idle start (not lifted here).** Machine G runs `P`; every thread but `thr` starts the idle function `r`.
    The lift to `gabbro_ziel`'s machine of `P.mitRuhe` must provide: (1) `Laufzeit (output.einheit Q)
    (speicherR output.sp0) initR` for `initR t = ⟨some main, envR output.args⟩` at `thr` and `⟨none, .nil⟩`
    elsewhere; (2) a simulation of the machines reached from `RufStartG P output.sp0 (bildInit thr main args r ρr)`
    by steps of `thr` by machines reached from `RufStartG P.mitRuhe (speicherR output.sp0) initR` by steps of
    `thr`, thread `thr`'s frames carried by `ruEnd`/`Endblock.umΛ`, every other thread at the idle root's residue;
    (3) the transfer of each leg of `Ziel` (or `ZielX`) from the `P.mitRuhe` machine back to its `P` machine. Then
    `hRuhig`, `hreqr` and `bildInit` leave the premises and (a′), (d′) become (a), (d) of `gabbro_ziel`. -/
theorem Emitted.bild_ziel [Kern] (output : Emitted src K options)
    (hZ : OldSource.zertifizierbar output.compiled.unit = true) (hr : output.compiled.unit.roots = [])
    (hg : output.compiled.unit.gestartet = []) (hAt : ∀ g, (declOf output.compiled.unit).atomar g = false)
    {r : (declOf output.compiled.unit).Fn}
    {ρr : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params r)}
    (hRuhig : Ruhig output.compiled.program output.fsA.1 r)
    (hreqr : ReqAmEintritt output.compiled.program r (output.sp0.welt []) ρr)
    {Q : AxEns (declOf output.compiled.unit)} (hN : NutzerPflichtA (output.einheit Q))
    {O : Orakel (declOf output.compiled.unit)} (hH : HardwareAnnahmen O Q)
    [TorOK output.image.Y O] [SichtOK O] {m : Runner.Mem} (loaded : BytesAt m Runner.Prog.IMG output.bytes)
    {thr : Faden} {Agl : (declOf output.compiled.unit).Lock → Prop}
    {Γe : Ctx} {Λe : List (Res (declOf output.compiled.unit))}
    {ebe : Endblock (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) output.compiled.main)
      false Γe Λe}
    {σe : World (declOf output.compiled.unit)}
    {ρe : Env (declOf output.compiled.unit) Γe}
    {Cg : (declOf output.compiled.unit).Fn → Prop}
    (hRuf : RufOk output.compiled.program O output.image.passes thr Agl
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
        (∃ M', Korrespondenz (output.rahmen O C Lm rp ens) thr [] output.args (output.sp0.welt []) Agl false
            t m' M' ∧
          RufErreichbarG output.compiled.program O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) M' ∧
          Ziel output.compiled.program (output.einheit Q).S O output.image.passes
            (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr)) M') ∨
        (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG (declOf output.compiled.unit)),
          Rand (output.rahmen O C Lm rp ens) thr [] output.args (output.sp0.welt []) Agl ebe pce me Me σe ρe ∧
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
  · rcases bild_ziel_start (fs := output.fsA) (ls := output.lsA) hOk hA0 hL hH hZ'
        hRuf hk' hSt hnach with h1 | h2
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)

end Gabbro.Stage0
