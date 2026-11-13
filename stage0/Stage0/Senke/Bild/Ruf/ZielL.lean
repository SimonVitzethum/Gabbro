/-
  File:      stage0/Stage0/Senke/Bild/Ruf/ZielL.lean
  Subject:   **The goal legs at the machines G the image corresponds to, with calls** (package P3 of the closed calls
             of the image theorem, part 3). `bild_ziel_seqL`/`bild_ziel_startL` are `bild_ziel_seq`/`bild_ziel_start`
             (`Bild/Ziel.lean`) with the call obligation up to read events (`RufOkGleich`), the named oracle property
             `LeseblindOK`, and the correspondence with machine G up to read events (`KorrespondenzL`, `RandL`).
             `Ziel` is unchanged: it is a statement about the machines G reached by steps of the image's thread, not
             about any world, so the read events `rufAt` adds to the sequential world never reach it. The exact forms
             stay in `Bild/Ziel.lean`.
-/
module
public import Stage0.Senke.Bild.Ruf.KorrespondenzL
public import Stage0.Senke.Bild.Ziel
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

variable [Kern]

/-- **`Ziel` at the machines G the sequential image corresponds to, with calls (T1)**: `bild_ziel_seq` with the call
    obligation up to read events (`hRuf : RufOkGleich …`) and machine G up to read events. Under the checker's facts
    (a′), the user's logic (b), the named hardware assumptions (c), an admissible start (d′) and a read-blind oracle,
    from a body boundary that corresponds to a reachable machine `M`, in front of a decomposed prefix whose calls go
    to the admitted callees `Cg`, every prefix of `n` memory-only image steps corresponds (inside a decomposed step,
    or at the boundary behind the prefix) to a reachable machine at which every leg of `Ziel` holds. -/
theorem bild_ziel_seqL [DecidableEq D.Fn] {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] [LeseblindOK B.O]
    (hB : B.Ok) {S : SperrInv D} {Q : AxEns D} {fs : Aufzaehlung D.Fn} (ls : Aufzaehlung D.Lock) {ws : List D.Fn}
    {Acc : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpec B.P S fs.1 ws Acc) (hN : LogikPflicht B.P S Q) (hH : HardwareAnnahmen B.O Q)
    {sp : Speicher D} {init : Faden → Σ g : D.Fn, Env D (D.params g)} (hZ : StartZulaessig B.P S fs.1 ws sp init)
    {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {thr : Faden} {stapel : List (RufRahmenG D)}
    {rho : Env D (D.params B.f)} {s0 : World D} (hRuf : RufOkGleich B.P B.O B.passes thr Agl B.R Cg)
    {l : Bool} {Γ Γe : Ctx} {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe}
    (hk : Zerlegung B Agl Cg eb σ ρ ebe σe ρe) {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D}
    (hM : RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) M)
    (hR : RandL B thr stapel rho s0 Agl eb pc m M σ ρ) {n : Nat} {t : T} {m' : Runner.Mem}
    (hrun : StarM n ⟨pc, B.fp⟩ m t m') :
    (∃ M', KorrespondenzL B thr stapel rho s0 Agl l t m' M' ∧
        RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) M' ∧
        Ziel B.P S B.O B.passes (RufStartG B.P sp init) M') ∨
    (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG D),
        RandL B thr stapel rho s0 Agl ebe pce me Me σe ρe ∧
        RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) Me ∧
        Ziel B.P S B.O B.passes (RufStartG B.P sp init) Me ∧ ∃ k, StarM k ⟨pce, B.fp⟩ me t m') := by
  rcases korrespondenzL_lauf hB hRuf hk hR hrun with ⟨M', hl, hK⟩ | ⟨pce, me, Me, hRe, hl, k, hk'⟩
  · have hr := rufErreichbar_lauf hl hM
    exact Or.inl ⟨M', hK, hr, ziel_aus B.P S Q fs ls ws hA hN B.O hH B.passes sp init hZ M' hr⟩
  · have hr := rufErreichbar_lauf hl hM
    exact Or.inr ⟨pce, me, Me, hRe, hr, ziel_aus B.P S Q fs ls ws hA hN B.O hH B.passes sp init hZ Me hr, k, hk'⟩

/-- **T1 from the image's first body boundary, with calls**: `bild_ziel_seqL` from the start machine, under the
    exact start premise `StartEntspricht` (at the start both sides hold the same world). -/
theorem bild_ziel_startL [DecidableEq D.Fn] {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] [LeseblindOK B.O]
    (hB : B.Ok) {S : SperrInv D} {Q : AxEns D} {fs : Aufzaehlung D.Fn} (ls : Aufzaehlung D.Lock) {ws : List D.Fn}
    {Acc : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpec B.P S fs.1 ws Acc) (hN : LogikPflicht B.P S Q) (hH : HardwareAnnahmen B.O Q)
    {sp : Speicher D} {init : Faden → Σ g : D.Fn, Env D (D.params g)} (hZ : StartZulaessig B.P S fs.1 ws sp init)
    {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {thr : Faden} {rho : Env D (D.params B.f)}
    (hRuf : RufOkGleich B.P B.O B.passes thr Agl B.R Cg) {Γe : Ctx} {Λe : List (Res D)}
    {ebe : Endblock D (vertragVon D B.f) false Γe Λe} {σ σe : World D} {ρe : Env D Γe}
    (hk : Zerlegung B Agl Cg (B.P.rumpf B.f) σ rho ebe σe ρe) {pc : Runner.W} {m : Runner.Mem}
    (hSt : StartEntspricht B sp init thr rho Agl pc m σ) {n : Nat} {t : T} {m' : Runner.Mem}
    (hrun : StarM n ⟨pc, B.fp⟩ m t m') :
    (∃ M', KorrespondenzL B thr [] rho (sp.welt []) Agl false t m' M' ∧
        RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) M' ∧
        Ziel B.P S B.O B.passes (RufStartG B.P sp init) M') ∨
    (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG D),
        RandL B thr [] rho (sp.welt []) Agl ebe pce me Me σe ρe ∧
        RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) Me ∧
        Ziel B.P S B.O B.passes (RufStartG B.P sp init) Me ∧ ∃ k, StarM k ⟨pce, B.fp⟩ me t m') :=
  bild_ziel_seqL (ls := ls) hB hA hN hH hZ hRuf hk RufErreichbarG.start (randL_von hSt) hrun

#print axioms bild_ziel_startL

end Gabbro.Stage0.Senke.BildLauf
