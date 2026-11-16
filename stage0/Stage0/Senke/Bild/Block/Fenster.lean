/- Goal preservation inside a block call, through its return to either channel. -/
module
public import Stage0.Senke.Bild.Block.LaufElse
public import Stage0.Senke.Bild.Rek.Fenster
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- The return part of a block-call window. Both endpoints correspond to reachable
    machines satisfying `Z`; the image is still before its fixed caller endpoint. -/
def ImBlockRueck (B Bc : BodyFrame D) (thr : Faden) (caller : RufRahmenG D)
    (stapel : List (RufRahmenG D)) (ρc : Env D (D.params Bc.f)) (σm : World D)
    (Agl : D.Lock → Prop) {Γe : Ctx} {Λe : List (Res D)}
    (ebe : Endblock D (vertragVon D Bc.f) false Γe Λe) (σe : World D) (ρe : Env D Γe)
    (pcN : Runner.W) (mN : Runner.Mem) (out : Runner.W → Runner.Mem → RufMaschineG D → Prop)
    (Z : RufMaschineG D → Prop) (t : T) (m : Runner.Mem) : Prop :=
  ∃ (pce : Runner.W) (me : Runner.Mem) (Me M3 : RufMaschineG D),
    RandL Bc thr (caller :: stapel) ρc σm Agl ebe pce me Me σe ρe ∧ Z Me ∧
    (∃ n, StarM n ⟨pce, Bc.fp⟩ me t m) ∧ Star t m ⟨pcN, B.fp⟩ mN ∧
    RufLaufG B.P B.O B.passes thr Me M3 ∧ out pcN mN M3 ∧ Z M3

/-- The image classification of a complete call, with its fixed caller endpoint
    and the source continuation described by `out`. Every named machine has `Z`. -/
def BlockBild (B : BodyFrame D) (Lm j : Nat) (g : D.Fn) (σc : World D)
    (ρc : Env D (D.params g)) (thr : Faden) (caller : RufRahmenG D)
    (stapel : List (RufRahmenG D)) (Agl : D.Lock → Prop)
    {Γe : Ctx} {Λe : List (Res D)} (ebe : Endblock D (vertragVon D g) false Γe Λe)
    (σe : World D) (ρe : Env D Γe) (pc : Runner.W) (m : Runner.Mem)
    (out : Runner.W → Runner.Mem → RufMaschineG D → Prop) (Z : RufMaschineG D → Prop) : Prop :=
  ∃ (fpc rpc : Runner.W) (Kc Ksc : Nat) (ensc : List II × Nat)
    (pcI pcN : Runner.W) (mI mN : Runner.Mem) (M2 : RufMaschineG D) (σm : World D),
    let Bc := rumpfRahmen B.L B.O B.passes B.P B.A B.C Lm j g fpc Kc Ksc rpc B.fp σc ρc B.H ensc
    Star ⟨pc, B.fp⟩ m ⟨pcN, B.fp⟩ mN ∧ out pcN mN M2 ∧ Z M2 ∧
    Star ⟨pc, B.fp⟩ m ⟨pcI, fpc⟩ mI ∧
    ∀ {n : Nat} {t : T} {m' : Runner.Mem}, StarM n ⟨pc, B.fp⟩ m t m' →
      Star t m' ⟨pcN, B.fp⟩ mN →
      Star t m' ⟨pcI, fpc⟩ mI ∨
      (∃ M', KorrespondenzL Bc thr (caller :: stapel) ρc σm Agl false t m' M' ∧ Z M') ∨
      ImBlockRueck B Bc thr caller stapel ρc σm Agl ebe σe ρe pcN mN out Z t m'

/-- Refine a whole block call into entry, callee-body and return windows. This one
    proof serves plain calls and both channels of bound calls. No image endpoint
    or machine correspondence is assumed beyond the proved `BlockFenster`.
    Every machine named is reachable and carries every leg of the goal theorem. -/
theorem BlockFenster.ziel [DecidableEq D.Fn] {B : BodyFrame D}
    [TorOK B.L B.O] [SichtOK B.O]
    {Lm j : Nat} {g : D.Fn} {σc : World D} {ρc : Env D (D.params g)}
    {thr : Faden} {caller : RufRahmenG D} {stapel : List (RufRahmenG D)} {Agl : D.Lock → Prop}
    {Γe : Ctx} {Λe : List (Res D)} {ebe : Endblock D (vertragVon D g) false Γe Λe}
    {σe : World D} {ρe : Env D Γe} {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D}
    {out : Runner.W → Runner.Mem → RufMaschineG D → Prop}
    (h : BlockFenster B Lm j g σc ρc thr caller stapel Agl ebe σe ρe pc m M out)
    (hkC : Zerlegung (rufZRahmen B.L B.O B.passes B.P B.A j g σc ρc) Agl
      (TiefAlle B.P Agl j) (B.P.rumpf g) σc ρc ebe σe ρe)
    {S : SperrInv D} {Q : AxEns D} {fs : Aufzaehlung D.Fn} (ls : Aufzaehlung D.Lock)
    {ws : List D.Fn} {Acc : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpec B.P S fs.1 ws Acc) (hN : LogikPflicht B.P S Q)
    (hH : HardwareAnnahmen B.O Q) {sp : Speicher D}
    {init : Faden → Σ f : D.Fn, Env D (D.params f)} (hZ : StartZulaessig B.P S fs.1 ws sp init)
    (hM : RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) M) :
    BlockBild B Lm j g σc ρc thr caller stapel Agl ebe σe ρe pc m out
      (fun M' => RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) M' ∧
        Ziel B.P S B.O B.passes (RufStartG B.P sp init) M') := by
  obtain ⟨fpc, rpc, Kc, Ksc, ensc, pcI, pcN, mI, mN, M1, M2, σm,
    hOk, sI, hl1, hI, sN, hl2, hN2, hout⟩ := h
  have hr1 := rufErreichbar_lauf hl1 hM
  have hr2 := rufErreichbar_lauf hl2 hM
  have hRuf := rufOk_gleich_tiefAlle (P := B.P) (passes := B.passes) thr Agl j
  have hkC' : Zerlegung (rumpfRahmen B.L B.O B.passes B.P B.A B.C Lm j g fpc Kc Ksc rpc B.fp
      σc ρc B.H ensc) Agl (TiefAlle B.P Agl j) (B.P.rumpf g) σc ρc ebe σe ρe :=
    zerlegung_rahmen hkC
  refine ⟨fpc, rpc, Kc, Ksc, ensc, pcI, pcN, mI, mN, M2, σm, sN, hN2,
    ⟨hr2, ziel_aus B.P S Q fs ls ws hA hN B.O hH B.passes sp init hZ M2 hr2⟩, sI, ?_⟩
  intro n t m' hrun hvorN
  rcases hrun.weiche sI with hvor | ⟨nI, hnach⟩
  · exact Or.inl hvor
  · rcases bild_ziel_seqL (ls := ls) hOk hA hN hH hZ hRuf hkC' hr1 hI hnach with
      ⟨M', hK, hr', hz'⟩ | ⟨pce, me, Me, hRe, hre, hze, k', hk'⟩
    · exact Or.inr (Or.inl ⟨M', hK, hr', hz'⟩)
    · obtain ⟨M3, hl3, hN3⟩ := hout hRe.2
      have hr3 := rufErreichbar_lauf hl3 hre
      exact Or.inr (Or.inr ⟨pce, me, Me, M3, hRe, ⟨hre, hze⟩, ⟨k', hk'⟩,
        hvorN, hl3, hN3, hr3, ziel_aus B.P S Q fs ls ws hA hN B.O hH B.passes sp init hZ M3 hr3⟩)

#print axioms BlockFenster.ziel

end Gabbro.Stage0.Senke.BildLauf
