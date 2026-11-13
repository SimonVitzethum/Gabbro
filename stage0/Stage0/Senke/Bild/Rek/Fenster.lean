/-
  File:      stage0/Stage0/Senke/Bild/Rek/Fenster.lean
  Subject:   **A whole call, in and out, both sides** (package P5 of the closed calls of the image theorem, part 3).
             In the caller's decomposed prefix a plain call of an admitted callee is ONE step: the image runs the
             call's code from the boundary in front of it to the boundary behind it (`randL_schritt`), and every image
             state in between corresponds only to the caller's machine in front of the call (G stutters). P4 refined
             the first half: from the callee's first body boundary, the states inside the callee's decomposed prefix
             correspond to machines inside the callee. `bild_ziel_fenster` refines the WHOLE window of the call:
             every state between the boundary in front of the call and the boundary behind it is
             (a) in front of the callee's first body boundary (the caller's machine in front of the call),
             (b) inside a decomposed step of the callee's body (`KorrespondenzL` in the callee's frame), or
             (c) behind the callee's decomposed prefix and in front of the caller's next boundary (`ImRueck`): it lies
                 on the image run from the callee's boundary `ebeC`, which corresponds to `Me`, to the caller's
                 boundary in front of `rest`, which corresponds to a machine `M3` that thread `thr` reaches from `Me`
                 by running the rest of the callee and popping into the caller (`randGL_rueck`).
             Every machine named is reachable and satisfies every leg of `Ziel`. The callee is admitted with
             recursion (`TiefAlle`, `Rek/Alle.lean`); the callee's prefix admits its own callees one level down.

             The window's two ends are the caller's (exact image side `RandIR` from `randL_schritt`), so the image needs
             no new run lemma for the epilogue: the image's run of the whole call is fixed, and the fork of
             memory-only runs (`StarM.weiche`) places every state relative to the callee's boundaries.
             At a boundary of the callee in front of a further call the window applies again, one level down.
-/
module
public import Stage0.Senke.Bild.Rek.RueckG
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

variable [Kern]

/-- **An image state in the return window of a call**: it lies on the image run from a boundary `ebeC` of the
    callee's body (frame `Bc`), which corresponds to a machine `Me` with `Z`, to the caller's boundary in front of
    `rest` at `(pcN, B.fp, mN)`, which corresponds to a machine `M3` with `Z` that thread `thr` reaches from `Me`. -/
def ImRueck (B Bc : BodyFrame D) (thr : Faden) (stapel : List (RufRahmenG D)) (rho : Env D (D.params B.f))
    (s0 : World D) (Agl : D.Lock → Prop) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (rest : Endblock D (vertragVon D B.f) l Γ Λ) (pcN : Runner.W) (mN : Runner.Mem) (σ1 : World D)
    (ρ1 : Env D Γ) (stapelC : List (RufRahmenG D)) (rhoC : Env D (D.params Bc.f)) (s0C : World D)
    {ΓeC : Ctx} {ΛeC : List (Res D)} (ebeC : Endblock D (vertragVon D Bc.f) false ΓeC ΛeC) (σeC : World D)
    (ρeC : Env D ΓeC) (Z : RufMaschineG D → Prop) (t : T) (m : Runner.Mem) : Prop :=
  ∃ (pce : Runner.W) (me : Runner.Mem) (Me M3 : RufMaschineG D),
    RandL Bc thr stapelC rhoC s0C Agl ebeC pce me Me σeC ρeC ∧ Z Me ∧ (∃ k, StarM k ⟨pce, Bc.fp⟩ me t m) ∧
    Star t m ⟨pcN, B.fp⟩ mN ∧ RufLaufG B.P B.O B.passes thr Me M3 ∧
    RandL B thr stapel rho s0 Agl rest pcN mN M3 σ1 ρ1 ∧ Z M3

/-- **THE GOAL LEGS ALONG A WHOLE CALL (T1 in and out of a callee, one thread).** Under the checker's facts (a′), the
    user's logic (b), the named hardware assumptions (c), an admissible start (d′) and a read-blind oracle: let the
    caller's boundary (frame `rumpfRahmen` at handler depth `k = j + 1`) in front of a plain call `g(args); rest`
    correspond to a reachable machine `M`, the call end normally under `rufAt k`, the callee be admitted at depth `k`
    (`TiefAlle`, recursion included), and the callee's decomposed prefix (callees admitted at depth `j`) reach `ebeC`.
    Then the image runs the call's code to the caller's boundary in front of `rest`, which corresponds to a reachable
    machine `M2` with `Ziel`, passing the callee's first body boundary; and every memory-only prefix of the image's run
    from the caller's boundary that is still in front of the caller's next boundary is in front of the callee's first
    body boundary, or inside a decomposed step of the callee's body corresponding to a reachable machine with `Ziel`,
    or in the call's return window (`ImRueck`), between two boundaries that correspond to reachable machines with
    `Ziel`, the second reached from the first. -/
theorem bild_ziel_fenster [DecidableEq D.Fn] {Y : Lay D} {O : Orakel D} [TorOK Y O] [SichtOK O]
    {passes : Nat} {P : Programm D} {A : D.Fn → Nat} {C : D.Fn → List II} {Lm : Nat}
    (hc : BildCodes Y P passes A C Lm) {S : SperrInv D} {Q : AxEns D} {fs : Aufzaehlung D.Fn}
    (ls : Aufzaehlung D.Lock) {ws : List D.Fn} {Acc : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpec P S fs.1 ws Acc) (hN : LogikPflicht P S Q) (hH : HardwareAnnahmen O Q)
    {sp : Speicher D} {init : Faden → Σ g : D.Fn, Env D (D.params g)} (hZ : StartZulaessig P S fs.1 ws sp init)
    {k j : Nat} (hkj : k = j + 1) (hk64 : k < 2 ^ 64) {f : D.Fn} {fp : Runner.W} {K Ks : Nat}
    {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {H : List D.Lock} {ens : List II × Nat}
    (hB : (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens).Ok)
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params f)} {s0 : World D}
    {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Endblock D (vertragVon D f) l Γ (nach D g Λ)} {pc : Runner.W} {m : Runner.Mem}
    {M : RufMaschineG D} {σ σ1 : World D} {ρ ρ1 : Env D Γ}
    (hM : RufErreichbarG P O passes (RufStartG P sp init) M)
    (h : RandL (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens) thr stapel rho s0 Agl
      (.cons (.call g args hp hr) rest) pc m M σ ρ)
    (hex : execStmt O passes (rufAt P O passes k)
      (.call g args hp hr : Stmt D (vertragVon D f) l Γ Λ (nach D g Λ)) σ ρ = .ok σ1 ρ1)
    (hg : TiefAlle P Agl k g)
    {ΓeC : Ctx} {ΛeC : List (Res D)} {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D}
    {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)) Agl
      (TiefAlle P Agl j) (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ebeC σeC ρeC) :
    ∃ (n1 : Nat) (m1 : Runner.Mem) (M2 : RufMaschineG D) (fpc rpc : Runner.W) (Kc Ksc : Nat)
      (ensc : List II × Nat) (pcI : Runner.W) (mI : Runner.Mem) (σm : World D),
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * n1), fp⟩ m1 ∧
      RandL (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens) thr stapel rho s0 Agl rest
        (pc + BitVec.ofNat 64 (16 * n1)) m1 M2 σ1 ρ1 ∧
      RufErreichbarG P O passes (RufStartG P sp init) M2 ∧ Ziel P S O passes (RufStartG P sp init) M2 ∧
      Star ⟨pc, fp⟩ m ⟨pcI, fpc⟩ mI ∧
      ∀ {n : Nat} {t : T} {m' : Runner.Mem}, StarM n ⟨pc, fp⟩ m t m' →
        Star t m' ⟨pc + BitVec.ofNat 64 (16 * n1), fp⟩ m1 →
        Star t m' ⟨pcI, fpc⟩ mI ∨
        (∃ M', KorrespondenzL (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args)
            (rufEnv g σ Λ args ρ) H ensc) thr (rufRahmenNach rho s0 ρ rest :: stapel) (rufEnv g σ Λ args ρ) σm
            Agl false t m' M' ∧
          RufErreichbarG P O passes (RufStartG P sp init) M' ∧ Ziel P S O passes (RufStartG P sp init) M') ∨
        ImRueck (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens)
          (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) H
            ensc) thr stapel rho s0 Agl rest (pc + BitVec.ofNat 64 (16 * n1)) m1 σ1 ρ1
          (rufRahmenNach rho s0 ρ rest :: stapel) (rufEnv g σ Λ args ρ) σm ebeC σeC ρeC
          (fun M' => RufErreichbarG P O passes (RufStartG P sp init) M' ∧
            Ziel P S O passes (RufStartG P sp init) M') t m' := by
  subst hkj
  haveI : LeseblindOK O := leseblindOK_hardware hH
  have hO : LeseblindP P O := leseblindP_alle P O
  -- the whole call as one step of the caller
  have hRuf := rufOk_gleich_tiefAlle (P := P) (passes := passes) hO thr Agl (j + 1)
  have hs : StmtR Agl (TiefAlle P Agl (j + 1)) false
      (.call g args hp hr : Stmt D (vertragVon D f) l Γ Λ (nach D g Λ)) :=
    StmtR.call _ g rfl hg
  obtain ⟨n1, m1, M2, sB, _, hl2, hRB⟩ := randL_schritt hB hRuf hs hex h
  have hM2 := rufErreichbar_lauf hl2 hM
  -- the descent to the callee's first body boundary
  obtain ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, M1, σm, sI, hl1, _, hOkC, hRI⟩ :=
    randL_ruf_eintritt (thr := thr) (stapel := stapel) (Agl := Agl) hc rfl hk64 hB h hex
  have hM1 := rufErreichbar_lauf hl1 hM
  have hRufC := rufOk_gleich_tiefAlle (P := P) (passes := passes) hO thr Agl j
  have hkC' : Zerlegung (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args)
      (rufEnv g σ Λ args ρ) H ensc) Agl (TiefAlle P Agl j) (P.rumpf g) (rufWelt P g σ Λ args)
      (rufEnv g σ Λ args ρ) ebeC σeC ρeC :=
    zerlegung_rahmen hkC
  refine ⟨n1, m1, M2, fpc, rpc, Kc, Ksc, ensc, pcI, mI, σm, sB, hRB, hM2,
    ziel_aus P S Q fs ls ws hA hN O hH passes sp init hZ M2 hM2, sI, ?_⟩
  intro n t m' hrun hvorB
  rcases hrun.weiche sI with hvor | ⟨k1, hnach⟩
  · exact Or.inl hvor
  · rcases bild_ziel_seqL (ls := ls) hOkC hA hN hH hZ hRufC hkC' hM1 hRI hnach with
      ⟨M', hK, hr', hz'⟩ | ⟨pce, me, Me, hRe, hre, hze, k', hk'⟩
    · exact Or.inr (Or.inl ⟨M', hK, hr', hz'⟩)
    · -- the return: the rest of the callee and the pop, to the caller's boundary behind the call
      obtain ⟨M3, hl3, hG3⟩ := randGL_rueck hO hg h.2 hex hkC hRe.2
      have hM3 := rufErreichbar_lauf hl3 hre
      exact Or.inr (Or.inr ⟨pce, me, Me, M3, hRe, ⟨hre, hze⟩, ⟨k', hk'⟩, hvorB, hl3, ⟨hRB.1, hG3⟩, hM3,
        ziel_aus P S Q fs ls ws hA hN O hH passes sp init hZ M3 hM3⟩)

#print axioms bild_ziel_fenster

end Gabbro.Stage0.Senke.BildLauf
