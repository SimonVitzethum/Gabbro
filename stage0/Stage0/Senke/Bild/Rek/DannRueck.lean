/-
  File:      stage0/Stage0/Senke/Bild/Rek/DannRueck.lean
  Subject:   **Calls in block position, machine G: in and out** (package P5 of the closed calls of the image theorem,
             part 7). For each call form in a block -- a plain call, `let x = g(…)`, and `let x = g(…) else { … }` with
             BOTH exits -- from a block-position boundary (`RandDannGL`) in front of the call whose sequential run
             ends (normally, or with a reason), machine G descends into the callee (`Rek/Dann.lean`), and from EVERY
             boundary the callee's decomposed prefix reaches, thread `thr` alone returns to the caller's next
             block-position boundary: behind the plain call, with the value bound into `rest`, or with the reason
             bound into the else block. The caller's locks behind the call are read off the callee obligation at the
             callee's entry (`offen_rueck_ok`, `offen_rueck_why`: the pop keeps the entry's held set, `RufOk`), so no
             lock fact about the callee's inner boundary is needed. The callee is admitted with recursion
             (`TiefAlle`).
-/
module
public import Stage0.Senke.Bild.Rek.Dann
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## The held set at the pop is the entry's -/

/-- **Normal exit**: when the call `rufAt (j + 1) g σc ρc` ends normally and machine `M1` stands at the callee's exact
    entry (world `σm ≈ σc`), every world `≈` to the call's world has the entry's held set. -/
theorem offen_rueck_ok {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) {thr : Faden}
    {caller : RufRahmenG D} {stapel : List (RufRahmenG D)} {Agl : D.Lock → Prop} {g : D.Fn} {j : Nat}
    {σc σ2 : World D} {ρc : Env D (D.params g)} {v : ErgVal D (D.erg g)}
    (hR : rufAt P O passes (j + 1) g σc ρc = .ok σ2 v) (hg : TiefAlle P Agl (j + 1) g) {M1 : RufMaschineG D}
    {σm : World D} (hw : WeltGleich σc σm) (hE : RandG thr (caller :: stapel) g ρc σm Agl (P.rumpf g) M1 σm ρc)
    {ziel : ErgVal D (D.erg g) → RufRahmenG D} (hart : PopArt g caller ziel) {σ'' : World D}
    (h2 : WeltGleich σ2 σ'') : offen σ''.spur = offen σm.spur := by
  obtain ⟨⟨log, hZ1⟩, hΛ1, hA1⟩ := hE
  obtain ⟨σx, hRx, hwx⟩ := rufAt_ok_rufRumpf hO hw hR
  obtain ⟨_, _, _, _, hoffx⟩ := (rufOk_tiefAlle P O passes thr Agl (j + 1)).1 g hg σm σx ρc v hRx M1 caller
    stapel log hZ1 ziel hart hΛ1 hA1
  exact (h2.symm.trans hwx).offen_eq.trans hoffx

/-- **Reason exit**: as `offen_rueck_ok`, when the call answers a reason. -/
theorem offen_rueck_why {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) {thr : Faden}
    {caller : RufRahmenG D} {stapel : List (RufRahmenG D)} {Agl : D.Lock → Prop} {g : D.Fn} {j : Nat}
    {σc σ2 : World D} {ρc : Env D (D.params g)} {r : Fin (D.gruende g)}
    (hR : rufAt P O passes (j + 1) g σc ρc = .why σ2 r) (hg : TiefAlle P Agl (j + 1) g) {M1 : RufMaschineG D}
    {σm : World D} (hw : WeltGleich σc σm) (hE : RandG thr (caller :: stapel) g ρc σm Agl (P.rumpf g) M1 σm ρc)
    {zielG : Fin (D.gruende g) → RufRahmenG D} (hart : PopGrund g caller zielG) {σ'' : World D}
    (h2 : WeltGleich σ2 σ'') : offen σ''.spur = offen σm.spur := by
  obtain ⟨⟨log, hZ1⟩, hΛ1, hA1⟩ := hE
  obtain ⟨σx, hRx, hwx⟩ := rufAt_why_rufRumpf hO hw hR
  obtain ⟨_, _, _, _, hoffx⟩ := (rufOk_tiefAlle P O passes thr Agl (j + 1)).2 g hg σm σx ρc r hRx M1 caller
    stapel log hZ1 zielG hart hΛ1 hA1
  exact (h2.symm.trans hwx).offen_eq.trans hoffx

variable [Runner.IR.Kern]

/-! ## The pop into a block-position caller -/

/-- **Out of the callee, normal exit, into a block-position caller frame**: the caller of `f` stood at a
    block-position boundary (`σ ≈ σm0`, locks `Λ`), the call `g(args)` ends normally with `v`, machine `M1` stood at the
    callee's exact entry, and `Me` stands at a boundary of the callee behind its decomposed prefix. Then `thr` alone
    pops from `Me` into `ziel v`, at a world `≈` to the call's world, holding the locks of `nach D g Λ`. -/
theorem randDannGL_rueck_ok {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {Agl : D.Lock → Prop} {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn}
    {args : Args D Γ Λ (D.params g)} {σ σm0 : World D} {ρ : Env D Γ} (hw : WeltGleich σ σm0)
    (hΛ : HeldB (vertragVon D f).boden Λ (offen σm0.spur)) {caller : RufRahmenG D} {M1 : RufMaschineG D}
    {σm : World D} (hw1 : WeltGleich (σ.lese Λ args.orte) σm)
    (hE : RandG thr (caller :: stapel) g (rufEnv g σ Λ args ρ) σm Agl (P.rumpf g) M1 σm (rufEnv g σ Λ args ρ))
    {j : Nat} {σ2 : World D} {v : ErgVal D (D.erg g)}
    (hR : rufAt P O passes (j + 1) g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v)
    (hg : TiefAlle P Agl (j + 1) g) {Y : Lay D} {A : D.Fn → Nat} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)) Agl
      (TiefAlle P Agl j) (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ebeC σeC ρeC)
    {ziel : ErgVal D (D.erg g) → RufRahmenG D} (hart : PopArt g caller ziel) {Me : RufMaschineG D}
    (hMe : RandGL thr (caller :: stapel) g (rufEnv g σ Λ args ρ) σm Agl ebeC Me σeC ρeC) :
    ∃ (M' : RufMaschineG D) (σ'' : World D) (lg : List (RufEreignisF D)),
      RufLaufG P O passes thr Me M' ∧ WeltGleich σ2 σ'' ∧
      GepopptG M' thr (ziel v) stapel g (rufEnv g σ Λ args ρ) σm lg v σ'' ∧
      HeldB (vertragVon D f).boden (nach D g Λ) (offen σ''.spur) ∧ FreiA Agl M' thr := by
  obtain ⟨M', σ'', lg, hl, hw2, hGp, _⟩ := randGL_rueck_ruf_ok hO hR hg hkC hMe hart
  have hoff : offen σ''.spur = offen σm.spur := offen_rueck_ok hO hR hg hw1 hE hart hw2
  have hoffm : offen σm.spur = offen σm0.spur :=
    (hw1.symm.trans ((weltGleich_lese σ Λ args.orte).symm.trans hw)).offen_eq
  obtain ⟨_, _, _, _, hAe⟩ := hMe
  refine ⟨M', σ'', lg, hl, hw2, hGp, ?_, hAe.lauf hl⟩
  exact heldB_iff (fun L => held_nachSig_iff _ _ L) (by rw [hoff, hoffm]; exact hΛ)

/-- **Out of the callee, reason exit, into a block-position caller frame**: as `randDannGL_rueck_ok`, when the call
    answers the reason `r`; `thr` pops through the error channel into `zielG r`. -/
theorem randDannGL_rueck_why {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {Agl : D.Lock → Prop} {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn}
    {args : Args D Γ Λ (D.params g)} {σ σm0 : World D} {ρ : Env D Γ} (hw : WeltGleich σ σm0)
    (hΛ : HeldB (vertragVon D f).boden Λ (offen σm0.spur)) {caller : RufRahmenG D} {M1 : RufMaschineG D}
    {σm : World D} (hw1 : WeltGleich (σ.lese Λ args.orte) σm)
    (hE : RandG thr (caller :: stapel) g (rufEnv g σ Λ args ρ) σm Agl (P.rumpf g) M1 σm (rufEnv g σ Λ args ρ))
    {j : Nat} {σ2 : World D} {r : Fin (D.gruende g)}
    (hR : rufAt P O passes (j + 1) g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .why σ2 r)
    (hg : TiefAlle P Agl (j + 1) g) {Y : Lay D} {A : D.Fn → Nat} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)) Agl
      (TiefAlle P Agl j) (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ebeC σeC ρeC)
    {zielG : Fin (D.gruende g) → RufRahmenG D} (hart : PopGrund g caller zielG) {Me : RufMaschineG D}
    (hMe : RandGL thr (caller :: stapel) g (rufEnv g σ Λ args ρ) σm Agl ebeC Me σeC ρeC) :
    ∃ (M' : RufMaschineG D) (σ'' : World D) (lg : List (RufEreignisF D)),
      RufLaufG P O passes thr Me M' ∧ WeltGleich σ2 σ'' ∧
      GepopptGrundG M' thr (zielG r) stapel g (rufEnv g σ Λ args ρ) σm lg r σ'' ∧
      HeldB (vertragVon D f).boden (nach D g Λ) (offen σ''.spur) ∧ FreiA Agl M' thr := by
  obtain ⟨M', σ'', lg, hl, hw2, hGp, _⟩ := randGL_rueck_ruf_why hO hR hg hkC hMe hart
  have hoff : offen σ''.spur = offen σm.spur := offen_rueck_why hO hR hg hw1 hE hart hw2
  have hoffm : offen σm.spur = offen σm0.spur :=
    (hw1.symm.trans ((weltGleich_lese σ Λ args.orte).symm.trans hw)).offen_eq
  obtain ⟨_, _, _, _, hAe⟩ := hMe
  refine ⟨M', σ'', lg, hl, hw2, hGp, ?_, hAe.lauf hl⟩
  exact heldB_iff (fun L => held_nachSig_iff _ _ L) (by rw [hoff, hoffm]; exact hΛ)

/-! ## Every call form in a block, in and out -/

/-- **A plain call in a block, in and out** (`g(args); rest` at `.dann`): machine G descends into the callee, and from
    every boundary of the callee behind its decomposed prefix, `thr` returns to the caller's boundary in front of
    `rest`, at a world `≈` to the call's world. -/
theorem randDannGL_ruf_ein_aus {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Block D (vertragVon D f) l Γ (nach D g Λ) Λ''} {k : GRest D (vertragVon D f) l Γ Λ''}
    {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandDannGL thr stapel f rho s0 Agl (.cons (.call g args hp hr) rest) k M σ ρ) {j : Nat}
    {σ2 : World D} {v : ErgVal D (D.erg g)}
    (hR : rufAt P O passes (j + 1) g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v)
    (hg : TiefAlle P Agl (j + 1) g) {Y : Lay D} {A : D.Fn → Nat} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)) Agl
      (TiefAlle P Agl j) (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ebeC σeC ρeC) :
    ∃ (M1 : RufMaschineG D) (σm : World D), RufLaufG P O passes thr M M1 ∧
      RandGL thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: stapel) g (rufEnv g σ Λ args ρ) σm Agl
        (P.rumpf g) M1 (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ∧
      ∀ {Me : RufMaschineG D}, RandGL thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: stapel) g
          (rufEnv g σ Λ args ρ) σm Agl ebeC Me σeC ρeC →
        ∃ M', RufLaufG P O passes thr Me M' ∧ RandDannGL thr stapel f rho s0 Agl rest k M' σ2 ρ := by
  obtain ⟨M1, σm, hl1, hw1, hE⟩ := randDannGL_ruf_eintritt (P := P) (O := O) (passes := passes) h
  obtain ⟨σm0, hw, _, hΛ, _⟩ := h
  refine ⟨M1, σm, hl1, randGL_von_eintritt hw1 hE, ?_⟩
  intro Me hMe
  obtain ⟨M', σ'', lg, hl, hw2, hGp, hΛ', hA'⟩ :=
    randDannGL_rueck_ok hO hw hΛ hw1 hE hR hg hkC (PopArt.wie rfl) hMe
  exact ⟨M', hl, σ'', hw2, ⟨_, hGp.1, hGp.2⟩, hΛ', hA'⟩

/-- **`let x = g(…)` in a block, in and out**: the return binds the value into `rest`. -/
theorem randDannGL_bindCall_ein_aus {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O)
    {thr : Faden} {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D}
    {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn}
    {args : Args D Γ Λ (D.params g)} {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ}
    {hr : D.gruende g = 0} {rest : Block D (vertragVon D f) l (τ :: Γ) (nach D g Λ) Λ'}
    {k : GRest D (vertragVon D f) l Γ Λ'} {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandDannGL thr stapel f rho s0 Agl (.bindCall g args he hp hr rest) k M σ ρ) {j : Nat}
    {σ2 : World D} {v : ErgVal D (D.erg g)}
    (hR : rufAt P O passes (j + 1) g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v)
    (hg : TiefAlle P Agl (j + 1) g) {Y : Lay D} {A : D.Fn → Nat} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)) Agl
      (TiefAlle P Agl j) (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ebeC σeC ρeC) :
    ∃ (M1 : RufMaschineG D) (σm : World D), RufLaufG P O passes thr M M1 ∧
      RandGL thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ :: stapel) g (rufEnv g σ Λ args ρ) σm Agl
        (P.rumpf g) M1 (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ∧
      ∀ {Me : RufMaschineG D}, RandGL thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ :: stapel) g
          (rufEnv g σ Λ args ρ) σm Agl ebeC Me σeC ρeC →
        ∃ M', RufLaufG P O passes thr Me M' ∧
          RandDannGL thr stapel f rho s0 Agl rest (.schrumpf k) M' σ2 (.cons (ergWert he v) ρ) := by
  obtain ⟨M1, σm, hl1, hw1, hE⟩ := randDannGL_bindCall_eintritt (P := P) (O := O) (passes := passes) h
  obtain ⟨σm0, hw, _, hΛ, _⟩ := h
  refine ⟨M1, σm, hl1, randGL_von_eintritt hw1 hE, ?_⟩
  intro Me hMe
  obtain ⟨M', σ'', lg, hl, hw2, hGp, hΛ', hA'⟩ :=
    randDannGL_rueck_ok hO hw hΛ hw1 hE hR hg hkC (PopArt.bind rest k ρ rfl he) hMe
  exact ⟨M', hl, σ'', hw2, ⟨_, hGp.1, hGp.2⟩, hΛ', hA'⟩

/-- **`let x = g(…) else { err }` in a block, normal exit, in and out**: the return binds the value into `rest`. -/
theorem randDannGL_bindCallElse_ein_aus {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O)
    {thr : Faden} {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D}
    {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn}
    {args : Args D Γ Λ (D.params g)} {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ}
    {hr : 0 < D.gruende g} {err : Endblock D (vertragVon D f) l (.why (D.gruende g) :: Γ) (nach D g Λ)}
    {rest : Block D (vertragVon D f) l (τ :: Γ) (nach D g Λ) Λ'} {k : GRest D (vertragVon D f) l Γ Λ'}
    {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandDannGL thr stapel f rho s0 Agl (.bindCallElse g args he hp hr err rest) k M σ ρ) {j : Nat}
    {σ2 : World D} {v : ErgVal D (D.erg g)}
    (hR : rufAt P O passes (j + 1) g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v)
    (hg : TiefAlle P Agl (j + 1) g) {Y : Lay D} {A : D.Fn → Nat} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)) Agl
      (TiefAlle P Agl j) (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ebeC σeC ρeC) :
    ∃ (M1 : RufMaschineG D) (σm : World D), RufLaufG P O passes thr M M1 ∧
      RandGL thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ :: stapel) g
        (rufEnv g σ Λ args ρ) σm Agl (P.rumpf g) M1 (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ∧
      ∀ {Me : RufMaschineG D},
        RandGL thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ :: stapel) g
          (rufEnv g σ Λ args ρ) σm Agl ebeC Me σeC ρeC →
        ∃ M', RufLaufG P O passes thr Me M' ∧
          RandDannGL thr stapel f rho s0 Agl rest (.schrumpf k) M' σ2 (.cons (ergWert he v) ρ) := by
  obtain ⟨M1, σm, hl1, hw1, hE⟩ := randDannGL_bindCallElse_eintritt (P := P) (O := O) (passes := passes) h
  obtain ⟨σm0, hw, _, hΛ, _⟩ := h
  refine ⟨M1, σm, hl1, randGL_von_eintritt hw1 hE, ?_⟩
  intro Me hMe
  obtain ⟨M', σ'', lg, hl, hw2, hGp, hΛ', hA'⟩ :=
    randDannGL_rueck_ok hO hw hΛ hw1 hE hR hg hkC (PopArt.bindSonst (D.gruende g) err rest k ρ rfl he) hMe
  exact ⟨M', hl, σ'', hw2, ⟨_, hGp.1, hGp.2⟩, hΛ', hA'⟩

/-- **`let x = g(…) else { err }` in a block, reason exit, in and out**: the return runs the else block with the
    reason bound. -/
theorem randDannGL_bindCallElse_ein_aus_why {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O)
    {thr : Faden} {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D}
    {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn}
    {args : Args D Γ Λ (D.params g)} {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ}
    {hr : 0 < D.gruende g} {err : Endblock D (vertragVon D f) l (.why (D.gruende g) :: Γ) (nach D g Λ)}
    {rest : Block D (vertragVon D f) l (τ :: Γ) (nach D g Λ) Λ'} {k : GRest D (vertragVon D f) l Γ Λ'}
    {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandDannGL thr stapel f rho s0 Agl (.bindCallElse g args he hp hr err rest) k M σ ρ) {j : Nat}
    {σ2 : World D} {r : Fin (D.gruende g)}
    (hR : rufAt P O passes (j + 1) g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .why σ2 r)
    (hg : TiefAlle P Agl (j + 1) g) {Y : Lay D} {A : D.Fn → Nat} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)) Agl
      (TiefAlle P Agl j) (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ebeC σeC ρeC) :
    ∃ (M1 : RufMaschineG D) (σm : World D), RufLaufG P O passes thr M M1 ∧
      RandGL thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ :: stapel) g
        (rufEnv g σ Λ args ρ) σm Agl (P.rumpf g) M1 (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ∧
      ∀ {Me : RufMaschineG D},
        RandGL thr (⟨f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ :: stapel) g
          (rufEnv g σ Λ args ρ) σm Agl ebeC Me σeC ρeC →
        ∃ M', RufLaufG P O passes thr Me M' ∧
          RandDannGL thr stapel f rho s0 Agl err.alsBlock.2 (.abbruch (.schrumpf k)) M' σ2 (.cons r ρ) := by
  obtain ⟨M1, σm, hl1, hw1, hE⟩ := randDannGL_bindCallElse_eintritt (P := P) (O := O) (passes := passes) h
  obtain ⟨σm0, hw, _, hΛ, _⟩ := h
  refine ⟨M1, σm, hl1, randGL_von_eintritt hw1 hE, ?_⟩
  intro Me hMe
  obtain ⟨M', σ'', lg, hl, hw2, hGp, hΛ', hA'⟩ :=
    randDannGL_rueck_why hO hw hΛ hw1 hE hR hg hkC (PopGrund.sonst err rest k ρ rfl) hMe
  exact ⟨M', hl, σ'', hw2, ⟨_, hGp.1, hGp.2⟩, hΛ', hA'⟩

#print axioms randDannGL_rueck_ok
#print axioms randDannGL_rueck_why
#print axioms randDannGL_ruf_ein_aus
#print axioms randDannGL_bindCall_ein_aus
#print axioms randDannGL_bindCallElse_ein_aus
#print axioms randDannGL_bindCallElse_ein_aus_why

end Gabbro.Stage0.Senke.BildLauf
