/-
  File:      stage0/Stage0/Senke/Bild/Rek/RueckG.lean
  Subject:   **The return to the caller, machine G** (package P5 of the closed calls of the image theorem, part 2).
             P4 descends: from a caller's boundary in front of a plain call `g(args); rest` (caller frame at handler
             depth `j + 1`) machine G takes the step `ruf` and the callee's decomposed prefix runs to a boundary `ebeC`
             of the callee's body, the caller frame `rufRahmenNach … rest` waiting on the thread's stack.
             `randGL_rueck` goes back UP: from that callee boundary thread `thr` runs the rest of the callee's body
             (`endRetR` with the body-running handler of depth `j`) and pops into the waiting caller frame, which
             stands at the residue `.ende rest` at a world `≈` to the sequential world behind the call. So the caller's
             next boundary corresponds again, reached from the machine at the callee's last boundary.

             The sequential side: the call ends normally under the image's handler `rufAt (j + 1)`, so the callee's
             body returned (`rufAt_ok_rumpf`: the call's world is the body's return world plus the contract reads,
             `≈`), and so does its residue behind the decomposed prefix (`Zerlegung.zurueck`). The residue is in the
             call fragment (`Zerlegung.endR`), and the body-running handler realises it up to read events
             (`execEnd_lg` with P2's `rufAt_rufRumpf_lg_alle`). The caller's holdings behind the call are those of the
             call step (`randGL_schritt`, the same worlds up to `≈`).
-/
module
public import Stage0.Senke.Bild.Rek.Alle
public import Stage0.Senke.Bild.Rek.Lauf
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## The sequential side -/

/-- **A normal end of a call is a return of the callee's body**: the call's world is the body's return world after the
    reads of `ensures` and of the owed invariants, so the two are `≈`. -/
theorem rufAt_ok_rumpf {P : Programm D} {O : Orakel D} {passes n : Nat} {g : D.Fn} {σ σ1 : World D}
    {ρ : Env D (D.params g)} {v : ErgVal D (D.erg g)} (h : rufAt P O passes (n + 1) g σ ρ = .ok σ1 v) :
    ∃ σ', execEnd (V := vertragVon D g) O passes (rufAt P O passes n) (P.rumpf g)
        (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ = .zurueck σ' v ∧ WeltGleich σ' σ1 := by
  simp only [rufAt] at h
  split at h
  · cases h
  rename_i hreq
  split at h
  · rename_i σ'' v'' hx
    split at h
    · cases h
    rename_i hens
    split at h
    · cases h
    · injection h with h1 h2
      subst h1
      have h2' : v'' = v := h2
      subst h2'
      exact ⟨σ'', hx, (weltGleich_lese σ'' _ _).trans (weltGleich_foldl_lese _ _ _ _)⟩
  all_goals first
    | exact absurd ‹false = true› (by decide)
    | (cases h; done)

variable [Runner.IR.Kern]

/-- **The residue of a decomposed prefix returns as the whole block does**: the prefix's steps end normally, so a
    return of the block is a return of the end block behind the prefix, with the same world and value. -/
theorem Zerlegung.zurueck {B : BodyFrame D} {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {l : Bool} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ} {ebe : Endblock D (vertragVon D B.f) l Γe Λe}
    {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe} (h : Zerlegung B Agl Cg eb σ ρ ebe σe ρe)
    {σ' : World D} {v : ErgVal D (vertragVon D B.f).erg} :
    execEnd B.O B.passes B.R eb σ ρ = .zurueck σ' v → execEnd B.O B.passes B.R ebe σe ρe = .zurueck σ' v := by
  induction h with
  | halt => exact id
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hex _ ih =>
    intro hz
    apply ih
    simp only [execEnd, hex] at hz
    exact hz
  | bind e rest ebe σ σe ρ ρe _ ih =>
    intro hz
    apply ih
    simp only [execEnd] at hz
    exact endSchrumpf_zurueck hz

/-- **The residue of a decomposed prefix stays in the call fragment.** -/
theorem Zerlegung.endR {B : BodyFrame D} {Agl : D.Lock → Prop} {Cg C' : D.Fn → Prop} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) false Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) false Γe Λe}
    {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe} (h : Zerlegung B Agl Cg eb σ ρ ebe σe ρe) :
    EndR Agl C' eb → EndR Agl C' ebe := by
  induction h with
  | halt => exact id
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hex _ ih =>
    intro hE
    cases hE with
    | cons _ _ _ hr => exact ih hr
  | bind e rest ebe σ σe ρ ρe _ ih =>
    intro hE
    cases hE with
    | bind _ _ hr => exact ih hr

/-! ## The return, machine G -/

/-- **Back to the caller, machine G**: let the caller's boundary in front of a plain call `g(args); rest` (frame of
    `f` above `stapel`, the callee admitted at the caller's handler depth `j + 1`) be one up to read events, and the
    call end normally under `rufAt (j + 1)`. Let the callee's decomposed prefix (handler `rufAt j`) reach `ebeC`, and
    machine `Me` stand at that boundary of the callee up to read events, the caller frame `rufRahmenNach … rest`
    waiting on the stack. Then thread `thr` alone runs from `Me` to a machine at the caller's boundary in front of
    `rest`, at a world `≈` to the sequential world behind the call. -/
theorem randGL_rueck {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Endblock D (vertragVon D f) l Γ (nach D g Λ)} {M : RufMaschineG D} {σ σ1 : World D}
    {ρ ρ1 : Env D Γ} {j : Nat} (hg : TiefAlle P Agl (j + 1) g)
    (hG : RandGL thr stapel f rho s0 Agl (.cons (.call g args hp hr) rest) M σ ρ)
    (hex : execStmt O passes (rufAt P O passes (j + 1))
      (.call g args hp hr : Stmt D (vertragVon D f) l Γ Λ (nach D g Λ)) σ ρ = .ok σ1 ρ1)
    {Y : Lay D} {A : D.Fn → Nat} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)) Agl
      (TiefAlle P Agl j) (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ebeC σeC ρeC)
    {rhoG : Env D (D.params g)} {s0G : World D} {Me : RufMaschineG D}
    (hMe : RandGL thr (rufRahmenNach rho s0 ρ rest :: stapel) g rhoG s0G Agl ebeC Me σeC ρeC) :
    ∃ M', RufLaufG P O passes thr Me M' ∧ RandGL thr stapel f rho s0 Agl rest M' σ1 ρ1 := by
  -- the residue of the callee is in the call fragment one level down
  have hEC : EndR Agl (TiefAlle P Agl j) ebeC :=
    hkC.endR (show EndR Agl (TiefAlle P Agl j) (P.rumpf g) from hg)
  -- the caller's step over the call: its holdings behind the call
  have hRuf := rufOk_gleich_tiefAlle (P := P) (passes := passes) hO thr Agl (j + 1)
  have hs : StmtR Agl (TiefAlle P Agl (j + 1)) false
      (.call g args hp hr : Stmt D (vertragVon D f) l Γ Λ (nach D g Λ)) :=
    StmtR.call _ g rfl hg
  obtain ⟨M2, _, σm2, hw2, hG2⟩ := randGL_schritt hO.rs hRuf hs hex hG
  -- the sequential call: the callee's body returned, and so did its residue
  simp only [execStmt] at hex
  split at hex
  · rename_i σ2 v hR2
    simp only [Ausgang.ok.injEq] at hex
    obtain ⟨rfl, rfl⟩ := hex
    obtain ⟨σ', hbody, hσ⟩ := rufAt_ok_rumpf hR2
    have hz : execEnd O passes (rufAt P O passes j) ebeC σeC ρeC = .zurueck σ' v := hkC.zurueck hbody
    -- machine G at the callee's boundary: the body-running handler returns from a `≈` world
    obtain ⟨σme, hwe, ⟨log, hZe⟩, hΛe, hAe⟩ := hMe
    have hl := execEnd_lg (passes := passes) (rufAt_rufRumpf_lg_alle (P := P) (passes := passes) hO j) hO.rs ebeC
      (Or.inl (axFrei_endR hEC)) hwe ρeC
    rw [hz] at hl
    obtain ⟨σ'', hz'', hw''⟩ := hl.zurueck_inv
    -- the rest of the callee and the pop into the waiting caller frame
    obtain ⟨M', ext, hl', hGp, _⟩ := endRetR P O passes thr g (rufRahmenNach rho s0 ρ rest) stapel rhoG s0G Agl
      (rufRumpf P O passes j) (TiefAlle P Agl j) (fun _ => rufRahmenNach rho s0 ρ rest)
      (fun _ => rufRahmenNach rho s0 ρ rest) (rufOk_tiefAlle P O passes thr Agl j) ebeC hEC log σme ρeC
      (.zurueck σ'' v) (PopArt.wie rfl) (by rw [hz'']; rfl) Me hZe hΛe hAe
    have hGp' : GepopptG M' thr (rufRahmenNach rho s0 ρ rest) stapel g rhoG s0G (ext ++ log) v σ'' := hGp
    have hoff : offen σ''.spur = offen σm2.spur := (hw''.symm.trans (hσ.trans hw2)).offen_eq
    refine ⟨M', hl', σ'', hσ.symm.trans hw'', ⟨⟨_, hGp'.1, hGp'.2⟩, ?_, hAe.lauf hl'⟩⟩
    rw [hoff]
    exact hG2.2.1
  · exact (Fin.cast hr ‹_›).elim0
  · cases hex
  · cases hex

#print axioms randGL_rueck

end Gabbro.Stage0.Senke.BildLauf
