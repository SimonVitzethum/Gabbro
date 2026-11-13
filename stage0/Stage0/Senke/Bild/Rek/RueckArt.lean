/-
  File:      stage0/Stage0/Senke/Bild/Rek/RueckArt.lean
  Subject:   **The return from a callee for every pop kind and both exits, machine G** (package P5 of the closed calls
             of the image theorem, part 5). `randGL_rueck` (`Rek/RueckG.lean`) returns from a callee boundary into
             the caller frame of a plain call at `ende` position. The machine pops into whatever the caller frame
             waits as: unchanged (`PopArt.wie`: a plain call at `ende` or in a block), with the value bound
             (`PopArt.bind`, `PopArt.bindSonst`: `let x = g(…)` and the normal exit of `let x = g(…) else { … }`), or
             through the reason channel into the else block (`PopGrund.sonst`: the reason exit of
             `let x = g(…) else { … }`). This file states the return once for every such caller frame:
             * `randGL_rueck_ok`, `randGL_rueck_why`: from a boundary of the callee's body (up to read events),
               whose residue returns (resp. answers a reason) under the image's handler `rufAt j`, thread `thr` alone
               pops into the caller frame `ziel v` (resp. `zielG r`) at a world `≈` to the sequential one;
             * `rufRest_zurueck`, `rufRest_why`: the residue behind the callee's decomposed prefix returns (answers a
               reason) as the whole call `rufAt (j + 1)` does;
             * `randGL_rueck_ruf_ok`, `randGL_rueck_ruf_why`: both together, from the call's sequential outcome.
             The callee is admitted with recursion (`TiefAlle`, `Rek/Alle.lean`).
-/
module
public import Stage0.Senke.Bild.Rek.RueckG
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## The sequential side of the reason exit -/

/-- **A reason of a call is a reason of the callee's body**, with the same world (the reason channel reads no
    contract). -/
theorem rufAt_why_rumpf {P : Programm D} {O : Orakel D} {passes n : Nat} {g : D.Fn} {σ σ1 : World D}
    {ρ : Env D (D.params g)} {r : Fin (D.gruende g)} (h : rufAt P O passes (n + 1) g σ ρ = .why σ1 r) :
    execEnd (V := vertragVon D g) O passes (rufAt P O passes n) (P.rumpf g)
      (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ = .why σ1 r := by
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
    · cases h
  · rename_i σ'' r'' hx
    injection h with h1 h2
    subst h1
    have h2' : r'' = r := h2
    subst h2'
    exact hx
  all_goals first
    | exact absurd ‹false = true› (by decide)
    | (cases h; done)

/-- A shrunk end outcome that answers a reason answered it before the shrink. -/
theorem endSchrumpf_why {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty} {o : EndAusgang V l (τ :: Γ)}
    {σ' : World D} {r : Fin V.gruende} (h : o.schrumpf = .why σ' r) : o = .why σ' r := by
  cases o <;> simp_all [EndAusgang.schrumpf]

variable [Runner.IR.Kern]

/-- **The residue of a decomposed prefix answers a reason as the whole block does.** -/
theorem Zerlegung.why {B : BodyFrame D} {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {l : Bool} {Γ Γe : Ctx}
    {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ} {ebe : Endblock D (vertragVon D B.f) l Γe Λe}
    {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe} (h : Zerlegung B Agl Cg eb σ ρ ebe σe ρe)
    {σ' : World D} {r : Fin (vertragVon D B.f).gruende} :
    execEnd B.O B.passes B.R eb σ ρ = .why σ' r → execEnd B.O B.passes B.R ebe σe ρe = .why σ' r := by
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
    exact endSchrumpf_why hz

/-! ## The residue behind the callee's prefix ends as the call does -/

/-- **Normal exit**: when the call `rufAt (j + 1) g σc ρc` ends normally with `v`, the residue `ebeC` behind the
    callee's decomposed prefix (from the handler's body world) returns `v` under `rufAt j`, at a world `≈` to the
    call's. -/
theorem rufRest_zurueck {P : Programm D} {O : Orakel D} {passes j : Nat} {g : D.Fn} {σc σ2 : World D}
    {ρc : Env D (D.params g)} {v : ErgVal D (D.erg g)} (hR : rufAt P O passes (j + 1) g σc ρc = .ok σ2 v)
    {Y : Lay D} {A : D.Fn → Nat} {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g
        (σc.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρc) Agl Cg (P.rumpf g)
      (σc.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρc ebeC σeC ρeC) :
    ∃ σ', execEnd O passes (rufAt P O passes j) ebeC σeC ρeC = .zurueck σ' v ∧ WeltGleich σ' σ2 := by
  obtain ⟨σ', hbody, hσ⟩ := rufAt_ok_rumpf hR
  exact ⟨σ', hkC.zurueck hbody, hσ⟩

/-- **Reason exit**: when the call answers the reason `r`, the residue behind the callee's decomposed prefix answers
    `r` under `rufAt j`, at the call's world. -/
theorem rufRest_why {P : Programm D} {O : Orakel D} {passes j : Nat} {g : D.Fn} {σc σ2 : World D}
    {ρc : Env D (D.params g)} {r : Fin (D.gruende g)} (hR : rufAt P O passes (j + 1) g σc ρc = .why σ2 r)
    {Y : Lay D} {A : D.Fn → Nat} {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g
        (σc.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρc) Agl Cg (P.rumpf g)
      (σc.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρc ebeC σeC ρeC) :
    execEnd O passes (rufAt P O passes j) ebeC σeC ρeC = .why σ2 r :=
  hkC.why (rufAt_why_rumpf hR)

/-! ## The pop, machine G -/

/-- **Back into the caller, normal exit, every pop kind**: machine `Me` stands at a boundary `ebeC` of the callee's
    body up to read events, the caller frame `caller` waiting on the stack; the residue is in the call fragment one
    level down and returns `v` under `rufAt j`. Then thread `thr` alone pops into the frame `ziel v` that `PopArt`
    names (the caller unchanged, or with `v` bound), at a world `≈` to the sequential one, with the locks of `σeC`. -/
theorem randGL_rueck_ok {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) {thr : Faden}
    {caller : RufRahmenG D} {stapel : List (RufRahmenG D)} {Agl : D.Lock → Prop} {g : D.Fn} {j : Nat}
    {ΓeC : Ctx} {ΛeC : List (Res D)} {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC}
    (hEC : EndR Agl (TiefAlle P Agl j) ebeC) {σeC : World D} {ρeC : Env D ΓeC} {rhoG : Env D (D.params g)}
    {s0G : World D} {Me : RufMaschineG D} (hMe : RandGL thr (caller :: stapel) g rhoG s0G Agl ebeC Me σeC ρeC)
    {σ' : World D} {v : ErgVal D (D.erg g)}
    (hz : execEnd O passes (rufAt P O passes j) ebeC σeC ρeC = .zurueck σ' v)
    {ziel : ErgVal D (D.erg g) → RufRahmenG D} (hart : PopArt g caller ziel) :
    ∃ (M' : RufMaschineG D) (σ'' : World D) (lg : List (RufEreignisF D)),
      RufLaufG P O passes thr Me M' ∧ WeltGleich σ' σ'' ∧ GepopptG M' thr (ziel v) stapel g rhoG s0G lg v σ'' ∧
      offen σ''.spur = offen σeC.spur := by
  obtain ⟨σme, hwe, ⟨log, hZe⟩, hΛe, hAe⟩ := hMe
  have hl := execEnd_lg (passes := passes) (rufAt_rufRumpf_lg_alle (P := P) (passes := passes) hO j) hO.rs ebeC
    (Or.inl (axFrei_endR hEC)) hwe ρeC
  rw [hz] at hl
  obtain ⟨σ'', hz'', hw''⟩ := hl.zurueck_inv
  obtain ⟨M', ext, hl', hGp, hoff⟩ := endRetR P O passes thr g caller stapel rhoG s0G Agl
    (rufRumpf P O passes j) (TiefAlle P Agl j) ziel (fun _ => caller) (rufOk_tiefAlle P O passes thr Agl j)
    ebeC hEC log σme ρeC (.zurueck σ'' v) hart (by rw [hz'']; rfl) Me hZe hΛe hAe
  have hGp' : GepopptG M' thr (ziel v) stapel g rhoG s0G (ext ++ log) v σ'' := hGp
  have hoff' : offen σ''.spur = offen σme.spur := hoff
  exact ⟨M', σ'', ext ++ log, hl', hw'', hGp', hoff'.trans hwe.offen_eq.symm⟩

/-- **Back into the caller, reason exit**: as `randGL_rueck_ok`, when the residue answers the reason `r`; thread
    `thr` pops through the error channel into the else block of the caller frame that `PopGrund` names. -/
theorem randGL_rueck_why {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) {thr : Faden}
    {caller : RufRahmenG D} {stapel : List (RufRahmenG D)} {Agl : D.Lock → Prop} {g : D.Fn} {j : Nat}
    {ΓeC : Ctx} {ΛeC : List (Res D)} {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC}
    (hEC : EndR Agl (TiefAlle P Agl j) ebeC) {σeC : World D} {ρeC : Env D ΓeC} {rhoG : Env D (D.params g)}
    {s0G : World D} {Me : RufMaschineG D} (hMe : RandGL thr (caller :: stapel) g rhoG s0G Agl ebeC Me σeC ρeC)
    {σ' : World D} {r : Fin (D.gruende g)}
    (hz : execEnd O passes (rufAt P O passes j) ebeC σeC ρeC = .why σ' r)
    {zielG : Fin (D.gruende g) → RufRahmenG D} (hart : PopGrund g caller zielG) :
    ∃ (M' : RufMaschineG D) (σ'' : World D) (lg : List (RufEreignisF D)),
      RufLaufG P O passes thr Me M' ∧ WeltGleich σ' σ'' ∧
      GepopptGrundG M' thr (zielG r) stapel g rhoG s0G lg r σ'' ∧ offen σ''.spur = offen σeC.spur := by
  obtain ⟨σme, hwe, ⟨log, hZe⟩, hΛe, hAe⟩ := hMe
  have hl := execEnd_lg (passes := passes) (rufAt_rufRumpf_lg_alle (P := P) (passes := passes) hO j) hO.rs ebeC
    (Or.inl (axFrei_endR hEC)) hwe ρeC
  rw [hz] at hl
  obtain ⟨σ'', hz'', hw''⟩ := hl.why_inv
  obtain ⟨M', ext, hl', hGp, hoff⟩ := endRetR P O passes thr g caller stapel rhoG s0G Agl
    (rufRumpf P O passes j) (TiefAlle P Agl j) (fun _ => caller) zielG (rufOk_tiefAlle P O passes thr Agl j)
    ebeC hEC log σme ρeC (.why σ'' r) hart (by rw [hz'']; rfl) Me hZe hΛe hAe
  have hGp' : GepopptGrundG M' thr (zielG r) stapel g rhoG s0G (ext ++ log) r σ'' := hGp
  have hoff' : offen σ''.spur = offen σme.spur := hoff
  exact ⟨M', σ'', ext ++ log, hl', hw'', hGp', hoff'.trans hwe.offen_eq.symm⟩

/-! ## From the call's sequential outcome -/

/-- **The return of a call, normal exit, every pop kind**: the call `rufAt (j + 1) g σc ρc` ends normally with `v`,
    the callee is admitted at `j + 1` (recursion included), its decomposed prefix (handler `rufAt j`) reaches `ebeC`,
    and machine `Me` stands there, the caller frame waiting. Then thread `thr` alone pops into `ziel v` at a world
    `≈` to the call's world. -/
theorem randGL_rueck_ruf_ok {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) {thr : Faden}
    {caller : RufRahmenG D} {stapel : List (RufRahmenG D)} {Agl : D.Lock → Prop} {g : D.Fn} {j : Nat}
    {σc σ2 : World D} {ρc : Env D (D.params g)} {v : ErgVal D (D.erg g)}
    (hR : rufAt P O passes (j + 1) g σc ρc = .ok σ2 v) (hg : TiefAlle P Agl (j + 1) g)
    {Y : Lay D} {A : D.Fn → Nat} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g
        (σc.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρc) Agl (TiefAlle P Agl j) (P.rumpf g)
      (σc.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρc ebeC σeC ρeC)
    {rhoG : Env D (D.params g)} {s0G : World D} {Me : RufMaschineG D}
    (hMe : RandGL thr (caller :: stapel) g rhoG s0G Agl ebeC Me σeC ρeC)
    {ziel : ErgVal D (D.erg g) → RufRahmenG D} (hart : PopArt g caller ziel) :
    ∃ (M' : RufMaschineG D) (σ'' : World D) (lg : List (RufEreignisF D)),
      RufLaufG P O passes thr Me M' ∧ WeltGleich σ2 σ'' ∧ GepopptG M' thr (ziel v) stapel g rhoG s0G lg v σ'' ∧
      offen σ''.spur = offen σeC.spur := by
  have hEC : EndR Agl (TiefAlle P Agl j) ebeC :=
    hkC.endR (show EndR Agl (TiefAlle P Agl j) (P.rumpf g) from hg)
  obtain ⟨σ', hz, hσ⟩ := rufRest_zurueck hR hkC
  obtain ⟨M', σ'', lg, hl, hw, hGp, hoff⟩ := randGL_rueck_ok hO hEC hMe hz hart
  exact ⟨M', σ'', lg, hl, hσ.symm.trans hw, hGp, hoff⟩

/-- **The return of a call, reason exit**: as `randGL_rueck_ruf_ok`, when the call answers the reason `r`; thread
    `thr` pops through the error channel into `zielG r`. -/
theorem randGL_rueck_ruf_why {P : Programm D} {O : Orakel D} {passes : Nat} (hO : LeseblindP P O) {thr : Faden}
    {caller : RufRahmenG D} {stapel : List (RufRahmenG D)} {Agl : D.Lock → Prop} {g : D.Fn} {j : Nat}
    {σc σ2 : World D} {ρc : Env D (D.params g)} {r : Fin (D.gruende g)}
    (hR : rufAt P O passes (j + 1) g σc ρc = .why σ2 r) (hg : TiefAlle P Agl (j + 1) g)
    {Y : Lay D} {A : D.Fn → Nat} {ΓeC : Ctx} {ΛeC : List (Res D)}
    {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D} {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g
        (σc.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρc) Agl (TiefAlle P Agl j) (P.rumpf g)
      (σc.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρc ebeC σeC ρeC)
    {rhoG : Env D (D.params g)} {s0G : World D} {Me : RufMaschineG D}
    (hMe : RandGL thr (caller :: stapel) g rhoG s0G Agl ebeC Me σeC ρeC)
    {zielG : Fin (D.gruende g) → RufRahmenG D} (hart : PopGrund g caller zielG) :
    ∃ (M' : RufMaschineG D) (σ'' : World D) (lg : List (RufEreignisF D)),
      RufLaufG P O passes thr Me M' ∧ WeltGleich σ2 σ'' ∧
      GepopptGrundG M' thr (zielG r) stapel g rhoG s0G lg r σ'' ∧ offen σ''.spur = offen σeC.spur := by
  have hEC : EndR Agl (TiefAlle P Agl j) ebeC :=
    hkC.endR (show EndR Agl (TiefAlle P Agl j) (P.rumpf g) from hg)
  exact randGL_rueck_why hO hEC hMe (rufRest_why hR hkC) hart

#print axioms randGL_rueck_ruf_ok
#print axioms randGL_rueck_ruf_why

end Gabbro.Stage0.Senke.BildLauf
