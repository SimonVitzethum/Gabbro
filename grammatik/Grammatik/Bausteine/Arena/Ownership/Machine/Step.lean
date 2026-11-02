module
public import Grammatik.Bausteine.Arena.Ownership.Machine.Stack.Return
public import Grammatik.Bausteine.Arena.Ownership.Machine.OwnInv_stepFaelle.Teil18
@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Machine
open Source Body
variable {D : Deklaration}
section Helpers
variable {A : FreiForm D} {I : Interfaces A} {fr : Frame} {s : State} {σ : World D} {f : D.Fn}
end Helpers

/-- **Every step of machine G keeps ownership on the machine**, given the rely for other threads. -/
theorem ownInv_step {P : Programm D} {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat}
    (hO : GutO O) (hc : Checked P A I) {M M' : RufMaschineG D} {u : Faden} (hinv : OwnInv A I M)
    (hrely : ∀ t, t ≠ u → ∀ g, pendWord A (M.faeden t).kopf.rest.2.2.2.2 = some g →
      M'.speicher.globs g = M.speicher.globs g)
    (hstep : RufSchrittG P O passes M u M') : OwnInv A I M' := by
  obtain ⟨s, hag, hfo, hd, hth⟩ := hinv
  have hW : MetaSame A (M.speicher.welt []) (M.weltVon u) := MetaSame.of_cells A rfl rfl (fun _ => rfl)
  have ha : s.agrees A (M.weltVon u) := State.agrees_meta hag hW
  have ho : A.FreiOk (M.weltVon u) := freiOk_meta hfo hW
  have hH : Head A I ⟨u, (M.faeden u).stapel.length⟩ s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest := (hth u).1.meta hW
  have fin : ∀ {M' : RufMaschineG D} {σ' : World D}
      {x' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ}
      {rho' : Env D (D.params (M.faeden u).kopf.f)} {s0' : World D} {spur' : List (Ereignis D)}
      {log' : List (RufEreignisF D)},
      Next A I ⟨u, (M.faeden u).stapel.length⟩ s (M.weltVon u) σ' (M.faeden u).kopf.f x' →
      M'.speicher = σ'.speicher →
      M'.faeden = rufUpdateG M.faeden u ⟨(M.faeden u).stapel, ⟨(M.faeden u).kopf.f, rho', s0', x'⟩, spur', log'⟩ →
      (∀ t, t ≠ u → ∀ g, pendWord A (M.faeden t).kopf.rest.2.2.2.2 = some g →
        M'.speicher.globs g = M.speicher.globs g) → OwnInv A I M' := by
    intro M' σ' x' rho' s0' spur' log' hn hmem hM' hr
    exact ownInv_local hag hfo hd hth hW (by rw [hmem]; exact welt_meta A σ') hr hM' hn
  cases hstep with
  | g1 hstep =>
    cases hstep with
    | blatt l Γ Λ Λ' st rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      exact ownInv_step_blatt (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (st := st) (rest := rest) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein) (hrely := hrely)
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact ownInv_step_ruf (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu) (hrely := hrely)
    | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      rw [hhead] at hH
      obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
      cases hor with
      | ende _ he =>
        cases he with
        | ret _ _ hcheck =>
          have hdu : depthOf M u = rst.length + 1 := by
            show (M.faeden u).stapel.length = _
            rw [hpop]; rfl
          have hsusp := caller_susp (hth u).2 hpop
          subst hfg
          subst hv
          have hres := ret_result hf hcheck s1 s1
          rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hres
          exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl (resume_plainX hd hdu hsusp hnw _ hres)
    | endeEntf l Γ Λ Λ' st rest ρ hent hhead =>
      exact ownInv_step_endeEntf (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (st := st) (rest := rest) (ρ := ρ) (hent := hent) (hhead := hhead) (hrely := hrely)
    | endeForm l Γ Λ e ρ hl hent hhead =>
      rw [hhead] at hH
      obtain ⟨k, c, g, hk, hf, hr⟩ := head_run hH rfl
      exact fin (run_endeForm hk hf ha ho hr) rfl rfl hrely
    | dannBlatt l Γ Λ Λ' Λ'' st rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      exact ownInv_step_dannBlatt (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (st := st) (rest := rest) (k := k) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein) (hrely := hrely)
    | dannLeer l Γ Λ k ρ hhead =>
      exact ownInv_step_dannLeer (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (k := k) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | dannIteWahr l Γ Λ Λ' Λ'' cnd t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_dannIteWahr (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cnd := cnd) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannIteFalsch l Γ Λ Λ' Λ'' cnd t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_dannIteFalsch (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cnd := cnd) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact ownInv_step_dannOnOptionSome (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
      exact ownInv_step_dannOnOptionNone (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw neu hneu hΛ =>
      exact ownInv_step_dannOnTagSome (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (lo := lo) (hi := hi) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
      exact ownInv_step_dannOnTagNone (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
      exact ownInv_step_dannOnGrund (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (r := r) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
      exact ownInv_step_endeBind (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (e := e) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | endeBindAxiom l Γ Λ τ a args he hw hg hd' hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact ownInv_step_endeBindAxiom (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd' := hd') (hgd := hgd) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
      exact ownInv_step_dannBind (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      exact ownInv_step_dannNarrowOk (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
  | g2 hstep =>
    cases hstep with
    | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      exact ownInv_step_dannNarrowElse (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannPruefWahr l Γ Λ Λ' Λ'' cnd sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_dannPruefWahr (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cnd := cnd) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannPruefFalsch l Γ Λ Λ' Λ'' cnd sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_dannPruefFalsch (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cnd := cnd) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
      exact ownInv_step_dannBreaking (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (i := i) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | dannLocks l Γ Λ Λ'' L hrk body rest k ρ hhead hself hrang hfrei =>
      exact ownInv_step_dannLocks (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (L := L) (hrk := hrk) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hself := hself) (hrang := hrang) (hfrei := hfrei) (hrely := hrely)
    | freiGib l Γ Λ L k ρ hhead =>
      exact ownInv_step_freiGib (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (L := L) (k := k) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
      exact ownInv_step_schrumpfVergiss (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (k := k) (v := v) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
      exact ownInv_step_dannTrav (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (inv := inv) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_travNext (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (i := i) (is := is) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | travFort l Γ Λ t inv body is k i ρ hhead =>
      exact ownInv_step_travFort (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (is := is) (k := k) (i := i) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_travDone (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
      exact ownInv_step_dannRetry (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (bis := bis) (body := body) (ueber := ueber) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
      exact ownInv_step_wiederUeber (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_wiederWeiter (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_wiederSchritt (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
      exact ownInv_step_wiederFort (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
      exact ownInv_step_dannForever (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (a := a) (inv := inv) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_ewigWeiter (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (a := a) (n := n) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | ewigFort l Γ Λ a n inv body k ρ hhead =>
      exact ownInv_step_ewigFort (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (a := a) (n := n) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (hrely := hrely)
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact ownInv_step_rufDann (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu) (hrely := hrely)
  | g3 hstep =>
    cases hstep with
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      exact ownInv_step_dannCallInd (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu) (hrely := hrely)
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      exact ownInv_step_rufCallInd (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu) (hrely := hrely)
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact ownInv_step_dannBindCall (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu) (hrely := hrely)
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      exact ownInv_step_dannBindCallInd (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu) (hrely := hrely)
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact ownInv_step_dannBindCallElse (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu) (hrely := hrely)
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
        neu hneu =>
      exact ownInv_step_dannBindCallIndElse (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu) (hrely := hrely)
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
        neu hneu =>
      exact ownInv_step_dannCallIndElse (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu) (hrely := hrely)
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1
        v hv he neu hneu =>
      rw [hhead] at hH
      obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
      cases hor with
      | ende _ hee =>
        cases hee with
        | ret _ _ hcheck =>
          have hdu : depthOf M u = rst.length + 1 := by
            show (M.faeden u).stapel.length = _
            rw [hpop]; rfl
          have hsusp := caller_susp (hth u).2 hpop
          subst hfg
          subst hv
          have hres := ret_result hf hcheck s1 s1
          rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hres
          rcases hcaller with hc' | ⟨n, err, hc'⟩
          · rw [hc'] at hsusp
            exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl
              (resume_bind hd hdu hsusp (Or.inl rfl) _ he hres)
          · rw [hc'] at hsusp
            exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl
              (resume_bind hd hdu hsusp (Or.inr ⟨n, err, rfl⟩) _ he hres)
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_leave hr
      simp only [execStmt] at hstep
      cases hstep
      exact fin (run_leaveTrav hf ha ho hx hX (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_next hr
      simp only [execStmt] at hstep
      cases hstep
      exact fin (run_nextTrav hf ha ho hx hX (MetaSame.refl A _)) rfl rfl hrely
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_leave hr
      simp only [execStmt] at hstep
      cases hstep
      exact fin (run_leaveWieder hf ha ho hx hX (MetaSame.refl A _)) rfl rfl hrely
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_next hr
      simp only [execStmt] at hstep
      cases hstep
      exact fin (run_nextWieder hf ha ho hx hX (MetaSame.refl A _)) rfl rfl hrely
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_leave hr
      simp only [execStmt] at hstep
      cases hstep
      exact fin (run_leaveEwig hf ha ho hx hX (MetaSame.refl A _)) rfl rfl hrely
  | g4 hstep =>
    cases hstep with
    | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_next hr
      simp only [execStmt] at hstep
      cases hstep
      exact fin (run_nextEwig hf ha ho hx hX (MetaSame.refl A _)) rfl rfl hrely
    | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_leave hr
      exact fin (run_peel hk hf ha ho (.leave hleave hx) (ox_top hX)) rfl rfl hrely
    | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_next hr
      exact fin (run_peel hk hf ha ho (.next hnext hx) (ox_top hX)) rfl rfl hrely
    | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_leave hr
      obtain ⟨hk', hX'⟩ := ox_top hX
      cases ρ with
      | cons v ρ0 =>
        exact fin (run_peelSchrumpf hk' hf ha ho (.leave hleave (exitsTo_shrink hf hx hk')) hX') rfl rfl hrely
    | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_next hr
      obtain ⟨hk', hX'⟩ := ox_top hX
      cases ρ with
      | cons v ρ0 =>
        exact fin (run_peelSchrumpf hk' hf ha ho (.next hnext (exitsTo_shrink hf hx hk')) hX') rfl rfl hrely
    | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_leave hr
      exact fin (run_peel hk hf ha ho (.leave hleave hx) (ox_top hX)) rfl rfl hrely
    | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
      rw [hhead] at hH
      obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
      obtain ⟨hx, hX⟩ := exit_next hr
      exact fin (run_peel hk hf ha ho (.next hnext hx) (ox_top hX)) rfl rfl hrely
    | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
      exact ownInv_step_peelAbbruchLeave (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (Γ := Γ) (Λ := Λ) (Λ1 := Λ1) (Λk := Λk) (rest := rest) (k := k) (ρ := ρ) (hleave := hleave) (hhead := hhead) (hrely := hrely)
    | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
      exact ownInv_step_peelAbbruchNext (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (Γ := Γ) (Λ := Λ) (Λ1 := Λ1) (Λk := Λk) (rest := rest) (k := k) (ρ := ρ) (hnext := hnext) (hhead := hhead) (hrely := hrely)
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu hnw =>
      exact ownInv_step_dannRet (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (e := e) (hperm := hperm) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hnw := hnw) (hrely := hrely)
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      rw [hhead] at hH
      obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
      obtain ⟨c2, hs, _⟩ := hor.stmtEnde
      have hcheck := os_top hs
      have hdu : depthOf M u = rst.length + 1 := by
        show (M.faeden u).stapel.length = _
        rw [hpop]; rfl
      have hsusp := caller_susp (hth u).2 hpop
      subst hfg
      subst hv
      have hres := ret_result hf hcheck s1 s1
      rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hres
      exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl (resume_plainX hd hdu hsusp hnw _ hres)
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ s1 hs1
        g hfg rho hrho s0 hs0 v hv he neu hneu =>
      exact ownInv_step_dannRetBind (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (lk := lk) (Γk := Γk) (Λk := Λk) (Λk'' := Λk'') (e := e) (hperm := hperm) (restk := restk) (kk := kk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu) (hrely := hrely)
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ s1 hs1
        g hfg rho hrho s0 hs0 v hv he neu hneu =>
      exact ownInv_step_rueckConsBind (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (lk := lk) (Γk := Γk) (Λk := Λk) (e := e) (hperm := hperm) (restk := restk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu) (hrely := hrely)
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0
        rg hrg hn =>
      rw [hhead] at hH
      obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
      cases hor with
      | ende _ hee =>
        cases hee with
        | retWhy _ _ hfin =>
          have hdu : depthOf M u = rst.length + 1 := by
            show (M.faeden u).stapel.length = _
            rw [hpop]; rfl
          have hsusp := caller_susp (hth u).2 hpop
          rw [hcaller] at hsusp
          have hcl := finish_void hf.1 hf.2.2.2 hfin
          rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hcl
          exact ownInv_pop hag hfo hd hth hpop rfl rfl rfl (resume_why hd hdu hsusp hcl _)
  | g5 hstep =>
    cases hstep with
    | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho
        s0 hs0 rg hrg hn =>
      rw [hhead] at hH
      obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
      obtain ⟨c2, hs, _⟩ := hor.stmtEnde
      have hfin := os_top hs
      have hdu : depthOf M u = rst.length + 1 := by
        show (M.faeden u).stapel.length = _
        rw [hpop]; rfl
      have hsusp := caller_susp (hth u).2 hpop
      rw [hcaller] at hsusp
      have hcl := finish_void hf.1 hf.2.2.2 hfin
      rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hcl
      exact ownInv_pop hag hfo hd hth hpop rfl rfl rfl (resume_why hd hdu hsusp hcl _)
    | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho
        s0 hs0 rg hrg hn =>
      rw [hhead] at hH
      obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
      obtain ⟨c2, hs, _⟩ := hor.stmt trivial
      have hfin := os_top hs
      have hdu : depthOf M u = rst.length + 1 := by
        show (M.faeden u).stapel.length = _
        rw [hpop]; rfl
      have hsusp := caller_susp (hth u).2 hpop
      rw [hcaller] at hsusp
      have hcl := finish_void hf.1 hf.2.2.2 hfin
      rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hcl
      exact ownInv_pop hag hfo hd hth hpop rfl rfl rfl (resume_why hd hdu hsusp hcl _)
    | dannRegLies l Γ Λ Λ' r hk' rest k ρ hhead v hv hz hΛ =>
      exact ownInv_step_dannRegLies (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk' := hk') (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (hz := hz) (hΛ := hΛ) (hrely := hrely)
    | dannRegLiesElseWahr l Γ Λ Λ' r hk' zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_dannRegLiesElseWahr (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk' := hk') (zusage := zusage) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannRegLiesElseFalsch l Γ Λ Λ' r hk' zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      exact ownInv_step_dannRegLiesElseFalsch (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk' := hk') (zusage := zusage) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannAwaits l Γ Λ Λ' gl payload hp hL hat rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
      exact ownInv_step_dannAwaits (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (gl := gl) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hvis := hvis) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannExchange l Γ Λ Λ' gl neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      exact ownInv_step_dannExchange (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (gl := gl) (neuE := neuE) (hw := hw) (hL := hL) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (hs₂ := hs₂) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact ownInv_step_dannGleit (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (l₂ := l₂) (h₂ := h₂) (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
      exact ownInv_step_dannGleitLit (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (q := q) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (hrely := hrely)
    | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact ownInv_step_dannGleitVon (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact ownInv_step_dannGleitNarrowOk (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      exact ownInv_step_dannGleitNarrowElse (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hn := hn) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd' hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact ownInv_step_dannBindAxiom (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd' := hd') (hgd := hgd) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr0 hw hg hd' hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact ownInv_step_dannBindAxiomElseOk (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hr0 := hr0) (hw := hw) (hg := hg) (hd' := hd') (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr0 hw hg hd' hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact ownInv_step_dannBindAxiomElseGrund (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hr0 := hr0) (hw := hw) (hg := hg) (hd' := hd') (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
  | g6 hstep =>
    cases hstep with
    | endeBindAxiomElseOk l Γ Λ τ a args he hr0 hw hg hd' hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact ownInv_step_endeBindAxiomElseOk (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hr0 := hr0) (hw := hw) (hg := hg) (hd' := hd') (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
    | endeBindAxiomElseGrund l Γ Λ τ a args he hr0 hw hg hd' hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact ownInv_step_endeBindAxiomElseGrund (D := D) (P := P) (A := A) (I := I) (O := O) (passes := passes) (hO := hO) (hc := hc) (M := M) (u := u) (s := s) (hag := hag) (hfo := hfo) (hd := hd) (hth := hth) (hW := hW) (ha := ha) (ho := ho) (hH := hH) (fin := fin) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hr0 := hr0) (hw := hw) (hg := hg) (hd' := hd') (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ) (hrely := hrely)
  | g7 hstep =>
    cases hstep with
    | dannVerbrauch l Γ Λ Λ'' t member edge inv bound mass body rest k ρ hhead =>
      exact ownInv_step_dannVerbrauch (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead v m σ₃ =>
      exact ownInv_step_verbrauchWeiter (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (m := m) (σ₃ := σ₃)
    | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₂ =>
      exact ownInv_step_verbrauchLeer (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₂ := σ₂)
    | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead σ₁ =>
      exact ownInv_step_verbrauchFort (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (i := i) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁)
    | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hleave hhead σ₁ =>
      exact ownInv_step_dannLeaveVerbrauch (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hleave := hleave) (hhead := hhead) (σ₁ := σ₁)
    | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hnext hhead σm =>
      exact ownInv_step_dannNextVerbrauch (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hnext := hnext) (hhead := hhead) (σm := σm)
#print axioms ownInv_step

end Gabbro.Grammatik.ArenaOwnership.Machine
