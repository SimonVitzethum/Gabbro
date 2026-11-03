/- Part 2 of 3 of `ZielOrtBeweis` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtBeweis.lean` imports all parts). -/
module
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1a
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil9
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.ScopedZeuge
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Push
variable {P : Programm D} {O : Orakel D} {passes : Nat}
end Push
section Akteur
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The acting thread keeps its replay and its log** -- every rule of G:
    the head-local steps of the fragment by the residue step lemmas at the
    sequential world, the pushes by `push_ok`, the pops by `pop_ens` and
    `pop_kopf`; every rule outside the fragment finds a head residue that is
    not in it. -/
theorem akteur (hK : ∀ f, KoerperGut P O passes f) (hFrag : ∀ f, (P.rumpf f).kOk = true)
    (e0 : Ereignis D) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log) :
    FadenOk P O passes (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      exact akteur_blatt (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (s := s) (rest := rest) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein)
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      exact akteur_dannBlatt (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (s := s) (rest := rest) (k := k) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein)
    | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
      exact akteur_endeEntf (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (s := s) (rest := rest) (ρ := ρ) (hent := hent) (hhead := hhead)
    | endeForm l Γ Λ e ρ hl hent hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenOk_lokal hF hhead ρ (.dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)) (M.faeden u).spur
        (fun σ hg hok => ?_), hL⟩
      obtain ⟨hk, hs⟩ := hok
      exact ⟨σ, Nat.le_refl _, hg, ⟨by rw [Endblock.kOk_alsBlock]; exact hk,
        by rw [blockOrteP_alsBlock]; exact hs, trivial⟩,
        fun R => ZErg.gleich_of_eq (semZ_alsBlock O passes R e .leer σ ρ)⟩
    | dannLeer l Γ Λ k ρ hhead =>
      exact akteur_dannLeer (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (k := k) (ρ := ρ) (hhead := hhead)
    | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteur_dannIteWahr (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteur_dannIteFalsch (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteur_dannOnOptionSome (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
      exact akteur_dannOnOptionNone (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw neu hneu hΛ =>
      exact akteur_dannOnTagSome (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (τ := τ) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
      exact akteur_dannOnTagNone (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
      exact akteur_dannOnGrund (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (r := r) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
      exact akteur_endeBind (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (e := e) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
      exact akteur_dannBind (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      exact akteur_dannNarrowOk (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact akteur_ruf (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      subst hfg hs0 hs1 hv
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hok := kopf_okZ hF.1 hhead
      have hens := pop_ens hK hF.1 hhead e hok.2 (fun R σ => semZ_rueck O passes R e hperm σ ρ)
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      refine ⟨⟨pop_kopf e0 hWc _ _ hens caller.rest.2.2.2.1 caller.rest.2.2.2.2 id
        (fun R σa X h1 _ => h1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩, logOk_rueck hL hens⟩
    | _ =>
      exact absurd (kopf_okZ hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okZ, Endblock.kOk, Bool.false_eq_true, false_and, not_false_eq_true, Block.kOk, Stmt.kOk, Bool.false_and, and_false, and_self])
  | g2 hs =>
    cases hs with
    | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      exact akteur_dannNarrowElse (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteur_dannPruefWahr (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteur_dannPruefFalsch (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
      exact akteur_dannBreaking (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (i := i) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      exact akteur_dannLocks (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (L := L) (hr := hr) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hself := hself) (hrang := hrang) (hfrei := hfrei)
    | freiGib l Γ Λ L k ρ hhead =>
      exact akteur_freiGib (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (L := L) (k := k) (ρ := ρ) (hhead := hhead)
    | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
      exact akteur_schrumpfVergiss (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (k := k) (v := v) (ρ := ρ) (hhead := hhead)
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact akteur_rufDann (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | _ =>
      exact absurd (kopf_okZ hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okZ, Endblock.kOk, Bool.false_eq_true, false_and, not_false_eq_true, Block.kOk, Stmt.kOk, Bool.false_and, and_false, and_self])
  | g3 hs =>
    cases hs with
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact akteur_dannBindCall (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    -- pops
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
        s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      subst hfg hs0 hs1 hv
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hok := kopf_okZ hF.1 hhead
      have hens := pop_ens hK hF.1 hhead e hok.2 (fun R σ => semZ_rueck O passes R e hperm σ ρ)
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      have hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ := by
        rcases hcaller with h | ⟨n, err, h⟩
        · exact h
        · obtain ⟨_, _, _, _, _, _, hokc, _⟩ := hWc
          rw [h] at hokc
          exact hokc.elim
      refine ⟨⟨pop_kopf e0 hWc _ _ hens (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
        (fun hokc => by rw [hc] at hokc; exact ⟨hokc.1, hokc.2.1, hokc.2.2⟩)
        (fun R σa X _ h2 => h2 l Γ Λ Λ' τ restb k ρc hc he) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_rueck hL hens⟩
    | _ =>
      exact absurd (kopf_okZ hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okZ, Endblock.kOk, Bool.false_eq_true, false_and, not_false_eq_true, Block.kOk, Stmt.kOk, Bool.false_and, and_false, and_self])
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
        hneu hnw =>
      subst hfg hs0 hs1 hv
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hok := okZ_ende_cons (kopf_okZ hF.1 hhead)
      have hens := pop_ens hK hF.1 hhead e hok.2.1
        (fun R σ => semZ_rueckCons O passes R e hperm rest σ ρ)
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      refine ⟨⟨pop_kopf e0 hWc _ _ hens caller.rest.2.2.2.1 caller.rest.2.2.2.2 id
        (fun R σa X h1 _ => h1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩, logOk_rueck hL hens⟩
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
        neu hneu hnw =>
      exact akteur_dannRet (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (e := e) (hperm := hperm) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hnw := hnw)
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      exact akteur_dannRetBind (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (lk := lk) (Γk := Γk) (Λk := Λk) (Λk'' := Λk'') (e := e) (hperm := hperm) (restk := restk) (kk := kk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu)
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
        s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      exact akteur_rueckConsBind (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (lk := lk) (Γk := Γk) (Λk := Λk) (e := e) (hperm := hperm) (restk := restk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu)
    -- every other rule: the head residue is outside the fragment
    | _ =>
      exact absurd (kopf_okZ hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okZ, Endblock.kOk, Bool.false_eq_true, false_and, not_false_eq_true, Block.kOk, Stmt.kOk, Bool.false_and, and_false, and_self])
  | g5 hs =>
    cases hs with
    | dannExchange _ _ l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      exact akteur_dannExchange (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (g := g) (neuE := neuE) (hw := hw) (hLg := hLg) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (hs₂ := hs₂) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleit _ _ l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteur_dannGleit (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (l₂ := l₂) (h₂ := h₂) (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitLit _ _ l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
      exact akteur_dannGleitLit (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (q := q) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv)
    | dannGleitVon _ _ l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteur_dannGleitVon (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitNarrowOk _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteur_dannGleitNarrowOk (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitNarrowElse _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      exact akteur_dannGleitNarrowElse (D := D) (P := P) (O := O) (passes := passes) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hn := hn) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    -- pushes
    | _ =>
      exact absurd (kopf_okZ hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okZ, Endblock.kOk, Bool.false_eq_true, false_and, not_false_eq_true, Block.kOk, Stmt.kOk, Bool.false_and, and_false, and_self])
  | g6 hs =>
    cases hs with
    | _ =>
      exact absurd (kopf_okZ hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okZ, Endblock.kOk, Bool.false_eq_true, false_and, not_false_eq_true, Block.kOk, Stmt.kOk, Bool.false_and, and_false, and_self])
  | g7 hs => exact akteur_gruppe7 hK e0 hs hF hL

end Akteur

end Gabbro.Grammatik
