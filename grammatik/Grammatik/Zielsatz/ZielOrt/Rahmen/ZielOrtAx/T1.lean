/-
  File:      Grammatik/ZielOrtAx.lean
  Subject:   `ziel_ort_voll_ax` -- `ziel_ort_voll` over the STRENGTHENED user
             obligation `KoerperGutA` (the body triple against every oracle
             that respects the declared axiom frames AND meets the axioms'
             declared ensures `Q`), with the hardware premise `AxVertragO Q O`
             and the locality `AxEnsLokal Q`.

  The acting-thread lemma, the rely, the start and the step are the ones of
  `ZielOrtVoll.lean`, over the replay of `ZielOrtAxBeweis.lean`; the only
  changes are the invariants (`FadenA`/`ZielInvA`), the obligation, and the
  two hypotheses threaded to where the obligation is applied or an axiom
  answer is recorded.
-/
module
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.AkteurAFaelle.EndFloat.Teil11
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.AkteurAFaelle.EndFloat.Teil10
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxBeweis
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.AkteurAFaelle.Tail.Teil20
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.AkteurAFaelle.Foreign.CallElse
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.AkteurAFaelle.Foreign.OptBlock
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.AkteurAFaelle.Foreign.OptEnd
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.AkteurAFaelle.Tail.Scoped
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Akteur
variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

/-- **The acting thread keeps its replay and its log** -- every rule of G:
    the head-local steps by the residue step lemmas at the sequential
    world, the leaves by leaf locality or by recording an axiom answer, the
    pushes by `pushV_ok` (direct) and `pushV_gen` (indirect: the pointer
    read at the key names the callee, whose contract carriers the fragment
    puts in the footprint), the normal pops by `popV_ens` and `popA_kopf`,
    the reason pops by `popA_kopf`; the rules outside the fragment (register
    reads, `awaits`) find a head residue that is not in it. -/
theorem akteurA (hO : GutO O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hK : ∀ f, KoerperGutA P passes Q f)
    (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true) (e0 : Ereignis D)
    {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (hF : FadenA P O passes Q (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log) :
    FadenA P O passes Q (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | g1 hs =>
    cases hs with
    | endeBindAxiomOpt l Γ Λ e a args he hp hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurA_endeBindAxiomOpt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      exact akteurA_blatt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (s := s) (rest := rest) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein)
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      exact akteurA_dannBlatt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (s := s) (rest := rest) (k := k) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein)
    | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
      exact akteurA_endeEntf (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (s := s) (rest := rest) (ρ := ρ) (hent := hent) (hhead := hhead)
    | endeForm l Γ Λ e ρ hl hent hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenA_lokal hF hhead ρ (.dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)) (M.faeden u).spur
        (fun σ hg hok => ?_), hL⟩
      exact ⟨σ, Nat.le_refl _, hg, okV_alsBlock e .leer (fun L => Iff.rfl) hok.1 hok.2 trivial,
        fun R O' => ZErg.folgt_of_eq (semV_endeForm O' passes R e σ ρ)⟩
    | dannLeer l Γ Λ k ρ hhead =>
      exact akteurA_dannLeer (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (k := k) (ρ := ρ) (hhead := hhead)
    | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurA_dannIteWahr (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurA_dannIteFalsch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurA_dannOnOptionSome (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
      exact akteurA_dannOnOptionNone (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw neu hneu hΛ =>
      exact akteurA_dannOnTagSome (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (τ := τ) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
      exact akteurA_dannOnTagNone (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
      exact akteurA_dannOnGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (r := r) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
      exact akteurA_endeBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (e := e) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
      exact akteurA_dannBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      exact akteurA_dannNarrowOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannNarrowRequired l Γ Λ Λ' lo hi lo' hi' e rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      exact akteurA_dannNarrowRequired (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurA_endeBindAxiom (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact akteurA_ruf (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      subst hfg hs0 hs1 hv
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hok := kopfA_okV hF.1 hhead
      have hens := popA_ens hO hQ hK hF.1 hhead e hok.2
        (fun O' R σ => semV_rueck O' passes R e hperm σ ρ)
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      refine ⟨⟨popA_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
        caller.rest.2.2.2.1 caller.rest.2.2.2.2 id (fun R O' σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_rueck hL hens⟩
  | g2 hs =>
    cases hs with
    | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      exact akteurA_dannNarrowElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurA_dannPruefWahr (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurA_dannPruefFalsch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
      exact akteurA_dannBreaking (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (i := i) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      exact akteurA_dannLocks (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (L := L) (hr := hr) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hself := hself) (hrang := hrang) (hfrei := hfrei)
    | freiGib l Γ Λ L k ρ hhead =>
      exact akteurA_freiGib (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (L := L) (k := k) (ρ := ρ) (hhead := hhead)
    | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
      exact akteurA_schrumpfVergiss (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (k := k) (v := v) (ρ := ρ) (hhead := hhead)
    -- loops
    | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
      exact akteurA_dannTrav (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (inv := inv) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurA_travNext (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (i := i) (is := is) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | travFort l Γ Λ t inv body is k i ρ hhead =>
      exact akteurA_travFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (is := is) (k := k) (i := i) (ρ := ρ) (hhead := hhead)
    | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurA_travDone (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
      exact akteurA_dannRetry (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (bis := bis) (body := body) (ueber := ueber) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
      exact akteurA_wiederUeber (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead)
    | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurA_wiederWeiter (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurA_wiederSchritt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
      exact akteurA_wiederFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead)
    | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
      exact akteurA_dannForever (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (a := a) (inv := inv) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurA_ewigWeiter (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (a := a) (n := n) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | ewigFort l Γ Λ a n inv body k ρ hhead =>
      exact akteurA_ewigFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (a := a) (n := n) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead)
    -- the exits
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact akteurA_rufDann (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
  | g3 hs =>
    cases hs with
    | dannAxiomCallElseOk l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurA_dannAxiomCallElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannAxiomCallElseGrund l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact akteurA_dannAxiomCallElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
        neu₁ hneu₁ hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      subst hs₁
      refine ⟨fadenA_lokal hF hhead ρ k _ (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hTR⟩ := hok
      obtain ⟨hinv, _, _, hk⟩ := hTR
      have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
        rw [eval_gleichAuf inv (fun _ h => hinv h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
        exact hw
      exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, hk,
        fun R O' => ZErg.folgt_of_eq
          (semV_leaveTrav O' passes R t inv body is k rest i σ ρ hleave hw')⟩
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      refine ⟨fadenA_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
        (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hTR⟩ := hok
      exact ⟨σ, Nat.le_refl _, hg, hTR,
        fun R O' => ZErg.folgt_of_eq (semV_nextTrav O' passes R t inv body is k rest i σ ρ hnext)⟩
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      refine ⟨fadenA_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hWR⟩ := hok
      obtain ⟨_, _, _, _, _, hk⟩ := hWR
      exact ⟨σ, Nat.le_refl _, hg, hk,
        fun R O' => ZErg.folgt_of_eq
          (semV_leaveWieder O' passes R n bis body ueber k rest σ ρ hleave)⟩
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      refine ⟨fadenA_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
        (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hWR⟩ := hok
      exact ⟨σ, Nat.le_refl _, hg, hWR,
        fun R O' => ZErg.folgt_of_eq
          (semV_nextWieder O' passes R n bis body ueber k rest σ ρ hnext)⟩
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      refine ⟨fadenA_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hER⟩ := hok
      obtain ⟨_, _, _, hk⟩ := hER
      exact ⟨σ, Nat.le_refl _, hg, hk,
        fun R O' => ZErg.folgt_of_eq (semV_leaveEwig O' passes R a n inv body k rest σ ρ hleave)⟩
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact akteurA_dannBindCall (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
        hneu =>
      exact akteurA_dannBindCallElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    -- indirect calls: the pointer read at the key names the callee
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      exact akteurA_dannCallInd (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      exact akteurA_rufCallInd (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu
        hneu =>
      exact akteurA_dannBindCallInd (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
        hrho neu hneu =>
      exact akteurA_dannBindCallIndElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
        hrho neu hneu =>
      exact akteurA_dannCallIndElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    -- normal pops
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
        s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      subst hfg hs0 hs1 hv
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hok := kopfA_okV hF.1 hhead
      have hens := popA_ens hO hQ hK hF.1 hhead e hok.2
        (fun O' R σ => semV_rueck O' passes R e hperm σ ρ)
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      refine ⟨⟨popA_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
        (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
        (fun hokc => by
          rcases hcaller with hc | ⟨n, err, hc⟩
          · have h' := rest_okV hc hokc
            exact ⟨h'.1, h'.2.1, h'.2.2⟩
          · have h' := rest_okV hc hokc
            exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
        (fun R O' σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_rueck hL hens⟩
  | g4 hs =>
    cases hs with
    | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      refine ⟨fadenA_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
        (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hER⟩ := hok
      exact ⟨σ, Nat.le_refl _, hg, hER,
        fun R O' => ZErg.folgt_of_eq (semV_nextEwig O' passes R a n inv body k rest σ ρ hnext)⟩
    | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenA_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, _, _, hk⟩ := hok
      exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
        fun R O' => ZErg.folgt_of_eq (semV_peelDann O' passes R rest b k σ ρ hleave true)⟩
    | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenA_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, _, _, hk⟩ := hok
      exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
        fun R O' => ZErg.folgt_of_eq (semV_peelDann O' passes R rest b k σ ρ hnext false)⟩
    | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenA_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hk⟩ := hok
      exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
        fun R O' => ZErg.folgt_of_eq (semV_peelSchrumpf O' passes R rest k σ ρ hleave true)⟩
    | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenA_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hk⟩ := hok
      exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
        fun R O' => ZErg.folgt_of_eq (semV_peelSchrumpf O' passes R rest k σ ρ hnext false)⟩
    | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenA_lokal hF hhead ρ _ (Ereignis.gibt L :: (M.faeden u).spur)
        (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hk⟩ := hok
      exact ⟨σ.gibt L, Nat.le_succ _, hg,
        ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
        fun R O' => ZErg.folgt_of_eq (semV_peelFrei O' passes R L rest k σ ρ hleave true)⟩
    | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenA_lokal hF hhead ρ _ (Ereignis.gibt L :: (M.faeden u).spur)
        (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hk⟩ := hok
      exact ⟨σ.gibt L, Nat.le_succ _, hg,
        ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
        fun R O' => ZErg.folgt_of_eq (semV_peelFrei O' passes R L rest k σ ρ hnext false)⟩
    | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
      exact akteurA_peelAbbruchLeave (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (Γ := Γ) (Λ := Λ) (Λ1 := Λ1) (Λk := Λk) (rest := rest) (k := k) (ρ := ρ) (hleave := hleave) (hhead := hhead)
    | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
      exact akteurA_peelAbbruchNext (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (Γ := Γ) (Λ := Λ) (Λ1 := Λ1) (Λk := Λk) (rest := rest) (k := k) (ρ := ρ) (hnext := hnext) (hhead := hhead)
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
        hneu hnw =>
      subst hfg hs0 hs1 hv
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hok := okV_ende_cons (kopfA_okV hF.1 hhead)
      have hens := popA_ens hO hQ hK hF.1 hhead e hok.2.1
        (fun O' R σ => semV_rueckCons O' passes R e hperm rest σ ρ)
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      refine ⟨⟨popA_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
        caller.rest.2.2.2.1 caller.rest.2.2.2.2 id (fun R O' σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_rueck hL hens⟩
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
        neu hneu hnw =>
      exact akteurA_dannRet (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (e := e) (hperm := hperm) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hnw := hnw)
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      exact akteurA_dannRetBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (lk := lk) (Γk := Γk) (Λk := Λk) (Λk'' := Λk'') (e := e) (hperm := hperm) (restk := restk) (kk := kk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu)
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
        s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      exact akteurA_rueckConsBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (lk := lk) (Γk := Γk) (Λk := Λk) (e := e) (hperm := hperm) (restk := restk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu)
    -- reason pops
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
        hrho s0 hs0 rg hrg hn =>
      subst hfg hs0 hrg
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      refine ⟨⟨popA_kopf e0 hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
        (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
        (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
        (fun hokc => okV_alsBlock err (.schrumpf k) restb.held_iff (rest_okV hcaller hokc).1
          (rest_okV hcaller hokc).2.1 (rest_okV hcaller hokc).2.2.2.2)
        (fun R O' σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_grund hL⟩
  | g5 hs =>
    cases hs with
    | dannBindAxiomOpt _ _ l Γ Λ Λ' e a args he hp hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurA_dannBindAxiomOpt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomOptElseOk _ _ l Γ Λ Λ' e a args he hr hp hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurA_dannBindAxiomOptElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomOptElseGrund _ _ l Γ Λ Λ' e a args he hr hp hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact akteurA_dannBindAxiomOptElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannExchange _ _ l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      exact akteurA_dannExchange (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (g := g) (neuE := neuE) (hw := hw) (hLg := hLg) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (hs₂ := hs₂) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleit _ _ l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurA_dannGleit (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (l₂ := l₂) (h₂ := h₂) (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitLit _ _ l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
      exact akteurA_dannGleitLit (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (q := q) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv)
    | dannGleitVon _ _ l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurA_dannGleitVon (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitNarrowOk _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurA_dannGleitNarrowOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitNarrowElse _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      exact akteurA_dannGleitNarrowElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hn := hn) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    -- the axiom bind
    | dannBindAxiom _ _ l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurA_dannBindAxiom (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomElseGrund _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact akteurA_dannBindAxiomElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomElseOk _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurA_dannBindAxiomElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | rueckConsGrund _ _ r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
        hfg rho hrho s0 hs0 rg hrg hn =>
      subst hfg hs0 hrg
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      refine ⟨⟨popA_kopf e0 hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
        (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
        (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
        (fun hokc => okV_alsBlock err (.schrumpf k) restb.held_iff (rest_okV hcaller hokc).1
          (rest_okV hcaller hokc).2.1 (rest_okV hcaller hokc).2.2.2.2)
        (fun R O' σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_grund hL⟩
    | dannRetGrund _ _ r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
        hfg rho hrho s0 hs0 rg hrg hn =>
      subst hfg hs0 hrg
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      refine ⟨⟨popA_kopf e0 hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
        (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
        (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
        (fun hokc => okV_alsBlock err (.schrumpf k) restb.held_iff (rest_okV hcaller hokc).1
          (rest_okV hcaller hokc).2.1 (rest_okV hcaller hokc).2.2.2.2)
        (fun R O' σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_grund hL⟩
    -- every other rule: the head residue is outside the fragment
    | dannRegLies =>
      exact absurd (kopfA_okV hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okV, Block.vOk, Bool.false_eq_true, false_and, not_false_eq_true])
    | dannRegLiesElseWahr =>
      exact absurd (kopfA_okV hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okV, Block.vOk, Bool.false_eq_true, false_and, not_false_eq_true])
    | dannRegLiesElseFalsch =>
      exact absurd (kopfA_okV hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okV, Block.vOk, Bool.false_eq_true, false_and, not_false_eq_true])
    | dannAwaits =>
      exact absurd (kopfA_okV hF.1 ‹(M.faeden u).kopf.rest = _›)
        (by simp only [GRest.okV, Block.vOk, Bool.false_eq_true, false_and, not_false_eq_true])
  | g6 hs =>
    cases hs with
    | endeBindAxiomOptElseOk l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurA_endeBindAxiomOptElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiomOptElseGrund l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact akteurA_endeBindAxiomOptElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact akteurA_endeBindAxiomElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurA_endeBindAxiomElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    -- pushes
    | endeGleit l Γ Λ l₁ h₁ l₂ h₂ op a b lo hi rest ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurA_endeGleit (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (l₁ := l₁) (h₁ := h₁) (l₂ := l₂) (h₂ := h₂) (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeGleitLit l Γ Λ q lo hi rest ρ hhead v hv =>
      exact akteurA_endeGleitLit (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (q := q) (lo := lo) (hi := hi) (rest := rest) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv)
    | endeGleitVon l Γ Λ l₁ h₁ e lo hi rest ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurA_endeGleitVon (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeGleitNarrowOk l Γ Λ l₁ h₁ e lo hi sonst rest ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurA_endeGleitNarrowOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeGleitNarrowElse l Γ Λ l₁ h₁ e lo hi sonst rest ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      exact akteurA_endeGleitNarrowElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hn := hn) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    -- the axiom bind
  | g7 hs =>
    exact akteurA_gruppe7 hO hQ hK hlok hFrag e0 hs hF hL
end Akteur

