/-
  File:      Grammatik/Speichermodell/AtomarAkteur.lean
  Subject:   THE REPLAY WITH THE ATOMIC RELY, part 3: the acting thread keeps its replay, every
             rule of G (`akteurSA`, the twin of `akteurS` in ZielOrtSperre.lean). Every rule
             that READS goes through `fadenSA_lese` (or records its read in `pushSA_gen`,
             `fadenSA_ax`, `popSA_ens`): the read is answered from the machine's presented
             memory at the shared atomics it touches. Opus lane O25b, 2026-09-26. Standalone.

  The step is a step of G from ANY machine `M` -- in particular from a machine whose memory at
  the shared atomics is what the weak memory presented (machine GA, Atomar.lean). Nothing here
  depends on how `M` was reached: the replay invariant `FadenSA` is the whole premise.
-/
module
public import Grammatik.Speichermodell.Atomar.AtomarReplay
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.B.Teil19
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.Foreign.CallElse
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.Foreign.OptEnd
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.Foreign.OptBlock
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Akteur
variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}

set_option maxHeartbeats 8000000 in
/-- **The acting thread keeps its replay and its log** -- every rule of G, over the semantics
    with the atomic rely. -/
theorem akteurSA (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) (hM : ∀ f, MassPflicht P passes Q S Tg m zyk f)
    (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f)
    {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
    (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel)
    (hSG : SperrInvG S M) :
    FadenSA P O passes Q S lok Tg m zyk (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | g1 hs =>
    cases hs with
    | endeBindAxiomOpt l Γ Λ e a args he hp hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurSA_endeBindAxiomOpt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      exact akteurSA_blatt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (s := s) (rest := rest) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein)
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      exact akteurSA_dannBlatt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (s := s) (rest := rest) (k := k) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein)
    | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
      exact akteurSA_endeEntf (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (s := s) (rest := rest) (ρ := ρ) (hent := hent) (hhead := hhead)
    | endeForm l Γ Λ e ρ hl hent hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenSA_lokal hF hhead ρ (.dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)) (M.faeden u).spur
        (fun σ hg hok => ?_), hL⟩
      exact ⟨rfl, hg, okS_alsBlock e .leer (fun L => Iff.rfl) hok.1 hok.2 trivial,
        fun R O' U A => ZErgG.folgt_of_eq (semHA_endeForm S O' U A passes R e σ ρ)⟩
    | dannLeer l Γ Λ k ρ hhead =>
      exact akteurSA_dannLeer (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (k := k) (ρ := ρ) (hhead := hhead)
    | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurSA_dannIteWahr (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurSA_dannIteFalsch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurSA_dannOnOptionSome (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
      exact akteurSA_dannOnOptionNone (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw neu hneu hΛ =>
      exact akteurSA_dannOnTagSome (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (τ := τ) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
      exact akteurSA_dannOnTagNone (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
      exact akteurSA_dannOnGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (r := r) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
      exact akteurSA_endeBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (e := e) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
      exact akteurSA_dannBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      exact akteurSA_dannNarrowOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurSA_endeBindAxiom (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact akteurSA_ruf (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      subst hfg hs0 hs1 hv
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hok := kopfSA_okS hF.1 hhead
      have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2)
        (ens_stabilX (hFS _) hTV hperm) (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ)
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      have hRS' := hRS
      rw [hpop] at hRS'
      refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
        (fun hE => popSA_begr_ok hE hF.1 hhead e
          (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ))
        (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
        caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
        (fun R O' U A σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_rueck hL hens⟩
  | g2 hs =>
    cases hs with
    | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      exact akteurSA_dannNarrowElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurSA_dannPruefWahr (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurSA_dannPruefFalsch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
      exact akteurSA_dannBreaking (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (i := i) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      exact akteurSA_dannLocks (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (L := L) (hr := hr) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hself := hself) (hrang := hrang) (hfrei := hfrei)
    | freiGib l Γ Λ L k ρ hhead =>
      exact akteurSA_freiGib (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (L := L) (k := k) (ρ := ρ) (hhead := hhead)
    | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
      exact akteurSA_schrumpfVergiss (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (k := k) (v := v) (ρ := ρ) (hhead := hhead)
    -- loops
    | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
      exact akteurSA_dannTrav (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (inv := inv) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurSA_travNext (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (i := i) (is := is) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | travFort l Γ Λ t inv body is k i ρ hhead =>
      exact akteurSA_travFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (is := is) (k := k) (i := i) (ρ := ρ) (hhead := hhead)
    | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurSA_travDone (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
      exact akteurSA_dannRetry (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (bis := bis) (body := body) (ueber := ueber) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
      exact akteurSA_wiederUeber (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead)
    | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurSA_wiederWeiter (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurSA_wiederSchritt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
      exact akteurSA_wiederFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead)
    | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
      exact akteurSA_dannForever (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (a := a) (inv := inv) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurSA_ewigWeiter (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (a := a) (n := n) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | ewigFort l Γ Λ a n inv body k ρ hhead =>
      exact akteurSA_ewigFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (a := a) (n := n) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead)
    -- the exits
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact akteurSA_rufDann (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
  | g3 hs =>
    cases hs with
    | dannAxiomCallElseOk l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurSA_dannAxiomCallElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannAxiomCallElseGrund l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact akteurSA_dannAxiomCallElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
        neu₁ hneu₁ hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      subst hs₁
      refine ⟨fadenSA_lese hF hhead ρ k _ Λ inv.orte
        (fun hok => by
          obtain ⟨_, _, hTR⟩ := hok
          obtain ⟨hinv, _, _, _⟩ := hTR
          intro c hc
          rcases expr_stabilX (hFS _) inv hinv c hc with h | h
          · exact Or.inl (stabilS_iff (fun L => Block.held_iff rest L) h)
          · exact Or.inr h)
        (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hTR⟩ := hok
      obtain ⟨_, _, _, hk⟩ := hTR
      have hw' : wahr? (eval σ inv σ ρ) = true := by
        rw [eval_gleichAuf inv (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
      exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L)
        (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg), hk,
        fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
          rw [semHA_leaveTrav S O' U A passes R t inv body is k rest i σ0 ρ hleave
            (by rw [hσ0]; exact hw'), hσ0])⟩
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      refine ⟨fadenSA_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
        (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hTR⟩ := hok
      exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hTR,
        fun R O' U A => ZErgG.folgt_of_eq
          (semHA_nextTrav S O' U A passes R t inv body is k rest i σ ρ hnext)⟩
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      refine ⟨fadenSA_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hWR⟩ := hok
      obtain ⟨_, _, _, _, _, hk⟩ := hWR
      exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hk,
        fun R O' U A => ZErgG.folgt_of_eq
          (semHA_leaveWieder S O' U A passes R n bis body ueber k rest σ ρ hleave)⟩
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      refine ⟨fadenSA_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
        (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hWR⟩ := hok
      exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hWR,
        fun R O' U A => ZErgG.folgt_of_eq
          (semHA_nextWieder S O' U A passes R n bis body ueber k rest σ ρ hnext)⟩
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      refine ⟨fadenSA_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hER⟩ := hok
      obtain ⟨_, _, _, hk⟩ := hER
      exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hk,
        fun R O' U A => ZErgG.folgt_of_eq
          (semHA_leaveEwig S O' U A passes R a n inv body k rest σ ρ hleave)⟩
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact akteurSA_dannBindCall (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
        hneu =>
      exact akteurSA_dannBindCallElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    -- indirect calls: the pointer read at the key names the callee
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      exact akteurSA_dannCallInd (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
        neu hneu =>
      exact akteurSA_dannCallIndElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      exact akteurSA_rufCallInd (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu
        hneu =>
      exact akteurSA_dannBindCallInd (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu
        hneu =>
      exact akteurSA_dannBindCallIndElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    -- normal pops
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
        s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      subst hfg hs0 hs1 hv
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hok := kopfSA_okS hF.1 hhead
      have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2)
        (ens_stabilX (hFS _) hTV hperm) (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ)
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      have hRS' := hRS
      rw [hpop] at hRS'
      refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
        (fun hE => popSA_begr_ok hE hF.1 hhead e
          (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ))
        (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
        (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
        (fun L h => by rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> exact h)
        (fun hokc => by
          rcases hcaller with hc | ⟨n, err, hc⟩
          · have h' := rest_okS hc hokc
            exact ⟨h'.1, h'.2.1, h'.2.2⟩
          · have h' := rest_okS hc hokc
            exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
        (fun R O' U A σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_rueck hL hens⟩
  | g4 hs =>
    cases hs with
    | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      simp only [RufBlattG, execStmt] at hstep
      cases hstep
      refine ⟨fadenSA_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
        (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hER⟩ := hok
      exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hER,
        fun R O' U A => ZErgG.folgt_of_eq
          (semHA_nextEwig S O' U A passes R a n inv body k rest σ ρ hnext)⟩
    | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenSA_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, _, _, hk⟩ := hok
      exact ⟨rfl,
        gleichAuf_stabil_iff (fun L => (Block.held_iff b L).trans (Block.held_iff rest L)) hg,
        ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
        fun R O' U A => ZErgG.folgt_of_eq (semHA_peelDann S O' U A passes R rest b k σ ρ hleave true)⟩
    | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenSA_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, _, _, hk⟩ := hok
      exact ⟨rfl,
        gleichAuf_stabil_iff (fun L => (Block.held_iff b L).trans (Block.held_iff rest L)) hg,
        ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
        fun R O' U A => ZErgG.folgt_of_eq (semHA_peelDann S O' U A passes R rest b k σ ρ hnext false)⟩
    | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenSA_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hk⟩ := hok
      exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg,
        ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
        fun R O' U A => ZErgG.folgt_of_eq
          (semHA_peelSchrumpf S O' U A passes R rest k σ ρ hleave true)⟩
    | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenSA_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      obtain ⟨_, _, hk⟩ := hok
      exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg,
        ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
        fun R O' U A => ZErgG.folgt_of_eq
          (semHA_peelSchrumpf S O' U A passes R rest k σ ρ hnext false)⟩
    | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      exact ⟨fadenSA_peelFrei hO hRL hQ hS hsp hK hF L rest k ρ hleave true hhead _, hL⟩
    | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      exact ⟨fadenSA_peelFrei hO hRL hQ hS hsp hK hF L rest k ρ hnext false hhead _, hL⟩
    | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
      exact akteurSA_peelAbbruchLeave (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (Γ := Γ) (Λ := Λ) (Λ1 := Λ1) (Λk := Λk) (rest := rest) (k := k) (ρ := ρ) (hleave := hleave) (hhead := hhead)
    | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
      exact akteurSA_peelAbbruchNext (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (Γ := Γ) (Λ := Λ) (Λ1 := Λ1) (Λk := Λk) (rest := rest) (k := k) (ρ := ρ) (hnext := hnext) (hhead := hhead)
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
        hneu hnw =>
      subst hfg hs0 hs1 hv
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hok := okS_ende_cons (kopfSA_okS hF.1 hhead)
      have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2.1)
        (ens_stabilX (hFS _) hTV hperm)
        (fun O' R U A σ => semHA_rueckCons S O' U A passes R e hperm rest σ ρ)
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      have hRS' := hRS
      rw [hpop] at hRS'
      refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
        (fun hE => popSA_begr_ok hE hF.1 hhead e
          (fun O' R U A σ => semHA_rueckCons S O' U A passes R e hperm rest σ ρ))
        (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
        caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
        (fun R O' U A σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_rueck hL hens⟩
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
        neu hneu hnw =>
      exact akteurSA_dannRet (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (e := e) (hperm := hperm) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hnw := hnw)
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      exact akteurSA_dannRetBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (lk := lk) (Γk := Γk) (Λk := Λk) (Λk'' := Λk'') (e := e) (hperm := hperm) (restk := restk) (kk := kk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu)
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
        s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      exact akteurSA_rueckConsBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (lk := lk) (Γk := Γk) (Λk := Λk) (e := e) (hperm := hperm) (restk := restk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu)
    -- reason pops
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
        hrho s0 hs0 rg hrg hn =>
      subst hfg hs0 hrg
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      have hRS' := hRS
      rw [hpop] at hRS'
      refine ⟨⟨popSA_kopf hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
        (fun hE => popSA_begr_grund hE hF.1 hhead rg
          (fun O' R U A σ => semHA_rueckGrund S O' U A passes R rg hperm σ ρ))
        (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
        (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
        (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
        (fun L h => by rw [hcaller]; exact h)
        (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
          (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
        (fun R O' U A σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_grund hL⟩
  | g5 hs =>
    cases hs with
    | dannBindAxiomOpt _ _ l Γ Λ Λ' e a args he hp hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurSA_dannBindAxiomOpt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomOptElseOk _ _ l Γ Λ Λ' e a args he hr hp hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurSA_dannBindAxiomOptElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomOptElseGrund _ _ l Γ Λ Λ' e a args he hr hp hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact akteurSA_dannBindAxiomOptElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannExchange _ _ l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      exact akteurSA_dannExchange (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (g := g) (neuE := neuE) (hw := hw) (hLg := hLg) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (hs₂ := hs₂) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleit _ _ l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurSA_dannGleit (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (l₂ := l₂) (h₂ := h₂) (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitLit _ _ l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
      exact akteurSA_dannGleitLit (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (q := q) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv)
    | dannGleitVon _ _ l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurSA_dannGleitVon (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitNarrowOk _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact akteurSA_dannGleitNarrowOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitNarrowElse _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      exact akteurSA_dannGleitNarrowElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hn := hn) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    -- the axiom bind
    | dannBindAxiom _ _ l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurSA_dannBindAxiom (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomElseGrund _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact akteurSA_dannBindAxiomElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomElseOk _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurSA_dannBindAxiomElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | rueckConsGrund _ _ r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
        hfg rho hrho s0 hs0 rg hrg hn =>
      subst hfg hs0 hrg
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      have hRS' := hRS
      rw [hpop] at hRS'
      refine ⟨⟨popSA_kopf hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
        (fun hE => popSA_begr_grund hE hF.1 hhead rg
          (fun O' R U A σ => semHA_rueckConsGrund S O' U A passes R rg hperm restk σ ρ))
        (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
        (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
        (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
        (fun L h => by rw [hcaller]; exact h)
        (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
          (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
        (fun R O' U A σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_grund hL⟩
    | dannRetGrund _ _ r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
        hfg rho hrho s0 hs0 rg hrg hn =>
      subst hfg hs0 hrg
      subst hrho
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      have hSt := hF.2
      rw [hpop] at hSt
      obtain ⟨hWc, hSt'⟩ := hSt
      have hRS' := hRS
      rw [hpop] at hRS'
      refine ⟨⟨popSA_kopf hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
        (fun hE => popSA_begr_grund hE hF.1 hhead rg
          (fun O' R U A σ => semHA_dannRetGrund S O' U A passes R rg hperm restk kk σ ρ))
        (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
        (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
        (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
        (fun L h => by rw [hcaller]; exact h)
        (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
          (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
        (fun R O' U A σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
        logOk_grund hL⟩
    -- register reads and `awaits`
    | dannRegLies _ _ l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
      exact akteurSA_dannRegLies (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk := hk) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (hz := hz) (hΛ := hΛ)
    | dannRegLiesElseWahr _ _ l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      exact akteurSA_dannRegLiesElseWahr (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannRegLiesElseFalsch _ _ l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu
        hΛ =>
      exact akteurSA_dannRegLiesElseFalsch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannAwaits _ _ l Γ Λ Λ' g payload hp hLg hat rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
      exact akteurSA_dannAwaits (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (g := g) (payload := payload) (hp := hp) (hLg := hLg) (hat := hat) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hvis := hvis) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | g6 hs =>
    cases hs with
    | endeBindAxiomOptElseOk l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurSA_endeBindAxiomOptElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiomOptElseGrund l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact akteurSA_endeBindAxiomOptElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact akteurSA_endeBindAxiomElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact akteurSA_endeBindAxiomElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    -- pushes
  | g7 hs =>
    cases hs with
    | dannVerbrauch l Γ Λ Λ'' t member edge inv bound mass body rest k ρ hhead =>
      exact akteurSA_dannVerbrauch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ v hv σ₃ hs₃ m hm neu hneu hΛ =>
      exact akteurSA_verbrauchWeiter (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (σ₂ := σ₂) (hs₂ := hs₂) (v := v) (hv := hv) (σ₃ := σ₃) (hs₃ := hs₃) (m := m) (hm := hm) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ hleer hkein neu hneu hΛ =>
      exact akteurSA_verbrauchLeer (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (σ₂ := σ₂) (hs₂ := hs₂) (hleer := hleer) (hkein := hkein) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead σ₁ hs₁ m' hm' hfall neu hneu hΛ =>
      exact akteurSA_verbrauchFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (i := i) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (m' := m') (hm' := hm') (hfall := hfall) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
      exact akteurSA_dannLeaveVerbrauch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hleave := hleave) (hhead := hhead) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein_nimmt := hkein_nimmt) (σm := σm) (hsm := hsm) (m' := m') (hm' := hm') (hfall := hfall) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu₁ := neu₁) (hneu₁ := hneu₁) (hΛ := hΛ)
    | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall neum hneum hΛ =>
      exact akteurSA_dannNextVerbrauch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hnext := hnext) (hhead := hhead) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein_nimmt := hkein_nimmt) (σm := σm) (hsm := hsm) (m' := m') (hm' := hm') (hfall := hfall) (neum := neum) (hneum := hneum) (hΛ := hΛ)
end Akteur

end Gabbro.Grammatik
