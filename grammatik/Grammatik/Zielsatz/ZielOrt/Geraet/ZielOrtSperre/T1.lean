/-
  File:      Grammatik/ZielOrtSperre.lean
  Subject:   THE GOAL THEOREM WITH LOCK INVARIANTS -- `ziel_ort_sperre`.
             Contracts over shared state across a lock boundary, and readers
             inside `locks L { … }` blocks (verdict item 2,
             `messung/URTEIL-OPUS-2026-09-13.md`, probes B and C).

  The rule-by-rule step of the replay (`akteurS`, as `akteurR` in
  `ZielOrtRahmen.lean`) over the semantics with lock invariants, the rely,
  the start, the invariant on every reachable machine -- the replay, the
  machine lock invariant `SperrInvG` and the log -- and the theorem. The
  acquire step records the environment's move (`fadenS_locks`), fed by the
  machine lock invariant; the release steps (`fadenS_frei`,
  `fadenS_peelFrei`) use the second clause of the obligation, and give the
  machine lock invariant back (`kopfS_frei_inv`).
-/
module
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreMaschine
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre.AkteurSFaelle.Teil18
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Akteur
variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}

set_option maxHeartbeats 4000000 in
/-- **The acting thread keeps its replay and its log** -- every rule of G
    (as `akteurR`), over the semantics with lock invariants: the acquire by
    recording the environment's move (the machine lock invariant `SperrInvG`
    gives the invariant of the free lock), the releases by the second
    clause of the obligation. -/
theorem akteurS (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f)
    {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (hF : FadenS P O passes Q S lok (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
    (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel)
    (hSG : SperrInvG S M) :
    FadenS P O passes Q S lok (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    exact akteurS_blatt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (s := s) (rest := rest) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein)
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    exact akteurS_dannBlatt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (s := s) (rest := rest) (k := k) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein)
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    exact akteurS_endeEntf (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (s := s) (rest := rest) (ρ := ρ) (hent := hent) (hhead := hhead)
  | endeForm l Γ Λ e ρ hl hent hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, okS_alsBlock e .leer (fun L => Iff.rfl) hok.1 hok.2 trivial,
      fun R O' U => ZErgG.folgt_of_eq (semH_endeForm S O' U passes R e σ ρ)⟩
  | dannLeer l Γ Λ k ρ hhead =>
    exact akteurS_dannLeer (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (k := k) (ρ := ρ) (hhead := hhead)
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    exact akteurS_dannIteWahr (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    exact akteurS_dannIteFalsch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    exact akteurS_dannOnOptionSome (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
    exact akteurS_dannOnOptionNone (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
    exact akteurS_dannOnTagSome (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (lo := lo) (hi := hi) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
    exact akteurS_dannOnTagNone (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
    exact akteurS_dannOnGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (r := r) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
    exact akteurS_endeBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (e := e) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
    exact akteurS_dannBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    exact akteurS_dannNarrowOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    exact akteurS_dannNarrowElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (h := h) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    exact akteurS_dannPruefWahr (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    exact akteurS_dannPruefFalsch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
    exact akteurS_dannBreaking (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (i := i) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
    exact akteurS_dannLocks (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (L := L) (hr := hr) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hself := hself) (hrang := hrang) (hfrei := hfrei)
  | freiGib l Γ Λ L k ρ hhead =>
    exact akteurS_freiGib (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (L := L) (k := k) (ρ := ρ) (hhead := hhead)
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
    exact akteurS_schrumpfVergiss (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (k := k) (v := v) (ρ := ρ) (hhead := hhead)
  -- loops
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    exact akteurS_dannTrav (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (inv := inv) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    exact akteurS_travNext (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (i := i) (is := is) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | travFort l Γ Λ t inv body is k i ρ hhead =>
    exact akteurS_travFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (is := is) (k := k) (i := i) (ρ := ρ) (hhead := hhead)
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    exact akteurS_travDone (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
    exact akteurS_dannRetry (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (bis := bis) (body := body) (ueber := ueber) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    exact akteurS_wiederUeber (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead)
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    exact akteurS_wiederWeiter (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    exact akteurS_wiederSchritt (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
    exact akteurS_wiederFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead)
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
    exact akteurS_dannForever (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (a := a) (inv := inv) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    exact akteurS_ewigWeiter (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (a := a) (n := n) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
    exact akteurS_ewigFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (a := a) (n := n) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead)
  -- the exits
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    subst hs₁
    refine ⟨fadenS_lokal hF hhead ρ k _ (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hTR⟩ := hok
    obtain ⟨hinv, _, _, hk⟩ := hTR
    have hg' := gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hinv h') h)
        (hg'.lese Λ Λ inv.orte inv.orte) ρ]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg', hk,
      fun R O' U => ZErgG.folgt_of_eq
        (semH_leaveTrav S O' U passes R t inv body is k rest i σ ρ hleave hw')⟩
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenS_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hTR⟩ := hok
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hTR,
      fun R O' U => ZErgG.folgt_of_eq (semH_nextTrav S O' U passes R t inv body is k rest i σ ρ hnext)⟩
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenS_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hWR⟩ := hok
    obtain ⟨_, _, _, _, _, hk⟩ := hWR
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hk,
      fun R O' U => ZErgG.folgt_of_eq
        (semH_leaveWieder S O' U passes R n bis body ueber k rest σ ρ hleave)⟩
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenS_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hWR⟩ := hok
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hWR,
      fun R O' U => ZErgG.folgt_of_eq
        (semH_nextWieder S O' U passes R n bis body ueber k rest σ ρ hnext)⟩
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenS_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hER⟩ := hok
    obtain ⟨_, _, _, hk⟩ := hER
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hk,
      fun R O' U => ZErgG.folgt_of_eq (semH_leaveEwig S O' U passes R a n inv body k rest σ ρ hleave)⟩
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenS_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hER⟩ := hok
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hER,
      fun R O' U => ZErgG.folgt_of_eq (semH_nextEwig S O' U passes R a n inv body k rest σ ρ hnext)⟩
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _,
      gleichAuf_stabil_iff (fun L => (Block.held_iff b L).trans (Block.held_iff rest L)) hg, ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_peelDann S O' U passes R rest b k σ ρ hleave true)⟩
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _,
      gleichAuf_stabil_iff (fun L => (Block.held_iff b L).trans (Block.held_iff rest L)) hg, ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_peelDann S O' U passes R rest b k σ ρ hnext false)⟩
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_peelSchrumpf S O' U passes R rest k σ ρ hleave true)⟩
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, ⟨rfl, fun _ h => by simp only [blockOrteP, stmtOrteP, List.append_nil, List.not_mem_nil] at h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_peelSchrumpf S O' U passes R rest k σ ρ hnext false)⟩
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenS_peelFrei hO hRL hQ hS hsp hK hF L rest k ρ hleave true hhead _, hL⟩
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenS_peelFrei hO hRL hQ hS hsp hK hF L rest k ρ hnext false hhead _, hL⟩
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
    exact akteurS_peelAbbruchLeave (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (Γ := Γ) (Λ := Λ) (Λ1 := Λ1) (Λk := Λk) (rest := rest) (k := k) (ρ := ρ) (hleave := hleave) (hhead := hhead)
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
    exact akteurS_peelAbbruchNext (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (Γ := Γ) (Λ := Λ) (Λ1 := Λ1) (Λk := Λk) (rest := rest) (k := k) (ρ := ρ) (hnext := hnext) (hhead := hhead)
  | dannExchange l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    exact akteurS_dannExchange (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (g := g) (neuE := neuE) (hw := hw) (hLg := hLg) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (hs₂ := hs₂) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    exact akteurS_dannGleit (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (l₂ := l₂) (h₂ := h₂) (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
    exact akteurS_dannGleitLit (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (q := q) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv)
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    exact akteurS_dannGleitVon (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    exact akteurS_dannGleitNarrowOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    exact akteurS_dannGleitNarrowElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hn := hn) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  -- the axiom bind
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    exact akteurS_dannBindAxiom (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
    exact akteurS_dannBindAxiomElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    exact akteurS_dannBindAxiomElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    exact akteurS_endeBindAxiom (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
    exact akteurS_endeBindAxiomElseGrund (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    exact akteurS_endeBindAxiomElseOk (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  -- pushes
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    exact akteurS_ruf (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    exact akteurS_rufDann (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    exact akteurS_dannBindCall (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
      hneu =>
    exact akteurS_dannBindCallElse (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
  -- indirect calls: the pointer read at the key names the callee
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    exact akteurS_dannCallInd (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    exact akteurS_rufCallInd (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu
      hneu =>
    exact akteurS_dannBindCallInd (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
  -- normal pops
  | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := kopfS_okS hF.1 hhead
    have hens := popS_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabil (hFS _) e hok.2)
      (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popS_begr_ok hE hF.1 hhead e
        (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
      (fun R O' U σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
      hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okS_ende_cons (kopfS_okS hF.1 hhead)
    have hens := popS_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabil (hFS _) e hok.2.1)
      (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popS_begr_ok hE hF.1 hhead e
        (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
      (fun R O' U σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
    exact akteurS_dannRet (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (e := e) (hperm := hperm) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hnw := hnw)
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
      s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := kopfS_okS hF.1 hhead
    have hens := popS_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabil (hFS _) e hok.2)
      (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popS_begr_ok hE hF.1 hhead e
        (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun L h => by rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> exact h)
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' U σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    exact akteurS_dannRetBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (lk := lk) (Γk := Γk) (Λk := Λk) (Λk'' := Λk'') (e := e) (hperm := hperm) (restk := restk) (kk := kk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu)
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
      s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    exact akteurS_rueckConsBind (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (lk := lk) (Γk := Γk) (Λk := Λk) (e := e) (hperm := hperm) (restk := restk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu)
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
    refine ⟨⟨popS_kopf hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popS_begr_grund hE hF.1 hhead rg
        (fun O' R U σ => semH_rueckGrund S O' U passes R rg hperm σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun L h => by rw [hcaller]; exact h)
      (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
        (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
      (fun R O' U σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    subst hfg hs0 hrg
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popS_begr_grund hE hF.1 hhead rg
        (fun O' R U σ => semH_rueckConsGrund S O' U passes R rg hperm restk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun L h => by rw [hcaller]; exact h)
      (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
        (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
      (fun R O' U σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    subst hfg hs0 hrg
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popS_begr_grund hE hF.1 hhead rg
        (fun O' R U σ => semH_dannRetGrund S O' U passes R rg hperm restk kk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun L h => by rw [hcaller]; exact h)
      (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
        (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
      (fun R O' U σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  -- register reads and `awaits`: the sequential oracle answers what the machine read
  | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
    exact akteurS_dannRegLies (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk := hk) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (hz := hz) (hΛ := hΛ)
  | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    exact akteurS_dannRegLiesElseWahr (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu
      hΛ =>
    exact akteurS_dannRegLiesElseFalsch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannAwaits l Γ Λ Λ' g payload hp hLg hat rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
    exact akteurS_dannAwaits (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (g := g) (payload := payload) (hp := hp) (hLg := hLg) (hat := hat) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hvis := hvis) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
end Akteur

end Gabbro.Grammatik
