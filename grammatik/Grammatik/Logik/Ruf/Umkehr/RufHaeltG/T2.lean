/- Part 2 of 3 of `RufHaeltG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufHaeltG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.AntwortHaelt
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil7
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil8
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil8b
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil9
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

set_option maxHeartbeats 1000000 in
/-- **Every rule keeps the thread invariant of the acting thread.** -/
theorem rufSchrittG_haeltInv {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (h : HaeltInvG (M.faeden f)) : HaeltInvG (M'.faeden f) := by
  have hk0 := h.2.1 _ List.mem_cons_self
  have hh0 := h.kopf
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      exact rufSchrittG_haeltInv_blatt (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (s := s) (rest := rest) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein)
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact rufSchrittG_haeltInv_ruf (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | rueck caller rst hpop Γ Λ e hperm ρ _ g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      simp only [rufUpdateG_self]
      exact haeltInvG_pop_gleich h hpop _ _ (by rw [hs1, offen_lese]; rfl)
    | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
      exact rufSchrittG_haeltInv_endeEntf (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (s := s) (rest := rest) (ρ := ρ) (hent := hent) (hhead := hhead)
    | endeForm l Γ Λ e ρ hl hent hhead =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      exact haeltInvG_kopf h (by ho_tac) (by fr_tac)
        (kette_abbruch _ hk (GRest.leer (Λ := Λ)) hk (fun L hL => hL)) hh
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      exact rufSchrittG_haeltInv_dannBlatt (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (s := s) (rest := rest) (k := k) (ρ := ρ) (hleaf := hleaf) (hhead := hhead) (hΛ := hΛ) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein := hkein)
    | dannLeer l Γ Λ k ρ hhead =>
      exact rufSchrittG_haeltInv_dannLeer (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (k := k) (ρ := ρ) (hhead := hhead)
    | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannIteWahr (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannIteFalsch (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (t := t) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannOnOptionSome (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannOnOptionNone (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (o := o) (p := p) (a := a) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannOnTagSome (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (τ := τ) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannOnTagNone (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (cs := cs) (v := v) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (nutz := nutz) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannOnGrund (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (r := r) (arms := arms) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (b := b) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
      exact rufSchrittG_haeltInv_endeBind (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (e := e) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact rufSchrittG_haeltInv_endeBindAxiom (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiomOpt l Γ Λ e a args he hp hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact rufSchrittG_haeltInv_endeBindAxiomOpt (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannBind (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (e := e) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannNarrowOk (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hn := hn) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | g2 hs =>
    cases hs with
    | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannNarrowElse (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') (e := e) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hn := hn) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannPruefWahr (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannPruefFalsch (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (c := c) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
      exact rufSchrittG_haeltInv_dannBreaking (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (i := i) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      exact rufSchrittG_haeltInv_dannLocks (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (L := L) (hr := hr) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hself := hself) (hrang := hrang) (hfrei := hfrei)
    | freiGib l Γ Λ L k ρ hhead =>
      exact rufSchrittG_haeltInv_freiGib (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (L := L) (k := k) (ρ := ρ) (hhead := hhead)
    | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
      exact rufSchrittG_haeltInv_schrumpfVergiss (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (k := k) (v := v) (ρ := ρ) (hhead := hhead)
    | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
      exact rufSchrittG_haeltInv_dannTrav (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (inv := inv) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_travNext (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (i := i) (is := is) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | travFort l Γ Λ t inv body is k i ρ hhead =>
      exact rufSchrittG_haeltInv_travFort (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (is := is) (k := k) (i := i) (ρ := ρ) (hhead := hhead)
    | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_travDone (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
      exact rufSchrittG_haeltInv_dannRetry (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (bis := bis) (body := body) (ueber := ueber) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
      exact rufSchrittG_haeltInv_wiederUeber (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead)
    | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_wiederWeiter (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_wiederSchritt (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
      exact rufSchrittG_haeltInv_wiederFort (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueber := ueber) (k := k) (ρ := ρ) (hhead := hhead)
    | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
      exact rufSchrittG_haeltInv_dannForever (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (a := a) (inv := inv) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      exact rufSchrittG_haeltInv_ewigWeiter (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (a := a) (n := n) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | ewigFort l Γ Λ a n inv body k ρ hhead =>
      exact rufSchrittG_haeltInv_ewigFort (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (a := a) (n := n) (inv := inv) (body := body) (k := k) (ρ := ρ) (hhead := hhead)
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact rufSchrittG_haeltInv_rufDann (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (g := g) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
  | g3 hs =>
    cases hs with
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      exact rufSchrittG_haeltInv_dannCallInd (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      exact rufSchrittG_haeltInv_rufCallInd (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (rest := rest) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      exact rufSchrittG_haeltInv_dannBindCall (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
        neu hneu =>
      exact rufSchrittG_haeltInv_dannBindCallInd (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
        hneu =>
      exact rufSchrittG_haeltInv_dannBindCallElse (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
        neu hneu =>
      exact rufSchrittG_haeltInv_dannBindCallIndElse (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
        neu hneu =>
      exact rufSchrittG_haeltInv_dannCallIndElse (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (Λ'' := Λ'') (τ := τ) (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (hΛ := hΛ) (s0 := s0) (hs0 := hs0) (g := g) (hg := hg) (hv := hv) (rho := rho) (hrho := hrho) (neu := neu) (hneu := hneu)
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ _ g hfg rho hrho s0
        hs0 hΛ s1 hs1 v hv he neu hneu =>
      simp only [rufUpdateG_self]
      have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
        h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have hck : (GRest.dann restb (.schrumpf k) :
          GRest D (vertragVon D caller.f) l (τ :: Γ) Λ).kette (D.haelt caller.f) := by
        rcases hcaller with hcaller | ⟨_, _, hcaller⟩
        · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
        · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
      refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck (by rw [hs1, offen_lese]; rfl)
      intro L hL
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] <;> exact hL
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁
        hw neu₁ hneu₁ hΛ =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      have e := leave_welt' O passes keinRuf _ _ hleave σ' ρ' hstep
      refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2.2 ?_
      rw [hs₁, offen_lese, e]; exact heldIn_block rest hh
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      have e := next_welt' O passes keinRuf _ _ hnext σ' ρ' hstep
      refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 ?_
      rw [e]; exact heldIn_block rest hh
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      have e := leave_welt' O passes keinRuf _ _ hleave σ' ρ' hstep
      refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2.2 ?_
      rw [e]; exact heldIn_block rest hh
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      have e := next_welt' O passes keinRuf _ _ hnext σ' ρ' hstep
      refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 ?_
      rw [e]; exact heldIn_block rest hh
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      have e := leave_welt' O passes keinRuf _ _ hleave σ' ρ' hstep
      refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2.2 ?_
      rw [e]; exact heldIn_block rest hh
    | dannAxiomCallElseOk l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannAxiomCallElseOk (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannAxiomCallElseGrund l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      exact rufSchrittG_haeltInv_dannAxiomCallElseGrund (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | g4 hs =>
    cases hs with
    | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      have e := next_welt' O passes keinRuf _ _ hnext σ' ρ' hstep
      refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 ?_
      rw [e]; exact heldIn_block rest hh
    | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩
        (heldIn_block b (heldIn_block rest hh))
    | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩
        (heldIn_block b (heldIn_block rest hh))
    | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ (heldIn_block rest hh)
    | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ (heldIn_block rest hh)
    | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      refine haeltInvG_kopf h (fun K hK hnf => (List.mem_erase_of_ne (fun e => hnf (by
          rw [freis_von hhead]; simp only [GRest.freis, e, List.mem_cons, true_or]))).mpr hK) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ ?_
      intro K hK
      have hKL : K ≠ L := fun e => hk.2.1 (e ▸ hK)
      exact (List.mem_erase_of_ne hKL).mpr
        (heldIn_block rest hh K (List.mem_cons_of_mem _ hK))
    | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      refine haeltInvG_kopf h (fun K hK hnf => (List.mem_erase_of_ne (fun e => hnf (by
          rw [freis_von hhead]; simp only [GRest.freis, e, List.mem_cons, true_or]))).mpr hK) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ ?_
      intro K hK
      have hKL : K ≠ L := fun e => hk.2.1 (e ▸ hK)
      exact (List.mem_erase_of_ne hKL).mpr
        (heldIn_block rest hh K (List.mem_cons_of_mem _ hK))
    | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hl hhead =>
      exact rufSchrittG_haeltInv_peelAbbruchLeave (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (Γ := Γ) (Λ := Λ) (Λ1 := Λ1) (Λk := Λk) (rest := rest) (k := k) (ρ := ρ) (hl := hl) (hhead := hhead)
    | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hl hhead =>
      exact rufSchrittG_haeltInv_peelAbbruchNext (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (Γ := Γ) (Λ := Λ) (Λ1 := Λ1) (Λk := Λk) (rest := rest) (k := k) (ρ := ρ) (hl := hl) (hhead := hhead)
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
        neu hneu hnw =>
      exact rufSchrittG_haeltInv_dannRet (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (e := e) (hperm := hperm) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hnw := hnw)
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ _ g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
        hnw =>
      simp only [rufUpdateG_self]
      exact haeltInvG_pop_gleich h hpop _ _ (by rw [hs1, offen_lese]; rfl)
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      exact rufSchrittG_haeltInv_dannRetBind (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (lk := lk) (Γk := Γk) (Λk := Λk) (Λk'' := Λk'') (e := e) (hperm := hperm) (restk := restk) (kk := kk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu)
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
        s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      exact rufSchrittG_haeltInv_rueckConsBind (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (lk := lk) (Γk := Γk) (Λk := Λk) (e := e) (hperm := hperm) (restk := restk) (ρ := ρ) (hhead := hhead) (caller := caller) (rst := rst) (hpop := hpop) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (restb := restb) (k := k) (ρc := ρc) (hcaller := hcaller) (hΛ := hΛ) (s1 := s1) (hs1 := hs1) (g := g) (hfg := hfg) (rho := rho) (hrho := hrho) (s0 := s0) (hs0 := hs0) (v := v) (hv := hv) (he := he) (neu := neu) (hneu := hneu)
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
        hrho s0 hs0 rg hrg hn =>
      simp only [rufUpdateG_self]
      have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
        h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have hcw := kette_von hcaller hc
      have hck := kette_abbruch (Endblock.alsBlock err).2 hcw.1 (.schrumpf k)
        ⟨GRest.kette_top k hcw.2, hcw.2⟩ (fun L hL => (Block.held_iff restb L).mp hL)
      refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck rfl
      intro L hL
      rw [hcaller]; exact hL
  | g5 hs =>
    cases hs with
    | rueckConsGrund =>
      rename_i ρ caller rst l Γ Λ Λ' τ n err restb k ρc hcaller g rho s0 rg hn r hperm restk hhead hpop hΛ hfg hrho hs0 hrg
      simp only [rufUpdateG_self]
      have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
        h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have hcw := kette_von hcaller hc
      have hck := kette_abbruch (Endblock.alsBlock err).2 hcw.1 (.schrumpf k)
        ⟨GRest.kette_top k hcw.2, hcw.2⟩ (fun L hL => (Block.held_iff restb L).mp hL)
      refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck rfl
      intro L hL
      rw [hcaller]; exact hL
    | dannRetGrund =>
      rename_i ρ caller rst l Γ Λ Λ' τ n err restb k ρc hcaller g rho s0 rg hn r hperm restk kk hhead hpop hΛ hfg hrho hs0 hrg
      simp only [rufUpdateG_self]
      have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
        h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have hcw := kette_von hcaller hc
      have hck := kette_abbruch (Endblock.alsBlock err).2 hcw.1 (.schrumpf k)
        ⟨GRest.kette_top k hcw.2, hcw.2⟩ (fun L hL => (Block.held_iff restb L).mp hL)
      refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck rfl
      intro L hL
      rw [hcaller]; exact hL
    | dannRegLies =>
      rename_i l Γ Λ Λ' r hk ρ v hz rest k hhead hv hΛ
      exact rufSchrittG_haeltInv_dannRegLies (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk := hk) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (hz := hz) (hΛ := hΛ)
    | dannRegLiesElseWahr =>
      rename_i l Γ Λ Λ' r hk zusage ρ v σ₁ hw neu sonst rest k hhead hv hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannRegLiesElseWahr (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannRegLiesElseFalsch =>
      rename_i l Γ Λ Λ' r hk zusage ρ v σ₁ hw neu sonst rest k hhead hv hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannRegLiesElseFalsch (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannAwaits =>
      rename_i l Γ Λ Λ' g payload hp hL hat ρ σ₁ neu rest k hhead hvis hs₁ hneu hΛ
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
      rw [hs₁, offen_lese]; exact hh
    | dannExchange =>
      rename_i l Γ Λ Λ' g neuE hL ρ σ₁ σ₂ hs₂ neu hw rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannExchange (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (g := g) (neuE := neuE) (hw := hw) (hL := hL) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (hs₂ := hs₂) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleit =>
      rename_i l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi ρ σ₁ v hv neu rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannGleit (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (l₂ := l₂) (h₂ := h₂) (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitLit =>
      rename_i l Γ Λ Λ' q lo hi ρ v hv rest k hhead
      exact rufSchrittG_haeltInv_dannGleitLit (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (q := q) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (hv := hv)
    | dannGleitVon =>
      rename_i l Γ Λ Λ' l₁ h₁ e lo hi ρ σ₁ v hv neu rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannGleitVon (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitNarrowOk =>
      rename_i l Γ Λ Λ' l₁ h₁ e lo hi ρ σ₁ v hv neu sonst rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannGleitNarrowOk (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (v := v) (hv := hv) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannGleitNarrowElse =>
      rename_i l Γ Λ Λ' l₁ h₁ e lo hi ρ σ₁ hn neu sonst rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannGleitNarrowElse (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (l₁ := l₁) (h₁ := h₁) (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hn := hn) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiom =>
      rename_i l Γ Λ Λ' τ a args he hd hgd ρ σ₁ σ₂ v hax neu hw hg rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannBindAxiom (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomElseOk =>
      rename_i l Γ Λ Λ' τ a args he hr hd hgd ρ σ₁ σ₂ v hax neu hw hg err rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannBindAxiomElseOk (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomElseGrund =>
      rename_i l Γ Λ Λ' τ a args he hr hd hgd ρ σ₁ σ₂ r hax neu hw hg err rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannBindAxiomElseGrund (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomOpt =>
      rename_i x l Γ Λ Λ' e a args he hd hgd ρ σ₁ σ₂ v hax neu hp rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannBindAxiomOpt (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomOptElseOk =>
      rename_i x l Γ Λ Λ' e a args he hr hd hgd ρ σ₁ σ₂ v hax neu hp err rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannBindAxiomOptElseOk (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannBindAxiomOptElseGrund =>
      rename_i l Γ Λ Λ' e a args he hr hd hgd ρ σ₁ σ₂ r hax neu hp err rest k hhead hs₁ hneu hΛ
      exact rufSchrittG_haeltInv_dannBindAxiomOptElseGrund (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ' := Λ') (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | g6 hs =>
    cases hs with
    | endeBindAxiomElseOk =>
      rename_i l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ
      exact rufSchrittG_haeltInv_endeBindAxiomElseOk (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiomElseGrund =>
      rename_i l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ
      exact rufSchrittG_haeltInv_endeBindAxiomElseGrund (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (τ := τ) (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiomOptElseOk =>
      rename_i l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ
      exact rufSchrittG_haeltInv_endeBindAxiomOptElseOk (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (v := v) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | endeBindAxiomOptElseGrund =>
      rename_i l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ
      exact rufSchrittG_haeltInv_endeBindAxiomOptElseGrund (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (e := e) (a := a) (args := args) (he := he) (hr := hr) (hp := hp) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (σ₂ := σ₂) (r := r) (hax := hax) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | g7 hs =>
    cases hs with
    | dannVerbrauch l Γ Λ Λ'' t member edge inv bound mass body rest k ρ hhead =>
      exact rufSchrittG_haeltInv_dannVerbrauch (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
    | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ v _ σ₃ hs₃ m _ neu hneu hΛ =>
      exact rufSchrittG_haeltInv_verbrauchWeiter (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (σ₂ := σ₂) (hs₂ := hs₂) (v := v) (σ₃ := σ₃) (hs₃ := hs₃) (m := m) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ _ _ neu hneu hΛ =>
      exact rufSchrittG_haeltInv_verbrauchLeer (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (σ₂ := σ₂) (hs₂ := hs₂) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead σ₁ hs₁ m' hm' hfall neu hneu hΛ =>
      exact rufSchrittG_haeltInv_verbrauchFort (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (M := M) (f := f) (h := h) (hk0 := hk0) (hh0 := hh0) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (i := i) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (m' := m') (hm' := hm'.symm) (hfall := hfall) (neu := neu) (hneu := hneu) (hΛ := hΛ)
    | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb _ ρ hleave hhead σ' ρ' neu hstep hneu _ σm hsm _ _ _ σ₁ hs₁ _ neu₁ hneu₁ hΛ =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      have e := leave_welt' O passes keinRuf _ _ hleave σ' ρ' hstep
      refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2.2 ?_
      simp only [hsm, hs₁, offen_lese]
      rw [e]; exact heldIn_block restb hh
    | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb _ ρ hnext hhead σ' ρ' neu hstep hneu _ σm hsm _ _ _ neum hneum hΛ =>
      simp only [rufUpdateG_self]
      have hk := kette_von hhead hk0
      have hh := heldIn_von hhead hh0
      have e := next_welt' O passes keinRuf _ _ hnext σ' ρ' hstep
      refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 ?_
      simp only [hsm, offen_lese]
      rw [e]; exact heldIn_block restb hh
    | rueckFreigabe ρ a L remaining hhead =>
      simp only [rufUpdateG_self]
      exact haeltInvG_scopedRelease ρ a L remaining hhead h
    | rueckScopedWertDirekt ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z ha =>
      simp only [rufUpdateG_self]
      apply haeltInvG_rufAntwort h ?_ ha
      subst σ₁
      exact offen_lese _ _ _
    | rueckScopedGrundDirekt ρ r grund R hhead hret hscope hΛ hempty z ha =>
      simp only [rufUpdateG_self]
      exact haeltInvG_rufAntwort h rfl ha
    | rueckFreigabeLetzte ρ a L hhead z ha =>
      simp only [rufUpdateG_self]
      have hrelease := haeltInvG_scopedRelease ρ a L [] hhead h
      exact haeltInvG_rufAntwort (vor := a.2) (σ := (M.weltVon f).gibt L)
        (a := a.1) hrelease rfl ha
end Gabbro.Grammatik
