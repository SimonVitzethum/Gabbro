module

public import Grammatik.Bausteine.Arena.Ownership.Machine.Stack.Return
public import Grammatik.Bausteine.Arena.Ownership.Machine.OwnInv_stepFaelle.Teil18

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body
variable {D : Deklaration}

/-- Group 7 preserves ownership; pending-return residues are outside the
    ownership checker's currently admitted source fragment. -/
theorem ownInv_step_g7 {P : Programm D} {A : FreiForm D} {I : Interfaces A}
    {O : Orakel D} {passes : Nat} {M M' : RufMaschineG D} {u : Faden} {s : State}
    (hH : Head A I ⟨u, (M.faeden u).stapel.length⟩ s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest)
    (hstep : RufSchrittG7 P O passes M u M') : OwnInv A I M' := by
  cases hstep with
  | dannVerbrauch l Γ Λ Λ'' t member edge inv bound mass body rest k ρ hhead =>
    exact ownInv_step_dannVerbrauch (P := P) (O := O) (passes := passes) (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
  | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ v hv σ₃ hs₃ m hm neu hneu hΛ =>
    exact ownInv_step_verbrauchWeiter (P := P) (O := O) (passes := passes) (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (v := v) (m := m) (σ₃ := σ₃)
  | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ hleer hkein neu hneu hΛ =>
    exact ownInv_step_verbrauchLeer (P := P) (O := O) (passes := passes) (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₂ := σ₂)
  | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead σ₁ hs₁ m' hm' hfall neu hneu hΛ =>
    exact ownInv_step_verbrauchFort (P := P) (O := O) (passes := passes) (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (i := i) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁)
  | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
    exact ownInv_step_dannLeaveVerbrauch (P := P) (O := O) (passes := passes) (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hleave := hleave) (hhead := hhead) (σ₁ := σ₁)
  | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall neum hneum hΛ =>
    exact ownInv_step_dannNextVerbrauch (P := P) (O := O) (passes := passes) (M := M) (u := u) (s := s) (hH := hH) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hnext := hnext) (hhead := hhead) (σm := σm) (ρr := ρ'.tail)

  | rueckScopedWert ρ r e R hhead hret
  | rueckScopedWertDirekt ρ r e R hhead hret =>
    rcases GRest.scopedWert_faelle hret with hr | ⟨rest, hr⟩ | ⟨Λ', rest, k, hr⟩ <;> subst r <;>
      rw [hhead] at hH <;> obtain ⟨k0, c, g, hk, hf, hor⟩ := head_run hH rfl
    · cases hor with | ende _ he => cases he
    · obtain ⟨c2, hs, _⟩ := hor.stmtEnde; cases hs
    · obtain ⟨c2, hs, _⟩ := hor.stmt trivial; cases hs
  | rueckScopedGrund ρ r grund R hhead hret
  | rueckScopedGrundDirekt ρ r grund R hhead hret =>
    rcases GRest.scopedGrund_faelle hret with hr | ⟨rest, hr⟩ | ⟨Λ', rest, k, hr⟩ <;> subst r <;>
      rw [hhead] at hH <;> obtain ⟨k0, c, g, hk, hf, hor⟩ := head_run hH rfl
    · cases hor with | ende _ he => cases he
    · obtain ⟨c2, hs, _⟩ := hor.stmtEnde; cases hs
    · obtain ⟨c2, hs, _⟩ := hor.stmt trivial; cases hs
  | rueckFreigabe ρ a L remaining hhead =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hor⟩ := head_run hH rfl
    cases hor
  | rueckFreigabeLetzte ρ a L hhead z hantwort =>
    rw [hhead] at hH
    obtain ⟨k0, c, g, hk, hf, hor⟩ := head_run hH rfl
    cases hor

end Gabbro.Grammatik.ArenaOwnership.Machine
