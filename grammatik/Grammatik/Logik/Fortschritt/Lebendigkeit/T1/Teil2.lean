module

public import Grammatik.Logik.Fortschritt.Fortschritt
public import Grammatik.Logik.Fortschritt.PlanLauf
public import Grammatik.Logik.Fortschritt.Warten
public import Grammatik.Logik.Fortschritt.Lebendigkeit.T1.Teil1
public import Grammatik.Logik.Fortschritt.Lebendigkeit.T1.Teil1a

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section MaschineG
variable {P : Programm D} {O : Orakel D} {passes : Nat}

set_option maxHeartbeats 4000000 in
/-- **A finished thread cannot step**: an empty stack under a `return` head
    -- every pop needs a caller, and no other rule has that head. -/
theorem ende_ret_kein_schritt {M M' : RufMaschineG D} {t : Faden}
    (hst : (M.faeden t).stapel = [])
    (hk : (M.faeden t).kopf.rest.2.2.2.2.istEndeRet = true)
    (hs : RufSchrittG P O passes M t M') : False := by
  cases hs with
  | g1 hs =>
    cases hs with
    | rueck caller rest hpop => rw [hst] at hpop; cases hpop
    | endeForm l Γ Λ e ρ hl hent hhead =>
        rw [hhead] at hk
        cases e <;> simp_all [GRest.istEndeRet, EndEntfaltbar]
    | _ =>
        rw [‹(M.faeden t).kopf.rest = _›] at hk
        simp only [GRest.istEndeRet, Bool.false_eq_true] at hk
  | g2 hs =>
    cases hs with
    | _ =>
        rw [‹(M.faeden t).kopf.rest = _›] at hk
        simp only [GRest.istEndeRet, Bool.false_eq_true] at hk
  | g3 hs =>
    cases hs with
    | rueckBind caller rest hpop => rw [hst] at hpop; cases hpop
    | _ =>
        rw [‹(M.faeden t).kopf.rest = _›] at hk
        simp only [GRest.istEndeRet, Bool.false_eq_true] at hk
  | g4 hs =>
    cases hs with
    | _ =>
        rw [‹(M.faeden t).kopf.rest = _›] at hk
        simp only [GRest.istEndeRet, Bool.false_eq_true] at hk
  | g5 hs =>
    cases hs with
    | _ =>
        rw [‹(M.faeden t).kopf.rest = _›] at hk
        simp only [GRest.istEndeRet, Bool.false_eq_true] at hk
  | g6 hs =>
    cases hs with
    | _ =>
        rw [‹(M.faeden t).kopf.rest = _›] at hk
        simp only [GRest.istEndeRet, Bool.false_eq_true] at hk
  | g7 hs =>
    cases hs with
    | rueckScopedWert ρ r e R hhead hret =>
      rcases GRest.scopedWert_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;> subst r <;>
        rw [hhead] at hk <;> simp only [GRest.istEndeRet, Bool.false_eq_true, reduceCtorEq] at hk
    | rueckScopedGrund ρ r grund R hhead hret =>
      rcases GRest.scopedGrund_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;> subst r <;>
        rw [hhead] at hk <;> simp only [GRest.istEndeRet, Bool.false_eq_true, reduceCtorEq] at hk
    | _ =>
        rw [‹(M.faeden t).kopf.rest = _›] at hk
        simp only [GRest.istEndeRet, Bool.false_eq_true] at hk

/-- A named hardware stop, read off the head residue. -/
theorem halt_kopf {M : RufMaschineG D} {t : Faden} {k : Zielsatz.HaltArt}
    (h : Zielsatz.HaltBenannt O passes M k t) :
    Zielsatz.RestHalt O passes (M.weltVon t) (M.faeden t).kopf.rest.2.2.2.1 k
      (M.faeden t).kopf.rest.2.2.2.2 := by
  obtain ⟨l, Γ, Λ, ρ, r, he, hr⟩ := h
  rw [he]
  exact hr

end MaschineG
/-! ## 5. The runtime assumption and the premises, on a run -/

section Annahmen

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- A lock holder can step or stands at a `locks` head (no other stop inside
    a critical section). Derived from progress in `abschnittAktiv_aus`. -/
def AbschnittAktiv (R : PlanLauf P O passes) : Prop :=
  ∀ n u L, L ∈ offen ((R.M n).faeden u).spur →
    Bereit P O passes (R.M n) u ∨ ∃ L', AnSperre (R.M n) u L'

end Annahmen
/-! ## 6. Runs: frozen threads -/
