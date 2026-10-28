/-
  File:      stage0/Stage0/Schnell/Stand.lean
  Subject:   **The fast machine.** `FStand`: a memory, a table of the running threads in normal form, the number of
             questions each one's compact trace dropped; every thread beyond the table never runs and is read from
             the start machine. `FStand.schritt`: a step is `zug` on the fast machine under the fast oracle, then
             the stepped thread is normalised into the table. `SStand`: a fast machine together with -- erased at
             run time -- a machine `M` reachable from the start machine under the machine's oracle whose normal
             form it is; `sim` carries it over every step (`SStand.schritt`).
-/
import Stage0.Schnell.Sim
import Stage0.Schnell.Orakel
import Stage0.Schnell.AWelt
import Stage0.Schritt.Zug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- The threads of the fast machine: those in the table, every other one from `rest`. -/
def tabelle (arr : Array (RufFadenG D)) (rest : Faden → RufFadenG D) (g : Faden) : RufFadenG D :=
  arr[g]?.getD (rest g)

/-- The fast machine of a memory and a thread table. -/
def sMaschine (ww : World D) (M0 : RufMaschineG D) (S : Speicher D) (arr : Array (RufFadenG D)) :
    RufMaschineG D :=
  ⟨S, tabelle arr (fun g => fadenNormal ww (M0.faeden g)), [], ww⟩

/-- **The fast machine**: array memory, thread table, dropped questions. -/
structure FStand (K : Kodierung D) (n : Nat) where
  A : AWelt D
  faeden : Array (RufFadenG D)
  zahl : Array Nat
  groesse : faeden.size = n
  groesseZ : zahl.size = n

variable {K : Kodierung D} {n : Nat}

/-- The fast machine as a machine. -/
def FStand.F (ww : World D) (M0 : RufMaschineG D) (s : FStand K n) : RufMaschineG D :=
  sMaschine ww M0 (s.A.sicht K) s.faeden

/-- The questions thread `f`'s compact trace dropped. -/
def FStand.c (s : FStand K n) (f : Faden) : Nat := s.zahl[f]?.getD 0

/-- The threads that never run hold no lock. -/
theorem FStand.ruhe {ww : World D} {M0 : RufMaschineG D} (h0 : ∀ g, n ≤ g → offen (M0.faeden g).spur = [])
    (s : FStand K n) : ∀ g, g ∉ List.range n → offen ((s.F ww M0).faeden g).spur = [] := by
  intro g hg
  have hg' : n ≤ g := by simpa using hg
  have : s.faeden[g]? = none := Array.getElem?_eq_none (by rw [s.groesse]; exact hg')
  simp only [FStand.F, sMaschine, tabelle, this, Option.getD_none, offen_kompakt, fadenNormal]
  exact h0 g hg'

/-- The fast machine after thread `f` stepped to `F'` with the writes `w`: the writes go into the arrays in place
    (everything read from `F'` and from `s` first, so the arrays are unshared when they are written). -/
def FStand.nach (s : FStand K n) (ww : World D) (f : Faden) (F' : RufMaschineG D) (w : List (Schreib D)) :
    FStand K n :=
  let z := fadenNormal ww (F'.faeden f)
  let c := s.c f + fremdZahl (F'.faeden f).spur
  let fa := s.faeden.setIfInBounds f z
  let za := s.zahl.setIfInBounds f c
  ⟨s.A.schreibe K w, fa, za, by simp only [Array.size_setIfInBounds, s.groesse, fa], by simp only [Array.size_setIfInBounds, s.groesseZ, za]⟩

/-- **One step of thread `f`** on the fast machine under the log `log`: the stepped machine, or the unchanged one
    handed back (so no caller keeps a second reference to the arrays). -/
def FStand.schritt (P : Programm D) (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (log : List (Antwort D))
    (passes : Nat) (ww : World D) (M0 : RufMaschineG D) (h0 : ∀ g, n ≤ g → offen (M0.faeden g).spur = [])
    (s : FStand K n) (f : Faden) :
    FStand K n ⊕ {t : FStand K n // ∃ F' w, RufSchrittG P (orakelZ kf (s.c f) log) passes (s.F ww M0) f F' ∧
      F'.speicher = schreibAuf w (s.A.sicht K) ∧ t = s.nach ww f F' w} :=
  match zug P (orakelZ kf (s.c f) log) passes (orakelZ_treu kf _ log) (orakelZZellen kf _ log)
      (orakelZ_schreibt kf _ log) (s.F ww M0) f (List.range n) (s.ruhe h0) with
  | some z => .inr ⟨s.nach ww f z.M' z.w, z.M', z.w, z.schritt, z.hw, rfl⟩
  | none => .inl s

variable (P : Programm D) (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (log : List (Antwort D))
  (passes : Nat) (ww : World D) (M0 : RufMaschineG D)

/-- What the fast machine stands for: a reachable machine it is the normal form of. -/
def SInv (s : FStand K n) : Prop :=
  ∃ M : RufMaschineG D, RufErreichbarG P (orakelZ kf 0 log) passes M0 M ∧ s.F ww M0 = normal ww M ∧
    (∀ g < n, s.c g = fremdZahl (M.faeden g).spur) ∧ (∀ g, n ≤ g → M.faeden g = M0.faeden g)

/-- **The fast machine on a run.** -/
structure SStand (K : Kodierung D) (n : Nat) where
  s : FStand K n
  inv : SInv P kf log passes ww M0 s

variable {P kf log passes ww M0}

/-- **A step keeps the invariant.** -/
theorem SInv.schritt {s : FStand K n} (hi : SInv P kf log passes ww M0 s) {f : Faden} (hf : f < n)
    {F' : RufMaschineG D} (hs : RufSchrittG P (orakelZ kf (s.c f) log) passes (s.F ww M0) f F')
    {w : List (Schreib D)} (hw : F'.speicher = schreibAuf w (s.A.sicht K)) :
    SInv P kf log passes ww M0 (s.nach ww f F' w) := by
  obtain ⟨M, hr, hF, hz, hrest⟩ := hi
  have hc : s.c f = fremdZahl (M.faeden f).spur := hz f hf
  rw [hc, hF] at hs
  obtain ⟨M', hM', hn, hfr⟩ := sim (orakelZ_paar kf _ log) hs
  have hfremd : ∀ g, g ≠ f → M'.faeden g = M.faeden g := fun g hg => rufSchrittG_fremd hM' g hg
  have hsp : F'.speicher = M'.speicher := by
    have := congrArg RufMaschineG.speicher hn
    exact this
  have hfa : ∀ g, fadenNormal ww (F'.faeden g) = fadenNormal ww (M'.faeden g) :=
    fun g => congrFun (congrArg RufMaschineG.faeden hn) g
  have hold : ∀ g, tabelle s.faeden (fun g => fadenNormal ww (M0.faeden g)) g = fadenNormal ww (M.faeden g) :=
    fun g => congrFun (congrArg RufMaschineG.faeden hF) g
  have hfs : f < s.faeden.size := by rw [s.groesse]; exact hf
  have hfz : f < s.zahl.size := by rw [s.groesseZ]; exact hf
  refine ⟨M', .schritt _ _ f hr hM', ?_, ?_, ?_⟩
  · simp only [FStand.F, FStand.nach, sMaschine, normal, RufMaschineG.mk.injEq, and_true]
    refine ⟨by rw [sicht_schreibe, ← hw, hsp], ?_⟩
    funext g
    by_cases hg : f = g
    · subst hg
      simp only [tabelle, Array.getElem?_setIfInBounds_self_of_lt hfs, Option.getD_some]
      exact hfa f
    · simp only [tabelle, Array.getElem?_setIfInBounds_ne hg]
      have := hold g
      simp only [tabelle] at this
      rw [this, hfremd g (Ne.symm hg)]
  · intro g hg
    by_cases hgf : f = g
    · subst hgf
      simp only [FStand.c, FStand.nach]
      rw [Array.getElem?_setIfInBounds_self_of_lt hfz, Option.getD_some, hfr]
      simp only [FStand.c] at hc
      rw [hc]
      omega
    · simp only [FStand.c, FStand.nach, Array.getElem?_setIfInBounds_ne hgf]
      rw [hfremd g (Ne.symm hgf)]
      exact hz g hg
  · intro g hg
    rw [hfremd g (by intro h; subst h; exact absurd hg (Nat.not_le.mpr hf))]
    exact hrest g hg

/-- **One step of thread `f`** on the run: the stepped run, or the unchanged one handed back. -/
def SStand.schritt (h0 : ∀ g, n ≤ g → offen (M0.faeden g).spur = []) (s : SStand P kf log passes ww M0 K n)
    (f : Faden) (hf : f < n) : SStand P kf log passes ww M0 K n ⊕ SStand P kf log passes ww M0 K n :=
  match s with
  | ⟨s0, hi⟩ =>
    match h : s0.schritt P kf log passes ww M0 h0 f with
    | .inr ⟨t, ht⟩ => .inr ⟨t, by
        obtain ⟨F', w, hs, hw, rfl⟩ := ht
        exact hi.schritt hf hs hw⟩
    | .inl t => .inl ⟨t, by
        have : t = s0 := by
          simp only [FStand.schritt] at h
          split at h <;> simp_all
        exact this ▸ hi⟩

end Gabbro.Stage0
