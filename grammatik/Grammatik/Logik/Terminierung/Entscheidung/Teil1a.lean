module

public import Grammatik.Logik.Terminierung.Entscheidung.Teil1
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
/-! ## 2. The rank from the call graph; the gate holds for every program -/

section Rang

variable [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn)

/-- **The rank of `f`**: how many functions it reaches. -/
def rangB (f : D.Fn) : Nat := fs.countP (reachB P fs f)

variable {P fs} (hvoll : ∀ g : D.Fn, g ∈ fs)
include hvoll

theorem reachB_trans {f g h : D.Fn} (h1 : reachB P fs f g = true) (h2 : reachB P fs g h = true) :
    reachB P fs f h = true :=
  Zielsatz.reachB_in P fs (Z := fun x => reachB P fs f x = true) h1
    (fun _ _ ha hr => Zielsatz.reachB_ruft P hvoll ha hr) h h2

theorem rangB_le {f g : D.Fn} (h : reachB P fs f g = true) : rangB P fs g ≤ rangB P fs f :=
  List.countP_mono_left (fun _ _ hx => reachB_trans hvoll h hx)

theorem rangB_lt {f g : D.Fn} (h : reachB P fs f g = true) (hn : reachB P fs g f = false) :
    rangB P fs g < rangB P fs f :=
  Zielsatz.countP_lt_of (reachB P fs g) (reachB P fs f) fs (fun _ hx => reachB_trans hvoll h hx)
    ⟨f, hvoll f, reachB_wurzel P fs f, hn⟩

/-- **Every callee passes the gate**: it reaches no more than its caller, and as many only on the caller's cycle. -/
theorem tor_ruft {f g : D.Fn} (hr : ruftB P f g = true) : tor (zykS P fs) (rangB P fs) f g = true := by
  have hfg : reachB P fs f g = true := Zielsatz.reachB_ruft P hvoll (reachB_wurzel P fs f) hr
  unfold tor
  cases hgf : reachB P fs g f
  · simp only [rangB_lt hvoll hfg hgf, decide_true, Bool.true_or]
  · have e : rangB P fs g = rangB P fs f := Nat.le_antisymm (rangB_le hvoll hfg) (rangB_le hvoll hgf)
    simp only [e, Nat.lt_irrefl, decide_false, Bool.false_or, beq_self_eq_true, Bool.true_and]
    simp only [zykS, zyklusMit, hfg, hgf, Bool.and_self, Bool.true_and]
    exact List.any_eq_true.2 ⟨g, hvoll g, by simp only [hr, hgf, Bool.and_self]⟩

/-- A gate that every callee of `f` passes admits `f`'s body. -/
theorem rufeE_aus_ruft (Z : D.Fn → Bool) {f : D.Fn} (hZ : ∀ g, ruftB P f g = true → Z g = true) :
    rufeE Z (fun n => fs.all fun g => !(D.passt g n) || Z g) true (P.rumpf f) = true := by
  rw [rufeE_mE]
  show mE (rufM fs Z) (P.rumpf f) = true
  rw [Gen.rufM_zerlegt fs hvoll]
  apply List.all_eq_true.2
  intro g _
  cases h : ruftB P f g
  · have e := Gen.ruftB_eq P f g
    rw [h] at e
    have hm : mE (Gen.ohneRuf g) (P.rumpf f) = true := by
      cases hm : mE (Gen.ohneRuf g) (P.rumpf f)
      · rw [hm] at e; cases e
      · rfl
    simp only [hm, Bool.or_true]
  · simp only [hZ g h, Bool.true_or]

/-- **THE GATE HOLDS FOR EVERY PROGRAM.** -/
theorem tor_gut (f : D.Fn) :
    rufeE (tor (zykS P fs) (rangB P fs) f) (torS (zykS P fs) (rangB P fs) fs f) true (P.rumpf f) = true :=
  rufeE_aus_ruft hvoll _ fun _ hr => tor_ruft hvoll hr

end Rang

/-! ## 3. Every program terminates under its measure duty -/

section Satz

variable [DecidableEq D.Fn] {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
  (m : Mass D) {fs : List D.Fn}

/-- **TERMINATION** (T5, first half): every program whose measures fall where the user's duty says (`MassPflicht`
    for the cycles of `zykS`) and have one length along a cycle: on every infinite GX run from the start, every
    thread takes only finitely many steps. No static premise beyond the measures: the gate holds for every program
    (`tor_gut`). -/
theorem terminierung (Q : AxEns D) (S : SperrInv D) (K : Faden → D.Fn → Bool)
    (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S lok f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f) (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hK : ∀ f : D.Fn, KoerperGutSA P pa Q S Tg f) (hM : ∀ f, MassPflicht P pa Q S Tg m (zykS P fs) f)
    (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hL : ∀ f g, zykS P fs f g = true → (m f).length = (m g).length)
    (R : LaufGX P O pa Tg) (h0 : R.M 0 = RufStartG P sp init) (t : Faden) :
    ∃ N, ∀ j, N ≤ j → R.akt j ≠ some t :=
  rekursion_endlich_aus m (zykS P fs) (rangB P fs) fs Q S K lok sp init hO hRL hQ hlok hS hvoll hAbg
    hWurzel hTA hTV hTS hTO hFragS hFS hlokK hK hM hStart hsp hex (tor_gut hvoll) hL R h0 t

end Satz

/-! ## 4. The class `endet` keeps its hull free of `forever` -/

section Klasse

variable [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn) (mass : D.Fn → Bool)

theorem klasse_foldl (w : D.Fn) : ∀ (l : List D.Fn) (k : TermKlasse),
    k.rang ≤ (l.foldl (fun k g => if reachB P fs w g then k.schwaecher (lokal P fs mass g) else k) k).rang ∧
    ∀ g ∈ l, reachB P fs w g = true →
      (lokal P fs mass g).rang ≤ (l.foldl (fun k g => if reachB P fs w g then k.schwaecher (lokal P fs mass g) else k) k).rang
  | [], _ => ⟨Nat.le_refl _, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, k => by
      simp only [List.foldl_cons]
      have ih := klasse_foldl w l (if reachB P fs w a then k.schwaecher (lokal P fs mass a) else k)
      have hk : k.rang ≤ (if reachB P fs w a then k.schwaecher (lokal P fs mass a) else k).rang := by
        split
        · rw [TermKlasse.schwaecher_rang]; omega
        · exact Nat.le_refl _
      refine ⟨Nat.le_trans hk ih.1, fun g hg hr => ?_⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · have : (lokal P fs mass g).rang ≤ (if reachB P fs w g then k.schwaecher (lokal P fs mass g) else k).rang := by
          rw [if_pos hr, TermKlasse.schwaecher_rang]; omega
        exact Nat.le_trans this ih.1
      · exact ih.2 g hg hr

/-- **The class of `w` is the weakest local class of its hull**: `endet` for `w` means `endet` for every function it
    reaches. -/
theorem klasse_endet_lokal {w : D.Fn} (h : klasse P fs mass w = .endet) {g : D.Fn} (hg : g ∈ fs)
    (hr : reachB P fs w g = true) : lokal P fs mass g = .endet := by
  have := (klasse_foldl P fs mass w fs .endet).2 g hg hr
  unfold klasse at h
  rw [h] at this
  apply TermKlasse.rang_inj
  simp only [TermKlasse.rang] at this ⊢
  omega

theorem lokal_endet_ewig {g : D.Fn} (h : lokal P fs mass g = .endet) : (befund P g).ewig = false := by
  unfold lokal at h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h4
  simpa using h4

/-- No function `g` reaches holds a `forever`. -/
def ewigFrei (g : D.Fn) : Bool := fs.all fun h => !(reachB P fs g h) || !(befund P h).ewig

/-- The indirect-call gate of `ewigFrei`. -/
def ewigFreiS (n : Nat) : Bool := fs.all fun g => !(D.passt g n) || ewigFrei P fs g

theorem ewigFrei_klasse (hvoll : ∀ g : D.Fn, g ∈ fs) {w : D.Fn} (h : klasse P fs mass w = .endet) :
    ewigFrei P fs w = true := by
  apply List.all_eq_true.2
  intro g _
  cases hr : reachB P fs w g
  · rfl
  · simp only [Bool.not_true, lokal_endet_ewig P fs mass (klasse_endet_lokal P fs mass h (hvoll g) hr),
  Bool.not_false, Bool.or_true]

end Klasse
end Gabbro.Grammatik
