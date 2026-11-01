module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Geteilt.Teil2
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.Interferenz
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
public import Grammatik.Kern.Syntax.Extraktion.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Extraktion
variable {D : Deklaration}

theorem paarTreue_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (Nb : Nebeneinander) (hpaar : ∀ p ∈ paare, Nb p.1 p.2) :
    paarTreue (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare)
      Nb := by
  intro i j hmem
  have hmem' : (i, j) ∈ nebenAus eintritt.length paare := hmem
  obtain ⟨hm, _⟩ := List.mem_filter.mp hmem'
  exact hpaar _ hm

/-- Die Paarrechnung ist paarvollstaendig, sobald die Fassung es ist (`hvoll`)
    und kein deklariertes Paar ausserhalb der Eintritte haengt (`hbound`). -/
theorem paarVoll_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (Nb : Nebeneinander)
    (hvoll : ∀ i j, Nb i j → (i, j) ∈ paare ∨ (j, i) ∈ paare)
    (hbound : ∀ i j, Nb i j → i < eintritt.length ∧ j < eintritt.length) :
    paarVoll (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare)
      Nb := by
  intro i j hnb
  obtain ⟨hi, hj⟩ := hbound i j hnb
  rcases hvoll i j hnb with h | h
  · left
    have h' : (i, j) ∈ nebenAus eintritt.length paare :=
      List.mem_filter.mpr ⟨h, decide_eq_true ⟨hi, hj⟩⟩
    exact h'
  · right
    have h' : (j, i) ∈ nebenAus eintritt.length paare :=
      List.mem_filter.mpr ⟨h, decide_eq_true ⟨hj, hi⟩⟩
    exact h'

/-! ## 9. Die Einspeisung: der errechnete Bau in `geteilt_treu` -/

/-- **Geteilt, errechnet.** Der Pruefer `pruefeUngeteilt` laeuft ueber dem
    errechneten Bau; ein ungeteilter Traeger darin gehoert einem Faden. -/
theorem geteilt_treu_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (fuel : Nat)
    (h : Geteilt.pruefeUngeteilt
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare)
      fuel = true)
    (c : Nat)
    (hmem : c ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).traeger)
    (hu : (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).geteilt c = false)
    (f g : Nat)
    (hf : Geteilt.ErreichtBau
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare) fuel f c)
    (hg : Geteilt.ErreichtBau
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare) fuel g c) :
    f = g :=
  Geteilt.geteilt_treu _ fuel h c hmem hu f g hf hg

/-- **(W5) ueber errechneten Laeufen**, die Form, die `kein_wettlauf`
    verbraucht. -/
theorem ungeteilt_aus_baulauf_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (fuel : Nat) (l : List (Nat × Nat))
    (h : Geteilt.pruefeUngeteilt
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare)
      fuel = true)
    (hl : bauLaufSpiegel
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare) fuel l)
    (c : Nat)
    (hmem : c ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).traeger)
    (hu : (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).geteilt c = false)
    (s₁ s₂ : Nat × Nat) (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l)
    (hg : s₁.2 = s₂.2) (hc : s₁.2 = c) : s₁.1 = s₂.1 :=
  Geteilt.ungeteilt_aus_baulauf _ fuel h l
    ((bauLaufSpiegel_genau _ fuel l).mp hl) c hmem hu s₁ s₂ h₁ h₂ hg hc

#print axioms Gabbro.Grammatik.Extraktion.kantenTreue_aus_bau
#print axioms Gabbro.Grammatik.Extraktion.fussTreue_aus_bau
#print axioms Gabbro.Grammatik.Extraktion.geteilt_treu_aus_bau
#print axioms Gabbro.Grammatik.Extraktion.ungeteilt_aus_baulauf_aus_bau


end Gabbro.Grammatik.Extraktion
