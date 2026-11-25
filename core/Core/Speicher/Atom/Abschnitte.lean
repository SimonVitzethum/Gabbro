/-
  File:      core/Core/Speicher/Atom/Abschnitte.lean
  Subject:   LOCK SECTIONS ORDER THEIR PLAIN ACCESSES (MK-04, the graph part of `RennfreiAusLokalAussage`). A lock
             word is accessed only by acquire events (they read it, at least acquire strength) and release events
             (they write it, at least release strength). A WINDOW of a lock is a pair of such events, the release
             after the acquire in program order; every access to a location the lock guards stands inside a window of
             its lock. Two windows of one lock are the same window or one HANDS OVER to the other (the second acquire
             reads from a write of the first release's release sequence), and the accesses inside one window are in
             program order. Under these premises two conflicting accesses one of which is plain are ordered by
             happens-before (`rennfrei_aus_abschnitten`): the first access precedes its release, the release
             synchronises with the next acquire, the next acquire precedes the second access.
             The premises are exactly what the lock protocol of the machine owes (`Maschine/Sperre`: an owner
             change is an update or a release write on the lock word with `ra` strength) and what the checker's lock
             rule owes (every plain access of a guarded location stands in a section). No premise says anything about
             consistency: the argument is an order argument.
-/
module

public import Core.Speicher.Konsistent

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Graph

variable {E Ort Wert : Type} (G : Graph E Ort Wert)

/-- **Race freedom on a set of real accesses**: two conflicting real accesses, one of which is plain, are ordered by
    happens-before. (`Graph.Rennfrei` asks it of all events; the machine's initial writes are no accesses.) -/
def RennfreiAuf (real : E → Prop) : Prop :=
  ∀ a b, real a → real b → G.Konflikt a b → (G.na a ∨ G.na b) → G.hb a b ∨ G.hb b a

/-- **A window of the lock word at location `schloss`**: an acquire event `a` that reads the lock word and an
    release event `b` that writes it, `a` before `b` in program order, both at least release/acquire. -/
structure Fenster (schloss : Ort) (a b : E) : Prop where
  erwerb_liest : G.liest a
  erwerb_stark : (G.modus a).stark
  erwerb_ort : G.ort a = schloss
  frei_schreibt : G.schreibt b
  frei_stark : (G.modus b).stark
  frei_ort : G.ort b = schloss
  po : G.po a b

/-- **The release `b` hands over to the acquire `a`**: `a` reads from a write of the release sequence of `b`. -/
def Uebergabe (b a : E) : Prop := ∃ x, G.Rs b x ∧ G.rf x a

/-- **The lock discipline on a graph** for the guard map `schloss` (the lock word of every guarded location) and the
    real accesses `real`. -/
structure Abschnitte (schloss : Ort → Option Ort) (real : E → Prop) : Prop where
  /-- Every real plain access stands at a guarded location. -/
  geschuetzt : ∀ i, real i → G.na i → ∃ l, schloss (G.ort i) = some l
  /-- Every real access to a guarded location stands inside a window of its lock. -/
  fenster : ∀ i, real i → ∀ l, schloss (G.ort i) = some l →
    ∃ a b, G.Fenster l a b ∧ G.po a i ∧ G.po i b
  /-- Two windows of one lock are the same window or one hands over to the other (mutual exclusion). -/
  ausschluss : ∀ l a₁ b₁ a₂ b₂, G.Fenster l a₁ b₁ → G.Fenster l a₂ b₂ →
    (a₁ = a₂ ∧ b₁ = b₂) ∨ G.Uebergabe b₁ a₂ ∨ G.Uebergabe b₂ a₁
  /-- The accesses inside one window are in program order (a section is sequential code). -/
  innerhalb : ∀ l a b i j, G.Fenster l a b → G.po a i → G.po i b → G.po a j → G.po j b →
    real i → real j → i = j ∨ G.po i j ∨ G.po j i

variable {G}

/-- **Lock sections order their plain accesses**: under the discipline of `Abschnitte`, two conflicting real
    accesses one of which is plain are ordered by happens-before. -/
theorem rennfrei_aus_abschnitten {schloss : Ort → Option Ort} {real : E → Prop}
    (d : G.Abschnitte schloss real) : G.RennfreiAuf real := by
  intro i j hi hj hkonf hna
  obtain ⟨hne, hort, _⟩ := hkonf
  obtain ⟨l, hl⟩ : ∃ l, schloss (G.ort i) = some l := by
    rcases hna with h | h
    · exact d.geschuetzt i hi h
    · obtain ⟨l, hl⟩ := d.geschuetzt j hj h
      exact ⟨l, hort ▸ hl⟩
  have hl' : schloss (G.ort j) = some l := hort ▸ hl
  obtain ⟨a₁, b₁, f₁, p₁, q₁⟩ := d.fenster i hi l hl
  obtain ⟨a₂, b₂, f₂, p₂, q₂⟩ := d.fenster j hj l hl'
  rcases d.ausschluss l a₁ b₁ a₂ b₂ f₁ f₂ with ⟨rfl, rfl⟩ | ⟨x, hrs, hrf⟩ | ⟨x, hrs, hrf⟩
  · rcases d.innerhalb l a₁ b₁ i j f₁ p₁ q₁ p₂ q₂ hi hj with h | h | h
    · exact absurd h hne
    · exact Or.inl (G.hb_von_po h)
    · exact Or.inr (G.hb_von_po h)
  · left
    have sw : G.sw b₁ a₂ := sw_von_klassisch
      ⟨f₁.frei_schreibt, f₁.frei_stark, f₂.erwerb_liest, f₂.erwerb_stark, x, hrs, hrf⟩
    exact G.hb_trans (G.hb_trans (G.hb_von_po q₁) (G.hb_von_sw sw)) (G.hb_von_po p₂)
  · right
    have sw : G.sw b₂ a₁ := sw_von_klassisch
      ⟨f₂.frei_schreibt, f₂.frei_stark, f₁.erwerb_liest, f₁.erwerb_stark, x, hrs, hrf⟩
    exact G.hb_trans (G.hb_trans (G.hb_von_po q₂) (G.hb_von_sw sw)) (G.hb_von_po p₁)

end Graph

end Gabbro.Core.Speicher
