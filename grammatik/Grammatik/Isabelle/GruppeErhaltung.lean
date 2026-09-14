/-
  File:      Grammatik/Isabelle/GruppeErhaltung.lean
  Port of:   beweise/Gruppe_Erhaltung.thy (templates `gruppe.ops` S19 and
              `gruppe.sperrabdruck` S20)

  Part (a): rank order is acyclic -- otherwise the DEADLOCK-FREEDOM of the
  stock is lost, not just the invariant -- plus the converse witness that one
  edge against the order suffices for a cycle. Part (b): the move (`zug`
  locale): the invariant holds at the BEGINNING and the END, the footprint is
  whole INSIDE, and every observable step satisfies the invariant. Part (c):
  the intermediate exit as a counterexample, and the half footprint that is no
  move.

  Adaptations (same content, Lean core without mathlib):
  - Relations are `Nat → Nat → Prop` (Isabelle: sets of pairs); `W ⊆ less_than`
    becomes `∀ a b, W a b → a < b`. Same mathematical content.
  - `acyclic` is defined here (`¬ ∃ x, TrCl W x x`) since Lean core has no
    relation library.
  - The `zug` locale becomes a `structure Zug` over `List Z`; `zs ! i` becomes
    `zs[i]? = some z` (explicit instead of partial). Same premises, same
    conclusion.
-/

namespace Gabbro.Grammatik.Isabelle.GruppeErhaltung

/-! ## Part (a) -- the rank order -/

/-- The transitive closure of a relation on `Nat`. -/
inductive TrCl (W : Nat → Nat → Prop) : Nat → Nat → Prop where
  | base {a b : Nat} (h : W a b) : TrCl W a b
  | step {a b c : Nat} (h : W a b) (t : TrCl W b c) : TrCl W a c

/-- Acyclicity: no state reaches itself. -/
def azyklisch (W : Nat → Nat → Prop) : Prop := ¬ ∃ x, TrCl W x x

/-- A chain along `W` strictly rises in rank. -/
theorem kette_steigt {W : Nat → Nat → Prop}
    (hW : ∀ a b, W a b → a < b) {a b : Nat} (h : TrCl W a b) : a < b := by
  induction h with
  | base h => exact hW _ _ h
  | step h _ ih =>
    have h1 : _ := hW _ _ h
    omega

/-- Rank order is acyclic. (Isabelle: `rangordnung_azyklisch`.) -/
theorem rangordnung_azyklisch {W : Nat → Nat → Prop}
    (hW : ∀ a b, W a b → a < b) : azyklisch W := by
  intro hx
  obtain ⟨x, hxx⟩ := hx
  have hlt := kette_steigt hW hxx
  omega

/-- One edge against the order suffices for a cycle.
    (Isabelle: `eine_kante_gegen_die_ordnung_reicht`.) -/
theorem eine_kante_gegen_die_ordnung_reicht :
    ¬ azyklisch (fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) := by
  intro h
  exact h ⟨0, .step (Or.inl ⟨rfl, rfl⟩) (.base (Or.inr ⟨rfl, rfl⟩))⟩

/-! ## Part (b) -- the move: broken inside, whole outside -/

/-- A move is a nonempty sequence of states with the invariant at the
    beginning and the end and the WHOLE footprint inside -- then nobody else
    can look at the carriers. (Isabelle: `locale zug`.) -/
structure Zug (Z : Type) where
  zs : List Z
  I : Z → Prop
  voll : Nat → Prop
  nichtleer : zs ≠ []
  anfang : ∀ z, zs[0]? = some z → I z
  ende : ∀ z, zs[zs.length - 1]? = some z → I z
  abdruck_innen : ∀ i, 0 < i → i < zs.length - 1 → voll i

/-- Observable is a step exactly when the footprint is NOT held whole --
    then another core can take the locks and look at the carriers together.
    (Isabelle: `zug.beobachtbar`.) -/
def beobachtbar {Z : Type} (g : Zug Z) (i : Nat) : Prop :=
  i < g.zs.length ∧ ¬ g.voll i

/-- THE theorem: at every observable step the invariant holds. The
    intermediate state is allowed because it is invisible.
    (Isabelle: `zug.beobachtbares_gilt`.) -/
theorem beobachtbares_gilt {Z : Type} (g : Zug Z) {i : Nat}
    (h : beobachtbar g i) {z : Z} (hz : g.zs[i]? = some z) : g.I z := by
  obtain ⟨hgrenze, hoffen⟩ := h
  have hrand : i = 0 ∨ i = g.zs.length - 1 := by
    have h1 : 0 < i ∨ i = 0 := by omega
    have h2 : i < g.zs.length - 1 ∨ i = g.zs.length - 1 := by omega
    rcases h1 with h1 | rfl
    · rcases h2 with h2 | h2
      · exfalso
        exact hoffen (g.abdruck_innen i h1 h2)
      · exact Or.inr h2
    · exact Or.inl rfl
  rcases hrand with rfl | rfl
  · exact g.anfang z hz
  · exact g.ende z hz

/-! ## Part (c) -- the intermediate exit, as a counterexample -/

/-- The connecting invariant over two carriers. (Isabelle: `paarig`.) -/
def paarig (z : Nat × Nat) : Prop := z.1 = z.2

/-- The whole move: set the first carrier, then the second.
    (Isabelle: `ganzer_zug`.) -/
def ganzerZug : List (Nat × Nat) := [(0, 0), (1, 0), (1, 1)]

/-- The aborted move: stops after the first step.
    (Isabelle: `abgebrochen`.) -/
def abgebrochen : List (Nat × Nat) := [(0, 0), (1, 0)]

/-- The whole move IS a move. (Isabelle: `ganzer_zug_ist_einer`.) -/
theorem ganzer_zug_ist_einer :
    ∃ g : Zug (Nat × Nat),
      g.zs = ganzerZug ∧ g.I = paarig ∧ g.voll = fun i => i = 1 := by
  refine ⟨⟨ganzerZug, paarig, fun i => i = 1, by decide, ?_, ?_, ?_⟩,
    rfl, rfl, rfl⟩
  · intro z hz
    have h0 : ganzerZug[0]? = some (0, 0) := rfl
    rw [h0] at hz
    have e := Option.some_inj.mp hz
    subst e
    rfl
  · intro z hz
    have h2 : ganzerZug[ganzerZug.length - 1]? = some (1, 1) := rfl
    rw [h2] at hz
    have e := Option.some_inj.mp hz
    subst e
    rfl
  · intro i h1 h2
    have hlen : ganzerZug.length = 3 := rfl
    show i = 1
    omega

/-- The aborted move ends BROKEN. (Isabelle: `zwischenaustritt_bricht`.) -/
theorem zwischenaustritt_bricht : ¬ paarig (1, 0) := by
  unfold paarig
  decide

/-- Its last cell really is the broken one. -/
theorem abgebrochen_letzter :
    abgebrochen[abgebrochen.length - 1]? = some (1, 0) := by
  decide

/-- The aborted move is NO move: its last cell violates the invariant, and
    `ende` is exactly the condition ruling that out.
    (Isabelle: `abgebrochener_ist_kein_zug`.) -/
theorem abgebrochener_ist_kein_zug (f : Nat → Prop) :
    ¬ ∃ g : Zug (Nat × Nat),
      g.zs = abgebrochen ∧ g.I = paarig ∧ g.voll = f := by
  rintro ⟨g, hzs, hI, -⟩
  have hlast : g.zs[g.zs.length - 1]? = some (1, 0) := by
    rw [hzs]
    exact abgebrochen_letzter
  have hende := g.ende (1, 0) hlast
  rw [hI] at hende
  exact zwischenaustritt_bricht hende

/-- A HALF footprint is no move: holding only part of the footprint inside
    makes the step observable by definition -- and then `beobachtbares_gilt`
    no longer covers it but demands the invariant exactly where it is broken.
    (Isabelle: `halber_abdruck_ist_kein_zug`.) -/
theorem halber_abdruck_ist_kein_zug :
    ¬ ∃ g : Zug (Nat × Nat),
      g.zs = ganzerZug ∧ g.I = paarig ∧ g.voll = fun _ => False := by
  rintro ⟨g, hzs, -, hvoll⟩
  have h2 : (1 : Nat) < g.zs.length - 1 := by
    rw [hzs]
    decide
  have hvoll1 := g.abdruck_innen 1 (by decide) h2
  rw [hvoll] at hvoll1
  exact hvoll1

/-! ## Witness: rank chains on a concrete instance -/

/-- Witness: the concrete two-edge relation `{(0,1),(1,0)}` reaches `(0,0)`
    (the cycle), while the singleton `{(0,1)}` is acyclic by rank order. No
    lemma above quantifies over syntax, so the inhabitation obligation is
    vacuous; these are data-level witnesses. -/
theorem rangordnung_zeuge :
    TrCl (fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) 0 0 ∧
    azyklisch (fun a b => a = 0 ∧ b = 1) := by
  constructor
  · exact .step (Or.inl ⟨rfl, rfl⟩) (.base (Or.inr ⟨rfl, rfl⟩))
  · apply rangordnung_azyklisch
    intro a b h
    obtain ⟨rfl, rfl⟩ := h
    decide

/-! ## Bridge

  `SchablonenT5Sem.lean` ties `gruppe.sperrabdruck` to the Lean model: wait
  edges over `Ereignis`, rank chains rise (`kette_steigt` there), no wait
  cycle (`kein_wartezyklus`), and the `locks` footprint shape
  (`sperrabdruck_form`). That file's `kette_steigt`/`kein_wartezyklus` are the
  bridge targets of `kette_steigt`/`rangordnung_azyklisch` here (same
  mathematics, over `Ereignis` traces instead of abstract `Nat` edges).
  Parts (b)/(c) of the move -- invariant at begin/end, no intermediate exit --
  have no counterpart in `execStmt` (stated in that file's CUTS, not repeated
  as a theorem here): to state them would need an invariant parameter the
  statement semantics does not carry. Named, not faked. -/

#print axioms Gabbro.Grammatik.Isabelle.GruppeErhaltung.rangordnung_azyklisch
#print axioms Gabbro.Grammatik.Isabelle.GruppeErhaltung.eine_kante_gegen_die_ordnung_reicht
#print axioms Gabbro.Grammatik.Isabelle.GruppeErhaltung.beobachtbares_gilt
#print axioms Gabbro.Grammatik.Isabelle.GruppeErhaltung.ganzer_zug_ist_einer
#print axioms Gabbro.Grammatik.Isabelle.GruppeErhaltung.zwischenaustritt_bricht
#print axioms Gabbro.Grammatik.Isabelle.GruppeErhaltung.abgebrochener_ist_kein_zug
#print axioms Gabbro.Grammatik.Isabelle.GruppeErhaltung.halber_abdruck_ist_kein_zug
#print axioms Gabbro.Grammatik.Isabelle.GruppeErhaltung.rangordnung_zeuge

end Gabbro.Grammatik.Isabelle.GruppeErhaltung
