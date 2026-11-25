/-
  File:      core/Core/Speicher/Litmus/Kohaerenz.lean
  Subject:   THE COHERENCE GROUP of the RC11 catalogue: CoWW, CoRR, CoRW and CoWR as litmus
             tests with their forbidden and allowed results.

  Source: Batty et al., "Mathematizing C++ Concurrency" (POPL 2011), the four C11 coherence
  requirements; Lahav et al., "Repairing sequential consistency in C/C++11" (PLDI 2017), Def. 1
  (`hb ; eco?` irreflexive); the herd C11 catalogue entries CoWW/CoRR/CoRW/CoWR.
  Modes: forbidden in EVERY mode -- coherence is a language rule for every atomic access, including
  `relaxed`; the forbidden statements quantify over every consistent graph and never assume `sc`.
  Allowed in every mode; the exhibited coherent graph is in fact consistent for every mode.
  Expected: FORBIDDEN for the direction contradicting `hb` (`mo` against `hb` for CoWW, an older
  source for a later read for CoRR, a source after a later write for CoRW, a source before a later
  write for CoWR); ALLOWED for the complementary, `hb`-respecting direction.
-/
module

public import Core.Speicher.Trennung
public import Core.Speicher.Einbettung

@[expose] public section

namespace Gabbro.Core.Speicher

/-! ## The four forbidden outcomes, in every mode -/

/-- **CoWW (write-write coherence) is forbidden.** Two writes `w₁`, `w₂` of one location with
    `hb w₁ w₂` may never stand in `mo w₂ w₁`. Covers `seq_cst`, release/acquire and relaxed alike. -/
def CoWWVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
      ∃ w₁ w₂ : E, G.hb w₁ w₂ ∧ G.mo w₂ w₁

theorem coWW_verboten : CoWWVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, w₁, w₂, hb, mo⟩
  exact hk.kohaerent w₁ w₂ hb (G.eco_von_mo mo)

/-- **CoRR (read-read coherence) is forbidden.** A read `r₂` after `r₁` in `hb` never takes a
    modification-order predecessor of the write that `r₁` took. -/
def CoRRVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
      ∃ r₁ r₂ w₁ w₂ : E,
        G.hb r₁ r₂ ∧ G.rf w₁ r₁ ∧ G.rf w₂ r₂ ∧ G.mo w₂ w₁

theorem coRR_verboten : CoRRVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, r₁, r₂, w₁, w₂, hb, rf₁, rf₂, mo⟩
  have hne : r₂ ≠ w₁ := by
    intro e
    exact hk.kohaerent r₁ r₂ hb (e.symm ▸ (G.eco_von_rf rf₁))
  exact hk.kohaerent r₁ r₂ hb
    ((G.eco_von_rb ⟨w₂, rf₂, mo, hne⟩).tail (Or.inl rf₁))

/-- **CoRW (read-write coherence) is forbidden.** A read `r` before a write `w` of its location
    in `hb` never takes a write that `mo` orders after `w`. -/
def CoRWVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
      ∃ r w w' : E, G.hb r w ∧ G.rf w' r ∧ G.mo w w'

theorem coRW_verboten : CoRWVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, r, w, w', hb, rf, mo⟩
  exact hk.kohaerent r w hb ((G.eco_von_mo mo).tail (Or.inl rf))

/-- **CoWR (write-read coherence) is forbidden.** A write `w` before a read `r` of its location
    in `hb` is never preceded in `mo` by the write that `r` takes. -/
def CoWRVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
      ∃ w r w' : E, G.hb w r ∧ G.rf w' r ∧ G.mo w' w

theorem coWR_verboten : CoWRVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, w, r, w', hb, rf, mo⟩
  have hne : r ≠ w := by
    intro e
    subst r
    exact hk.hb_irrefl w hb
  exact hk.kohaerent w r hb (G.eco_von_rb ⟨w', rf, mo, hne⟩)

/-! ## One coherent graph witnessing all four allowed outcomes -/

/-- The eight events at a single location: thread 0 writes `1`, `2`, reads `2`, writes `4`, reads
    `4`; thread 1 writes `3` and reads `3`; `w0` is the initial write. -/
inductive CoEv where
  | w0
  | a1
  | a2
  | a3
  | a4
  | a5
  | b1
  | b2
  deriving DecidableEq, Repr

open CoEv

def coLab (m : Modus) : CoEv → Etikett Bool Nat
  | w0 => ⟨.schreiben, false, m, 0, 0⟩
  | a1 => ⟨.schreiben, false, m, 0, 1⟩
  | a2 => ⟨.schreiben, false, m, 0, 2⟩
  | a3 => ⟨.lesen, false, m, 2, 0⟩
  | a4 => ⟨.schreiben, false, m, 0, 4⟩
  | a5 => ⟨.lesen, false, m, 4, 0⟩
  | b1 => ⟨.schreiben, false, m, 0, 3⟩
  | b2 => ⟨.lesen, false, m, 3, 0⟩

abbrev coPo (a b : CoEv) : Prop :=
  (a = w0 ∧ b ≠ w0) ∨
  (a = a1 ∧ (b = a2 ∨ b = a3 ∨ b = a4 ∨ b = a5)) ∨
  (a = a2 ∧ (b = a3 ∨ b = a4 ∨ b = a5)) ∨
  (a = a3 ∧ (b = a4 ∨ b = a5)) ∨
  (a = a4 ∧ b = a5) ∨
  (a = b1 ∧ b = b2)

abbrev coRf (a b : CoEv) : Prop := (a = a2 ∧ b = a3) ∨ (a = a4 ∧ b = a5) ∨ (a = b1 ∧ b = b2)

abbrev coMo (a b : CoEv) : Prop :=
  (a = w0 ∧ (b = a1 ∨ b = a2 ∨ b = b1 ∨ b = a4)) ∨
  (a = a1 ∧ (b = a2 ∨ b = b1 ∨ b = a4)) ∨
  (a = a2 ∧ (b = b1 ∨ b = a4)) ∨
  (a = b1 ∧ b = a4)

abbrev coRb (a b : CoEv) : Prop :=
  (a = a3 ∧ (b = b1 ∨ b = a4)) ∨ (a = b2 ∧ b = a4)

/-- One rank that increases along program order, reads-from, modification order and reads-before:
    `w0 < a1 < a2 < a3 < b1 < b2 < a4 < a5`. -/
def coRang : CoEv → Nat
  | w0 => 0
  | a1 => 1
  | a2 => 2
  | a3 => 3
  | b1 => 4
  | b2 => 5
  | a4 => 6
  | a5 => 7

def coGraph (m : Modus) : Graph CoEv Bool Nat := ⟨coLab m, coPo, coRf, coMo⟩

abbrev coSchreibt (m : Modus) (a : CoEv) : Prop := (coLab m a).art.schreibt
abbrev coLiest (m : Modus) (a : CoEv) : Prop := (coLab m a).art.liest

theorem coPo_trans (a b c : CoEv) : (coPo a b ∧ coPo b c) → coPo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem coPo_irrefl (a : CoEv) : ¬ coPo a a := by
  cases a <;> decide

theorem coMo_trans (a b c : CoEv) : (coMo a b ∧ coMo b c) → coMo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem coMo_irrefl (a : CoEv) : ¬ coMo a a := by
  cases a <;> decide

theorem coRf_eindeutig (w w' r : CoEv) : (coRf w r ∧ coRf w' r) → w = w' := by
  cases w <;> cases w' <;> cases r <;> decide

theorem coRf_schreibt (m : Modus) (w r : CoEv) (h : coRf w r) : coSchreibt m w := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial

theorem coRf_liest (m : Modus) (w r : CoEv) (h : coRf w r) : coLiest m r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial

theorem coRf_ort (m : Modus) (w r : CoEv) (h : coRf w r) :
    (coGraph m).ort w = (coGraph m).ort r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem coRf_wert (m : Modus) (w r : CoEv) (h : coRf w r) :
    (coLab m w).geschrieben = (coLab m r).gelesen := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem coMo_schreibt (m : Modus) (a b : CoEv) (h : coMo a b) :
    coSchreibt m a ∧ coSchreibt m b := by
  rcases h with (⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨trivial, trivial⟩

theorem coMo_ort (m : Modus) (a b : CoEv) (h : coMo a b) :
    (coGraph m).ort a = (coGraph m).ort b := by
  rcases h with (⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

theorem coMo_total (m : Modus) (a b : CoEv) (ha : coSchreibt m a) (hb : coSchreibt m b)
    (ho : (coGraph m).ort a = (coGraph m).ort b) (hne : a ≠ b) : coMo a b ∨ coMo b a := by
  cases a <;> cases b <;>
    first
      | decide
      | exact False.elim ha
      | exact False.elim hb
      | exact False.elim (hne rfl)

theorem co_wf (m : Modus) : (coGraph m).Wohlgeformt where
  po_trans := by
    intro a b c hab hbc
    exact coPo_trans a b c ⟨hab, hbc⟩
  po_irrefl := coPo_irrefl
  rf_schreibt := by
    intro w r h
    exact coRf_schreibt m w r h
  rf_liest := by
    intro w r h
    exact coRf_liest m w r h
  rf_ort := by
    intro w r h
    exact coRf_ort m w r h
  rf_wert := by
    intro w r h
    exact coRf_wert m w r h
  rf_eindeutig := by
    intro w w' r h1 h2
    exact coRf_eindeutig w w' r ⟨h1, h2⟩
  mo_schreibt := by
    intro a b h
    exact coMo_schreibt m a b h
  mo_ort := by
    intro a b h
    exact coMo_ort m a b h
  mo_trans := by
    intro a b c hab hbc
    exact coMo_trans a b c ⟨hab, hbc⟩
  mo_irrefl := coMo_irrefl
  mo_total := by
    intro a b ha hb ho hne
    exact coMo_total m a b ha hb ho hne
  rmw_nicht_na := by
    intro a h
    cases a <;> simp only [Graph.istRmw, coGraph, coLab, reduceCtorEq] at h

theorem co_kein_rmw (m : Modus) (u : CoEv) : ¬ (coGraph m).istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, coGraph, coLab, reduceCtorEq] at hu

theorem co_kein_zaun (m : Modus) (a : CoEv) : ¬ (coGraph m).istZaun a := by
  intro ha
  cases a <;> simp only [Graph.istZaun, coGraph, coLab, reduceCtorEq] at ha

theorem coRb_closed (w' r w : CoEv) : (coRf w' r ∧ coMo w' w) → coRb r w := by
  cases w' <;> cases r <;> cases w <;> decide

theorem co_rb {m : Modus} {r w : CoEv} (h : (coGraph m).rb r w) : coRb r w := by
  obtain ⟨w', h1, h2, -⟩ := h
  exact coRb_closed w' r w ⟨h1, h2⟩

theorem coPo_rang (a b : CoEv) : coPo a b → coRang a < coRang b := by
  cases a <;> cases b <;> decide

theorem coRf_rang (a b : CoEv) : coRf a b → coRang a < coRang b := by
  cases a <;> cases b <;> decide

theorem coMo_rang (a b : CoEv) : coMo a b → coRang a < coRang b := by
  cases a <;> cases b <;> decide

theorem coRb_rang (a b : CoEv) : coRb a b → coRang a < coRang b := by
  cases a <;> cases b <;> decide

theorem transGen_rang {E : Type} {r : E → E → Prop} {f : E → Nat}
    (h : ∀ a b, r a b → f a < f b) {a b : E} (t : Relation.TransGen r a b) : f a < f b := by
  induction t with
  | single h1 => exact h _ _ h1
  | tail _ h2 ih => exact Nat.lt_trans ih (h _ _ h2)

theorem coRang_hbSchritt (m : Modus) (a b : CoEv) :
    (coGraph m).hbSchritt a b → coRang a < coRang b := by
  intro h
  rcases h with hpo | hsw
  · exact coPo_rang a b hpo
  · obtain ⟨_, _, _, _, x, hrs, hrf⟩ :=
      Graph.sw_klassisch (co_kein_zaun m a) (co_kein_zaun m b) hsw
    have hax : a = x ∨ coPo a x := Graph.Rs.ohne_rmw (co_kein_rmw m) hrs
    rcases hax with rfl | hpx
    · exact coRf_rang a b hrf
    · exact Nat.lt_trans (coPo_rang a x hpx) (coRf_rang x b hrf)

theorem coRang_hb (m : Modus) {a b : CoEv} (h : (coGraph m).hb a b) : coRang a < coRang b :=
  transGen_rang (coRang_hbSchritt m) h

theorem coRang_ecoSchritt (m : Modus) (a b : CoEv) :
    (coGraph m).ecoSchritt a b → coRang a < coRang b := by
  intro h
  rcases h with hrf | hmo | hrb
  · exact coRf_rang a b hrf
  · exact coMo_rang a b hmo
  · exact coRb_rang a b (co_rb hrb)

theorem coRang_eco (m : Modus) {a b : CoEv} (h : (coGraph m).eco a b) : coRang a < coRang b :=
  transGen_rang (coRang_ecoSchritt m) h

theorem coRang_porf (m : Modus) (a b : CoEv) : (coGraph m).porf a b → coRang a < coRang b := by
  intro h
  rcases h with hpo | hrf
  · exact coPo_rang a b hpo
  · exact coRf_rang a b hrf

theorem coOrt (m : Modus) (a : CoEv) : (coGraph m).ort a = false := by
  cases a <;> rfl

theorem coRang_scb (m : Modus) {a b : CoEv} (h : (coGraph m).scb a b) : coRang a < coRang b := by
  rcases h with hpo | hcross | hbloc | hmo | hrb
  · exact coPo_rang a b hpo
  · obtain ⟨c, d, hac, hneac, hcd, hdb, hnedb⟩ := hcross
    exact False.elim (hneac ((coOrt m a).trans (coOrt m c).symm))
  · exact coRang_hb m hbloc.1
  · exact coMo_rang a b hmo
  · exact coRb_rang a b (co_rb hrb)

theorem coRang_psc (m : Modus) {a b : CoEv} (h : (coGraph m).psc a b) : coRang a < coRang b := by
  obtain ⟨_, _, hscb⟩ := Graph.psc_klassisch (co_kein_zaun m a) (co_kein_zaun m b) h
  exact coRang_scb m hscb

theorem co_konsistent (m : Modus) : (coGraph m).Konsistent where
  wf := co_wf m
  hb_irrefl := by
    intro a h
    exact Nat.lt_irrefl _ (coRang_hb m h)
  kohaerent := by
    intro a b hab he
    exact Nat.lt_asymm (coRang_hb m hab) (coRang_eco m he)
  atomar := by
    intro w u _ _ hu
    exact absurd hu (co_kein_rmw m u)
  psc := by
    intro a h
    exact Nat.lt_irrefl _ (transGen_rang (fun x y hxy => coRang_psc m hxy) h)
  ohneLB := by
    intro a h
    exact Nat.lt_irrefl _ (transGen_rang (fun x y hxy => coRang_porf m x y hxy) h)
  liest_vorher := by
    intro w u _ hu
    exact absurd hu (co_kein_rmw m u)

theorem co_vollstaendig : (coGraph .rlx).Vollstaendig := by
  intro r hr
  cases r with
  | w0 => exact (hr : False).elim
  | a1 => exact (hr : False).elim
  | a2 => exact (hr : False).elim
  | a4 => exact (hr : False).elim
  | b1 => exact (hr : False).elim
  | a3 => exact ⟨a2, Or.inl ⟨rfl, rfl⟩⟩
  | a5 => exact ⟨a4, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | b2 => exact ⟨b1, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-! ## The four allowed outcomes -/

/-- **CoWW allowed:** `hb` and `mo` agree on the two writes. -/
def CoWWErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧ G.Vollstaendig ∧
      ∃ w₁ w₂ : E, G.hb w₁ w₂ ∧ G.mo w₁ w₂

theorem coWW_erlaubt : CoWWErlaubtAussage := by
  have hb : (coGraph .rlx).hb a1 a2 := (coGraph .rlx).hb_von_po (by show coPo a1 a2; decide)
  have mo : (coGraph .rlx).mo a1 a2 := by show coMo a1 a2; decide
  exact ⟨CoEv, Bool, Nat, coGraph .rlx, co_konsistent .rlx, co_vollstaendig, a1, a2, hb, mo⟩

/-- **CoRR allowed:** the later read takes a modification-order successor of the write the earlier
    read took. -/
def CoRRErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧ G.Vollstaendig ∧
      ∃ r₁ r₂ w₁ w₂ : E,
        G.hb r₁ r₂ ∧ G.rf w₁ r₁ ∧ G.rf w₂ r₂ ∧ G.mo w₁ w₂

theorem coRR_erlaubt : CoRRErlaubtAussage := by
  have hb : (coGraph .rlx).hb a3 a5 := (coGraph .rlx).hb_von_po (by show coPo a3 a5; decide)
  have f1 : (coGraph .rlx).rf a2 a3 := by show coRf a2 a3; decide
  have f2 : (coGraph .rlx).rf a4 a5 := by show coRf a4 a5; decide
  have mo : (coGraph .rlx).mo a2 a4 := by show coMo a2 a4; decide
  exact ⟨CoEv, Bool, Nat, coGraph .rlx, co_konsistent .rlx, co_vollstaendig,
    a3, a5, a2, a4, hb, f1, f2, mo⟩

/-- **CoRW allowed:** the source of a read precedes, in `mo`, a write that happens after the read. -/
def CoRWErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧ G.Vollstaendig ∧
      ∃ r w w' : E, G.hb r w ∧ G.rf w' r ∧ G.mo w' w

theorem coRW_erlaubt : CoRWErlaubtAussage := by
  have hb : (coGraph .rlx).hb a3 a4 := (coGraph .rlx).hb_von_po (by show coPo a3 a4; decide)
  have rf : (coGraph .rlx).rf a2 a3 := by show coRf a2 a3; decide
  have mo : (coGraph .rlx).mo a2 a4 := by show coMo a2 a4; decide
  exact ⟨CoEv, Bool, Nat, coGraph .rlx, co_konsistent .rlx, co_vollstaendig,
    a3, a4, a2, hb, rf, mo⟩

/-- **CoWR allowed:** the source of a read follows, in `mo`, a write that happens before the read. -/
def CoWRErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧ G.Vollstaendig ∧
      ∃ w r w' : E, G.hb w r ∧ G.rf w' r ∧ G.mo w w'

theorem coWR_erlaubt : CoWRErlaubtAussage := by
  have hb : (coGraph .rlx).hb a1 a3 := (coGraph .rlx).hb_von_po (by show coPo a1 a3; decide)
  have rf : (coGraph .rlx).rf a2 a3 := by show coRf a2 a3; decide
  have mo : (coGraph .rlx).mo a1 a2 := by show coMo a1 a2; decide
  exact ⟨CoEv, Bool, Nat, coGraph .rlx, co_konsistent .rlx, co_vollstaendig,
    a1, a3, a2, hb, rf, mo⟩

/-- **The coherence group:** the four forbidden outcomes never occur and their coherent
    complements do. This is the single pin root of the group. -/
def KohaerenzLitmusAussage : Prop :=
  CoWWVerbotenAussage ∧ CoWWErlaubtAussage ∧
  CoRRVerbotenAussage ∧ CoRRErlaubtAussage ∧
  CoRWVerbotenAussage ∧ CoRWErlaubtAussage ∧
  CoWRVerbotenAussage ∧ CoWRErlaubtAussage

theorem kohaerenz_litmus : KohaerenzLitmusAussage :=
  ⟨coWW_verboten, coWW_erlaubt, coRR_verboten, coRR_erlaubt,
    coRW_verboten, coRW_erlaubt, coWR_verboten, coWR_erlaubt⟩

end Gabbro.Core.Speicher
