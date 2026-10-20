/-
  File:      Grammatik/Gen/Abdeckung/Satz/Raum.lean
  Subject:   ANY PROGRAM WITHIN THE BOUNDS HAS ITS CELLS IN THE SPACE. The generator walks de-duplicated body tables
             (`Spez.tabellenD`), so a given program is usually not literally in its stream. But every body of size
             `≤ nb` has a representative of the same summary at a size not larger (`tabellenD_vollst`, from
             `entdoppelt_vollst`), and bodies of the same summary give the same cells and the same verdict (T1,
             `SchluesselZellen.lean`). So a valid program of a member, with bodies `≤ nb`, skeleton size `≤ kmax` and a
             contract variant of size `≤ nc`, puts each of its cells into `RaumGut` (`raumGut_aus`); a single-fault
             program with one bad cell puts that cell into `RaumSchlecht` (`raumSchlecht_aus`). Nothing is evaluated.
-/
import Grammatik.Gen.Abdeckung.Satz.ErzeugtVoll
import Grammatik.Gen.Abdeckung.Satz.SchluesselZellen

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Adaequanz

section

variable {D : Deklaration} [Aufz D] [Zahlen]

/-- `hautT_vollst` for any sizes the bodies sit at. -/
theorem hautT_mem (tbls : List (Σ f : D.Fn, List (List (Rumpf D f)))) (h : Haut D) (c : D.Fn → Nat)
    (hm : ∀ f, h.rumpf f ∈ rumpfS tbls f (c f)) : h ∈ hautT tbls (((Aufz.fn (D := D)).map c).sum) := by
  have hr : (fun f _ => h.rumpf f) ∈ piS (rumpfS tbls) Aufz.fn (((Aufz.fn (D := D)).map c).sum) :=
    mem_piS (L := rumpfS tbls) h.rumpf c Aufz.fn (fun f _ => hm f)
  have hus : (fun f _ => h.unterbricht f) ∈ piS (fun _ => Sz.wahl [false, true]) Aufz.fn 0 := by
    have := mem_piS (L := fun _ : D.Fn => Sz.wahl [false, true]) h.unterbricht (fun _ => 0) Aufz.fn
      (fun f _ => Sz.mem_wahl (by cases hb : h.unterbricht f <;> simp))
    have hz : ((Aufz.fn (D := D)).map fun _ => 0).sum = 0 := summe_null _
    rw [hz] at this
    exact this
  have hm' := Sz.mem_bind
    (F := fun rs => Sz.bind (piS (fun _ => Sz.wahl [false, true]) Aufz.fn) fun us =>
      Sz.pure (⟨fun f => rs f (Aufz.fn_mem f), fun f => us f (Aufz.fn_mem f)⟩ : Haut D))
    hr (Sz.mem_bind hus (Sz.mem_pure _))
  rw [show ((Aufz.fn (D := D)).map c).sum + (0 + 0) = ((Aufz.fn (D := D)).map c).sum by omega] at hm'
  exact hm'

omit [Aufz D] [Zahlen] in
theorem summe_le {l : List D.Fn} {a b : D.Fn → Nat} (h : ∀ f, a f ≤ b f) : (l.map a).sum ≤ (l.map b).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; have := h x; omega

end

/-- **The tables keep a representative of every body**: same summary, size not larger. -/
theorem tabellenD_vollst (z : Spez) (nb : Nat) (treu : Bool) (f : z.deklaration.Fn) (e : Rumpf z.deklaration f)
    (hn : @groesseEnd z.deklaration z.zahlen _ _ _ _ e ≤ nb) (hu : @groesseEnd z.deklaration z.zahlen _ _ _ _ e < unendlich)
    (haus : (treu && e.bodenAbgeleitet != z.bodenSoll f) = false) :
    ∃ k ≤ @groesseEnd z.deklaration z.zahlen _ _ _ _ e, ∃ b ∈ @rumpfS z.deklaration z.aufz (z.tabellenD nb treu) f k,
      @GleicherSchluessel z.deklaration z.aufz z.zahlen f b e := by
  letI : Zahlen := z.zahlen
  let ok : ∀ f : z.deklaration.Fn, Rumpf z.deklaration f → Bool := okFuer false false (List.finRange z.fns.length)
  have hT : z.tabellenD nb treu = (Aufz.fn (D := z.deklaration)).map fun f =>
      (⟨f, entdoppelt Rumpf.schluessel (fun b => treu && b.bodenAbgeleitet != z.bodenSoll f) (rumpfT ok f nb)⟩ :
        Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))) := by
    simp only [Spez.tabellenD, Spez.tabellen, rumpfTab, List.map_map]
    rfl
  have he : e ∈ (rumpfT ok f nb).getD (groesseEnd e) [] := by
    have := rumpfTab_mem ok nb f e hn hu (by simp [ok, okFuer])
    unfold rumpfS rumpfTab at this
    rwa [ofTy_rumpfTab (fun f => rumpfT ok f nb) f] at this
  have hl : groesseEnd e < (rumpfT ok f nb).length := by simp [rumpfT]; omega
  obtain ⟨k, hk, b, hb, hkb⟩ :=
    entdoppelt_vollst Rumpf.schluessel (fun b => treu && b.bodenAbgeleitet != z.bodenSoll f) _ _ hl e he haus
  refine ⟨k, hk, b, ?_, hkb⟩
  unfold rumpfS
  rw [hT, ofTy_rumpfTab (fun f => entdoppelt Rumpf.schluessel
    (fun b => treu && b.bodenAbgeleitet != z.bodenSoll f) (rumpfT ok f nb)) f]
  exact hb

theorem vertragsL_rumpf {z : Spez} {nc : Nat} {h : Haut z.deklaration} {P : Programm z.deklaration}
    (hP : P ∈ z.vertragsL nc h) : P.rumpf = h.rumpf := by
  simp only [Spez.vertragsL, List.mem_cons, List.mem_flatMap, List.mem_append, List.mem_map] at hP
  rcases hP with rfl | ⟨f, _, ⟨n, _, e, _, rfl⟩ | ⟨n, _, e, _, rfl⟩⟩ <;> rfl

theorem vertragsL_mitRumpf {z : Spez} {nc : Nat} {h : Haut z.deklaration} {P : Programm z.deklaration}
    (r : ∀ f, Rumpf z.deklaration f) (hP : P ∈ z.vertragsL nc h) :
    P.mitRumpf r ∈ z.vertragsL nc ⟨r, h.unterbricht⟩ := by
  simp only [Spez.vertragsL, List.mem_cons, List.mem_flatMap, List.mem_append, List.mem_map] at hP ⊢
  rcases hP with rfl | ⟨f, hf, ⟨n, hn, e, he, rfl⟩ | ⟨n, hn, e, he, rfl⟩⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨f, hf, Or.inl ⟨n, hn, e, he, rfl⟩⟩
  · exact Or.inr ⟨f, hf, Or.inr ⟨n, hn, e, he, rfl⟩⟩

theorem einzigSchlecht_iff (l : List Zelle) (x : Zelle) :
    einzigSchlecht l = some x ↔ x ∈ l ∧ x.schlecht = true ∧ ∀ y ∈ l, y.schlecht = true → y = x := by
  unfold einzigSchlecht
  generalize hf : l.filter (·.schlecht) = m
  have hm : ∀ y, y ∈ m ↔ y ∈ l ∧ y.schlecht = true := fun y => by rw [← hf, List.mem_filter]
  match m, hm with
  | [], hm =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro hx hs _
    exact absurd ((hm x).2 ⟨hx, hs⟩) List.not_mem_nil
  | y :: r, hm =>
    simp only
    constructor
    · intro h
      by_cases hr : (r.all (· == y)) = true
      · have h' : some y = some x := by simpa [hr] using h
        cases h'
        refine ⟨((hm x).1 List.mem_cons_self).1, ((hm x).1 List.mem_cons_self).2, fun z hz hzs => ?_⟩
        rcases List.mem_cons.1 ((hm z).2 ⟨hz, hzs⟩) with h1 | h1
        · exact h1
        · simpa using (List.all_eq_true.1 hr) z h1
      · simp [hr] at h
    · rintro ⟨hx, hxs, hall⟩
      have hy : y = x := hall y ((hm y).1 List.mem_cons_self).1 ((hm y).1 List.mem_cons_self).2
      subst hy
      have hr : (r.all (· == y)) = true := List.all_eq_true.2 fun z hz => by
        have := hall z ((hm z).1 (List.mem_cons_of_mem _ hz)).1 ((hm z).1 (List.mem_cons_of_mem _ hz)).2
        simp [this]
      rw [if_pos hr]

/-- The bodies a program's bodies are replaced by: one representative per function from the tables. -/
theorem vertreter (z : Spez) (nb : Nat) (treu : Bool) (h0 : Haut z.deklaration)
    (hn : ∀ f, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ nb)
    (hu : ∀ f, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) < unendlich)
    (haus : ∀ f, (treu && Rumpf.bodenAbgeleitet (h0.rumpf f) != z.bodenSoll f) = false) :
    ∃ (c : z.deklaration.Fn → Nat) (r : ∀ f, Rumpf z.deklaration f),
      (∀ f, c f ≤ @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f)) ∧
      (∀ f, r f ∈ @rumpfS z.deklaration z.aufz (z.tabellenD nb treu) f (c f)) ∧
      (∀ f, @GleicherSchluessel z.deklaration z.aufz z.zahlen f (r f) (h0.rumpf f)) := by
  have hrep := fun f => tabellenD_vollst z nb treu f (h0.rumpf f) (hn f) (hu f) (haus f)
  refine ⟨fun f => Classical.choose (hrep f), fun f => Classical.choose (Classical.choose_spec (hrep f)).2,
    fun f => (Classical.choose_spec (hrep f)).1, fun f => (Classical.choose_spec (Classical.choose_spec (hrep f)).2).1,
    fun f => (Classical.choose_spec (Classical.choose_spec (hrep f)).2).2⟩

/-- **A valid program within the bounds puts its cells into the space.** -/
theorem raumGutIn_aus (z : Spez) (nb kmax nc : Nat) (treu : Bool) {x : Zelle} (h0 : Haut z.deklaration)
    (hn : ∀ f, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ nb)
    (hu : ∀ f, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) < unendlich)
    (haus : ∀ f, (treu && Rumpf.bodenAbgeleitet (h0.rumpf f) != z.bodenSoll f) = false)
    (hk : @groesseHaut z.deklaration z.aufz z.zahlen h0 ≤ kmax)
    {P : Programm z.deklaration} (hP : P ∈ z.vertragsL nc h0) {p : Sperrart × List z.deklaration.Fn}
    (hp : p ∈ z.parameter) (hv : z.gutB P (z.familie p.1) (z.wurzelnVon P p.2) = true)
    (hx : (z.einsatz P p.1 p.2).Hat x) : RaumGutIn z nb kmax nc treu x := by
  letI : Zahlen := z.zahlen
  obtain ⟨c, r, hc, hr, hg⟩ := vertreter z nb treu h0 hn hu haus
  have hgP : ∀ f, GleicherSchluessel (r f) (P.rumpf f) := fun f => by rw [vertragsL_rumpf hP]; exact hg f
  have hvoll : ∀ g : z.deklaration.Fn, g ∈ z.fnListe := List.mem_finRange
  have hls : ∀ L : z.deklaration.Lock, L ∈ z.lockListe := List.mem_finRange
  have hcs : ∀ c : z.deklaration.Tab ⊕ z.deklaration.Glob, c ∈ z.traegerListe := (z.einsatz P p.1 p.2).hcs
  refine ⟨((Aufz.fn (D := z.deklaration)).map c).sum, ?_, ⟨r, h0.unterbricht⟩, hautT_mem _ ⟨r, h0.unterbricht⟩ c hr,
    P.mitRumpf r, vertragsL_mitRumpf r hP, p, hp, ?_, ?_⟩
  · exact Nat.le_trans (summe_le hc) hk
  · rw [← hv]
    exact gs_akzeptiertX P r hgP _ _ _ _ _ hvoll hls hcs
  · exact (gs_alleZellen P r hgP _ _ _ _ _ x).2 hx

/-- **A single-fault program within the bounds with one bad cell puts that cell into the space.** -/
theorem raumSchlechtIn_aus (z : Spez) (nb kmax nc : Nat) (treu : Bool) {x : Zelle} (h0 : Haut z.deklaration)
    (hn : ∀ f, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ nb)
    (hu : ∀ f, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) < unendlich)
    (haus : ∀ f, (treu && Rumpf.bodenAbgeleitet (h0.rumpf f) != z.bodenSoll f) = false)
    (hk : @groesseHaut z.deklaration z.aufz z.zahlen h0 ≤ kmax)
    {P : Programm z.deklaration} (hP : P ∈ z.vertragsL nc h0) {p : Sperrart × List z.deklaration.Fn}
    (hp : p ∈ z.parameter) (c0 : Fin 10) (hv : z.nurB c0 P (z.familie p.1) (z.wurzelnVon P p.2) = true)
    (hx : einzigSchlecht (z.einsatz P p.1 p.2).zellen = some x) : RaumSchlechtIn z nb kmax nc treu x := by
  letI : Zahlen := z.zahlen
  obtain ⟨c, r, hc, hr, hg⟩ := vertreter z nb treu h0 hn hu haus
  have hgP : ∀ f, GleicherSchluessel (r f) (P.rumpf f) := fun f => by rw [vertragsL_rumpf hP]; exact hg f
  have hvoll : ∀ g : z.deklaration.Fn, g ∈ z.fnListe := List.mem_finRange
  have hls : ∀ L : z.deklaration.Lock, L ∈ z.lockListe := List.mem_finRange
  have hcs : ∀ c : z.deklaration.Tab ⊕ z.deklaration.Glob, c ∈ z.traegerListe := (z.einsatz P p.1 p.2).hcs
  refine ⟨((Aufz.fn (D := z.deklaration)).map c).sum, ?_, ⟨r, h0.unterbricht⟩, hautT_mem _ ⟨r, h0.unterbricht⟩ c hr,
    P.mitRumpf r, vertragsL_mitRumpf r hP, p, hp, c0, ?_, ?_⟩
  · exact Nat.le_trans (summe_le hc) hk
  · rw [← hv]
    simp only [Spez.nurB, nurAnB, gs_komp P r hgP _ _ _ _ _ hvoll hls hcs]
    rfl
  · rw [einzigSchlecht_iff] at hx ⊢
    obtain ⟨h1, h2, h3⟩ := hx
    refine ⟨(gs_alleZellen P r hgP _ _ _ _ _ x).2 h1, h2, fun y hy hys => h3 y ?_ hys⟩
    exact (gs_alleZellen P r hgP _ _ _ _ _ y).1 hy

end Gabbro.Grammatik.Gen
