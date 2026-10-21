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
theorem tabellenD_vollst (z : Spez) (nb : Nat) (hnb : nb < unendlich) (f : z.deklaration.Fn) (e : Rumpf z.deklaration f)
    (hn : @groesseEnd z.deklaration z.zahlen _ _ _ _ e ≤ nb) :
    ∃ k ≤ @groesseEnd z.deklaration z.zahlen _ _ _ _ e, ∃ b ∈ @rumpfS z.deklaration z.aufz (z.tabellenD nb) f k,
      @GleicherSchluessel z.deklaration z.aufz z.zahlen f b e := by
  letI : Zahlen := z.zahlen
  obtain ⟨e', he', g⟩ := rumpfTK_rep (fun _ _ => true) f nb hnb (fun _ => rfl) e hn
  have hgs : GleicherSchluessel e' e := schluessel_of_glN g
  have hl : groesseEnd e' < (rumpfTK (fun _ _ => true) f nb).length := by
    have := g.groesse; simp [rumpfTK]; omega
  obtain ⟨k, hk, b, hb, hkb⟩ := entdoppelt_vollst Rumpf.schluessel (fun _ => false) _ _ hl e' he' rfl
  refine ⟨k, by have := g.groesse; omega, b, ?_, hkb.trans hgs⟩
  unfold rumpfS Spez.tabellenD
  rw [ofTy_rumpfTab (fun f => entdoppelt Rumpf.schluessel (fun _ => false) (rumpfTK (fun _ _ => true) f nb)) f]
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

/-- The bodies a program's bodies are replaced by: one representative per function from the tables. -/
theorem vertreter (z : Spez) (nb : Nat) (h0 : Haut z.deklaration)
    (hn : ∀ f, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ nb)
    (hnb : nb < unendlich) :
    ∃ (c : z.deklaration.Fn → Nat) (r : ∀ f, Rumpf z.deklaration f),
      (∀ f, c f ≤ @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f)) ∧
      (∀ f, r f ∈ @rumpfS z.deklaration z.aufz (z.tabellenD nb) f (c f)) ∧
      (∀ f, @GleicherSchluessel z.deklaration z.aufz z.zahlen f (r f) (h0.rumpf f)) := by
  have hrep := fun f => tabellenD_vollst z nb hnb f (h0.rumpf f) (hn f)
  refine ⟨fun f => Classical.choose (hrep f), fun f => Classical.choose (Classical.choose_spec (hrep f)).2,
    fun f => (Classical.choose_spec (hrep f)).1, fun f => (Classical.choose_spec (Classical.choose_spec (hrep f)).2).1,
    fun f => (Classical.choose_spec (Classical.choose_spec (hrep f)).2).2⟩

/-- Bodies of the same summary take the same locks and call the same functions, so every round of the floor relation is
    the same. -/
theorem gs_bodenRunden (z : Spez) (P : Programm z.deklaration) (r : ∀ f, Rumpf z.deklaration f)
    (h : ∀ f, @GleicherSchluessel z.deklaration z.aufz z.zahlen f (r f) (P.rumpf f)) :
    ∀ n f, @Programm.bodenRunden z.deklaration z.aufz (P.mitRumpf r) n f = Programm.bodenRunden P n f := by
  letI : Zahlen := z.zahlen
  have hd : ∀ f, Rumpf.bodenAbgeleitet ((P.mitRumpf r).rumpf f) = Rumpf.bodenAbgeleitet (P.rumpf f) := fun f => by
    simp only [mitRumpf_rumpf, Rumpf.bodenAbgeleitet, gs_sperre (h f)]
  have hc : ∀ f g, ruftDirektB (P.mitRumpf r) f g = ruftDirektB P f g := fun f g => by
    simp only [ruftDirektB, mitRumpf_rumpf]
    exact congrArg (!·) (gs_ruf (h f) g)
  intro n
  induction n with
  | zero => intro f; exact hd f
  | succ n ih =>
    intro f
    have hcf : ruftDirektB (P.mitRumpf r) f = ruftDirektB P f := funext (hc f)
    simp only [Programm.bodenRunden, hd, hcf]
    congr 1
    funext a g
    rw [ih g]

/-- Bodies of the same summary derive the same floors. -/
theorem gs_bodenOk (z : Spez) (P : Programm z.deklaration) (r : ∀ f, Rumpf z.deklaration f)
    (h : ∀ f, @GleicherSchluessel z.deklaration z.aufz z.zahlen f (r f) (P.rumpf f)) :
    z.bodenOk (P.mitRumpf r) = z.bodenOk P := by
  letI : Zahlen := z.zahlen
  simp only [Spez.bodenOk, Programm.bodenP, gs_bodenRunden z P r h]

/-- **A valid program within the bounds puts its cells into the space.** -/
theorem raumGutIn_aus (z : Spez) (nb kmax nc : Nat) {x : Zelle} (h0 : Haut z.deklaration)
    (hn : ∀ f, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ nb)
    (hnb : nb < unendlich)
    (hk : @groesseHaut z.deklaration z.aufz z.zahlen h0 ≤ kmax)
    {P : Programm z.deklaration} (hP : P ∈ z.vertragsL nc h0) {ws : List z.deklaration.Fn}
    (hws : ws ∈ z.parameter) (hax : z.axs = []) (hb : z.bodenOk P = true)
    (hv : z.gutB P z.sperreMax (z.wurzelnVon P ws) = true)
    (hx : (z.einsatz P ws hax hb).Hat x) : RaumGutIn z nb kmax nc x := by
  letI : Zahlen := z.zahlen
  obtain ⟨c, r, hc, hr, hg⟩ := vertreter z nb h0 hn hnb
  have hgP : ∀ f, GleicherSchluessel (r f) (P.rumpf f) := fun f => by rw [vertragsL_rumpf hP]; exact hg f
  have hb' : z.bodenOk (P.mitRumpf r) = true := by rw [gs_bodenOk z P r hgP]; exact hb
  have hvoll : ∀ g : z.deklaration.Fn, g ∈ z.fnListe := List.mem_finRange
  have hls : ∀ L : z.deklaration.Lock, L ∈ z.lockListe := List.mem_finRange
  have hcs : ∀ c : z.deklaration.Tab ⊕ z.deklaration.Glob, c ∈ z.traegerListe := (z.einsatz P ws hax hb).hcs
  refine ⟨((Aufz.fn (D := z.deklaration)).map c).sum, ?_, ⟨r, h0.unterbricht⟩, hautT_mem _ ⟨r, h0.unterbricht⟩ c hr,
    P.mitRumpf r, vertragsL_mitRumpf r hP, ws, hws, hax, hb', ?_, ?_⟩
  · exact Nat.le_trans (summe_le hc) hk
  · rw [← hv]
    exact gs_akzeptiertX P r hgP _ _ _ _ _ hvoll hls hcs
  · exact (gs_alleZellen P r hgP _ _ _ _ _ x).2 hx

/-- **A refused program within the bounds puts itself into the space**: each of its cells in `B` or a good one of `er`. -/
theorem raumSchlechtIn_aus (z : Spez) (nb kmax nc : Nat) (h0 : Haut z.deklaration)
    (hn : ∀ f, @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ nb)
    (hnb : nb < unendlich)
    (hk : @groesseHaut z.deklaration z.aufz z.zahlen h0 ≤ kmax)
    {P : Programm z.deklaration} (hP : P ∈ z.vertragsL nc h0) {ws : List z.deklaration.Fn}
    (hws : ws ∈ z.parameter) (hax : z.axs = []) (hb : z.bodenOk P = true)
    (hv : z.gutB P z.sperreMax (z.wurzelnVon P ws) = false) {er B : List Zelle}
    (hE : gedeckt er B (z.einsatz P ws hax hb).zellen = true) : RaumSchlechtIn z nb kmax nc er B := by
  letI : Zahlen := z.zahlen
  obtain ⟨c, r, hc, hr, hg⟩ := vertreter z nb h0 hn hnb
  have hgP : ∀ f, GleicherSchluessel (r f) (P.rumpf f) := fun f => by rw [vertragsL_rumpf hP]; exact hg f
  have hb' : z.bodenOk (P.mitRumpf r) = true := by rw [gs_bodenOk z P r hgP]; exact hb
  have hvoll : ∀ g : z.deklaration.Fn, g ∈ z.fnListe := List.mem_finRange
  have hls : ∀ L : z.deklaration.Lock, L ∈ z.lockListe := List.mem_finRange
  have hcs : ∀ c : z.deklaration.Tab ⊕ z.deklaration.Glob, c ∈ z.traegerListe := (z.einsatz P ws hax hb).hcs
  refine ⟨((Aufz.fn (D := z.deklaration)).map c).sum, ?_, ⟨r, h0.unterbricht⟩, hautT_mem _ ⟨r, h0.unterbricht⟩ c hr,
    P.mitRumpf r, vertragsL_mitRumpf r hP, ws, hws, hax, hb', ?_, ?_⟩
  · exact Nat.le_trans (summe_le hc) hk
  · rw [← hv]
    exact gs_akzeptiertX P r hgP _ _ _ _ _ hvoll hls hcs
  · rw [← hE]
    exact all_mem_gleich _ (gs_alleZellen P r hgP _ _ _ _ _)

set_option maxRecDepth 200000 in
/-- The number of members, once (the witness files read it instead of deciding it). -/
theorem mitglieder_laenge : mitglieder.length = 371 := by
  simp only [mitglieder, List.length_append]
  decide

end Gabbro.Grammatik.Gen
