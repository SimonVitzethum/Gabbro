/-
  Body-table representatives preserve structural summaries and cells. Their full verification verdict is not determined by that summary.
-/
module
public import Grammatik.Gen.Abdeckung.Satz.ErzeugtVoll
public import Grammatik.Gen.Abdeckung.Satz.SchluesselZellen
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
      (fun f _ => Sz.mem_wahl (by cases hb : h.unterbricht f <;> simp only [List.mem_cons, Bool.false_eq_true, List.not_mem_nil, or_self, or_false, Bool.true_eq_false, or_true]))
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
  | nil => simp only [List.map_nil, List.sum_nil, Std.le_refl]
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
    have := g.groesse; simp only [rumpfTK, List.filter_true, List.length_map, List.length_range, gt_iff_lt]; omega
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


set_option maxRecDepth 200000 in
/-- The number of members, once (the witness files read it instead of deciding it). -/
theorem mitglieder_laenge : mitglieder.length = 373 := by
  simp only [mitglieder, List.length_append]
  decide

end Gabbro.Grammatik.Gen
