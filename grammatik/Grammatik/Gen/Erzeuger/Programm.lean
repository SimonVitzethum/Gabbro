/-
  File:      Grammatik/Gen/Erzeuger/Programm.lean
  Subject:   The generator of PROGRAMS. A program of the model (`Programm D`) is per function a body that does not
             fall off, a handler flag, a `requires` and an `ensures`, and per invariant its predicate. Two streams:

             * `hautS` -- the SKELETONS (`Haut D`: the bodies and the handler flags), exhaustive by size, with the
               contracts true (`Haut.programm`): the workhorse that reaches the larger sizes. Every body is drawn
               from the table of its function (`genT`), so the generator knows no function by name.
             * `progS` -- ALL programs: the skeleton and, per position, any contract expression of the table of
               its context. The unreduced statement; its size grows with every contract position.

             Both are by exact size and complete: a program of bounded pieces is in the stream of its size
             (`hautS_vollst`, `progS_vollst`).
-/
import Grammatik.Gen.Erzeuger.Knoten

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen]

/-! ## Families over a finite index list -/

/-- The streams of the families `i ↦ x i` over the indices of a list, from the stream `L i` at each index. -/
def piS {ι : Type} [DecidableEq ι] {X : ι → Type} (L : ∀ i, Sz (X i)) :
    (alle : List ι) → Sz (∀ i, i ∈ alle → X i)
  | [] => Sz.pure (fun _ h => absurd h List.not_mem_nil)
  | a :: as => Sz.bind (L a) fun x => Sz.map (fun f => fun i h =>
      if h' : i = a then h' ▸ x else f i ((List.mem_cons.1 h).resolve_left h')) (piS L as)

/-- Completeness of `piS`: a family whose every value is in its stream is in the stream of the summed size. -/
theorem mem_piS {ι : Type} [DecidableEq ι] {X : ι → Type} {L : ∀ i, Sz (X i)} (g : ∀ i, X i) (c : ι → Nat) :
    ∀ (alle : List ι), (∀ i ∈ alle, g i ∈ L i (c i)) → (fun i _ => g i) ∈ piS L alle ((alle.map c).sum) := by
  intro alle
  induction alle with
  | nil =>
    intro _
    simp only [piS, List.map_nil, List.sum_nil]
    have : (fun i (_ : i ∈ ([] : List ι)) => g i) = (fun _ h => absurd h List.not_mem_nil) := by
      funext i h
      exact absurd h List.not_mem_nil
    rw [this]
    exact Sz.mem_pure _
  | cons a as ih =>
    intro h
    simp only [piS, List.map_cons, List.sum_cons]
    have hx := h a List.mem_cons_self
    have hr := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    have hm := Sz.mem_bind (F := fun x => Sz.map (fun f => fun i (h : i ∈ a :: as) =>
        if h' : i = a then h' ▸ x else f i ((List.mem_cons.1 h).resolve_left h')) (piS L as))
      hx (Sz.mem_map (f := fun f => fun i (h : i ∈ a :: as) =>
        if h' : i = a then h' ▸ g a else f i ((List.mem_cons.1 h).resolve_left h')) hr)
    have heq : (fun i (_ : i ∈ a :: as) => g i) = (fun i (h : i ∈ a :: as) =>
        if h' : i = a then h' ▸ g a else (fun i (_ : i ∈ as) => g i) i ((List.mem_cons.1 h).resolve_left h')) := by
      funext i hi
      by_cases h' : i = a
      · subst h'; simp
      · simp [h']
    rw [heq]
    exact hm

theorem summe_null {α : Type} : ∀ l : List α, (l.map fun _ => 0).sum = 0
  | [] => rfl
  | _ :: as => by simp only [List.map_cons, List.sum_cons]; rw [summe_null as]

/-! ## The skeleton -/

/-- The skeleton of a program: the bodies (which do not fall off) and the handler flags. -/
structure Haut (D : Deklaration) where
  rumpf : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f))
  unterbricht : D.Fn → Bool

/-- The program of a skeleton: every contract and invariant true. -/
def Haut.programm (h : Haut D) : Programm D where
  invariante := fun _ => .tru
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := h.rumpf
  unterbricht := h.unterbricht

/-- The skeleton of a program. -/
def _root_.Gabbro.Grammatik.Programm.haut (P : Programm D) : Haut D := ⟨P.rumpf, P.unterbricht⟩

/-- The size of a skeleton: the sizes of the bodies (a handler flag is a free choice). -/
def groesseHaut (h : Haut D) : Nat := (Aufz.fn.map fun f => groesseEnd (h.rumpf f)).sum

/-- The body of a function. -/
abbrev Rumpf (D : Deklaration) (f : D.Fn) : Type :=
  Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f))

/-- The bodies of a function by exact size (the buckets `0 .. n` of its table), kept when `ok` accepts them. -/
def rumpfT (ok : ∀ f : D.Fn, Rumpf D f → Bool) (f : D.Fn) (n : Nat) : List (List (Rumpf D f)) :=
  let t := tabN (genT (vertragVon D f) n n false (D.params f) (Signatur.anfang D (D.signatur f)))
  (List.range (n + 1)).map fun k => (t k).filter (ok f)

/-- The tables of the bodies of every function: built once, read at every size. -/
def rumpfTab (ok : ∀ f : D.Fn, Rumpf D f → Bool) (n : Nat) : List (Σ f : D.Fn, List (List (Rumpf D f))) :=
  Aufz.fn.map fun f => ⟨f, rumpfT ok f n⟩

/-- The bodies of a function by exact size, read from the tables. -/
def rumpfS (tbls : List (Σ f : D.Fn, List (List (Rumpf D f)))) (f : D.Fn) : Sz (Rumpf D f) :=
  fun k => ((ofTy tbls f).headD []).getD k []

/-- **The skeletons of exact size `k`** from the tables of the bodies. -/
def hautT (tbls : List (Σ f : D.Fn, List (List (Rumpf D f)))) : Sz (Haut D) :=
  Sz.bind (piS (rumpfS tbls) Aufz.fn) fun rs =>
    Sz.bind (piS (fun _ => Sz.wahl [false, true]) Aufz.fn) fun us =>
      Sz.pure ⟨fun f => rs f (Aufz.fn_mem f), fun f => us f (Aufz.fn_mem f)⟩

/-- **The skeletons of exact size `k`** with every body of size at most `n` accepted by `ok`. -/
def hautS (ok : ∀ f : D.Fn, Rumpf D f → Bool) (n : Nat) : Sz (Haut D) := hautT (rumpfTab ok n)

/-- **Completeness of the skeletons from tables**: a skeleton whose every body is in its stream is in the stream of
    its size. -/
theorem hautT_vollst (tbls : List (Σ f : D.Fn, List (List (Rumpf D f)))) (h : Haut D)
    (hm : ∀ f, h.rumpf f ∈ rumpfS tbls f (groesseEnd (h.rumpf f))) : h ∈ hautT tbls (groesseHaut h) := by
  have hr : (fun f _ => h.rumpf f) ∈ piS (rumpfS tbls) Aufz.fn (groesseHaut h) := by
    unfold groesseHaut
    exact mem_piS (L := rumpfS tbls) h.rumpf (fun f => groesseEnd (h.rumpf f)) Aufz.fn (fun f _ => hm f)
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
  have : groesseHaut h + (0 + 0) = groesseHaut h := by omega
  rw [this] at hm'
  exact hm'

/-- The entry of a function in the tables of every function is its table. -/
theorem ofTy_rumpfTab (T : ∀ f : D.Fn, List (List (Rumpf D f))) (f : D.Fn) :
    (ofTy (Aufz.fn.map fun f' => (⟨f', T f'⟩ : Σ f : D.Fn, List (List (Rumpf D f)))) f).headD [] = T f := by
  have hall : ∀ x ∈ ofTy (Aufz.fn.map fun f' => (⟨f', T f'⟩ : Σ f : D.Fn, List (List (Rumpf D f)))) f, x = T f := by
    intro x hx
    unfold ofTy at hx
    obtain ⟨p, hp, hpx⟩ := List.mem_filterMap.1 hx
    obtain ⟨f', _, rfl⟩ := List.mem_map.1 hp
    by_cases h : f' = f
    · subst h
      simp at hpx
      exact hpx.symm
    · simp [h] at hpx
  have hne : (⟨f, T f⟩ : Σ f : D.Fn, List (List (Rumpf D f))) ∈
      (Aufz.fn.map fun f' => (⟨f', T f'⟩ : Σ f : D.Fn, List (List (Rumpf D f)))) := List.mem_map.2 ⟨f, Aufz.fn_mem f, rfl⟩
  have hmem := mem_ofTy hne
  cases hl : ofTy (Aufz.fn.map fun f' => (⟨f', T f'⟩ : Σ f : D.Fn, List (List (Rumpf D f)))) f with
  | nil => rw [hl] at hmem; exact absurd hmem List.not_mem_nil
  | cons x xs =>
    have := hall x (by rw [hl]; exact List.mem_cons_self)
    simpa using this

/-- A body the filter accepts, of size at most the bound, is in its stream. -/
theorem rumpfTab_mem (ok : ∀ f : D.Fn, Rumpf D f → Bool) (n : Nat) (f : D.Fn) (e : Rumpf D f)
    (hn : groesseEnd e ≤ n) (hu : groesseEnd e < unendlich) (hok : ok f e = true) :
    e ∈ rumpfS (rumpfTab ok n) f (groesseEnd e) := by
  unfold rumpfS rumpfTab
  rw [ofTy_rumpfTab (fun f => rumpfT ok f n) f]
  unfold rumpfT
  have hk : groesseEnd e < n + 1 := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some]
  exact List.mem_filter.2 ⟨(genT_vollst (vertragVon D f) n n false (D.params f)
    (Signatur.anfang D (D.signatur f))).2.2 e hn hn hu, hok⟩

/-- **Completeness of the skeletons**: a skeleton whose bodies have size at most `n` and are accepted by `ok` is in
    the stream of its size. -/
theorem hautS_vollst (ok : ∀ f : D.Fn, Rumpf D f → Bool) (n : Nat) (h : Haut D)
    (hn : ∀ f, groesseEnd (h.rumpf f) ≤ n) (hu : ∀ f, groesseEnd (h.rumpf f) < unendlich)
    (hok : ∀ f, ok f (h.rumpf f) = true) : h ∈ hautS ok n (groesseHaut h) :=
  hautT_vollst _ h fun f => rumpfTab_mem ok n f (h.rumpf f) (hn f) (hu f) (hok f)

/-! ## Programs with every contract -/

/-- The `requires` of a function by exact size. -/
def reqS (f : D.Fn) (n : Nat) : Sz (Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool) :=
  tyS (tab (genE n n (D.params f) (Signatur.anfang D (D.signatur f)))) .bool

/-- The `ensures` of a function by exact size. -/
def ensS (f : D.Fn) (n : Nat) : Sz (Expr D (ErgCtx (D.params f) (D.erg f)) (vertragVon D f).ende .bool) :=
  tyS (tab (genE n n (ErgCtx (D.params f) (D.erg f)) (vertragVon D f).ende)) .bool

/-- The predicate of an invariant by exact size. -/
def invS (i : D.Inv) (n : Nat) : Sz (Expr D [] (invSicht D i) .bool) :=
  tyS (tab (genE n n [] (invSicht D i))) .bool

/-- The size of a program: the skeleton and every contract and invariant. -/
def groesseProg (P : Programm D) : Nat :=
  groesseHaut P.haut + (Aufz.inv.map fun i => groesseExpr (P.invariante i)).sum +
    (Aufz.fn.map fun f => groesseExpr (P.requires f) + groesseExpr (P.ensures f)).sum

/-- **ALL programs of exact size `k`**: the skeleton (bodies of size at most `nb`) and every contract and invariant
    of size at most `nc`. -/
def progS (nb nc : Nat) : Sz (Programm D) :=
  Sz.bind (hautS (fun _ _ => true) nb) fun h =>
    Sz.bind (piS (fun i => invS i nc) Aufz.inv) fun is =>
      Sz.bind (piS (fun f => reqS f nc) Aufz.fn) fun rs =>
        Sz.bind (piS (fun f => ensS f nc) Aufz.fn) fun es =>
          Sz.pure { invariante := fun i => is i (Aufz.inv_mem i), requires := fun f => rs f (Aufz.fn_mem f),
                    ensures := fun f => es f (Aufz.fn_mem f), rumpf := h.rumpf, unterbricht := h.unterbricht }

theorem le_summe {α : Type} {l : List α} {a : α} (f : α → Nat) (h : a ∈ l) : f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h; simp only [List.map_cons, List.sum_cons]; omega

theorem summe_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; omega

/-- **Completeness of the programs**: a program whose bodies have size at most `nb` and whose contracts have size
    at most `nc` is in the stream of its size. -/
theorem progS_vollst (nb nc : Nat) (P : Programm D) (hb : ∀ f, groesseEnd (P.rumpf f) ≤ nb)
    (hc : ∀ f, groesseExpr (P.requires f) ≤ nc ∧ groesseExpr (P.ensures f) ≤ nc)
    (hi : ∀ i, groesseExpr (P.invariante i) ≤ nc) (hu : groesseProg P < unendlich) :
    P ∈ progS nb nc (groesseProg P) := by
  have hH : groesseHaut P.haut ≤ groesseProg P := by unfold groesseProg; omega
  have hI : (Aufz.inv.map fun i => groesseExpr (P.invariante i)).sum ≤ groesseProg P := by
    unfold groesseProg; omega
  have hF : (Aufz.fn.map fun f => groesseExpr (P.requires f) + groesseExpr (P.ensures f)).sum ≤ groesseProg P := by
    unfold groesseProg; omega
  have hh : P.haut ∈ hautS (fun _ _ => true) nb (groesseHaut P.haut) :=
    hautS_vollst (fun _ _ => true) nb P.haut hb
      (fun f => Nat.lt_of_le_of_lt (Nat.le_trans (le_summe (fun f => groesseEnd (P.rumpf f)) (Aufz.fn_mem f)) hH) hu)
      (fun _ => rfl)
  have his : (fun i _ => P.invariante i) ∈ piS (fun i => invS i nc) Aufz.inv
      ((Aufz.inv.map fun i => groesseExpr (P.invariante i)).sum) := by
    refine mem_piS (L := fun i => invS i nc) P.invariante (fun i => groesseExpr (P.invariante i)) Aufz.inv ?_
    intro i _
    have hlt : groesseExpr (P.invariante i) < unendlich :=
      Nat.lt_of_le_of_lt (Nat.le_trans (le_summe (fun i => groesseExpr (P.invariante i)) (Aufz.inv_mem i)) hI) hu
    exact mem_tyS (genE_vollst nc nc [] (invSicht D i) _ (P.invariante i) (hi i) (hi i) hlt)
  have hreq : (fun f _ => P.requires f) ∈ piS (fun f => reqS f nc) Aufz.fn
      ((Aufz.fn.map fun f => groesseExpr (P.requires f)).sum) := by
    refine mem_piS (L := fun f => reqS f nc) P.requires (fun f => groesseExpr (P.requires f)) Aufz.fn ?_
    intro f _
    have hlt : groesseExpr (P.requires f) < unendlich := by
      have := le_summe (fun f => groesseExpr (P.requires f) + groesseExpr (P.ensures f)) (Aufz.fn_mem f)
      omega
    exact mem_tyS (genE_vollst nc nc _ _ _ (P.requires f) (hc f).1 (hc f).1 hlt)
  have hens : (fun f _ => P.ensures f) ∈ piS (fun f => ensS f nc) Aufz.fn
      ((Aufz.fn.map fun f => groesseExpr (P.ensures f)).sum) := by
    refine mem_piS (L := fun f => ensS f nc) P.ensures (fun f => groesseExpr (P.ensures f)) Aufz.fn ?_
    intro f _
    have hlt : groesseExpr (P.ensures f) < unendlich := by
      have := le_summe (fun f => groesseExpr (P.requires f) + groesseExpr (P.ensures f)) (Aufz.fn_mem f)
      omega
    exact mem_tyS (genE_vollst nc nc _ _ _ (P.ensures f) (hc f).2 (hc f).2 hlt)
  have hm := Sz.mem_bind (F := fun h => Sz.bind (piS (fun i => invS i nc) Aufz.inv) fun is =>
        Sz.bind (piS (fun f => reqS f nc) Aufz.fn) fun rs =>
          Sz.bind (piS (fun f => ensS f nc) Aufz.fn) fun es =>
            Sz.pure ({ invariante := fun i => is i (Aufz.inv_mem i), requires := fun f => rs f (Aufz.fn_mem f),
                       ensures := fun f => es f (Aufz.fn_mem f), rumpf := h.rumpf,
                       unterbricht := h.unterbricht } : Programm D))
    hh (Sz.mem_bind his (Sz.mem_bind hreq (Sz.mem_bind hens (Sz.mem_pure _))))
  have hs : groesseProg P = groesseHaut P.haut + ((Aufz.inv.map fun i => groesseExpr (P.invariante i)).sum +
      (((Aufz.fn.map fun f => groesseExpr (P.requires f)).sum + ((Aufz.fn.map fun f => groesseExpr (P.ensures f)).sum +
        0)) + 0)) := by
    unfold groesseProg
    rw [summe_add]
    omega
  rw [hs]
  exact hm

end Gabbro.Grammatik.Gen
