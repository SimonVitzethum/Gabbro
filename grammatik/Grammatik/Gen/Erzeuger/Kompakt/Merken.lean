/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/Merken.lean
  Subject:   THE TABLE, BUILT ONCE PER CONTEXT. `genTK` asks the table of another context again at every bucket that
             needs it; `fuelle` builds the table of every context a body reaches once, children first, keeps it in a
             cache, and answers the oracle from the cache (`orakelM`). Every table in the cache IS the table of
             `genTK` (`fuelle_inv`): the oracle read from a cache that holds only such tables is the oracle of
             `genTK` (`orakelM_eq`), whatever the cache holds, so a table built over it is the table of `genTK`
             (`tafelM_eq`). The cache only saves work; a context it lacks is built where it is asked.
-/
import Grammatik.Gen.Erzeuger.Kompakt.MerkenAusdruck

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D}

/-- A cached table: its context, its bound, the table. -/
structure EintragT (V : Vertrag D) where
  l : Bool
  Γ : Ctx
  Λ : List (Res D)
  n : Nat
  t : List (Eimer V l Γ Λ)

/-- The cache: tables of statements, blocks and end blocks, and expression tables. -/
structure Cache (V : Vertrag D) where
  t : List (EintragT V)
  e : List (EintragE D)

/-- Every table of the cache is the table of `genTK` (of `genEK`) of its context and bound. -/
def CacheOk (c : Cache V) : Prop := (∀ x ∈ c.t, x.t = genTK V x.n x.l x.Γ x.Λ) ∧ CacheEOk c.e

/-- Bucket `i` of the table of a context: from a cached table whose bound reaches `i`, else built. -/
def bucketM (c : Cache V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (i : Nat) : Eimer V l Γ Λ :=
  if i = 0 then ([], [], []) else
  match c.t.findSome? (fun x => if h : x.l = l ∧ x.Γ = Γ ∧ x.Λ = Λ then
      (if i ≤ x.n then some ((castTab h x.t).getD i ([], [], [])) else none) else none) with
  | some e => e
  | none => (genTK V i l Γ Λ).getD i ([], [], [])

theorem bucketM_eq {c : Cache V} (hc : CacheOk c) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (i : Nat) :
    bucketM c l Γ Λ i = (genTK V i l Γ Λ).getD i ([], [], []) := by
  unfold bucketM
  split
  · subst i; rw [genTK_eq]; rfl
  split
  · rename_i e he
    obtain ⟨l₁, x, l₂, _, hx, _⟩ := List.findSome?_eq_some_iff.1 he
    have hxc : x ∈ c.t := by rw [‹c.t = l₁ ++ x :: l₂›]; simp only [List.mem_append, List.mem_cons, true_or, or_true]
    by_cases h : x.l = l ∧ x.Γ = Γ ∧ x.Λ = Λ
    · rw [dif_pos h] at hx
      by_cases hi : i ≤ x.n
      · rw [if_pos hi] at hx
        have := Option.some.inj hx
        rw [← this]
        obtain ⟨x1, x2, x3, x4, xt⟩ := x
        obtain ⟨h1, h2, h3⟩ := h
        simp only at h1 h2 h3 hi hc hxc ⊢
        subst h1 h2 h3
        have := hc.1 _ hxc
        simp only at this
        simp only [castTab]
        rw [this]
        exact genTK_getD_le _ _ _ hi (Nat.le_refl _)
      · rw [if_neg hi] at hx; cases hx
    · rw [dif_neg h] at hx; cases hx
  · rfl

/-- The oracle of bucket `k` of a table of bound `n`, read from the cache. -/
def orakelM (c : Cache V) (n k : Nat) : Orakel V where
  ex := fun Γ' Λ' _ => bucketE c.e Γ' Λ'
  bl := fun l' Γ' Λ' _ i => if i < k ∧ i < n then (bucketM c l' Γ' Λ' i).2.1 else []
  en := fun l' Γ' Λ' _ i => if i < k ∧ i < n then (bucketM c l' Γ' Λ' i).2.2 else []

theorem orakelM_eq {c : Cache V} (hc : CacheOk c) (n k : Nat) : orakelM c n k = orakelK V n k := by
  simp only [orakelM, orakelK, Orakel.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext Γ' Λ' _ i; exact bucketE_eq hc.2 Γ' Λ' i
  all_goals
  · funext l' Γ' Λ' _ i
    rw [bucketM_eq hc]
    rfl

/-- The table of a context of bound `n` over the cache. -/
def tafelM (c : Cache V) (n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Eimer V l Γ Λ) :=
  let Et := (List.range n).map (bucketE c.e Γ Λ)
  buckets ([], [], []) (fun prev k => schritt (orakelM c n k)
    (fun i => if i < n then Et.getD i [] else bucketE c.e Γ Λ i) prev k) n

theorem tafelM_eq {c : Cache V} (hc : CacheOk c) (n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) :
    tafelM c n l Γ Λ = genTK V n l Γ Λ := by
  rw [genTK_eq]
  unfold tafelM
  have hE : (fun i => if i < n then ((List.range n).map (bucketE c.e Γ Λ)).getD i [] else bucketE c.e Γ Λ i) =
      eK Γ Λ := by
    funext i
    split
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      exact bucketE_eq hc.2 Γ Λ i
    · exact bucketE_eq hc.2 Γ Λ i
  simp only
  rw [hE]
  exact buckets_gleich _ _ _ n fun prev k _ => by rw [orakelM_eq hc]

/-- A table of the context with a bound reaching `n` is cached. -/
def hatT (c : Cache V) (n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : Bool :=
  c.t.any fun x => decide (x.l = l ∧ x.Γ = Γ ∧ x.Λ = Λ ∧ n ≤ x.n)

/-- The child contexts a node of bound `n` builds first (only to save work; any list is sound): the keys of
    `knotenKeys'` whose lock may be taken over the resources held (its rank above every held lock), and the contexts
    after a register read and after an `awaits` or `exchange`, of bound `n - 1`. -/
def kinderK (n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (Et : List (List (SE D Γ Λ))) : List (Schl D) :=
  ((if n ≤ 1 then [] else
  ((knotenKeys' n l Γ Λ Et).filter fun k => k.2.2.1.length ≤ Λ.length ||
    match k.2.2.1 with
    | .held L :: _ => Λ.all fun r => match r with | .held M => decide (D.rang M < D.rang L) | _ => true
    | _ => true) ++
  ((Aufz.reg (D := D)).map fun r => (l, D.rtyp r :: Γ, Λ, n - 1)) ++
  ((Aufz.glob (D := D)).map fun g => (l, D.gtyp g :: Γ, Λ, n - 1))).filter fun k => 3 ≤ k.2.2.2)

/-- The contexts whose expressions a node asks besides its own: after a register read, after an exchange. -/
def nebenE (Γ : Ctx) : List Ctx :=
  ((Aufz.reg (D := D)).map fun r => D.rtyp r :: Γ) ++ ((Aufz.glob (D := D)).map fun g => D.gtyp g :: Γ)

theorem fuelleE_fold_ok (n : Nat) (Λ : List (Res D)) :
    ∀ (gs : List Ctx) (e : List (EintragE D)), CacheEOk e → CacheEOk (gs.foldl (fun e Γ' => fuelleE n Γ' Λ e) e)
  | [], _, h => h
  | _ :: gs, _, h => fuelleE_fold_ok n Λ gs _ (fuelleE_ok _ _ _ _ h)

/-- **Fill the cache** with the table of a context of bound `n`: the tables of the contexts its buckets ask for
    first (the keys of the node, each below `n`), then its own over them. -/
def fuelle (V : Vertrag D) (n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (c : Cache V) : Cache V :=
  if hatT c n l Γ Λ then c else
  let c1 : Cache V := ⟨c.t, (nebenE (D := D) Γ).foldl (fun e Γ' => fuelleE (n - 1) Γ' Λ e) (fuelleE (n - 1) Γ Λ c.e)⟩
  let Et := (List.range n).map (bucketE c1.e Γ Λ)
  let c' := (kinderK n l Γ Λ Et).attach.foldl (fun c k =>
    if h : k.1.2.2.2 < n then fuelle V k.1.2.2.2 k.1.1 k.1.2.1 k.1.2.2.1 c else c) c1
  let nah := (kinderK n l Γ Λ Et).filterMap fun k =>
    c'.t.find? fun x => decide (x.l = k.1 ∧ x.Γ = k.2.1 ∧ x.Λ = k.2.2.1)
  let nahE := (nebenE (D := D) Γ).filterMap fun Γ' => c'.e.find? fun x => decide (x.Γ = Γ' ∧ x.Λ = Λ)
  ⟨⟨l, Γ, Λ, n, tafelM ⟨nah ++ c'.t, nahE ++ c'.e⟩ n l Γ Λ⟩ :: c'.t, c'.e⟩
termination_by n
decreasing_by exact h

/-- A new entry built over a local cache of entries of the cache keeps the cache sound. -/
theorem ok_neu {c' : Cache V} (hc' : CacheOk c') (nah : List (EintragT V)) (hn : ∀ y ∈ nah, y ∈ c'.t)
    (nahE : List (EintragE D)) (hnE : ∀ y ∈ nahE, y ∈ c'.e) (n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) :
    CacheOk (V := V) ⟨⟨l, Γ, Λ, n, tafelM ⟨nah ++ c'.t, nahE ++ c'.e⟩ n l Γ Λ⟩ :: c'.t, c'.e⟩ := by
  refine ⟨fun x hx => ?_, hc'.2⟩
  rcases List.mem_cons.1 hx with rfl | hx
  · have hl : CacheOk (V := V) ⟨nah ++ c'.t, nahE ++ c'.e⟩ := ⟨fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · exact hc'.1 y (hn y hy)
      · exact hc'.1 y hy, fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · exact hc'.2 y (hnE y hy)
      · exact hc'.2 y hy⟩
    exact tafelM_eq hl n l Γ Λ
  · exact hc'.1 x hx

theorem fuelle_ok : ∀ (n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (c : Cache V), CacheOk c →
    CacheOk (fuelle V n l Γ Λ c) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro l Γ Λ c hc
  rw [fuelle]
  split
  · exact hc
  · have hfold : ∀ {Et : List (List (SE D Γ Λ))} (ks : List { k // k ∈ kinderK n l Γ Λ Et }) (c : Cache V),
        CacheOk c → CacheOk (ks.foldl (fun c k =>
          if h : k.1.2.2.2 < n then fuelle V k.1.2.2.2 k.1.1 k.1.2.1 k.1.2.2.1 c else c) c) := by
      intro Et ks
      induction ks with
      | nil => intro c hc; exact hc
      | cons k ks ihk =>
        intro c hc
        simp only [List.foldl_cons]
        apply ihk
        split
        · exact ih _ ‹_› _ _ _ _ hc
        · exact hc
    have hc1 : CacheOk (V := V) ⟨c.t, (nebenE (D := D) Γ).foldl (fun e Γ' => fuelleE (n - 1) Γ' Λ e)
        (fuelleE (n - 1) Γ Λ c.e)⟩ :=
      ⟨hc.1, fuelleE_fold_ok (n - 1) Λ _ _ (fuelleE_ok (n - 1) Γ Λ c.e hc.2)⟩
    have hc' := hfold (kinderK n l Γ Λ ((List.range n).map (bucketE
      ((nebenE (D := D) Γ).foldl (fun e Γ' => fuelleE (n - 1) Γ' Λ e) (fuelleE (n - 1) Γ Λ c.e)) Γ Λ))).attach _ hc1
    refine ok_neu hc' _ (fun y hy => ?_) _ (fun y hy => ?_) n l Γ Λ
    · obtain ⟨k, -, hk⟩ := List.mem_filterMap.1 hy
      exact List.mem_of_find?_eq_some hk
    · obtain ⟨k, -, hk⟩ := List.mem_filterMap.1 hy
      exact List.mem_of_find?_eq_some hk

/-- **The bodies of a function by size**, from the filled cache: bucket `k` of the table of bound `n`. -/
def rumpfTK (ok : ∀ f : D.Fn, Rumpf D f → Bool) (f : D.Fn) (n : Nat) : List (List (Rumpf D f)) :=
  let c := fuelle (vertragVon D f) n false (D.params f) (Signatur.anfang D (D.signatur f)) ⟨[], []⟩
  (List.range (n + 1)).map fun k =>
    (bucketM c false (D.params f) (Signatur.anfang D (D.signatur f)) k).2.2.filter (ok f)

/-- **Every body up to the bound has a representative** among the bodies of its function, in the bucket of its own
    size, standing for it. -/
theorem rumpfTK_rep (ok : ∀ f : D.Fn, Rumpf D f → Bool) (f : D.Fn) (n : Nat) (hn : n < unendlich)
    (hok : ∀ b, ok f b = true) (e : Rumpf D f) (he : groesseEnd e ≤ n) :
    ∃ e' : Rumpf D f, e' ∈ (rumpfTK ok f n).getD (groesseEnd e') [] ∧ GlN e' e := by
  obtain ⟨e', h, g⟩ := (genTK_rep n hn false (D.params f) (Signatur.anfang D (D.signatur f))).2.2 e he (by omega)
  refine ⟨e', ?_, g⟩
  have hk : groesseEnd e' ≤ n := Nat.le_trans g.groesse he
  unfold rumpfTK
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  have h0 : CacheOk ({ t := [], e := [] } : Cache (vertragVon D f)) :=
    ⟨fun _ hx => (nomatch hx), fun _ hx => (nomatch hx)⟩
  rw [bucketM_eq (fuelle_ok n false (D.params f) (Signatur.anfang D (D.signatur f)) _ h0)]
  refine List.mem_filter.2 ⟨?_, hok e'⟩
  unfold tabN at h
  rw [genTK_getD_le _ _ _ (Nat.le_refl _) hk]
  exact h

end Gabbro.Grammatik.Gen
