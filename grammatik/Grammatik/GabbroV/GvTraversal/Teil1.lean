module

public import Grammatik.Kern.Semantik.Semantik

@[expose] public section



namespace Gabbro.Grammatik.GabbroV.GvTraversal

open Gabbro.Grammatik

/-! ## 0. The schedule of a `traverse`, as numbers

    (These two facts about `alleIndizes` lived in `CFormenI.lean`, the C correspondence of the
    forms, deleted with the C emitter; they are statements about the model's own schedule.) -/

/-- The indices a `traverse` visits, as numbers: `0, 1, …, count - 1`. -/
theorem alleIndizes_n (n : Int) :
    (alleIndizes n).map Zahl.n = (List.range n.toNat).map (fun k : Nat => (k : Int)) := by
  unfold alleIndizes
  rw [List.map_filterMap]
  have hgen : ∀ (l : List Nat), (∀ k ∈ l, k < n.toNat) →
      l.filterMap (fun (k : Nat) =>
        (if h : ((k : Nat) : Int) ≤ n - 1 then
          some (⟨((k : Nat) : Int), by omega, h⟩ : Zahl 0 (n - 1)) else none).map Zahl.n) =
      l.map (fun k : Nat => (k : Int)) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
        intro hl
        have ha := hl a (List.mem_cons_self ..)
        rw [List.filterMap_cons, dif_pos (by omega)]
        simp only [Option.map_some, List.map_cons]
        rw [ih (fun k hk => hl k (List.mem_cons_of_mem _ hk))]
  exact hgen _ (fun k hk => List.mem_range.mp hk)

theorem alleIndizes_get (n : Int) (j : Nat) (hj : j < (alleIndizes n).length) :
    ((alleIndizes n)[j]).n = j := by
  have h := alleIndizes_n n
  have hj' : j < ((alleIndizes n).map Zahl.n).length := by simpa using hj
  have e1 : ((alleIndizes n).map Zahl.n)[j] = ((alleIndizes n)[j]).n := List.getElem_map ..
  rw [← e1]
  have hj'' : j < ((List.range n.toNat).map (fun k : Nat => (k : Int))).length := by
    rw [← h]; exact hj'
  have e2 : ((alleIndizes n).map Zahl.n)[j] =
      ((List.range n.toNat).map (fun k : Nat => (k : Int)))[j] := by
    simp only [h]
  rw [e2]
  simp only [List.getElem_map, List.getElem_range]


/-! ## 1. The visited set: what "covered" means

    The visited set of one traversal instance is the ghost log of the
    indices its passes were handed, in order. It covers the domain of a
    table with `count n` when every `m < n.toNat` occurs in it.
-/

/-- The visited log covers the domain: every member occurs in it. -/
def BesuchtDeckt (n : Int) (log : List Nat) : Prop :=
  ∀ m, m < n.toNat → m ∈ log

/-- Coverage is monotone in the log: a larger log covers what a
    smaller one covers. -/
theorem besuchtDeckt_mono (n : Int) (log₁ log₂ : List Nat)
    (hsub : ∀ x, x ∈ log₁ → x ∈ log₂) (h : BesuchtDeckt n log₁) :
    BesuchtDeckt n log₂ :=
  fun m hm => hsub m (h m hm)

/-! ## 2. The schedule is exactly the domain

    `Stmt.traverse t inv body` runs
    `traverseLauf … (alleIndizes (D.count t))` (Semantik.lean): the visit
    schedule is fixed before the first pass. What the `RunsLoop*` family
    does not state — membership and at-most-once — holds of this
    schedule, for the corpus loop shapes that have a G form (exporter
    `tr_traverse`, `crates/gabbro-check/src/lean_g.rs`):

    (S-slots) `traverse i over slots of T [by unvisited]`
    (`beispiele/57`: `traverse t over slots of Faden by unvisited`;
    `beispiele/19`, `46`: the same domain over a pointer-typed name
    for `T`). The mode, the `decreases` witness and `touches` are
    static annotations with no form; the invariant travels where it
    translates.

    Without a G form (exporter refusal LG006; coverage there is OPEN,
    see CUTS):
    (S-desc) `traverse opfer over descendants of … by consuming`
    (`beispiele/01`, `09`, `messung/caprock/kapraum`): its domain is a
    chain from a start slot, not the full table.
-/

/-- Every domain member is scheduled: the schedule misses nothing.
    This is the `index in domain` premise in its provable form: a
    scheduled index carries its bounds in its type (`Zahl`), so what
    must be proved is that every member IS scheduled. -/
theorem trav_schedule_vollstaendig (n : Int) (k : Zahl 0 (n - 1)) :
    k ∈ alleIndizes n := by
  have hmlt : k.n.toNat < n.toNat := by
    have h1 := k.lo_le
    have h2 := k.le_hi
    omega
  have hmem : k.n ∈ (alleIndizes n).map Zahl.n := by
    rw [alleIndizes_n n]
    exact List.mem_map.mpr
      ⟨k.n.toNat, List.mem_range.mpr hmlt, by have h1 := k.lo_le; omega⟩
  obtain ⟨k', hk', hkk⟩ := List.mem_map.mp hmem
  obtain ⟨n1, h1, h2⟩ := k'
  obtain ⟨n2, h3, h4⟩ := k
  have h12 : n1 = n2 := hkk
  subst h12
  exact hk'

/-- At most once: no index sits at two positions (`by unvisited`). -/
theorem trav_schedule_injektiv (n : Int) (i j : Nat)
    (hi : i < (alleIndizes n).length) (hj : j < (alleIndizes n).length)
    (heq : ((alleIndizes n)[i]).n = ((alleIndizes n)[j]).n) : i = j := by
  have e1 := alleIndizes_get n i hi
  have e2 := alleIndizes_get n j hj
  omega

/-- Sound: every scheduled index is in range. Proved through the
    construction (the premise is used by inversion over the mapped
    list), not through the value's fields. -/
theorem trav_schedule_bereich (n : Int) (k : Zahl 0 (n - 1))
    (hk : k ∈ alleIndizes n) : k.n.toNat < n.toNat := by
  have hmem : k.n ∈ (alleIndizes n).map Zahl.n :=
    List.mem_map.mpr ⟨k, hk, rfl⟩
  rw [alleIndizes_n n] at hmem
  obtain ⟨m, hmrange, hcast⟩ := List.mem_map.mp hmem
  have hlt : m < n.toNat := List.mem_range.mp hmrange
  omega

variable {D : Deklaration} {V : Vertrag D} {τ : Ty} {Γ : Ctx} {l : Bool}

/-! ## 3. The ghost trace: what one run visited

    `LaufSpur` records, for one `traverseLauf` run, which indices were
    handed to a pass, in order, and how the run ended. It is a ghost:
    every constructor applies the SAME `schritt` to the SAME states as
    `traverseLauf`, with the same outcome; only the visited prefix is
    additionally named. `WeiterSpur` is the leave-free regime: every
    pass continued with the next index.
-/

/-- The visited log of one `traverseLauf` run. -/
inductive LaufSpur (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) :
    List (Wert D τ) → World D → Env D Γ → List (Wert D τ) → Ausgang V l Γ → Prop where
  | invFehlt {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      (h : (inv σ ρ).2 = false) : LaufSpur schritt inv ks σ ρ [] (.logik .schleife)
  | leerOk {σ : World D} {ρ : Env D Γ}
      (h : (inv σ ρ).2 = true) : LaufSpur schritt inv [] σ ρ [] (.ok (inv σ ρ).1 ρ)
  | weiterOk {k : Wert D τ} {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      {σ' : World D} {ρ' : Env D (τ :: Γ)} {besucht : List (Wert D τ)} {aus : Ausgang V l Γ}
      (h : (inv σ ρ).2 = true) (hs : schritt (inv σ ρ).1 (.cons k ρ) = .ok σ' ρ')
      (rest : LaufSpur schritt inv ks σ' ρ'.tail besucht aus) :
      LaufSpur schritt inv (k :: ks) σ ρ (k :: besucht) aus
  | weiterNext {k : Wert D τ} {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      {hl : true = true} {σ' : World D} {ρ' : Env D (τ :: Γ)}
      {besucht : List (Wert D τ)} {aus : Ausgang V l Γ}
      (h : (inv σ ρ).2 = true) (hs : schritt (inv σ ρ).1 (.cons k ρ) = .next hl σ' ρ')
      (rest : LaufSpur schritt inv ks σ' ρ'.tail besucht aus) :
      LaufSpur schritt inv (k :: ks) σ ρ (k :: besucht) aus
  | verlassOk {k : Wert D τ} {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      {hl : true = true} {σ' : World D} {ρ' : Env D (τ :: Γ)}
      (h : (inv σ ρ).2 = true) (hs : schritt (inv σ ρ).1 (.cons k ρ) = .leave hl σ' ρ')
      (hinv : (inv σ' ρ'.tail).2 = true) :
      LaufSpur schritt inv (k :: ks) σ ρ [k] (.ok (inv σ' ρ'.tail).1 ρ'.tail)
  | verlassFehlt {k : Wert D τ} {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      {hl : true = true} {σ' : World D} {ρ' : Env D (τ :: Γ)}
      (h : (inv σ ρ).2 = true) (hs : schritt (inv σ ρ).1 (.cons k ρ) = .leave hl σ' ρ')
      (hinv : (inv σ' ρ'.tail).2 = false) :
      LaufSpur schritt inv (k :: ks) σ ρ [k] (.logik .schleife)
  | abZurueck {k : Wert D τ} {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      {σ' : World D} {v : ErgVal D V.erg}
      (h : (inv σ ρ).2 = true) (hs : schritt (inv σ ρ).1 (.cons k ρ) = .zurueck σ' v) :
      LaufSpur schritt inv (k :: ks) σ ρ [k] (.zurueck σ' v)
  | abGrund {k : Wert D τ} {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      {σ' : World D} {r : Fin V.gruende}
      (h : (inv σ ρ).2 = true) (hs : schritt (inv σ ρ).1 (.cons k ρ) = .why σ' r) :
      LaufSpur schritt inv (k :: ks) σ ρ [k] (.why σ' r)
  | abLogik {k : Wert D τ} {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      {e : Logik D}
      (h : (inv σ ρ).2 = true) (hs : schritt (inv σ ρ).1 (.cons k ρ) = .logik e) :
      LaufSpur schritt inv (k :: ks) σ ρ [k] (.logik e)
  | abHardware {k : Wert D τ} {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      {e : Hardware D}
      (h : (inv σ ρ).2 = true) (hs : schritt (inv σ ρ).1 (.cons k ρ) = .hardware e) :
      LaufSpur schritt inv (k :: ks) σ ρ [k] (.hardware e)

/-- Every run has a trace with the same outcome: the ghost is faithful. -/
theorem trav_lauf_hat_spur (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) (ks : List (Wert D τ)) (σ : World D)
    (ρ : Env D Γ) :
    ∃ (besucht : List (Wert D τ)) (aus : Ausgang V l Γ),
      LaufSpur schritt inv ks σ ρ besucht aus ∧
      traverseLauf schritt inv ks σ ρ = aus := by
  induction ks generalizing σ ρ with
  | nil =>
    cases heq : (inv σ ρ).2 with
    | true => exact ⟨[], _, LaufSpur.leerOk heq, by simp only [traverseLauf, heq, ↓reduceIte]⟩
    | false => exact ⟨[], _, LaufSpur.invFehlt heq, by simp only [traverseLauf, heq, Bool.false_eq_true, ↓reduceIte]⟩
  | cons k ks ih =>
    cases heq : (inv σ ρ).2 with
    | false => exact ⟨[], _, LaufSpur.invFehlt heq, by simp only [traverseLauf, heq, ↓reduceIte]⟩
    | true =>
      cases hs : schritt (inv σ ρ).1 (.cons k ρ) with
      | ok σ' ρ' =>
        obtain ⟨besucht, aus, hspur, hrun⟩ := ih σ' ρ'.tail
        exact ⟨k :: besucht, aus, LaufSpur.weiterOk heq hs hspur,
          by simp only [traverseLauf, heq, Bool.true_eq_false, ↓reduceIte, hs, hrun]⟩
      | next hl σ' ρ' =>
        obtain ⟨besucht, aus, hspur, hrun⟩ := ih σ' ρ'.tail
        exact ⟨k :: besucht, aus, LaufSpur.weiterNext heq hs hspur,
          by simp only [traverseLauf, heq, Bool.true_eq_false, ↓reduceIte, hs, hrun]⟩
      | leave hl σ' ρ' =>
        cases hinv : (inv σ' ρ'.tail).2 with
        | true => exact ⟨[k], _, LaufSpur.verlassOk heq hs hinv,
            by simp only [traverseLauf, heq, Bool.true_eq_false, ↓reduceIte, hs, hinv]⟩
        | false => exact ⟨[k], _, LaufSpur.verlassFehlt heq hs hinv,
            by simp only [traverseLauf, heq, Bool.true_eq_false, ↓reduceIte, hs, hinv, Bool.false_eq_true]⟩
      | zurueck σ' v =>
        exact ⟨[k], _, LaufSpur.abZurueck heq hs, by simp only [traverseLauf, heq, Bool.true_eq_false, ↓reduceIte, hs]⟩
      | why σ' r =>
        exact ⟨[k], _, LaufSpur.abGrund heq hs, by simp only [traverseLauf, heq, Bool.true_eq_false, ↓reduceIte, hs]⟩
      | logik e =>
        exact ⟨[k], _, LaufSpur.abLogik heq hs, by simp only [traverseLauf, heq, Bool.true_eq_false, ↓reduceIte, hs]⟩
      | hardware e =>
        exact ⟨[k], _, LaufSpur.abHardware heq hs, by simp only [traverseLauf, heq, Bool.true_eq_false, ↓reduceIte, hs]⟩

/-- A trace visits only scheduled indices. -/
theorem trav_spur_besucht_im_plan (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) (ks : List (Wert D τ)) (σ : World D)
    (ρ : Env D Γ) (besucht : List (Wert D τ)) (aus : Ausgang V l Γ)
    (hspur : LaufSpur schritt inv ks σ ρ besucht aus) :
    ∀ x ∈ besucht, x ∈ ks := by
  induction hspur with
  | invFehlt h => intro x hx; cases hx
  | leerOk h => intro x hx; cases hx
  | weiterOk h hs rest ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih _ hx')
  | weiterNext h hs rest ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih _ hx')
  | verlassOk h hs hinv =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact List.mem_cons_self ..
    · cases hx'
  | verlassFehlt h hs hinv =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact List.mem_cons_self ..
    · cases hx'
  | abZurueck h hs =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact List.mem_cons_self ..
    · cases hx'
  | abGrund h hs =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact List.mem_cons_self ..
    · cases hx'
  | abLogik h hs =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact List.mem_cons_self ..
    · cases hx'
  | abHardware h hs =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact List.mem_cons_self ..
    · cases hx'

/-- The leave-free regime: every pass continued with the next index. -/
inductive WeiterSpur (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) :
    List (Wert D τ) → World D → Env D Γ → List (Wert D τ) → Ausgang V l Γ → Prop where
  | leer {σ : World D} {ρ : Env D Γ}
      (h : (inv σ ρ).2 = true) : WeiterSpur schritt inv [] σ ρ [] (.ok (inv σ ρ).1 ρ)
  | weiterOk {k : Wert D τ} {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      {σ' : World D} {ρ' : Env D (τ :: Γ)} {besucht : List (Wert D τ)} {aus : Ausgang V l Γ}
      (h : (inv σ ρ).2 = true) (hs : schritt (inv σ ρ).1 (.cons k ρ) = .ok σ' ρ')
      (rest : WeiterSpur schritt inv ks σ' ρ'.tail besucht aus) :
      WeiterSpur schritt inv (k :: ks) σ ρ (k :: besucht) aus
  | weiterNext {k : Wert D τ} {ks : List (Wert D τ)} {σ : World D} {ρ : Env D Γ}
      {hl : true = true} {σ' : World D} {ρ' : Env D (τ :: Γ)}
      {besucht : List (Wert D τ)} {aus : Ausgang V l Γ}
      (h : (inv σ ρ).2 = true) (hs : schritt (inv σ ρ).1 (.cons k ρ) = .next hl σ' ρ')
      (rest : WeiterSpur schritt inv ks σ' ρ'.tail besucht aus) :
      WeiterSpur schritt inv (k :: ks) σ ρ (k :: besucht) aus

/-- A leave-free trace visits every scheduled index: the coverage
    statement for a `by unvisited` traversal without `leave`. -/
theorem weiter_besucht_voll (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) (ks : List (Wert D τ)) (σ : World D)
    (ρ : Env D Γ) (besucht : List (Wert D τ)) (aus : Ausgang V l Γ)
    (hspur : WeiterSpur schritt inv ks σ ρ besucht aus) : besucht = ks := by
  induction hspur with
  | leer h => rfl
  | weiterOk h hs rest ih => rw [ih]
  | weiterNext h hs rest ih => rw [ih]

/-- A run whose every pass continues has a leave-free trace covering
    the schedule. The continuation hypothesis is deliberately strong
    (every pass from every state); see CUTS. -/
theorem trav_ohne_verlasse_weiter (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) (ks : List (Wert D τ)) (σ : World D)
    (ρ : Env D Γ) (hinv : ∀ σ ρ, (inv σ ρ).2 = true)
    (hc : ∀ k σ ρ, k ∈ ks →
      (∃ σ' ρ', schritt σ (.cons k ρ) = .ok σ' ρ') ∨
      (∃ hl σ' ρ', schritt σ (.cons k ρ) = .next hl σ' ρ')) :
    ∃ (besucht : List (Wert D τ)) (aus : Ausgang V l Γ),
      WeiterSpur schritt inv ks σ ρ besucht aus ∧ besucht = ks ∧
      traverseLauf schritt inv ks σ ρ = aus := by
  induction ks generalizing σ ρ with
  | nil =>
    refine ⟨[], _, WeiterSpur.leer (hinv σ ρ), rfl, ?_⟩
    simp only [traverseLauf, hinv σ ρ, ↓reduceIte]
  | cons k ks ih =>
    have hkm : k ∈ k :: ks := List.mem_cons_self ..
    have hc' : ∀ k σ ρ, k ∈ ks →
        (∃ σ' ρ', schritt σ (.cons k ρ) = .ok σ' ρ') ∨
        (∃ hl σ' ρ', schritt σ (.cons k ρ) = .next hl σ' ρ') :=
      fun k σ ρ h => hc k σ ρ (List.mem_cons_of_mem _ h)
    rcases hc k ((inv σ ρ).1) ρ hkm with ⟨σ', ρ', hs⟩ | ⟨hl, σ', ρ', hs⟩
    · obtain ⟨besucht, aus, hspur, heq1, heq2⟩ := ih σ' ρ'.tail hc'
      exact ⟨k :: besucht, aus, WeiterSpur.weiterOk (hinv σ ρ) hs hspur, by rw [heq1],
        by simp only [traverseLauf, hinv σ ρ, Bool.true_eq_false, ↓reduceIte, hs, heq2]⟩
    · obtain ⟨besucht, aus, hspur, heq1, heq2⟩ := ih σ' ρ'.tail hc'
      exact ⟨k :: besucht, aus, WeiterSpur.weiterNext (hinv σ ρ) hs hspur, by rw [heq1],
        by simp only [traverseLauf, hinv σ ρ, Bool.true_eq_false, ↓reduceIte, hs, heq2]⟩

/-- A leave-free trace is a trace. -/
theorem weiter_zu_lauf (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) (ks : List (Wert D τ)) (σ : World D)
    (ρ : Env D Γ) (besucht : List (Wert D τ)) (aus : Ausgang V l Γ)
    (h : WeiterSpur schritt inv ks σ ρ besucht aus) :
    LaufSpur schritt inv ks σ ρ besucht aus := by
  induction h with
  | leer h => exact LaufSpur.leerOk h
  | weiterOk h hs rest ih => exact LaufSpur.weiterOk h hs ih
  | weiterNext h hs rest ih => exact LaufSpur.weiterNext h hs ih

/-! ## 4. Fixture and witnesses

    One table with three slots, written by the passes. `gvSchrittPos`
    writes the pass index and continues (coverage holds);
    `gvSchrittLeave` writes the first slot, then leaves at the second
    (coverage fails with a gap at the third). Both steps change the
    world through `World.schreibSlot`, for every `D`-free reason the
    model offers: the slot value and the trace event.
-/

/-- One signature: no parameters, no answers, no rights. -/
def gvSig : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []
  boden := none

/-- One table with three slots of `0 .. 10`, unguarded, one lock unused. -/
def gvD : Deklaration where
  Tab := Unit
  count := fun _ => 3
  Feld := fun _ => Unit
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => some ()
  Glob := Empty
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Unit
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Empty
  sig := fun e => nomatch e
  sigNr := fun _ => gvSig
  eigner_nie_erzeugt := by intro n t m s h; cases m
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e _ => nomatch e
  agschreibt := fun e _ => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := by intro t h; cases t; simp only [Bool.false_eq_true] at h
  invarianten_gehalten := by intro n i h; cases i
  ggeteilt_bewacht := by intro g h; cases g

/-- The contract the passes run under: writes the table, answers nothing. -/
def gvV : Vertrag gvD where
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  erg := none
  gruende := 0
  haelt := []
  produziert := []
  boden := none

/-- The start world: every slot holds `5`, the trace is empty. -/
def gvW0 : World gvD where
  slots := fun _ _ _ => ⟨5, by omega, by omega⟩
  globs := fun e => nomatch e
  spur := []

/-- The three domain members. -/
def gz0 : Zahl 0 2 := ⟨0, by omega, by omega⟩
def gz1 : Zahl 0 2 := ⟨1, by omega, by omega⟩
def gz2 : Zahl 0 2 := ⟨2, by omega, by omega⟩

/-- The schedule over three slots is the three members. -/
theorem gvKs_eq : alleIndizes 3 = [gz0, gz1, gz2] := by rfl

/-- The invariant holds at every boundary; the world passes through. -/
end Gabbro.Grammatik.GabbroV.GvTraversal
