module

public import Gabbro.Body
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Order.Lattice
public import Gabbro.Sicherheit.Ausdruck.Teil3

@[expose] public section

namespace Gabbro.Sicherheit
open Gabbro.Body

set_option linter.unusedSectionVars false in
theorem schluss_sicher_chainFrom (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (c)
    (hd)
    (x)
    (via)
    (cnt)
    (Δ : Lokal)
    (s : State)
    (sh : Shape)
    (ih_schluss_sicher_hd : ∀ (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ), ∀ (Δ : Lokal), ∀ (s : State), ∀ (sh : Shape), WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ hd = some sh → ∃ v, eval s hd = some v ∧ v.hasShape sh = true)
    (ih_schluss_sicher_x : ∀ (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ), ∀ (Δ : Lokal), ∀ (s : State), ∀ (sh : Shape), WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ x = some sh → ∃ v, eval s x = some v ∧ v.hasShape sh = true)
    : WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ (.chainFrom c hd x via cnt : Expr) = some sh → ∃ v, eval s (.chainFrom c hd x via cnt : Expr) = some v ∧ v.hasShape sh = true :=
  by
  have ihh := ih_schluss_sicher_hd D Γ hD
  have ihx := ih_schluss_sicher_x D Γ hD
  intro hw hl hk h
  simp only [schluss] at h
  split at h
  · rename_i sx hh hx hvia
    split at h
    · rename_i hzz
      cases h
      obtain ⟨vh, hvh, hvhs⟩ := ihh Δ s _ hw hl hk hh
      obtain ⟨vx, hvx, hvxs⟩ := ihx Δ s _ hw hl hk hx
      obtain ⟨t, rfl⟩ := zahl_some_int hzz hvxs
      rcases Value.hasShape_opt_true vh hvhs with rfl | ⟨m, rfl⟩
      · simp only [eval, hvh, hvx, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
      · obtain ⟨b, hb⟩ := chase_bool s.world c via t (fun k => hk c via k hvia) cnt.toNat m
        simp only [eval, hvh, hvx, hb, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

set_option linter.unusedSectionVars false in
theorem schluss_sicher_hasShape (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (n)
    (sh')
    (Δ : Lokal)
    (s : State)
    (sh : Shape)
    : WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ (.hasShape n sh' : Expr) = some sh → ∃ v, eval s (.hasShape n sh' : Expr) = some v ∧ v.hasShape sh = true :=
  by
  intro _ _ _ h
  simp only [schluss] at h; cases h
  exact ⟨_, rfl, by simp only [Value.hasShape]⟩

set_option linter.unusedSectionVars false in
theorem schluss_sicher_wrapTo (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (b)
    (sg)
    (a)
    (Δ : Lokal)
    (s : State)
    (sh : Shape)
    (ih_schluss_sicher_a : ∀ (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ), ∀ (Δ : Lokal), ∀ (s : State), ∀ (sh : Shape), WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ a = some sh → ∃ v, eval s a = some v ∧ v.hasShape sh = true)
    : WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ (.wrapTo b sg a : Expr) = some sh → ∃ v, eval s (.wrapTo b sg a : Expr) = some v ∧ v.hasShape sh = true :=
  by
  have ih := ih_schluss_sicher_a D Γ hD
  intro hw hl hk h
  simp only [schluss] at h
  split at h
  · rename_i sa ha
    split at h
    · rename_i hz
      cases h
      obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
      obtain ⟨n, rfl⟩ := zahl_some_int hz hvs
      simp only [eval, hv, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

mutual
/-- Der Sicherheitssatz fuer Ausdruecke. **BEWEIST NICHT**, dass der Pruefer in
    `gabbro-check` dasselbe rechnet wie `schluss` -- das ist die Naht (`W16`), und sie
    steht in keiner Zeile hier. Er beweist: WENN ein Pruefer so rechnet, DANN bleibt kein
    angenommener Ausdruck stecken. -/
theorem schluss_sicher (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ) :
    ∀ (e : Expr) (Δ : Lokal) (s : State) (sh : Shape),
      WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world →
      schluss D Δ e = some sh →
      ∃ v, eval s e = some v ∧ v.hasShape sh = true
  | .lit v, Δ, s, sh => by
      intro _ _ _ h
      exact ⟨v, rfl, literalShape_sicher v sh h⟩
  | .name n, Δ, s, sh => by
      intro _ hl _ h
      exact ⟨_, rfl, hl n sh h⟩
  | .global g, Δ, s, sh =>
      schluss_sicher_global (D := D) (Γ := Γ) (hD := hD) (g := g) (Δ := Δ) (s := s) (sh := sh)
  | .place c i f, Δ, s, sh =>
      schluss_sicher_place (D := D) (Γ := Γ) (hD := hD) (c := c) (i := i) (f := f) (Δ := Δ) (s := s) (sh := sh) (ih_schluss_sicher_i := fun D Γ hD => schluss_sicher D Γ hD i)
  | .fieldOf c f, Δ, s, sh =>
      schluss_sicher_fieldOf (D := D) (Γ := Γ) (hD := hD) (c := c) (f := f) (Δ := Δ) (s := s) (sh := sh)
  | .un op a, Δ, s, sh =>
      schluss_sicher_un (D := D) (Γ := Γ) (hD := hD) (op := op) (a := a) (Δ := Δ) (s := s) (sh := sh) (ih_schluss_sicher_a := fun D Γ hD => schluss_sicher D Γ hD a)
  | .bin op a b, Δ, s, sh =>
      schluss_sicher_bin (D := D) (Γ := Γ) (hD := hD) (op := op) (a := a) (b := b) (Δ := Δ) (s := s) (sh := sh) (ih_schluss_sicher_a := fun D Γ hD => schluss_sicher D Γ hD a) (ih_schluss_sicher_b := fun D Γ hD => schluss_sicher D Γ hD b)
  | .someOf a, Δ, s, sh =>
      schluss_sicher_someOf (D := D) (Γ := Γ) (hD := hD) (a := a) (Δ := Δ) (s := s) (sh := sh) (ih_schluss_sicher_a := fun D Γ hD => schluss_sicher D Γ hD a)
  | .forallSlots v n b, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD b
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i hb
        cases h
        obtain ⟨t, ht⟩ := allBelow_bool _ n.toNat (quant_rumpf D Γ ih Δ s n hw hl hk hb)
        simp only [eval, ht, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | .existsSlots v n b, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD b
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i hb
        cases h
        obtain ⟨t, ht⟩ := anyBelow_bool _ n.toNat (quant_rumpf D Γ ih Δ s n hw hl hk hb)
        simp only [eval, ht, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | .reaches c a z via cnt, Δ, s, sh =>
      schluss_sicher_reaches (D := D) (Γ := Γ) (hD := hD) (c := c) (a := a) (z := z) (via := via) (cnt := cnt) (Δ := Δ) (s := s) (sh := sh) (ih_schluss_sicher_a := fun D Γ hD => schluss_sicher D Γ hD a) (ih_schluss_sicher_z := fun D Γ hD => schluss_sicher D Γ hD z)
  | .chainFrom c hd x via cnt, Δ, s, sh =>
      schluss_sicher_chainFrom (D := D) (Γ := Γ) (hD := hD) (c := c) (hd := hd) (x := x) (via := via) (cnt := cnt) (Δ := Δ) (s := s) (sh := sh) (ih_schluss_sicher_hd := fun D Γ hD => schluss_sicher D Γ hD hd) (ih_schluss_sicher_x := fun D Γ hD => schluss_sicher D Γ hD x)
  | .hasShape n sh', Δ, s, sh =>
      schluss_sicher_hasShape (D := D) (Γ := Γ) (hD := hD) (n := n) (sh' := sh') (Δ := Δ) (s := s) (sh := sh)
  | .wrapTo b sg a, Δ, s, sh =>
      schluss_sicher_wrapTo (D := D) (Γ := Γ) (hD := hD) (b := b) (sg := sg) (a := a) (Δ := Δ) (s := s) (sh := sh) (ih_schluss_sicher_a := fun D Γ hD => schluss_sicher D Γ hD a)
  | .tagOf t p, Δ, s, sh => by
      intro _ _ _ h
      cases p <;> simp only [schluss, reduceCtorEq] at h
  | .recOf args, Δ, s, sh => by
      intro hw hl hk h
      simp only [schluss] at h
      cases hs : schlussAll D Δ args with
      | none => simp only [hs, Option.map_none, reduceCtorEq] at h
      | some ss =>
          simp only [hs, Option.map_some, Option.some.injEq] at h
          subst sh
          obtain ⟨vs, he, hlen, hf⟩ := schlussAll_sicher D Γ hD args Δ s ss hw hl hk hs
          exact ⟨.record vs, by simp only [eval_recOf, he, Option.map_some], by
            simp [hlen, hf]⟩
  | .recGet base idx, Δ, s, sh => by
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i ss hb
        obtain ⟨v, he, hv⟩ := schluss_sicher D Γ hD base Δ s (.record ss) hw hl hk hb
        obtain ⟨vs, rfl, _, hf⟩ := Value.hasShape_rec_true v ss hv
        obtain ⟨field, hg, hfield⟩ := fieldsHaveShape_get vs ss idx sh hf h
        exact ⟨field, by rw [eval_recGet s base vs idx he, hg], hfield⟩
      · cases h
  | .recSet base idx val, Δ, s, sh => by
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i ss fieldShape hb hval
        split at h
        · rename_i hi
          cases h
          obtain ⟨v, he, hv⟩ := schluss_sicher D Γ hD base Δ s (.record ss) hw hl hk hb
          obtain ⟨vs, rfl, hlen, hf⟩ := Value.hasShape_rec_true v ss hv
          obtain ⟨field, hev, hfield⟩ := schluss_sicher D Γ hD val Δ s fieldShape hw hl hk hval
          have hiv : idx < vs.length := by omega
          refine ⟨.record (vs.set idx field), eval_recSet s base val vs field idx he hev hiv, ?_⟩
          have hf' := fieldsHaveShape_setBoth vs ss idx field fieldShape hf hfield
          simp [List.length_set, hlen, hf']
        · cases h
      · cases h
termination_by structural e _ _ _ => e

/-- The safety induction follows the same field-list recursion as construction. -/
theorem schlussAll_sicher (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ) :
    ∀ (es : List Expr) (Δ : Lokal) (s : State) (ss : List Shape),
      WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world →
      schlussAll D Δ es = some ss →
      ∃ vs, evalAll s es = some vs ∧ vs.length = ss.length ∧
        Value.fieldsHaveShape vs ss = true
  | [], Δ, s, ss => by
      intro _ _ _ h
      simp only [schlussAll, Option.some.injEq] at h
      subst ss
      exact ⟨[], rfl, rfl, Value.fieldsHaveShape_nil_nil⟩
  | e :: es, Δ, s, ss => by
      intro hw hl hk h
      simp only [schlussAll] at h
      cases he : schluss D Δ e with
      | none => simp only [he, reduceCtorEq] at h
      | some sh =>
          cases ht : schlussAll D Δ es with
          | none => simp only [he, ht, reduceCtorEq] at h
          | some shapes =>
              simp only [he, ht, Option.some.injEq] at h
              subst ss
              obtain ⟨v, hev, hv⟩ := schluss_sicher D Γ hD e Δ s sh hw hl hk he
              obtain ⟨vs, hes, hlen, hf⟩ := schlussAll_sicher D Γ hD es Δ s shapes hw hl hk ht
              exact ⟨v :: vs, by simp only [evalAll, hev, hes], by
                simp only [List.length_cons, hlen], by
                simp only [Value.fieldsHaveShape_cons_cons, hv, hf, Bool.true_and]⟩
termination_by structural es _ _ _ => es
end

/-- The checker with a carried option target bound is still safe: what it accepts
    evaluates, and to a value of the computed shape. For every form but `someOf`
    this is `schluss_sicher` through the delegation; for `someOf` the inner value
    is a number by `schluss_sicher`, hence `present`, hence `.opt`. The bound
    itself leaves no trace in the shape -- `Shape.opt` carries none (Fund 2) --
    it only decides acceptance. -/
theorem schlussMitZiel_sicher (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (ziel : Option (Int × Int)) (e : Expr) (Δ : Lokal) (s : State) (sh : Shape)
    (hw : WF Γ s.world) (hl : WFL Δ s.local') (hk : KettenWohlgeformt D s.world)
    (h : schlussMitZiel D ziel Δ e = some sh) :
    ∃ v, eval s e = some v ∧ v.hasShape sh = true := by
  cases e with
  | someOf a =>
    simp only [schlussMitZiel] at h
    split at h
    · rename_i sa ha
      cases ziel with
      | none =>
        simp only [somePasst] at h
        split at h
        · rename_i hz
          cases h
          obtain ⟨v, hv, hvs⟩ := schluss_sicher D Γ hD a Δ s _ hw hl hk ha
          obtain ⟨n, rfl⟩ := zahl_some_int hz hvs
          simp only [eval, hv, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
        · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
      | some bh =>
        obtain ⟨lo, hi⟩ := bh
        cases sa with
        | int =>
          simp only [somePasst] at h
          cases h
        | bool =>
          simp only [somePasst] at h
          cases h
        | opt =>
          simp only [somePasst] at h
          cases h
        | intIn lo' hi' =>
          simp only [somePasst] at h
          split at h
          · rename_i hs
            cases h
            obtain ⟨v, hv, hvs⟩ := schluss_sicher D Γ hD a Δ s _ hw hl hk ha
            obtain ⟨n, rfl, _, _⟩ := Value.hasShape_intIn_true v lo' hi' hvs
            simp only [eval, hv, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
          · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
        | sum cs =>
          simp only [somePasst] at h
          cases h
        | record ss =>
          simp only [somePasst] at h
          cases h
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | lit v =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.lit v) Δ s sh hw hl hk h
  | name n =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.name n) Δ s sh hw hl hk h
  | place c i f =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.place c i f) Δ s sh hw hl hk h
  | global g =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.global g) Δ s sh hw hl hk h
  | un op a =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.un op a) Δ s sh hw hl hk h
  | bin op a b =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.bin op a b) Δ s sh hw hl hk h
  | fieldOf c f =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.fieldOf c f) Δ s sh hw hl hk h
  | forallSlots v n b =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.forallSlots v n b) Δ s sh hw hl hk h
  | existsSlots v n b =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.existsSlots v n b) Δ s sh hw hl hk h
  | reaches c a z via cnt =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.reaches c a z via cnt) Δ s sh hw hl hk h
  | chainFrom c hd x via cnt =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.chainFrom c hd x via cnt) Δ s sh hw hl hk h
  | hasShape n sh' =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.hasShape n sh') Δ s sh hw hl hk h
  | wrapTo b sg a =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.wrapTo b sg a) Δ s sh hw hl hk h
  | tagOf t p =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.tagOf t p) Δ s sh hw hl hk h
  | recOf args =>
    exact schluss_sicher D Γ hD (.recOf args) Δ s sh hw hl hk h
  | recGet base idx =>
    exact schluss_sicher D Γ hD (.recGet base idx) Δ s sh hw hl hk h
  | recSet base idx val =>
    exact schluss_sicher D Γ hD (.recSet base idx val) Δ s sh hw hl hk h

/-! ## 4. Decided examples -- the formulas above, computed

    Each example evaluates `schluss` (or `schlussMitZiel`) on literals and checks
    the exact range the checker promises. They run wherever the file builds. -/

/-- An empty declaration and an empty scope: literals need neither. -/
def leerD : Deklaration := ⟨fun _ _ => none, fun _ => 0, fun _ _ => none, fun _ => none⟩

/-- `7 / 2` over point ranges: `teile` gives `3 .. 3`. -/
example : schluss leerD (fun _ => none)
    (.bin .div (.lit (.int 7)) (.lit (.int 2))) = some (.intIn 3 3) := by decide

/-- `-7 / 2` truncates toward zero through the four corners: `-3 .. -3`. -/
example : schluss leerD (fun _ => none)
    (.bin .div (.lit (.int (-7))) (.lit (.int 2))) = some (.intIn (-3) (-3)) := by decide

/-- `7 % 2`: `rest` gives `0 .. min (2 - 1) 7`. -/
example : schluss leerD (fun _ => none)
    (.bin .rem (.lit (.int 7)) (.lit (.int 2))) = some (.intIn 0 1) := by decide

/-- `6 & 3`: `bitweise` gives `0 .. min 6 3`. -/
example : schluss leerD (fun _ => none)
    (.bin .band (.lit (.int 6)) (.lit (.int 3))) = some (.intIn 0 3) := by decide

/-- `6 | 3`: `bitweise` gives `0 .. maske 6` with `maske 6 = 7`. -/
example : schluss leerD (fun _ => none)
    (.bin .bor (.lit (.int 6)) (.lit (.int 3))) = some (.intIn 0 7) := by decide

/-- `3 << 2`: `schiebe_links` gives `3 * 2^2 .. 3 * 2^2`. -/
example : schluss leerD (fun _ => none)
    (.bin .shl (.lit (.int 3)) (.lit (.int 2))) = some (.intIn 12 12) := by decide

/-- `7 >> 1`: `schiebe_rechts` gives `7 / 2^1 .. 7 / 2^1`. -/
example : schluss leerD (fun _ => none)
    (.bin .shr (.lit (.int 7)) (.lit (.int 1))) = some (.intIn 3 3) := by decide

/-- `Some(8)` against the payload bound `0 .. 7` (`gift/170`): refused (F10). -/
example : schlussMitZiel leerD (some (0, 7)) (fun _ => none)
    (.someOf (.lit (.int 8))) = none := by decide

/-- ... and inside `0 .. 8` it passes. -/
example : schlussMitZiel leerD (some (0, 8)) (fun _ => none)
    (.someOf (.lit (.int 8))) = some .opt := by decide

end Gabbro.Sicherheit
