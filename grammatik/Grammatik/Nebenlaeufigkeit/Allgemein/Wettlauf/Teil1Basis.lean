module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Syntax.Marken.Teil2

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Lauf, Spur, Halten -/

abbrev Faden := Nat

structure Schritt (D : Deklaration) where
  faden : Faden
  ereignis : Ereignis D

abbrev Lauf (D : Deklaration) := List (Schritt D)

/-- Die Spur des Fadens `f` nach `j` Schritten, neuestes zuerst. -/
def Lauf.spur (l : Lauf D) (f : Faden) (j : Nat) : List (Ereignis D) :=
  ((l.take j).filterMap fun s => if s.faden = f then some s.ereignis else none).reverse

/-- Faden `f` haelt `L` zum Zeitpunkt `j` (vor Schritt `j`). -/
def Lauf.haelt (l : Lauf D) (f : Faden) (L : D.Lock) (j : Nat) : Prop :=
  L ∈ offen (l.spur f j)

theorem Lauf.spur_zero (l : Lauf D) (f : Faden) : l.spur f 0 = [] := by
  simp only [spur, List.take_zero, List.filterMap_nil, List.reverse_nil]

theorem Lauf.spur_succ_eigen (l : Lauf D) (f : Faden) (j : Nat) (e : Ereignis D)
    (h : l[j]? = some (Schritt.mk f e)) : l.spur f (j + 1) = e :: l.spur f j := by
  unfold Lauf.spur
  rw [List.take_add_one, h]
  simp only [Option.toList_some, List.filterMap_append, ↓reduceIte, Option.some.injEq, List.filterMap_cons_some,
  List.filterMap_nil, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]

theorem Lauf.spur_succ_fremd (l : Lauf D) (f : Faden) (j : Nat)
    (h : ∀ e, l[j]? ≠ some (Schritt.mk f e)) : l.spur f (j + 1) = l.spur f j := by
  unfold Lauf.spur
  rw [List.take_add_one]
  cases hj : l[j]? with
  | none => simp only [Option.toList_none, List.append_nil]
  | some s =>
      have : s.faden ≠ f := by
        intro hf; exact h s.ereignis (by rw [hj]; cases s; simp_all)
      simp only [Option.toList_some, List.filterMap_append, this, ↓reduceIte, List.filterMap_cons_none,
  List.filterMap_nil, List.append_nil]

/-! ## 2. Was `offen` ueber eine konsistente, gute Spur sagt -/

theorem konsistent_tail {e : Ereignis D} {s : List (Ereignis D)} (h : Konsistent (e :: s)) :
    Konsistent s := by
  intro n e' hn
  have := h (n + 1) e' (by simpa using hn)
  simpa using this

theorem konsistent_head {e : Ereignis D} {s : List (Ereignis D)} (h : Konsistent (e :: s)) :
    e.passt s := by
  have := h 0 e (by simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero])
  simpa using this

/-- Auf einer konsistenten, guten Spur ist keine Sperre zweimal offen. -/
theorem offen_nodup : ∀ (s : List (Ereignis D)), Konsistent s → (∀ e ∈ s, e.gut) → (offen s).Nodup
  | [], _, _ => List.nodup_nil
  | .zugriff .. :: s, hk, hg => offen_nodup s (konsistent_tail hk) (fun e he => hg e (List.mem_cons_of_mem _ he))
  | .gzugriff .. :: s, hk, hg => offen_nodup s (konsistent_tail hk) (fun e he => hg e (List.mem_cons_of_mem _ he))
  | .fremd _ :: s, hk, hg => offen_nodup s (konsistent_tail hk) (fun e he => hg e (List.mem_cons_of_mem _ he))
  | .gibt L :: s, hk, hg =>
      List.Nodup.erase L (offen_nodup s (konsistent_tail hk) (fun e he => hg e (List.mem_cons_of_mem _ he)))
  | .nimmt L h :: s, hk, hg => by
      have ih := offen_nodup s (konsistent_tail hk) (fun e he => hg e (List.mem_cons_of_mem _ he))
      have hp : h = offen s := konsistent_head hk
      have hL : L ∉ h := (hg _ List.mem_cons_self).2
      simp only [offen]
      exact List.nodup_cons.mpr ⟨hp ▸ hL, ih⟩

/-- Ist `L` offen, so steht ein `nimmt L` in der Spur, und kein `gibt L` DAVOR (neuer). -/
theorem offen_zeuge : ∀ (s : List (Ereignis D)), Konsistent s → (∀ e ∈ s, e.gut) → ∀ L, L ∈ offen s →
    ∃ (n : Nat) (h : List D.Lock), s[n]? = some (Ereignis.nimmt L h) ∧
      ∀ n' < n, s[n']? ≠ some (Ereignis.gibt L)
  | [], _, _, L, h => by simp only [offen, List.not_mem_nil] at h
  | .zugriff .. :: s, hk, hg, L, h => by
      obtain ⟨n, h', hn, hv⟩ := offen_zeuge s (konsistent_tail hk)
        (fun e he => hg e (List.mem_cons_of_mem _ he)) L (by simpa [offen] using h)
      refine ⟨n + 1, h', by simpa using hn, ?_⟩
      intro n' hn'
      cases n' with
      | zero => simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, ne_eq, Option.some.injEq,
  reduceCtorEq, not_false_eq_true]
      | succ n' => simp only [List.getElem?_cons_succ]; exact hv n' (by omega)
  | .gzugriff .. :: s, hk, hg, L, h => by
      obtain ⟨n, h', hn, hv⟩ := offen_zeuge s (konsistent_tail hk)
        (fun e he => hg e (List.mem_cons_of_mem _ he)) L (by simpa [offen] using h)
      refine ⟨n + 1, h', by simpa using hn, ?_⟩
      intro n' hn'
      cases n' with
      | zero => simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, ne_eq, Option.some.injEq,
  reduceCtorEq, not_false_eq_true]
      | succ n' => simp only [List.getElem?_cons_succ]; exact hv n' (by omega)
  | .fremd _ :: s, hk, hg, L, h => by
      obtain ⟨n, h', hn, hv⟩ := offen_zeuge s (konsistent_tail hk)
        (fun e he => hg e (List.mem_cons_of_mem _ he)) L (by simpa [offen] using h)
      refine ⟨n + 1, h', by simpa using hn, ?_⟩
      intro n' hn'
      cases n' with
      | zero => simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, ne_eq, Option.some.injEq,
  reduceCtorEq, not_false_eq_true]
      | succ n' => simp only [List.getElem?_cons_succ]; exact hv n' (by omega)
  | .nimmt M hm :: s, hk, hg, L, h => by
      simp only [offen, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, hm, by simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero], fun n' hn' => by omega⟩
      · obtain ⟨n, h', hn, hv⟩ := offen_zeuge s (konsistent_tail hk)
          (fun e he => hg e (List.mem_cons_of_mem _ he)) L h
        refine ⟨n + 1, h', by simpa using hn, ?_⟩
        intro n' hn'
        cases n' with
        | zero => simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, ne_eq, Option.some.injEq,
  reduceCtorEq, not_false_eq_true]
        | succ n' => simp only [List.getElem?_cons_succ]; exact hv n' (by omega)
  | .gibt M :: s, hk, hg, L, h => by
      simp only [offen] at h
      have hnd := offen_nodup s (konsistent_tail hk) (fun e he => hg e (List.mem_cons_of_mem _ he))
      have hne : M ≠ L := by
        rintro rfl
        exact (List.Nodup.not_mem_erase hnd) h
      obtain ⟨n, h', hn, hv⟩ := offen_zeuge s (konsistent_tail hk)
        (fun e he => hg e (List.mem_cons_of_mem _ he)) L (List.mem_of_mem_erase h)
      refine ⟨n + 1, h', by simpa using hn, ?_⟩
      intro n' hn'
      cases n' with
      | zero => simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, ne_eq, Option.some.injEq,
  Ereignis.gibt.injEq, hne, not_false_eq_true]
      | succ n' => simp only [List.getElem?_cons_succ]; exact hv n' (by omega)

/-- Was neuer ist als ein `nimmt L` und kein `gibt L` ist, laesst `L` offen. -/
theorem offen_bleibt (L : D.Lock) : ∀ (s : List (Ereignis D)), L ∈ offen s →
    ∀ e, e ≠ .gibt L → L ∈ offen (e :: s) := by
  intro s hs e he
  cases e with
  | zugriff _ _ _ _ => simpa [offen] using hs
  | gzugriff _ _ _ _ => simpa [offen] using hs
  | fremd _ => simpa [offen] using hs
  | nimmt M _ => simp only [offen, List.mem_cons, hs, or_true]
  | gibt M =>
      have : M ≠ L := fun h => he (by rw [h])
      simp only [offen]
      exact (List.mem_erase_of_ne (Ne.symm this)).mpr hs

/-! ## 3. Der gesittete Lauf -/

/-- Ein Zugriffsereignis nennt seinen Traeger und sein `Λ`. -/
def Ereignis.traeger : Ereignis D → Option (D.Tab ⊕ D.Glob)
  | .zugriff t _ _ _ => some (.inl t)
  | .gzugriff g _ _ _ => some (.inr g)
  | _ => none

def Ereignis.lambda : Ereignis D → List (Res D)
  | .zugriff _ _ Λ _ => Λ
  | .gzugriff _ _ Λ _ => Λ
  | _ => []

structure Gesittet (l : Lauf D) : Prop where
  /-- (W1) jede Fadenspur ist konsistent. -/
  konsistent : ∀ f j, Konsistent (l.spur f j)
  /-- (W2) jedes Ereignis ist gut. -/
  gut : ∀ f j, ∀ e ∈ l.spur f j, e.gut
  /-- (W3) Ausschluss: wer nimmt, nimmt, wenn kein anderer haelt. -/
  ausschluss : ∀ (j : Nat) (f : Faden) (L : D.Lock) (h : List D.Lock), l[j]? = some (Schritt.mk f (.nimmt L h)) → ∀ g, g ≠ f → ¬ l.haelt g L j
  /-- (W4) eine Marke ist in einem Faden. -/
  marke_eindeutig : ∀ (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat) (ei ej : Ereignis D),
    l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
    Res.marke m s ∈ ei.lambda → Res.marke m s' ∈ ej.lambda → f = g
  /-- (W5) ein ungeteilter Traeger gehoert einem Faden. -/
  ungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob) (ei ej : Ereignis D),
    l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) → ei.traeger = some o → ej.traeger = some o →
    (match o with | .inl t => D.geteilt t = false | .inr x => D.ggeteilt x = false) → f = g

/-- Happens-before: Programmfolge im Faden, `gibt L` vor `nimmt L`, transitiv. -/
inductive HB (l : Lauf D) : Nat → Nat → Prop
  | po (f : Faden) (i j : Nat) (ei ej : Ereignis D) (hi : l[i]? = some (Schritt.mk f ei))
      (hj : l[j]? = some (Schritt.mk f ej)) (hij : i < j) : HB l i j
  | sync (f g : Faden) (L : D.Lock) (h : List D.Lock) (i j : Nat) (hi : l[i]? = some (Schritt.mk f (.gibt L)))
      (hj : l[j]? = some (Schritt.mk g (.nimmt L h))) (hij : i < j) : HB l i j
  | trans (i j k : Nat) (h1 : HB l i j) (h2 : HB l j k) : HB l i k

end Gabbro.Grammatik
