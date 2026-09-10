/-
  Datei:      Grammatik/Wettlauf.lean
  Gegenstand: **Faeden, verschraenkt** -- und der Satz, dass zwei Faeden mit Spuren, wie die
              Grammatik sie hinterlaesst, einen bewachten Traeger nie im Wettlauf beruehren.

  ## Das Modell

  Ein LAUF ist eine Folge von Schritten (Faden, Ereignis), in Zeitfolge. Die Spur eines Fadens
  bis zum Zeitpunkt `j` ist, was `Semantik.lean` in `World.spur` schreibt: seine eigenen
  Ereignisse, neuestes zuerst. Was ein Faden HAELT, ist `offen` seiner Spur -- wie in der Welt.

  Ein Lauf ist GESITTET, wenn
    (W1) jede Fadenspur konsistent ist          -- `exec_spur`, Klausel 3
    (W2) jedes Ereignis gut ist                 -- `exec_spur`, Klausel 2
    (W3) Sperren einander AUSSCHLIESSEN: wer `L` nimmt, nimmt es, wenn kein anderer Faden
         `L` haelt                              -- was eine Sperre IST: die Zusage der
                                                   Sperrprimitive (ein fremder Rumpf), A_lock
    (W4) eine Marke ist in EINEM Faden          -- Linearitaet: keine Anweisung reicht eine
                                                   Marke an einen anderen Faden weiter, und
                                                   Eigentumsmarken erzeugt niemand
    (W5) ein ungeteilter Traeger gehoert EINEM Faden -- `geteilt`, die Erklaerung (`H013`)

  ## Der Satz

  `kein_wettlauf`: in einem gesitteten Lauf sind zwei Zugriffe verschiedener Faeden auf
  denselben Traeger durch HAPPENS-BEFORE geordnet -- Programmfolge im Faden, und `gibt L`
  vor `nimmt L`. Fuer ein Global: geordnet, oder das Global ist `atomic` -- und dann ordnet
  es die Maschine (A10, `Hardware.sichtbarkeit`). **Es gibt keinen dritten Fall**: das ist
  die Freiheit von Wettlaeufen als Satz ueber Verschraenkungen, nicht nur ueber Ableitungen.

  Der Beweis ist der klassische: beide Zugriffe tragen den Waechter des Traegers (W2); ist
  er eine Sperre, halten beide Faeden sie zu ihrer Zeit (W1); dann liegt zwischen dem
  ersten Zugriff und dem zweiten ein `gibt` des ersten Fadens und ein `nimmt` des zweiten
  (W3, und dass kein Faden eine Sperre zweimal nimmt -- `gut` am `nimmt`). Ist der Waechter
  eine Marke, sind es derselbe Faden (W4) -- kein zweiter Zugreifer.
-/
import Grammatik.Satz

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
  simp [Lauf.spur]

theorem Lauf.spur_succ_eigen (l : Lauf D) (f : Faden) (j : Nat) (e : Ereignis D)
    (h : l[j]? = some (Schritt.mk f e)) : l.spur f (j + 1) = e :: l.spur f j := by
  unfold Lauf.spur
  rw [List.take_add_one, h]
  simp [List.filterMap_append]

theorem Lauf.spur_succ_fremd (l : Lauf D) (f : Faden) (j : Nat)
    (h : ∀ e, l[j]? ≠ some (Schritt.mk f e)) : l.spur f (j + 1) = l.spur f j := by
  unfold Lauf.spur
  rw [List.take_add_one]
  cases hj : l[j]? with
  | none => simp
  | some s =>
      have : s.faden ≠ f := by
        intro hf; exact h s.ereignis (by rw [hj]; cases s; simp_all)
      simp [List.filterMap_append, this]

/-! ## 2. Was `offen` ueber eine konsistente, gute Spur sagt -/

theorem konsistent_tail {e : Ereignis D} {s : List (Ereignis D)} (h : Konsistent (e :: s)) :
    Konsistent s := by
  intro n e' hn
  have := h (n + 1) e' (by simpa using hn)
  simpa using this

theorem konsistent_head {e : Ereignis D} {s : List (Ereignis D)} (h : Konsistent (e :: s)) :
    e.passt s := by
  have := h 0 e (by simp)
  simpa using this

/-- Auf einer konsistenten, guten Spur ist keine Sperre zweimal offen. -/
theorem offen_nodup : ∀ (s : List (Ereignis D)), Konsistent s → (∀ e ∈ s, e.gut) → (offen s).Nodup
  | [], _, _ => List.nodup_nil
  | .zugriff .. :: s, hk, hg => offen_nodup s (konsistent_tail hk) (fun e he => hg e (List.mem_cons_of_mem _ he))
  | .gzugriff .. :: s, hk, hg => offen_nodup s (konsistent_tail hk) (fun e he => hg e (List.mem_cons_of_mem _ he))
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
  | [], _, _, L, h => by simp [offen] at h
  | .zugriff .. :: s, hk, hg, L, h => by
      obtain ⟨n, h', hn, hv⟩ := offen_zeuge s (konsistent_tail hk)
        (fun e he => hg e (List.mem_cons_of_mem _ he)) L (by simpa [offen] using h)
      refine ⟨n + 1, h', by simpa using hn, ?_⟩
      intro n' hn'
      cases n' with
      | zero => simp
      | succ n' => simp only [List.getElem?_cons_succ]; exact hv n' (by omega)
  | .gzugriff .. :: s, hk, hg, L, h => by
      obtain ⟨n, h', hn, hv⟩ := offen_zeuge s (konsistent_tail hk)
        (fun e he => hg e (List.mem_cons_of_mem _ he)) L (by simpa [offen] using h)
      refine ⟨n + 1, h', by simpa using hn, ?_⟩
      intro n' hn'
      cases n' with
      | zero => simp
      | succ n' => simp only [List.getElem?_cons_succ]; exact hv n' (by omega)
  | .nimmt M hm :: s, hk, hg, L, h => by
      simp only [offen, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, hm, by simp, fun n' hn' => by omega⟩
      · obtain ⟨n, h', hn, hv⟩ := offen_zeuge s (konsistent_tail hk)
          (fun e he => hg e (List.mem_cons_of_mem _ he)) L h
        refine ⟨n + 1, h', by simpa using hn, ?_⟩
        intro n' hn'
        cases n' with
        | zero => simp
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
      | zero => simp [hne]
      | succ n' => simp only [List.getElem?_cons_succ]; exact hv n' (by omega)

/-- Was neuer ist als ein `nimmt L` und kein `gibt L` ist, laesst `L` offen. -/
theorem offen_bleibt (L : D.Lock) : ∀ (s : List (Ereignis D)), L ∈ offen s →
    ∀ e, e ≠ .gibt L → L ∈ offen (e :: s) := by
  intro s hs e he
  cases e with
  | zugriff _ _ _ _ => simpa [offen] using hs
  | gzugriff _ _ _ _ => simpa [offen] using hs
  | nimmt M _ => simp [offen, hs]
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

/-! ## 4. Halten, in Laufzeit gesagt -/

/-- Wer `L` zur Zeit `j` haelt, hat es an einem `k < j` genommen und seither nicht gegeben. -/
theorem Lauf.haelt_zeuge (l : Lauf D) (hg : Gesittet l) (f : Faden) (L : D.Lock) :
    ∀ j, l.haelt f L j → ∃ k < j, ∃ h, l[k]? = some (Schritt.mk f (.nimmt L h)) ∧
      ∀ r, k < r → r < j → l[r]? ≠ some (Schritt.mk f (.gibt L)) := by
  intro j
  induction j with
  | zero => intro h; simp [Lauf.haelt, Lauf.spur_zero, offen] at h
  | succ j ih =>
      intro h
      by_cases hj : ∃ e, l[j]? = some (Schritt.mk f e)
      · obtain ⟨e, he⟩ := hj
        have hs := l.spur_succ_eigen f j e he
        unfold Lauf.haelt at h
        rw [hs] at h
        have hnd := offen_nodup (l.spur f j) (hg.konsistent f j) (hg.gut f j)
        -- ein Schritt von `f`: `e` entscheidet
        cases e with
        | nimmt M hm =>
            simp only [offen, List.mem_cons] at h
            rcases h with rfl | h
            · exact ⟨j, by omega, hm, he, fun r h1 h2 => by omega⟩
            · obtain ⟨k, hk, h', hn, hv⟩ := ih h
              refine ⟨k, by omega, h', hn, ?_⟩
              intro r h1 h2
              by_cases hr : r = j
              · subst hr; rw [he]; simp
              · exact hv r h1 (by omega)
        | gibt M =>
            simp only [offen] at h
            have hne : M ≠ L := by
              rintro rfl; exact (List.Nodup.not_mem_erase hnd) h
            obtain ⟨k, hk, h', hn, hv⟩ := ih (List.mem_of_mem_erase h)
            refine ⟨k, by omega, h', hn, ?_⟩
            intro r h1 h2
            by_cases hr : r = j
            · subst hr; rw [he]; simp [hne]
            · exact hv r h1 (by omega)
        | zugriff t w Λ hh =>
            simp only [offen] at h
            obtain ⟨k, hk, h', hn, hv⟩ := ih h
            refine ⟨k, by omega, h', hn, ?_⟩
            intro r h1 h2
            by_cases hr : r = j
            · subst hr; rw [he]; simp
            · exact hv r h1 (by omega)
        | gzugriff g w Λ hh =>
            simp only [offen] at h
            obtain ⟨k, hk, h', hn, hv⟩ := ih h
            refine ⟨k, by omega, h', hn, ?_⟩
            intro r h1 h2
            by_cases hr : r = j
            · subst hr; rw [he]; simp
            · exact hv r h1 (by omega)
      · have hs := l.spur_succ_fremd f j (fun e he => hj ⟨e, he⟩)
        unfold Lauf.haelt at h
        rw [hs] at h
        obtain ⟨k, hk, h', hn, hv⟩ := ih h
        refine ⟨k, by omega, h', hn, ?_⟩
        intro r h1 h2
        by_cases hr : r = j
        · subst hr; intro hc; exact hj ⟨_, hc⟩
        · exact hv r h1 (by omega)

/-- Wer `L` an `k` genommen und bis `j` nicht gegeben hat, haelt es an `j`. -/
theorem Lauf.haelt_von (l : Lauf D) (f : Faden) (L : D.Lock) (k : Nat) (h : List D.Lock)
    (hk : l[k]? = some (Schritt.mk f (.nimmt L h))) :
    ∀ j, k < j → (∀ r, k < r → r < j → l[r]? ≠ some (Schritt.mk f (.gibt L))) → l.haelt f L j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
      intro hkj hv
      by_cases hjk : j = k
      · subst hjk
        unfold Lauf.haelt
        rw [l.spur_succ_eigen f j _ hk]
        simp [offen]
      · have ih' := ih (by omega) (fun r h1 h2 => hv r h1 (by omega))
        unfold Lauf.haelt at ih' ⊢
        by_cases hj : ∃ e, l[j]? = some (Schritt.mk f e)
        · obtain ⟨e, he⟩ := hj
          rw [l.spur_succ_eigen f j e he]
          apply offen_bleibt L _ ih'
          intro hc; subst hc
          exact hv j (by omega) (by omega) he
        · rw [l.spur_succ_fremd f j (fun e he => hj ⟨e, he⟩)]
          exact ih'

/-- Der aufgezeichnete Sperrstand eines Zugriffs ist der gehaltene (W1). -/
theorem Lauf.aufzeichnung (l : Lauf D) (hg : Gesittet l) (f : Faden) (j : Nat) (e : Ereignis D)
    (he : l[j]? = some (Schritt.mk f e)) : e.passt (l.spur f j) := by
  have := hg.konsistent f (j + 1)
  rw [l.spur_succ_eigen f j e he] at this
  exact konsistent_head this

/-! ## 5. Der Satz -/

/-- Zwei Faeden, die dieselbe Sperre zu ihren Zeiten halten, sind geordnet: dazwischen liegt
    ein `gibt` des ersten und ein `nimmt` des zweiten. -/
theorem geordnet_durch_sperre (l : Lauf D) (hg : Gesittet l) (f g : Faden) (L : D.Lock)
    (i j : Nat) (hij : i < j) (hfg : f ≠ g) (ei ej : Ereignis D) (hei : ∀ L', ei ≠ .gibt L')
    (hi : l[i]? = some (Schritt.mk f ei)) (hj : l[j]? = some (Schritt.mk g ej))
    (hfi : l.haelt f L i) (hgj : l.haelt g L j) : HB l i j := by
  obtain ⟨k, hkj, hk, hnk, hvk⟩ := l.haelt_zeuge hg g L j hgj
  obtain ⟨k', hk'i, hk', hnk', hvk'⟩ := l.haelt_zeuge hg f L i hfi
  -- `k` (g nimmt) liegt nach `i`
  have hik : i < k := by
    apply Classical.byContradiction; intro hle
    have hlt : k < i := by
      rcases Nat.lt_or_ge k i with h | h
      · exact h
      · exfalso
        have : k = i := by omega
        subst this
        have := hi.symm.trans hnk
        simp at this
        exact hfg this.1
    -- dann haelt f `L` an `k` (genommen an k' < k, seit da nicht gegeben) -- gegen (W3)
    have hkk' : k' < k := by
      apply Classical.byContradiction; intro hge
      -- k < k' : dann haelt g `L` an k' (genommen an k, nicht gegeben bis j > k'), gegen (W3) an k'
      have hlt' : k < k' := by
        rcases Nat.lt_or_ge k k' with h | h
        · exact h
        · exfalso
          have : k = k' := by omega
          subst this
          have := hnk.symm.trans hnk'
          simp at this
          exact hfg this.1.symm
      have := hg.ausschluss k' f L hk' hnk' g (Ne.symm hfg)
      exact this (l.haelt_von g L k hk hnk k' hlt' (fun r h1 h2 => hvk r h1 (by omega)))
    have := hg.ausschluss k g L hk hnk f hfg
    exact this (l.haelt_von f L k' hk' hnk' k hkk' (fun r h1 h2 => hvk' r h1 (by omega)))
  -- zwischen `i` und `k` gibt f `L` (sonst hielte f an k, gegen W3)
  have hr : ∃ r, i < r ∧ r < k ∧ l[r]? = some (Schritt.mk f (.gibt L)) := by
    apply Classical.byContradiction; intro hno
    have := hg.ausschluss k g L hk hnk f hfg
    apply this
    apply l.haelt_von f L k' hk' hnk' k (by omega)
    intro r h1 h2 hc
    by_cases hri : r < i
    · exact hvk' r h1 hri hc
    · by_cases hri' : r = i
      · subst hri'
        have := hi.symm.trans hc
        simp at this
        exact hei L this
      · exact hno ⟨r, by omega, h2, hc⟩
  obtain ⟨r, hir, hrk, hgibt⟩ := hr
  exact HB.trans _ _ _ (HB.po f i r ei _ hi hgibt hir)
    (HB.trans _ _ _ (HB.sync f g L hk r k hgibt hnk hrk) (HB.po g k j _ ej hnk hj hkj))

/-- Ein guter Zugriff unter Sperre `L` haelt `L` zu seiner Zeit. -/
theorem Lauf.haelt_bei_zugriff (l : Lauf D) (hg : Gesittet l) (f : Faden) (j : Nat) (L : D.Lock)
    (e : Ereignis D) (he : l[j]? = some (Schritt.mk f e)) (hL : Res.held L ∈ e.lambda) (ht : e.traeger.isSome) :
    l.haelt f L j := by
  have hp := l.aufzeichnung hg f j e he
  have hgut : e.gut := hg.gut f (j + 1) e (by rw [l.spur_succ_eigen f j e he]; exact List.mem_cons_self)
  cases e with
  | zugriff t w Λ h =>
      simp only [Ereignis.passt] at hp
      simp only [Ereignis.gut] at hgut
      unfold Lauf.haelt; rw [← hp]; exact hgut.2 L hL
  | gzugriff x w Λ h =>
      simp only [Ereignis.passt] at hp
      simp only [Ereignis.gut] at hgut
      unfold Lauf.haelt; rw [← hp]; exact hgut.2 L hL
  | nimmt _ _ => simp [Ereignis.traeger] at ht
  | gibt _ => simp [Ereignis.traeger] at ht

/-- **Kein Wettlauf auf einem Traeger.** Zwei Zugriffe verschiedener Faeden auf dieselbe
    Tabelle sind durch happens-before geordnet. -/
theorem kein_wettlauf (l : Lauf D) (hg : Gesittet l) (i j : Nat) (hij : i < j) (f g : Faden)
    (hfg : f ≠ g) (t : D.Tab) (w w' : Bool) (Λ Λ' : List (Res D)) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.zugriff t w Λ h))) (hj : l[j]? = some (Schritt.mk g (.zugriff t w' Λ' h'))) :
    HB l i j := by
  -- der Traeger ist geteilt (W5), also bewacht
  have hget : D.geteilt t = true := by
    apply Classical.byContradiction; intro hn
    have := hg.ungeteilt i j f g (.inl t) _ _ hi hj rfl rfl (by simpa using hn)
    exact hfg this
  have hb := D.geteilt_bewacht t hget
  obtain ⟨wt, hwt⟩ : ∃ wt, wt ∈ D.braucht t := by
    cases hbt : D.braucht t with
    | nil => exact absurd hbt hb
    | cons x xs => exact ⟨x, List.mem_cons_self⟩
  have gi : (Ereignis.zugriff (D := D) t w Λ h).gut :=
    hg.gut f (i + 1) _ (by rw [l.spur_succ_eigen f i _ hi]; exact List.mem_cons_self)
  have gj : (Ereignis.zugriff (D := D) t w' Λ' h').gut :=
    hg.gut g (j + 1) _ (by rw [l.spur_succ_eigen g j _ hj]; exact List.mem_cons_self)
  simp only [Ereignis.gut] at gi gj
  cases wt with
  | inl L =>
      have hLi : Res.held L ∈ Λ := gi.1 _ hwt
      have hLj : Res.held L ∈ Λ' := gj.1 _ hwt
      exact geordnet_durch_sperre l hg f g L i j hij hfg _ _ (by intro L' h; cases h) hi hj
        (l.haelt_bei_zugriff hg f i L _ hi hLi (by simp [Ereignis.traeger]))
        (l.haelt_bei_zugriff hg g j L _ hj hLj (by simp [Ereignis.traeger]))
  | inr ms =>
      obtain ⟨m, s⟩ := ms
      have hmi : Res.marke m s ∈ Λ := gi.1 _ hwt
      have hmj : Res.marke m s ∈ Λ' := gj.1 _ hwt
      exact absurd (hg.marke_eindeutig i j f g m s s _ _ hi hj hmi hmj) hfg

/-- **Kein Wettlauf auf einem Global, oder es ist `atomic`** -- und dann ordnet die Maschine
    (A10): der dritte Fall existiert nicht. -/
theorem kein_wettlauf_global (l : Lauf D) (hg : Gesittet l) (i j : Nat) (hij : i < j) (f g : Faden)
    (hfg : f ≠ g) (x : D.Glob) (w w' : Bool) (Λ Λ' : List (Res D)) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.gzugriff x w Λ h))) (hj : l[j]? = some (Schritt.mk g (.gzugriff x w' Λ' h'))) :
    HB l i j ∨ D.atomar x = true := by
  have hget : D.ggeteilt x = true := by
    apply Classical.byContradiction; intro hn
    have := hg.ungeteilt i j f g (.inr x) _ _ hi hj rfl rfl (by simpa using hn)
    exact absurd this hfg
  rcases D.ggeteilt_bewacht x hget with hb | ha
  · left
    obtain ⟨wt, hwt⟩ : ∃ wt, wt ∈ D.gbraucht x := by
      cases hbt : D.gbraucht x with
      | nil => exact absurd hbt hb
      | cons y ys => exact ⟨y, List.mem_cons_self⟩
    have gi : (Ereignis.gzugriff (D := D) x w Λ h).gut :=
      hg.gut f (i + 1) _ (by rw [l.spur_succ_eigen f i _ hi]; exact List.mem_cons_self)
    have gj : (Ereignis.gzugriff (D := D) x w' Λ' h').gut :=
      hg.gut g (j + 1) _ (by rw [l.spur_succ_eigen g j _ hj]; exact List.mem_cons_self)
    simp only [Ereignis.gut] at gi gj
    cases wt with
    | inl L =>
        exact geordnet_durch_sperre l hg f g L i j hij hfg _ _ (by intro L' h; cases h) hi hj
          (l.haelt_bei_zugriff hg f i L _ hi (gi.1 _ hwt) (by simp [Ereignis.traeger]))
          (l.haelt_bei_zugriff hg g j L _ hj (gj.1 _ hwt) (by simp [Ereignis.traeger]))
    | inr ms =>
        obtain ⟨m, s⟩ := ms
        exact absurd (hg.marke_eindeutig i j f g m s s _ _ hi hj (gi.1 _ hwt) (gj.1 _ hwt)) hfg
  · right; exact ha

/-- **Keine Ueberkreuzung der Sperrordnung**, im Lauf: kein Faden nimmt `L2` mit `L1` in der
    Hand, waehrend ein anderer `L1` mit `L2` in der Hand nimmt -- die Raenge stiegen dann im
    Kreis. Das ist `keine_verklemmung` (Satz.lean) ueber Laeufen: die Wartekette, die eine
    Verklemmung braucht, hat keinen Anfang. -/
theorem keine_ueberkreuzung (l : Lauf D) (hg : Gesittet l) (i j : Nat) (f g : Faden)
    (L1 L2 : D.Lock) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.nimmt L2 h))) (hj : l[j]? = some (Schritt.mk g (.nimmt L1 h')))
    (h1 : L1 ∈ h) (h2 : L2 ∈ h') : False := by
  have gi : (Ereignis.nimmt (D := D) L2 h).gut :=
    hg.gut f (i + 1) _ (by rw [l.spur_succ_eigen f i _ hi]; exact List.mem_cons_self)
  have gj : (Ereignis.nimmt (D := D) L1 h').gut :=
    hg.gut g (j + 1) _ (by rw [l.spur_succ_eigen g j _ hj]; exact List.mem_cons_self)
  simp only [Ereignis.gut] at gi gj
  have a := gi.1 L1 h1
  have b := gj.1 L2 h2
  omega

/-! ## 5. Von den Ruempfen in den Lauf -- was `exec` liefert, und was fehlt

    `exec_spur` (`Satz.lean`) sagt ueber EINEN Rumpf: aus leerer Spur kommen nur
    konsistente Spuren mit guten Ereignissen zurueck (`Brav.konsistent_von_leer`,
    `Brav.gut_von_leer`). Was ein LAUF daraus macht, steht hier: jede
    beobachtete Teilspur ist eine Endstrecke der vollen (Verschraenkung
    unten), und Endstrecken bleiben konsistent (`Konsistent.drop`).

    EHRLICH GESAGT -- was dieser Satz NICHT baut (2026-09-10,
    `messung/ZIEL-BEWERTUNG-2026-09-10.md`):
    W3 (Ausschluss), W4 (Marke in einem Faden) und W5 (ungeteilt) bleiben
    PRAEMISSEN: sie sprechen ueber das Verhaeltnis der Faeden zueinander
    (fremde Sperrprimitive, disjunkte Markenmengen, `shared`-Deklaration), und
    kein Satz ueber je einen Rumpf kann sie schliessen. Ebenso fehlt der
    Owicki-Gries-Schritt: dass gueltige sequenzielle Logik (`requires` /
    `ensures`) unter Verschraenkung gueltig bleibt, folgt aus HB-Ordnung nicht
    -- dazu brauchte es eine gemeinsame Semantik mit Rahmen-Disjunktheit
    (`exec_rahmen` ist der Kandidat fuer die Praemisse), und die steht nirgends.
    Rennfreiheit und Logikbeweis sind damit zwei unverbundene Saetze. -/

/-- Eine beobachtete Teilspur ist eine Endstrecke der vollen: so sieht eine
    Verschraenkung aus, die die Faeden nur verzahnt statt umzuschreiben. Ein
    Lauf, der das verletzt, ist keine Verschraenkung dieser Ausfuehrungen. -/
def IstVerschraenkung (l : Lauf D) (voll : Faden → List (Ereignis D)) : Prop :=
  ∀ f j, ∃ k, l.spur f j = (voll f).drop k

/-- W1 und W2 ueber jeder Verschraenkung wohlgeformter Ausfuehrungen: was jeder
    Faden tut, ist konsistent und gut -- vererbt aus `exec_spur` ueber leere
    Spuren, erhalten ueber Endstrecken. Mit W3-W5 als Prämissen ist das
    `Gesittet`; ohne sie ist es genau die Haelfte, die ein Rumpf traegt. -/
theorem lauf_aus_brav (l : Lauf D) (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (hvers : IstVerschraenkung l voll) :
    (∀ f j, Konsistent (l.spur f j)) ∧ (∀ f j (e : Ereignis D), e ∈ l.spur f j → e.gut) := by
  constructor
  · intro f j
    obtain ⟨k, hk⟩ := hvers f j
    obtain ⟨a, b, hempty, hbrav, hspur⟩ := hvoll f
    rw [hk, ← hspur]
    exact (hbrav.konsistent_von_leer hempty).drop _ _
  · intro f j e he
    obtain ⟨k, hk⟩ := hvers f j
    obtain ⟨a, b, hempty, hbrav, hspur⟩ := hvoll f
    have hmem : e ∈ voll f := List.mem_of_mem_drop (hk ▸ he)
    rw [← hspur] at hmem
    exact hbrav.gut_von_leer hempty hmem

/-! ## 6. Declared concurrency -- who shares a run (lane C, 2026-09-10)

    The declaration `concurrent { f, g };` becomes the premise `Nebeneinander`:
    which bodies share a run. What stands in no set never runs concurrently
    (closed world). `kein_wettlauf` above holds over EVERY interleaving; the
    corollary below names the shape the joint model will consume: the same
    happens-before order, quantified over the RESTRICTED interleaving of
    declared pairs. `kein_wettlauf` itself stays as-is.

    The Owicki-Gries step -- `exec_rahmen` per body plus pairwise disjoint
    frames ⇒ sequential contracts survive interleaving -- is NOT here yet; it
    needs the joint model of the declared pair set, which stands nowhere. -/

/-- Which bodies share a run: the `concurrent { … }` declaration as a premise.
    It travels as an explicit `Nb : Nebeneinander` argument below, not a
    `variable`: the existing theorems above quantify over every interleaving,
    and a section variable here would rewrite their context. -/
abbrev Nebeneinander : Type := Faden → Faden → Prop

/-- A run in which only declared pairs interleave: any two steps of different
    threads stand in the declared relation. -/
def BeschraenkteVerschraenkung (Nb : Nebeneinander) (l : Lauf D) : Prop :=
  ∀ (i j : Nat) (f g : Faden) (ei ej : Ereignis D),
    l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) → f ≠ g →
    Nb f g

/-- **Nur Deklarierte teilen sich den Lauf (closed world, Satzform).** In einem
    Lauf, dessen Verschraenkung auf deklarierte Paare beschraenkt ist, haben
    zwei verschiedene Faeden nur dann Schritte, wenn sie deklariert sind.
    Das ist die Definition `BeschraenkteVerschraenkung`, angewendet -- kein
    neuer Inhalt, sondern die benannte Andockstelle: die Checker-Seite
    (`W002`) verweigert genau die Paare ohne `Nb`, und dieser Satz sagt, dass
    im beschraenkten Lauf nur `Nb`-Paare vorkommen. Die Prämisse wird benutzt;
    was hier stuende und mehr bewiebe, stuende als eigener Satz daneben. -/
theorem nur_deklariert_teilt_lauf (Nb : Nebeneinander) (l : Lauf D)
    (hb : BeschraenkteVerschraenkung (D := D) Nb l)
    (i j : Nat) (f g : Faden) (ei ej : Ereignis D)
    (hi : l[i]? = some (Schritt.mk f ei)) (hj : l[j]? = some (Schritt.mk g ej))
    (hfg : f ≠ g) : Nb f g :=
  hb i j f g ei ej hi hj hfg

#print axioms Gabbro.Grammatik.kein_wettlauf
#print axioms Gabbro.Grammatik.kein_wettlauf_global
#print axioms Gabbro.Grammatik.keine_ueberkreuzung
#print axioms Gabbro.Grammatik.lauf_aus_brav
#print axioms Gabbro.Grammatik.nur_deklariert_teilt_lauf

end Gabbro.Grammatik
