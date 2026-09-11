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
import Grammatik.Marken

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
    `messung/ZIEL-BEWERTUNG-2026-09-10.md`, Stand Bahn 78):
    W3 (Ausschluss) und W5 (ungeteilt) bleiben PRAEMISSEN: sie sprechen ueber
    das Verhaeltnis der Faeden zueinander (fremde Sperrprimitive,
    `shared`-Deklaration), und kein Satz ueber je einen Rumpf kann sie
    schliessen. W4 (Marke in einem Faden) ist seit Bahn 78 KEINE blosse
    Praemisse mehr: `Marken.lean` beweist die Einzelfaedrigkeit jedes
    `Verlauf`-Standes, und §7 unten projiziert `Einfaedig` in
    `marke_eindeutig` -- was noch fehlt, ist der Stand HINTER einem echten
    `Lauf D` (ein `Verlauf` je Faden durch `exec`), also reist `hEin` als
    explizite Hypothese. Ebenso fehlt der
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

/-! ## 7. W4 aus der Konstruktion -- `Einfaedig` liefert `marke_eindeutig`

    `Gesittet.marke_eindeutig` keeps its shape (the consumers in `Ziel.lean` and
    `Interferenz.lean` read exactly this field), but it is no longer a bare
    premise: `marke_eindeutig_aus_einfaedig` derives it from `Marken.Einfaedig`
    over the projected run, and `gesittet_aus_einfaedig` builds the whole
    `Gesittet` from the construction instead of the bare W4. `Marken.lean`
    proves that every `Verlauf` yields single-threaded stands
    (`verlauf_einfaedig`); what REMAINS open (rebooked cut): threading one
    `Verlauf` per run through `exec` -- the per-thread stand behind a real
    `Lauf D` stands nowhere yet, so the projection hypothesis `hEin` still
    travels as an explicit argument. -/

/-- Project a real guard into a code guard over `code`. -/
def markenProj (code : D.Marke → Nat) : Res D → Marken.Res
  | .held _ => .held
  | .marke m s => .marke (code m) s

/-- Project a real event: the same mark list, under codes. -/
def ereignisProj (code : D.Marke → Nat) (ei : Ereignis D) : Marken.Ereignis :=
  ⟨ei.lambda.map (markenProj code)⟩

/-- Project a real step: the same thread, the projected event. -/
def schrittProj (code : D.Marke → Nat) (s : Schritt D) : Marken.Schritt :=
  ⟨s.faden, ereignisProj code s.ereignis⟩

/-- Project a real run, step by step. -/
def laufProj (code : D.Marke → Nat) (l : Lauf D) : Marken.Lauf :=
  l.map (schrittProj code)

/-- Mark membership survives the projection. -/
theorem markenProj_mem (code : D.Marke → Nat) (ei : Ereignis D)
    (m : D.Marke) (s : Nat) (h : Res.marke m s ∈ ei.lambda) :
    Marken.Res.marke (code m) s ∈ (ereignisProj code ei).lambda := by
  unfold ereignisProj
  simp only
  exact List.mem_map.mpr ⟨_, h, rfl⟩

/-- Step lookup survives the projection. -/
theorem laufProj_get (code : D.Marke → Nat) (l : Lauf D)
    (i : Nat) (f : Faden) (ei : Ereignis D)
    (h : l[i]? = some (Schritt.mk f ei)) :
    (laufProj code l)[i]? =
      some (Marken.Schritt.mk f (ereignisProj code ei)) := by
  simp [laufProj, schrittProj, List.getElem?_map, h]

/-- **W4 from the construction.** `Einfaedig` over the projected run IS
    `marke_eindeutig` over the real run. -/
theorem marke_eindeutig_aus_einfaedig (code : D.Marke → Nat) (l : Lauf D)
    (hEin : Marken.Einfaedig (laufProj code l))
    (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat)
    (ei ej : Ereignis D)
    (hi : l[i]? = some (Schritt.mk f ei))
    (hj : l[j]? = some (Schritt.mk g ej))
    (hmi : Res.marke m s ∈ ei.lambda)
    (hmj : Res.marke m s' ∈ ej.lambda) : f = g := by
  exact hEin i j f g (code m) s s' _ _
    (laufProj_get code l i f ei hi) (laufProj_get code l j g ej hj)
    (markenProj_mem code ei m s hmi) (markenProj_mem code ej m s' hmj)

/-- **A `Gesittet` from the construction.** The whole bundle with W4 supplied
    by `Einfaedig` instead of the bare premise. -/
theorem gesittet_aus_einfaedig (l : Lauf D)
    (konsistent : ∀ f j, Konsistent (l.spur f j))
    (gut : ∀ f j, ∀ e ∈ l.spur f j, e.gut)
    (ausschluss : ∀ (j : Nat) (f : Faden) (L : D.Lock) (h : List D.Lock),
      l[j]? = some (Schritt.mk f (.nimmt L h)) → ∀ g, g ≠ f → ¬ l.haelt g L j)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code l))
    (ungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet l :=
  ⟨konsistent, gut, ausschluss, marke_eindeutig_aus_einfaedig code l hEin,
    ungeteilt⟩

#print axioms Gabbro.Grammatik.marke_eindeutig_aus_einfaedig
#print axioms Gabbro.Grammatik.gesittet_aus_einfaedig

#print axioms Gabbro.Grammatik.kein_wettlauf
#print axioms Gabbro.Grammatik.kein_wettlauf_global
#print axioms Gabbro.Grammatik.keine_ueberkreuzung
#print axioms Gabbro.Grammatik.lauf_aus_brav
#print axioms Gabbro.Grammatik.nur_deklariert_teilt_lauf

/-! ## 8. W4 from the Verlauf -- `verlauf_einfaedig` through the trace link

    `marke_eindeutig_aus_einfaedig` (§7) closes W4 against `Marken.Einfaedig`
    over the projected run. What the construction PROVES, though, is
    `Marken.verlauf_einfaedig`: every reachable stand is single-threaded
    (`StandEinfaedig σ` -- one stand, one point in time). That is a different
    level from `Einfaedig` (pairs of steps across time): a mark freed by one
    thread (`verbrauche`) and recreated by another (`erzeuge`) is owned by
    exactly one thread at every stand, yet named by two threads over the run.
    So no proof from `verlauf_einfaedig` alone can discharge W4 -- the trace
    link, that projected events name exactly what their thread owns, is the
    exact remainder, and it stands nowhere yet (no per-thread `Verlauf`
    through `exec` behind a real `Lauf D`).

    `SpurLink` names that remainder in minimal shape: every mark named by a
    projected event is owned by that event's thread at one shared reachable
    stand. Through `verlauf_einfaedig` that stand is single-threaded, and W4
    follows. `gesittet_aus_verlauf` is the bundle with the construction
    consumed: `hEin` narrows to a `Verlauf` plus the link. -/

/-- Trace link (booked remainder): every mark a projected event names is owned
    by that event's thread at one shared reachable stand. -/
def SpurLink (code : D.Marke → Nat) (l : Lauf D) (σ : Marken.Stand) : Prop :=
  ∀ (i : Nat) (f : Faden) (ei : Ereignis D),
    l[i]? = some (Schritt.mk f ei) →
    ∀ (m : D.Marke) (s : Nat), Res.marke m s ∈ ei.lambda →
      Marken.Besitzt σ f (code m)

/-- **W4 from the Verlauf.** `verlauf_einfaedig` through the trace link IS
    `marke_eindeutig` over the real run. -/
theorem marke_eindeutig_aus_verlauf
    (κ : Marken.MarkDekl) {σ : Marken.Stand} (v : Marken.Verlauf κ σ)
    (code : D.Marke → Nat) (l : Lauf D)
    (hlink : SpurLink (D := D) code l σ)
    (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat)
    (ei ej : Ereignis D)
    (hi : l[i]? = some (Schritt.mk f ei))
    (hj : l[j]? = some (Schritt.mk g ej))
    (hmi : Res.marke m s ∈ ei.lambda)
    (hmj : Res.marke m s' ∈ ej.lambda) : f = g :=
  Marken.verlauf_einfaedig κ v (code m) f g
    (hlink i f ei hi m s hmi) (hlink j g ej hj m s' hmj)

/-- **A `Gesittet` from the Verlauf.** The whole bundle with W4 supplied by
    `verlauf_einfaedig` plus the trace link instead of the bare premise. -/
theorem gesittet_aus_verlauf (l : Lauf D)
    (konsistent : ∀ f j, Konsistent (l.spur f j))
    (gut : ∀ f j, ∀ e ∈ l.spur f j, e.gut)
    (ausschluss : ∀ (j : Nat) (f : Faden) (L : D.Lock) (h : List D.Lock),
      l[j]? = some (Schritt.mk f (.nimmt L h)) → ∀ g, g ≠ f → ¬ l.haelt g L j)
    (κ : Marken.MarkDekl) {σ : Marken.Stand} (v : Marken.Verlauf κ σ)
    (code : D.Marke → Nat) (hlink : SpurLink (D := D) code l σ)
    (ungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet l :=
  ⟨konsistent, gut, ausschluss, marke_eindeutig_aus_verlauf κ v code l hlink,
    ungeteilt⟩

#print axioms Gabbro.Grammatik.marke_eindeutig_aus_verlauf
#print axioms Gabbro.Grammatik.gesittet_aus_verlauf

/-! ## 9. The bridge -- from `exec` traces to `Gesittet`, with honest coverage

    `hBridge` (`Ziel.lean`, `ziel_nutzer_last`): every interleaving of well-formed
    bodies is `Gesittet`. One body reaches W1 and W2 (through `Brav` over empty
    traces, inherited over tails -- `lauf_aus_brav`); no single-body sentence can
    reach W3 (exclusion speaks about FOREIGN lock primitives), W4 (one mark in
    one thread, across threads), or W5 (an unshared carrier belongs to one
    thread -- the declaration). This section discharges the bridge over EXACTLY
    the covered class, and names every premise that remains.

    COVERAGE (proved, not claimed):
    - W2 needs no suffix: `gut_without_suffix` -- any observation whose events
      all occur in the full per-thread trace is good. The suffix restriction is
      unnecessary for goodness (membership is all `Brav.gut_von_leer` reads).
    - W1 keeps the suffix: `Konsistent` reads `offen` of the REST (`passt`), so
      only tails (`drop`) inherit it. The covered interleavings are exactly the
      suffix-closed ones -- `IstVerschraenkung` -- and `covered_prefix` shows the
      class is closed under halting early (a temporal prefix stays covered).
    - `bruecke_exec_gesittet` discharges THOSE interleavings: per-thread `Brav`
      provenance (closed per body by `ziel_brav_aus_exec`) plus the three
      cross-thread shapes yields `Gesittet`. `ExecEng` (`Ziel.lean`) is the same
      bundle as a structure -- the narrowed corollary; this theorem is its
      unfolded form beside `lauf_aus_brav`.

    PREMISES (named, bounded):
    - W3 travels as `ForeignExclusion`: the mutual-exclusion promise of the
      FOREIGN lock primitives (`A_lock`). No sentence over one body can close
      it -- the other thread's `nimmt`/`gibt` steps are not in this body's
      trace. Hardware-assumption class, goal-conform: named here, and BOUNDED
      to lock takes (it constrains only `nimmt` steps -- accesses, releases,
      and marks pass through untouched). THE single remaining HW-adjacent
      premise: W4 is construction (`Marken.lean`), W5 is declaration
      (`Geteilt.lean` wiring, see below).
    - W4 travels as `hEin`: `Einfaedig` over the projected run. Where a
      per-thread `Verlauf` plus the trace link stands, `SpurLink` narrows it --
      `bruecke_exec_gesittet_of_verlauf` consumes the construction instead.
      The link itself (projected events name what their thread owns) stands
      nowhere yet: no per-thread `Verlauf` through `exec` behind a real
      `Lauf D` -- rebooked cut, stated in §8.
    - W5 travels inline (the `ungeteilt` shape): the declaration side is
      discharged by `Geteilt.ungeteilt_aus_bau` (passing check plus static
      coverage gives one thread); what remains here is the run-to-`Bau` wiring
      (body-extraction coverage, cut C2 there) -- a declaration premise, not a
      hardware one.
    - The Owicki-Gries step is NOT here: valid sequential contracts surviving
      interleaving needs the joint model with frame disjointness -- stands
      nowhere yet, stays open (as in `Ziel.lean` §2b).
    - No `sorry`, no `admit`, no `axiom` -- the `#print axioms` lines below
      show only Lean's own (`propext`, `Classical.choice`, `Quot.sound`). -/

/-- (W3) as the named HW-adjacent premise: foreign lock exclusion. Who takes `L`
    takes it while no other thread holds it -- the promise of the FOREIGN lock
    primitives (`A_lock`), bounded to `nimmt` steps. -/
def ForeignExclusion (l : Lauf D) : Prop :=
  ∀ (j : Nat) (f : Faden) (L : D.Lock) (h : List D.Lock),
    l[j]? = some (Schritt.mk f (.nimmt L h)) → ∀ g, g ≠ f → ¬ l.haelt g L j

/-- W2 needs no suffix: any observation whose events all occur in the full
    per-thread trace is good. The suffix restriction of `lauf_aus_brav` is
    unnecessary for goodness -- `Brav.gut_von_leer` reads membership only. -/
theorem gut_without_suffix (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (f : Faden) {s : List (Ereignis D)} (hmem : ∀ e ∈ s, e ∈ voll f) :
    ∀ e ∈ s, e.gut := by
  intro e he
  obtain ⟨a, b, hempty, hbrav, hspur⟩ := hvoll f
  have hmem' : e ∈ b.spur := by rw [hspur]; exact hmem e he
  exact hbrav.gut_von_leer hempty hmem'

/-- The covered class is closed under halting early: a temporal prefix of a
    suffix-closed interleaving is suffix-closed (per thread, the observed trace
    at `j` in the prefix is the observed trace at `min n j` in the full run). -/
theorem covered_prefix (l : Lauf D) (voll : Faden → List (Ereignis D))
    (hvers : IstVerschraenkung l voll) (n : Nat) :
    IstVerschraenkung (l.take n) voll := by
  intro f j
  obtain ⟨k, hk⟩ := hvers f (min n j)
  refine ⟨k, ?_⟩
  unfold Lauf.spur
  rw [List.take_take, Nat.min_comm j n]
  exact hk

/-- **The bridge: from `exec` traces to `Gesittet`, over exactly the covered
    interleavings.** Per-thread `Brav` provenance (W1, W2 via `lauf_aus_brav`)
    plus the three cross-thread shapes (W3 as `ForeignExclusion`, W4 as `hEin`,
    W5 inline) yields `Gesittet`. -/
theorem bruecke_exec_gesittet (l : Lauf D) (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (hvers : IstVerschraenkung l voll)
    (hausschluss : ForeignExclusion (D := D) l)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code l))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet l := by
  obtain ⟨hkons, hgut⟩ := lauf_aus_brav l voll hvoll hvers
  exact gesittet_aus_einfaedig l hkons hgut hausschluss code hEin hungeteilt

/-- **The bridge through the per-thread Verlauf.** The same covered
    interleavings, with W4 supplied by `verlauf_einfaedig` plus the trace link
    (`SpurLink` narrows `hEin`) instead of the bare `Einfaedig` hypothesis. -/
theorem bruecke_exec_gesittet_of_verlauf (l : Lauf D)
    (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (hvers : IstVerschraenkung l voll)
    (hausschluss : ForeignExclusion (D := D) l)
    (κ : Marken.MarkDekl) {σ : Marken.Stand} (v : Marken.Verlauf κ σ)
    (code : D.Marke → Nat) (hlink : SpurLink (D := D) code l σ)
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet l := by
  obtain ⟨hkons, hgut⟩ := lauf_aus_brav l voll hvoll hvers
  exact gesittet_aus_verlauf l hkons hgut hausschluss κ v code hlink hungeteilt

#print axioms Gabbro.Grammatik.ForeignExclusion
#print axioms Gabbro.Grammatik.gut_without_suffix
#print axioms Gabbro.Grammatik.covered_prefix
#print axioms Gabbro.Grammatik.bruecke_exec_gesittet
#print axioms Gabbro.Grammatik.bruecke_exec_gesittet_of_verlauf

end Gabbro.Grammatik
