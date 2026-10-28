/- Part 5 of 9 of `Extraktion` (split by instrumente/teile/lean-teilen.py; the umbrella `Extraktion.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Extraktion.T4

namespace Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

/-! ## 16. Die Treue der gerechneten Huellen: Rumpf, Vertrag, Traeger, Lauf

    (Bahn 123, Saetze -- Anhang: nichts Bestehendes ist geaendert, kein
    Schnitt geoeffnet.)

    Was §8 fuer Kanten/Fuesse/Paare ueber der W-EXT-Traversierung und §15
    fuer die Vertrags-Huellen bewies, steht hier geschlossen nebeneinander --
    ueber denselben Rechnungen, nicht ueber Nacherzaehlungen:

    * `liesTreue_aus_liesAus` ist die fehlende Schwester von
      `liesTreueMitVertrag`/`liesTreueMitInv`: die Rumpf-Huelle `liesAus`
      (§12) hatte bisher KEINEN Treue-Satz -- jede Lesung in der Domaene
      landet in der gerechneten Code-Liste. Damit traegt jede der drei
      Huellschichten (Rumpf, Vertrag, Vertrag-mit-Invarianten) ihren Satz.
    * `liestTab_in_liestVertragTab`/`liestGlob_in_liestVertragGlob` und
      `liestVertragTab_in_MitInvTab`/`liestVertragGlob_in_MitInvGlob`
      schichten die Huellen (Rumpf IN Vertrag IN Invarianten), und
      `liesAus_in_MitVertrag`/`liesAusMitVertrag_in_MitInv` heben die
      Schichtung auf die Code-Listen: keine Lesung geht beim Erweitern
      verloren.
    * `fussAus_in_traegerAus`/`liesAus_in_traegerAus`/
      `liesAusMitVertrag_in_traegerAus`/`liesAusMitInv_in_traegerAus` legen
      jeden gerechneten Fussabdruck in die Traegerdomaene (`traegerAus`), und
      `bauAus_schreibtFn_in_traeger` hebt das auf den `Geteilt.Bau`: was der
      errechnete Bau als beruehrt meldet, liegt in seinem `traeger` -- die
      `hmem`-Seite der `geteilt_treu`-Praemissen, eingeloeost statt getragen.
      Die `hu`-Seite (`geteilt`-Marke) loesen `geteiltAus_tab`/
      `geteiltAus_glob`/`geteiltAus_fremd` (§4) ein.
    * `eintritt_aus_baulaufSpiegel_aus_bau` und
      `nur_deklariert_aus_baulaufSpiegel_aus_bau` tragen zwei weitere
      `Geteilt`-Saetze auf die Spiegel-Form: jeder Schritt hat einen Eintritt
      (`lauf_hat_eintritt`), zwei Faeden nennen ein deklariertes Paar
      (`nur_deklariert_teilt_lauf`) -- dieselbe Verdrahtung wie
      `ungeteilt_aus_baulauf_aus_bau` (§9).

    Gebucht, nicht versteckt (die Verweigerungspflichten des Pruefers, mit
    der jeweils fehlenden Regel beim Namen -- `offeneVerweigerungspflichten`
    fuehrt sie als ein Register):
    B1. `kantenVoll`: Zeigerziele (`callInd`, `bindCallInd`) und fremde
        Ruempfe (`axiomCall`, `bindAxiom`) liefern keine Kante (S2), Codes
        ausserhalb der Domaene wirft `ruftNorm` (fehlende Regel: keine
        statische Aufloesung indirekter/fremder Ziele -- verweigern,
        fail-closed wie `W003`).
    B2. `liesVollMitVertrag` (darin `liesVoll`): Lesungen ausserhalb der
        Domaene -- Rumpf, `requires`/`ensures`, geschuldete Invarianten --
        wirft `liesAus`/`liesAusMitVertrag`/`liesAusMitInv` (fehlende Regel:
        keine Domaene fuer fremde Orte -- verweigern, S3/S6/S7).
    B3. `paarVoll`: haengende (`hbound`) und unerklaerte (`hvoll`) Paare wirft
        `nebenAus` (fehlende Regel: kein Lauf ausserhalb der Eintritte und
        kein Paar ausserhalb der Fassung -- verweigern, S4).
    B4. `liesTreue` IN den Bau: unbeweisbar fuer `bauAus` -- der Bau traegt
        nur Schreib-Effekte (`fussAus`), die Lesehuelle lebt in `liesAus*`,
        in keinem `Bau`-Feld (fehlende Regel: kein `Bau`-Feld traegt die
        Lesehuelle -- ein Pruefer, der Lesungen im Bau braucht, verweigert;
        ein `lesesFn`-Feld aenderte `Geteilt.Bau` und `bauAus` und liegt
        ausserhalb dieses Anhangs).
    B5. R1a/R1b/R1c wie im §12-Nachtrag gebucht: `old(…)` als Zwei-Welt-Lesung,
        nur-Welt-Praedikate ueber geteilter Umgebung, fremde Rufziele.
 -/

/-- **Lesetreue der Rumpf-Huelle:** jede Lesung in der Domaene landet in der
    gerechneten Code-Liste -- die fehlende Schwester von
    `liesTreueMitVertrag`/`liesTreueMitInv` (§15) fuer `liesAus` (§12). -/
theorem liesTreue_aus_liesAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D) :
    (∀ f ∈ fns, ∀ t ∈ liestTab P f,
      tabCode t ∈ tabs.map tabCode →
        tabCode t ∈ liesAus tabs tabCode globs globCode fns fnCode P (fnCode f)) ∧
    (∀ f ∈ fns, ∀ g ∈ liestGlob P f,
      globCode g ∈ globs.map globCode →
        globCode g ∈ liesAus tabs tabCode globs globCode fns fnCode P (fnCode f)) := by
  constructor
  · intro f hf t ht hdom
    show tabCode t ∈ liesAus tabs tabCode globs globCode fns fnCode P (fnCode f)
    unfold liesAus
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inl (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨t, ht, rfl⟩, decide_eq_true hdom⟩))⟩
  · intro f hf g hg hdom
    show globCode g ∈ liesAus tabs tabCode globs globCode fns fnCode P (fnCode f)
    unfold liesAus
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inr (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨g, hg, rfl⟩, decide_eq_true hdom⟩))⟩

/-- Die Rumpf-Huelle liegt in der Vertrags-Huelle (Traegerhaelfte). -/
theorem liestTab_in_liestVertragTab (P : Programm D) (f : D.Fn) (t : D.Tab)
    (h : t ∈ liestTab P f) : t ∈ liestVertragTab P f := by
  unfold liestTab at h
  obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
  cases o with
  | inl t' =>
      have heq : t' = t := by simpa using hfo
      rw [heq] at ho
      unfold liestVertragTab
      exact List.mem_filterMap.mpr
        ⟨.inl t, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ho))), rfl⟩
  | inr _ =>
      simp only [reduceCtorEq] at hfo

/-- Die Rumpf-Huelle liegt in der Vertrags-Huelle (Globalhaelfte). -/
theorem liestGlob_in_liestVertragGlob (P : Programm D) (f : D.Fn) (g : D.Glob)
    (h : g ∈ liestGlob P f) : g ∈ liestVertragGlob P f := by
  unfold liestGlob at h
  obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
  cases o with
  | inl _ =>
      simp only [reduceCtorEq] at hfo
  | inr g' =>
      have heq : g' = g := by simpa using hfo
      rw [heq] at ho
      unfold liestVertragGlob
      exact List.mem_filterMap.mpr
        ⟨.inr g, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ho))), rfl⟩

/-- Die Vertrags-Huelle liegt in der Invarianten-Huelle (Traegerhaelfte). -/
theorem liestVertragTab_in_MitInvTab (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (t : D.Tab)
    (h : t ∈ liestVertragTab P f) : t ∈ liestVertragMitInvTab P f invs := by
  unfold liestVertragTab at h
  obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
  cases o with
  | inl t' =>
      have heq : t' = t := by simpa using hfo
      rw [heq] at ho
      unfold liestVertragMitInvTab liestVertragMitInv
      exact List.mem_filterMap.mpr
        ⟨.inl t, List.mem_append.mpr (Or.inl ho), rfl⟩
  | inr _ =>
      simp only [reduceCtorEq] at hfo

/-- Die Vertrags-Huelle liegt in der Invarianten-Huelle (Globalhaelfte). -/
theorem liestVertragGlob_in_MitInvGlob (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (g : D.Glob)
    (h : g ∈ liestVertragGlob P f) : g ∈ liestVertragMitInvGlob P f invs := by
  unfold liestVertragGlob at h
  obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
  cases o with
  | inl _ =>
      simp only [reduceCtorEq] at hfo
  | inr g' =>
      have heq : g' = g := by simpa using hfo
      rw [heq] at ho
      unfold liestVertragMitInvGlob liestVertragMitInv
      exact List.mem_filterMap.mpr
        ⟨.inr g, List.mem_append.mpr (Or.inl ho), rfl⟩

/-- Die Rumpf-Codes ueberleben die Vertrags-Erweiterung: keine Lesung geht
    beim Erweitern verloren. -/
theorem liesAus_in_MitVertrag (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (n : Nat) (c : Nat)
    (h : c ∈ liesAus tabs tabCode globs globCode fns fnCode P n) :
    c ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P n := by
  unfold liesAus at h
  obtain ⟨f, hf, hmem⟩ := List.mem_flatMap.mp h
  unfold liesAusMitVertrag
  have hgoal : c ∈ ((((liestVertragTab P f).map tabCode).filter
        fun c => decide (c ∈ tabs.map tabCode)) ++
      (((liestVertragGlob P f).map globCode).filter
        fun c => decide (c ∈ globs.map globCode))) := by
    rcases List.mem_append.mp hmem with hT | hG
    · obtain ⟨hm, hd⟩ := List.mem_filter.mp hT
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
      exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨t, liestTab_in_liestVertragTab P f t ht, rfl⟩, hd⟩))
    · obtain ⟨hm, hd⟩ := List.mem_filter.mp hG
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
      exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨g, liestGlob_in_liestVertragGlob P f g hg, rfl⟩, hd⟩))
  exact List.mem_flatMap.mpr ⟨f, hf, hgoal⟩

/-- Die Vertrags-Codes ueberleben die Invarianten-Erweiterung. -/
theorem liesAusMitVertrag_in_MitInv (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (invs : List D.Inv) (n : Nat) (c : Nat)
    (h : c ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P n) :
    c ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs n := by
  unfold liesAusMitVertrag at h
  obtain ⟨f, hf, hmem⟩ := List.mem_flatMap.mp h
  unfold liesAusMitInv
  have hgoal : c ∈ ((((liestVertragMitInvTab P f invs).map tabCode).filter
        fun c => decide (c ∈ tabs.map tabCode)) ++
      (((liestVertragMitInvGlob P f invs).map globCode).filter
        fun c => decide (c ∈ globs.map globCode))) := by
    rcases List.mem_append.mp hmem with hT | hG
    · obtain ⟨hm, hd⟩ := List.mem_filter.mp hT
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
      exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨t, liestVertragTab_in_MitInvTab P f invs t ht, rfl⟩, hd⟩))
    · obtain ⟨hm, hd⟩ := List.mem_filter.mp hG
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
      exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨g, liestVertragGlob_in_MitInvGlob P f invs g hg, rfl⟩, hd⟩))
  exact List.mem_flatMap.mpr ⟨f, hf, hgoal⟩

/-- Der gerechnete Schreib-Fussabdruck liegt in der Traegerdomaene. -/
theorem fussAus_in_traegerAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat)
    (n : Nat) (c : Nat)
    (h : c ∈ fussAus tabs tabCode globs globCode fns fnCode n) :
    c ∈ traegerAus tabs tabCode globs globCode := by
  unfold fussAus at h
  obtain ⟨f, _, hmem⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hmem with hT | hG
  · obtain ⟨t, htmem, rfl⟩ := List.mem_map.mp hT
    unfold traegerAus
    exact List.mem_append.mpr
      (Or.inl (List.mem_map.mpr ⟨t, (List.mem_filter.mp htmem).1, rfl⟩))
  · obtain ⟨g, hgmem, rfl⟩ := List.mem_map.mp hG
    unfold traegerAus
    exact List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨g, (List.mem_filter.mp hgmem).1, rfl⟩))

/-- Die Rumpf-Lesehuelle liegt in der Traegerdomaene. -/
theorem liesAus_in_traegerAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (n : Nat) (c : Nat)
    (h : c ∈ liesAus tabs tabCode globs globCode fns fnCode P n) :
    c ∈ traegerAus tabs tabCode globs globCode := by
  unfold liesAus at h
  obtain ⟨f, _, hmem⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hmem with hT | hG
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hT
    have hd' : decide (c ∈ tabs.map tabCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inl (of_decide_eq_true hd'))
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hG
    have hd' : decide (c ∈ globs.map globCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inr (of_decide_eq_true hd'))

/-- Die Vertrags-Lesehuelle liegt in der Traegerdomaene. -/
theorem liesAusMitVertrag_in_traegerAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (n : Nat) (c : Nat)
    (h : c ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P n) :
    c ∈ traegerAus tabs tabCode globs globCode := by
  unfold liesAusMitVertrag at h
  obtain ⟨f, _, hmem⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hmem with hT | hG
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hT
    have hd' : decide (c ∈ tabs.map tabCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inl (of_decide_eq_true hd'))
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hG
    have hd' : decide (c ∈ globs.map globCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inr (of_decide_eq_true hd'))

/-- Die Invarianten-Lesehuelle liegt in der Traegerdomaene. -/
theorem liesAusMitInv_in_traegerAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (invs : List D.Inv) (n : Nat) (c : Nat)
    (h : c ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs n) :
    c ∈ traegerAus tabs tabCode globs globCode := by
  unfold liesAusMitInv at h
  obtain ⟨f, _, hmem⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hmem with hT | hG
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hT
    have hd' : decide (c ∈ tabs.map tabCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inl (of_decide_eq_true hd'))
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hG
    have hd' : decide (c ∈ globs.map globCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inr (of_decide_eq_true hd'))

/-- **Beruehrt heisst getragen:** was der errechnete Bau als Fussabdruck
    meldet, liegt in seinem `traeger` -- die `hmem`-Seite der
    `geteilt_treu`-Praemissen, eingeloeost statt getragen. -/
theorem bauAus_schreibtFn_in_traeger (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (g : Nat) (c : Nat)
    (h : c ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).schreibtFn g) :
    c ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).traeger := by
  have h' : c ∈ fussAus tabs tabCode globs globCode fns fnCode g := h
  show c ∈ traegerAus tabs tabCode globs globCode
  exact fussAus_in_traegerAus tabs tabCode globs globCode fns fnCode g c h'

/-- **Jeder Schritt hat einen Eintritt**, ueber dem errechneten Bau in
    Spiegel-Form (`Geteilt.lauf_hat_eintritt` durch `bauLaufSpiegel_genau`). -/
theorem eintritt_aus_baulaufSpiegel_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (fuel : Nat) (l : List (Nat × Nat))
    (hl : bauLaufSpiegel
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare) fuel l)
    (s : Nat × Nat) (hs : s ∈ l) :
    ∃ e, (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).eintritt[s.1]? = some e :=
  Geteilt.lauf_hat_eintritt _ fuel l
    ((bauLaufSpiegel_genau _ fuel l).mp hl) s hs

/-- **Nur deklarierte Paare teilen den Lauf**, ueber dem errechneten Bau in
    Spiegel-Form (`Geteilt.nur_deklariert_teilt_lauf` durch
    `bauLaufSpiegel_genau`). -/
theorem nur_deklariert_aus_baulaufSpiegel_aus_bau (P : Programm D)
    (fns : List D.Fn) (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (fuel : Nat) (l : List (Nat × Nat))
    (hl : bauLaufSpiegel
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare) fuel l)
    (s₁ s₂ : Nat × Nat) (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l) (hfg : s₁.1 ≠ s₂.1) :
    (s₁.1, s₂.1) ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).neben ∨
    (s₂.1, s₁.1) ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).neben :=
  Geteilt.nur_deklariert_teilt_lauf _ fuel l
    ((bauLaufSpiegel_genau _ fuel l).mp hl) s₁ s₂ h₁ h₂ hfg

/-- **Die Verweigerungspflichten des Pruefers, ein Register (gebucht, nicht
    bewiesen).** Jede Konjunktion nennt die fehlende Regel beim Namen (B1-B3
    im Kopf dieses Abschnitts): was die Rechnung wirft (`ruftNorm`,
    `liesAus*`, `nebenAus`), verweigert der Pruefer -- fail-closed, nicht
    geraten. -/
def offeneVerweigerungspflichten (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (invs : List D.Inv)
    (B : Geteilt.Bau) (Nb : Nebeneinander) : Prop :=
  kantenVoll P fns fnCode ∧
  liesVollMitVertrag P fns invs tabs tabCode globs globCode ∧
  paarVoll B Nb

#print axioms Gabbro.Grammatik.Extraktion.liesTreue_aus_liesAus
#print axioms Gabbro.Grammatik.Extraktion.liestTab_in_liestVertragTab
#print axioms Gabbro.Grammatik.Extraktion.liestGlob_in_liestVertragGlob
#print axioms Gabbro.Grammatik.Extraktion.liestVertragTab_in_MitInvTab
#print axioms Gabbro.Grammatik.Extraktion.liestVertragGlob_in_MitInvGlob
#print axioms Gabbro.Grammatik.Extraktion.liesAus_in_MitVertrag
#print axioms Gabbro.Grammatik.Extraktion.liesAusMitVertrag_in_MitInv
#print axioms Gabbro.Grammatik.Extraktion.fussAus_in_traegerAus
#print axioms Gabbro.Grammatik.Extraktion.liesAus_in_traegerAus
#print axioms Gabbro.Grammatik.Extraktion.liesAusMitVertrag_in_traegerAus
#print axioms Gabbro.Grammatik.Extraktion.liesAusMitInv_in_traegerAus
#print axioms Gabbro.Grammatik.Extraktion.bauAus_schreibtFn_in_traeger
#print axioms Gabbro.Grammatik.Extraktion.eintritt_aus_baulaufSpiegel_aus_bau
#print axioms Gabbro.Grammatik.Extraktion.nur_deklariert_aus_baulaufSpiegel_aus_bau

/-! ## 14. The `prog` extraction: per-thread atoms from bodies

    What `Ziel.lean` §9b books as its single residual footprint premise: the
    goal consumes `prog : PCProg D` (one atom per thread and step) as
    own-logic -- the per-thread atom sequences are handed in by hand, and
    each `PCSchritt` rule verifies the pointed-to atom (`hpc` positions it,
    `hΛa` ties it to the fired statement, `hmark`/`hcar` check it against
    the step's events). This section computes that annotation from bodies,
    in the `fussAus`/`stmtOrte` style: a traversal over `Stmt`/`Block`/
    `Endblock`/`Arms`/`GrundArms` flattens each body into its atom sequence
    (`stmtAtome` and friends), and `progAus` runs that flattening per
    thread through a thread-to-function map (`code`).

    Every constructor stands explicitly -- including the ones that emit NO
    atom -- for the same reason as in §1: a silent drop must read as a
    decision, not as an oversight.

    What emits an atom: exactly the constructs a `GenSchritt`/`PCSchritt`
    can fire. A leaf `Stmt` (`istBlatt = true`) fires as `blatt`, so it
    emits one atom: `leaf` carrying the statement's own `Λ` as `Λa` (hence
    `hΛa` closes by `rfl` -- `stmtAtome_blatt_eq`) and, as `cs`, the written
    carrier plus the `stmtOrte` read hull (`stmtTraeger`,
    `stmtAtome_traeger_deckt`). A `locks L` side fires as `take`/`rel`, so
    it emits the bracket around its body (`stmtAtome_locks`). Compound
    statements (`ite`, calls, loops, ...) never fire as steps -- they open
    into further steps -- so they emit only their sub-bodies' atoms (both
    arms of a branch: over-approximation, never less, as in §8).

    What emits NO atom, and why (booked, not hidden):
    S8. Block-level reads (`bind`, `awaits`, `exchange`, the `regLiesElse`
        promise, `narrow`/`pruefung`/`gleit` conditions): no `GenSchritt`
        case fires a `Block` form, so these reads produce no PC-step event.
        They stay covered by the `stmtOrte` hull (§12); threading them as
        steps is `Maschine.lean` §12's booked Block-continuation work.
    S9. Call arguments and branch conditions: calls and compounds never
        fire, so their argument/condition reads produce no PC-step event.
        Callee bodies reach threads through the thread map (`code`); the
        foreign-body duty stays with S7.
    S10. Terminal `Endblock` forms (`ret`, `leave`, `next`):
        `GenSchritt.blatt` fires `Stmt` only, so a terminal never fires.
        Its expression reads are booked with S8.
    S11. `axiomCall` writes come from the axiom declaration, not the body:
        `stmtTraeger` filters the declared domains (`tabs`/`globs`) by
        `D.aschreibt`/`D.agschreibt`, exactly as `fussAus` filters by
        `D.schreibt`/`D.gschreibt` (§3).

    Remainder (booked, not hidden): the execution link. What closes here is
    the program-text match -- extracted atoms carry the fired statement's
    `Λ` definitionally and cover its static footprint. Discharging `hmark`/
    `hcar` of a fired step against the extracted atom needs, per leaf, the
    `execStmt` event characterization (every event's `lambda` is the
    statement's `Λ`; every event's `traeger` is the written carrier or a
    `stmtOrte` carrier) -- unwritten, the same grain as the §13 keystone
    but one level up (steps instead of expressions).
-/

/-- The written carrier of one statement: the touch no read hull covers.
    Compounds carry none (they never fire); `axiomCall` carries its declared
    writes over the given domains (`fussAus` in §3). -/
def stmtTraeger (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .assignSlot t _ _ _ _ _ => [.inl t]
  | .assignThru _ t _ _ _ _ _ _ => [.inl t]
  | .assignSlotRef _ t _ _ _ _ _ _ => [.inl t]
  | .assignGlob g _ _ _ => [.inr g]
  | .putBytes t _ _ _ _ _ _ _ _ _ => [.inl t]
  | .assignVar _ _ => []
  | .shift t _ _ _ _ _ _ _ _ _ => [.inl t]
  | .ite _ _ _ => []
  | .onOption _ _ _ => []
  | .onTag _ _ => []
  | .onWhy _ _ => []
  | .call _ _ _ _ => []
  | .callInd _ _ _ _ => []
  | .locks _ _ _ => []
  | .breaking _ _ => []
  | .traverse _ _ _ => []
  | .retry _ _ _ _ => []
  | .forever _ _ _ => []
  | .axiomCall a _ _ _ _ _ _ =>
      (tabs.filter (D.aschreibt a)).map .inl ++
        (globs.filter (D.agschreibt a)).map .inr
  | .regWrite _ _ _ => []
  | .transition _ _ _ _ _ _ _ => []
  | .publish g _ _ _ _ _ => [.inr g]
  | .advances _ _ _ _ => []
  | .retires _ _ _ _ => []
  | .ret _ _ => []
  | .retWhy _ _ => []
  | .leave _ => []
  | .next _ => []


end Gabbro.Grammatik.Extraktion
