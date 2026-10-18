/- Part 4 of 9 of `Extraktion` (split by instrumente/teile/lean-teilen.py; the umbrella `Extraktion.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Extraktion.T3

namespace Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

/-- The `requires` footprint discharges `HaengtAb` at the signature frame --
    the :387 premise for `requires`-shaped assertions. -/
theorem haengtAb_requires (P : Programm D) (f : D.Fn)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.requires f).orte → D.schreibt f t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.requires f).orte → D.gschreibt f g = true) :
    HaengtAb (D.schreibt f) (D.gschreibt f) (QRequires P f) :=
  haengtAb_weitet (fun t ht => hT t ((vertragW_mem _ t).mp ht))
    (fun g hg => hG g ((vertragG_mem _ g).mp hg))
    (haengtAb_expr (P.requires f))

/-- The `ensures` footprint discharges `HaengtAb` at the signature frame. -/
theorem haengtAb_ensures (P : Programm D) (f : D.Fn)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.ensures f).orte → D.schreibt f t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.ensures f).orte → D.gschreibt f g = true) :
    HaengtAb (D.schreibt f) (D.gschreibt f) (QEnsures P f) :=
  haengtAb_weitet (fun t ht => hT t ((vertragW_mem _ t).mp ht))
    (fun g hg => hG g ((vertragG_mem _ g).mp hg))
    (haengtAb_ensures_shape P f)

/-- An invariant footprint discharges `HaengtAb` at any covering frame --
    the :431 premise wherever the invariant is expression-shaped. -/
theorem haengtAb_invariante (P : Programm D) (i : D.Inv)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.invariante i).orte → W t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.invariante i).orte → G g = true) :
    HaengtAb W G (QInvariante P i) :=
  haengtAb_weitet (fun t ht => hT t ((vertragW_mem _ t).mp ht))
    (fun g hg => hG g ((vertragG_mem _ g).mp hg))
    (haengtAb_invariante_shape P i)

/-- `HaengtAb` distributes over conjunction: the combined contract hangs on
    one frame. -/
theorem haengtAb_konjunktion {W : D.Tab → Bool} {G : D.Glob → Bool}
    {Q₁ Q₂ : World D → Prop}
    (h₁ : HaengtAb W G Q₁) (h₂ : HaengtAb W G Q₂) :
    HaengtAb W G (fun σ => Q₁ σ ∧ Q₂ σ) := by
  intro σ σ' hRR
  show (Q₁ σ ∧ Q₂ σ) ↔ (Q₁ σ' ∧ Q₂ σ')
  rw [h₁ σ σ' hRR, h₂ σ σ' hRR]

/-- The :387 premise for contract-shaped assertions: `requires` and `ensures`
    together hang on the signature frame once both footprints lie inside. -/
theorem haengtAb_vertrag_gesamt (P : Programm D) (f : D.Fn)
    (hReqT : ∀ t : D.Tab, .inl t ∈ (P.requires f).orte → D.schreibt f t = true)
    (hReqG : ∀ g : D.Glob, .inr g ∈ (P.requires f).orte → D.gschreibt f g = true)
    (hEnsT : ∀ t : D.Tab, .inl t ∈ (P.ensures f).orte → D.schreibt f t = true)
    (hEnsG : ∀ g : D.Glob, .inr g ∈ (P.ensures f).orte → D.gschreibt f g = true) :
    HaengtAb (D.schreibt f) (D.gschreibt f)
      (fun σ => QRequires P f σ ∧ QEnsures P f σ) :=
  haengtAb_konjunktion
    (haengtAb_requires P f hReqT hReqG)
    (haengtAb_ensures P f hEnsT hEnsG)

/-- The :220 site for `requires`-shaped assertions: `StabilKette` from the
    computed footprint, no `HaengtAb` premise left. -/
theorem stabilKette_requires_gilt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (P : Programm D) (f : D.Fn)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.requires f).orte → D.schreibt f t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.requires f).orte → D.gschreibt f g = true) :
    StabilKette Nb J (D.schreibt f) (D.gschreibt f) (QRequires P f) :=
  stabilKette_gilt Nb J _ _ _ (haengtAb_requires P f hT hG)

/-- The :220 site for `ensures`-shaped assertions. -/
theorem stabilKette_ensures_gilt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (P : Programm D) (f : D.Fn)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.ensures f).orte → D.schreibt f t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.ensures f).orte → D.gschreibt f g = true) :
    StabilKette Nb J (D.schreibt f) (D.gschreibt f) (QEnsures P f) :=
  stabilKette_gilt Nb J _ _ _ (haengtAb_ensures P f hT hG)

/-- The :220 site for invariant-shaped assertions, at any covering frame. -/
theorem stabilKette_invariante_gilt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (P : Programm D) (i : D.Inv)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.invariante i).orte → W t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.invariante i).orte → G g = true) :
    StabilKette Nb J W G (QInvariante P i) :=
  stabilKette_gilt Nb J _ _ _ (haengtAb_invariante P i W G hT hG)

/-! ## 15. Vertraege in der §12-Rechnung: kein Vertragsfussabdruck faellt heraus

    `liestVertrag` fuehrt `requires`/`ensures` derselben Rechnung zu wie den
    Rumpf (`liestDirekt`), `liestVertragMitInv` nimmt die geschuldeten
    Invarianten dazu; `liesAusMitVertrag`/`liesAusMitInv` rechnen die Codes
    ueber der Domaene (`liesAus` in §12), und `liesTreueMitVertrag`/
    `liesTreueMitInv` beweisen die Deckung: keine Lesung -- Rumpf wie Vertrag
    -- faellt aus der Rechnung. `rahmenDecktLiesMitVertrag`/
    `rahmenDecktLiesMitInv` knuepfen die erweiterte Huelle an die Rahmen von
    `Interferenz.lean`; `liesVollMitVertrag` nennt die Pflicht des Pruefers
    auch fuer die Vertraege (unbewiesen als Form, wie `liesVoll`). -/

/-- The body PLUS its contracts: `requires` and `ensures` join the hull (S6). -/
def liestVertrag (P : Programm D) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte

/-- The table half of the contract hull. -/
def liestVertragTab (P : Programm D) (f : D.Fn) : List D.Tab :=
  (liestVertrag P f).filterMap fun o => match o with
    | .inl t => some t
    | .inr _ => none

/-- The global half of the contract hull. -/
def liestVertragGlob (P : Programm D) (f : D.Fn) : List D.Glob :=
  (liestVertrag P f).filterMap fun o => match o with
    | .inl _ => none
    | .inr g => some g

/-- Owed invariants join the hull: what `f` owes at `return`, it also reads. -/
def liestVertragMitInv (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) : List (D.Tab ⊕ D.Glob) :=
  liestVertrag P f ++
    (invs.filter (schuldet f)).flatMap (fun i => (P.invariante i).orte)

/-- The table half with owed invariants. -/
def liestVertragMitInvTab (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) : List D.Tab :=
  (liestVertragMitInv P f invs).filterMap fun o => match o with
    | .inl t => some t
    | .inr _ => none

/-- The global half with owed invariants. -/
def liestVertragMitInvGlob (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) : List D.Glob :=
  (liestVertragMitInv P f invs).filterMap fun o => match o with
    | .inl _ => none
    | .inr g => some g

/-- `requires` reads land in the contract hull. -/
theorem liestVertragTab_deckt_requires (P : Programm D) (f : D.Fn) (t : D.Tab)
    (h : (.inl t : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte) :
    t ∈ liestVertragTab P f := by
  unfold liestVertragTab
  exact List.mem_filterMap.mpr
    ⟨.inl t,
      by show (.inl t : D.Tab ⊕ D.Glob) ∈
             liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte
         exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))),
      rfl⟩

/-- `ensures` reads land in the contract hull. -/
theorem liestVertragTab_deckt_ensures (P : Programm D) (f : D.Fn) (t : D.Tab)
    (h : (.inl t : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte) :
    t ∈ liestVertragTab P f := by
  unfold liestVertragTab
  exact List.mem_filterMap.mpr
    ⟨.inl t,
      by show (.inl t : D.Tab ⊕ D.Glob) ∈
             liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte
         exact List.mem_append.mpr (Or.inr h),
      rfl⟩

/-- `requires` global reads land in the contract hull. -/
theorem liestVertragGlob_deckt_requires (P : Programm D) (f : D.Fn) (g : D.Glob)
    (h : (.inr g : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte) :
    g ∈ liestVertragGlob P f := by
  unfold liestVertragGlob
  exact List.mem_filterMap.mpr
    ⟨.inr g,
      by show (.inr g : D.Tab ⊕ D.Glob) ∈
             liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte
         exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))),
      rfl⟩

/-- `ensures` global reads land in the contract hull. -/
theorem liestVertragGlob_deckt_ensures (P : Programm D) (f : D.Fn) (g : D.Glob)
    (h : (.inr g : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte) :
    g ∈ liestVertragGlob P f := by
  unfold liestVertragGlob
  exact List.mem_filterMap.mpr
    ⟨.inr g,
      by show (.inr g : D.Tab ⊕ D.Glob) ∈
             liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte
         exact List.mem_append.mpr (Or.inr h),
      rfl⟩

/-- Owed invariant reads land in the hull with invariants. -/
theorem liestVertragMitInvTab_deckt_invariante (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (i : D.Inv) (hi : i ∈ invs)
    (hs : schuldet f i = true) (t : D.Tab)
    (h : (.inl t : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte) :
    t ∈ liestVertragMitInvTab P f invs := by
  unfold liestVertragMitInvTab
  exact List.mem_filterMap.mpr
    ⟨.inl t,
      by show (.inl t : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs
         exact List.mem_append.mpr (Or.inr
           (List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, hs⟩, h⟩)),
      rfl⟩

/-- Owed invariant global reads land in the hull with invariants. -/
theorem liestVertragMitInvGlob_deckt_invariante (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (i : D.Inv) (hi : i ∈ invs)
    (hs : schuldet f i = true) (g : D.Glob)
    (h : (.inr g : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte) :
    g ∈ liestVertragMitInvGlob P f invs := by
  unfold liestVertragMitInvGlob
  exact List.mem_filterMap.mpr
    ⟨.inr g,
      by show (.inr g : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs
         exact List.mem_append.mpr (Or.inr
           (List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, hs⟩, h⟩)),
      rfl⟩

/-- Case split on the contract hull: body, `requires`, or `ensures`. -/
theorem liestVertragTab_fall (P : Programm D) (f : D.Fn) (t : D.Tab)
    (h : t ∈ liestVertragTab P f) :
    t ∈ liestTab P f ∨ (.inl t : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte ∨
      (.inl t : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte := by
  have hmem : (.inl t : D.Tab ⊕ D.Glob) ∈ liestVertrag P f := by
    unfold liestVertragTab at h
    obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
    cases o with
    | inl t' =>
        have heq : t' = t := by simpa using hfo
        subst heq
        exact ho
    | inr _ =>
        simp at hfo
  have h2 : (.inl t : D.Tab ⊕ D.Glob) ∈
      liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte := hmem
  rcases List.mem_append.mp h2 with hV | hens
  · rcases List.mem_append.mp hV with hbody | hreq
    · left
      unfold liestTab
      exact List.mem_filterMap.mpr ⟨.inl t, hbody, rfl⟩
    · exact Or.inr (Or.inl hreq)
  · exact Or.inr (Or.inr hens)

/-- Case split on the global contract hull. -/
theorem liestVertragGlob_fall (P : Programm D) (f : D.Fn) (g : D.Glob)
    (h : g ∈ liestVertragGlob P f) :
    g ∈ liestGlob P f ∨ (.inr g : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte ∨
      (.inr g : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte := by
  have hmem : (.inr g : D.Tab ⊕ D.Glob) ∈ liestVertrag P f := by
    unfold liestVertragGlob at h
    obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
    cases o with
    | inl _ =>
        simp at hfo
    | inr g' =>
        have heq : g' = g := by simpa using hfo
        subst heq
        exact ho
  have h2 : (.inr g : D.Tab ⊕ D.Glob) ∈
      liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte := hmem
  rcases List.mem_append.mp h2 with hV | hens
  · rcases List.mem_append.mp hV with hbody | hreq
    · left
      unfold liestGlob
      exact List.mem_filterMap.mpr ⟨.inr g, hbody, rfl⟩
    · exact Or.inr (Or.inl hreq)
  · exact Or.inr (Or.inr hens)

/-- Case split with owed invariants: contract hull or an owed invariant. -/
theorem liestVertragMitInvTab_fall (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (t : D.Tab)
    (h : t ∈ liestVertragMitInvTab P f invs) :
    t ∈ liestVertragTab P f ∨
      ∃ i ∈ invs, schuldet f i = true ∧
        (.inl t : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte := by
  have hmem : (.inl t : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs := by
    unfold liestVertragMitInvTab at h
    obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
    cases o with
    | inl t' =>
        have heq : t' = t := by simpa using hfo
        subst heq
        exact ho
    | inr _ =>
        simp at hfo
  have h2 : (.inl t : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs := hmem
  rcases List.mem_append.mp h2 with hV | hI
  · left
    unfold liestVertragTab
    show t ∈ (liestVertrag P f).filterMap _
    exact List.mem_filterMap.mpr ⟨.inl t, hV, rfl⟩
  · right
    obtain ⟨i, hi, hmem_i⟩ := List.mem_flatMap.mp hI
    obtain ⟨hi_in, hi_sch⟩ := List.mem_filter.mp hi
    exact ⟨i, hi_in, hi_sch, hmem_i⟩

/-- Case split with owed invariants, global half. -/
theorem liestVertragMitInvGlob_fall (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (g : D.Glob)
    (h : g ∈ liestVertragMitInvGlob P f invs) :
    g ∈ liestVertragGlob P f ∨
      ∃ i ∈ invs, schuldet f i = true ∧
        (.inr g : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte := by
  have hmem : (.inr g : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs := by
    unfold liestVertragMitInvGlob at h
    obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
    cases o with
    | inl _ =>
        simp at hfo
    | inr g' =>
        have heq : g' = g := by simpa using hfo
        subst heq
        exact ho
  have h2 : (.inr g : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs := hmem
  rcases List.mem_append.mp h2 with hV | hI
  · left
    unfold liestVertragGlob
    show g ∈ (liestVertrag P f).filterMap _
    exact List.mem_filterMap.mpr ⟨.inr g, hV, rfl⟩
  · right
    obtain ⟨i, hi, hmem_i⟩ := List.mem_flatMap.mp hI
    obtain ⟨hi_in, hi_sch⟩ := List.mem_filter.mp hi
    exact ⟨i, hi_in, hi_sch, hmem_i⟩

/-- The read hull per code: body AND contracts, filtered to the domain
    (`liesAus` in §12, contracts included). -/
def liesAusMitVertrag (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D) :
    Nat → List Nat :=
  fun n =>
    ((fns.filter fun f => decide (fnCode f = n)).flatMap fun f =>
      (((liestVertragTab P f).map tabCode).filter fun c => decide (c ∈ tabs.map tabCode)) ++
      (((liestVertragGlob P f).map globCode).filter fun c => decide (c ∈ globs.map globCode)))

/-- The read hull per code, owed invariants included. -/
def liesAusMitInv (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (invs : List D.Inv) : Nat → List Nat :=
  fun n =>
    ((fns.filter fun f => decide (fnCode f = n)).flatMap fun f =>
      (((liestVertragMitInvTab P f invs).map tabCode).filter fun c => decide (c ∈ tabs.map tabCode)) ++
      (((liestVertragMitInvGlob P f invs).map globCode).filter fun c => decide (c ∈ globs.map globCode)))

/-- **No contract footprint falls out:** every read in the contract hull --
    body, `requires`, `ensures` -- lands in the code footprint. -/
theorem liesTreueMitVertrag (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D) :
    (∀ f ∈ fns, ∀ t ∈ liestVertragTab P f,
      tabCode t ∈ tabs.map tabCode →
        tabCode t ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P (fnCode f)) ∧
    (∀ f ∈ fns, ∀ g ∈ liestVertragGlob P f,
      globCode g ∈ globs.map globCode →
        globCode g ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P (fnCode f)) := by
  constructor
  · intro f hf t ht hdom
    show tabCode t ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P (fnCode f)
    unfold liesAusMitVertrag
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inl (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨t, ht, rfl⟩, decide_eq_true hdom⟩))⟩
  · intro f hf g hg hdom
    show globCode g ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P (fnCode f)
    unfold liesAusMitVertrag
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inr (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨g, hg, rfl⟩, decide_eq_true hdom⟩))⟩

/-- **No owed invariant footprint falls out.** -/
theorem liesTreueMitInv (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (invs : List D.Inv) :
    (∀ f ∈ fns, ∀ t ∈ liestVertragMitInvTab P f invs,
      tabCode t ∈ tabs.map tabCode →
        tabCode t ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs (fnCode f)) ∧
    (∀ f ∈ fns, ∀ g ∈ liestVertragMitInvGlob P f invs,
      globCode g ∈ globs.map globCode →
        globCode g ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs (fnCode f)) := by
  constructor
  · intro f hf t ht hdom
    show tabCode t ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs (fnCode f)
    unfold liesAusMitInv
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inl (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨t, ht, rfl⟩, decide_eq_true hdom⟩))⟩
  · intro f hf g hg hdom
    show globCode g ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs (fnCode f)
    unfold liesAusMitInv
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inr (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨g, hg, rfl⟩, decide_eq_true hdom⟩))⟩

/-- **Read-completeness with contracts (the checker's duty).** No read hangs
    outside the domain -- body (§12 `liesVoll`) or contracts: what falls, the
    checker refuses (unproved as a shape, like `liesVoll`). -/
def liesVollMitVertrag (P : Programm D) (fns : List D.Fn) (invs : List D.Inv)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat) : Prop :=
  liesVoll P fns tabs tabCode globs globCode ∧
  (∀ f ∈ fns, ∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte →
    tabCode t ∈ tabs.map tabCode) ∧
  (∀ f ∈ fns, ∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte →
    globCode g ∈ globs.map globCode) ∧
  (∀ f ∈ fns, ∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte →
    tabCode t ∈ tabs.map tabCode) ∧
  (∀ f ∈ fns, ∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte →
    globCode g ∈ globs.map globCode) ∧
  (∀ f ∈ fns, ∀ i ∈ invs, schuldet f i = true →
    (∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte →
      tabCode t ∈ tabs.map tabCode) ∧
    (∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte →
      globCode g ∈ globs.map globCode))

/-- **The hull in the frame, contracts included.** What bodies, `requires`,
    and `ensures` read lies in the named frame -- the shape the two-thread
    model consumes (`rahmenDecktLies` in §12, contracts included). -/
def rahmenDecktLiesMitVertrag (P : Programm D) (fns : List D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool) : Prop :=
  (∀ f ∈ fns, ∀ t ∈ liestVertragTab P f, W t = true) ∧
  (∀ f ∈ fns, ∀ g ∈ liestVertragGlob P f, G g = true)

/-- **The hull in the frame, owed invariants included.** -/
def rahmenDecktLiesMitInv (P : Programm D) (fns : List D.Fn)
    (invs : List D.Inv) (W : D.Tab → Bool) (G : D.Glob → Bool) : Prop :=
  (∀ f ∈ fns, ∀ t ∈ liestVertragMitInvTab P f invs, W t = true) ∧
  (∀ f ∈ fns, ∀ g ∈ liestVertragMitInvGlob P f invs, G g = true)

/-- The frame covers the contract hull once it covers the body and every
    contract footprint. -/
theorem rahmenDecktLiesMitVertrag_aus_rahmen (P : Programm D)
    (fns : List D.Fn) (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hR : rahmenDecktLies P fns W G)
    (hReqT : ∀ f ∈ fns, ∀ t : D.Tab,
      (.inl t : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte → W t = true)
    (hReqG : ∀ f ∈ fns, ∀ g : D.Glob,
      (.inr g : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte → G g = true)
    (hEnsT : ∀ f ∈ fns, ∀ t : D.Tab,
      (.inl t : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte → W t = true)
    (hEnsG : ∀ f ∈ fns, ∀ g : D.Glob,
      (.inr g : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte → G g = true) :
    rahmenDecktLiesMitVertrag P fns W G := by
  constructor
  · intro f hf t ht
    rcases liestVertragTab_fall P f t ht with hbody | hreq | hens
    · exact hR.1 f hf t hbody
    · exact hReqT f hf t hreq
    · exact hEnsT f hf t hens
  · intro f hf g hg
    rcases liestVertragGlob_fall P f g hg with hbody | hreq | hens
    · exact hR.2 f hf g hbody
    · exact hReqG f hf g hreq
    · exact hEnsG f hf g hens

/-- The frame covers the hull with owed invariants once it covers the
    contract hull and every owed invariant footprint. -/
theorem rahmenDecktLiesMitInv_aus_rahmen (P : Programm D)
    (fns : List D.Fn) (invs : List D.Inv)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hV : rahmenDecktLiesMitVertrag P fns W G)
    (hInvT : ∀ f ∈ fns, ∀ i ∈ invs, schuldet f i = true →
      ∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte → W t = true)
    (hInvG : ∀ f ∈ fns, ∀ i ∈ invs, schuldet f i = true →
      ∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte → G g = true) :
    rahmenDecktLiesMitInv P fns invs W G := by
  constructor
  · intro f hf t ht
    rcases liestVertragMitInvTab_fall P f invs t ht with hVtab | ⟨i, hi, hs, hmem⟩
    · exact hV.1 f hf t hVtab
    · exact hInvT f hf i hi hs t hmem
  · intro f hf g hg
    rcases liestVertragMitInvGlob_fall P f invs g hg with hVglob | ⟨i, hi, hs, hmem⟩
    · exact hV.2 f hf g hVglob
    · exact hInvG f hf i hi hs g hmem

#print axioms Gabbro.Grammatik.Extraktion.eval_liest_orte
#print axioms Gabbro.Grammatik.Extraktion.eval_aus_rahmen
#print axioms Gabbro.Grammatik.Extraktion.vertragW_mem
#print axioms Gabbro.Grammatik.Extraktion.vertragG_mem
#print axioms Gabbro.Grammatik.Extraktion.haengtAb_requires
#print axioms Gabbro.Grammatik.Extraktion.haengtAb_ensures
#print axioms Gabbro.Grammatik.Extraktion.haengtAb_invariante
#print axioms Gabbro.Grammatik.Extraktion.haengtAb_vertrag_gesamt
#print axioms Gabbro.Grammatik.Extraktion.stabilKette_requires_gilt
#print axioms Gabbro.Grammatik.Extraktion.stabilKette_ensures_gilt
#print axioms Gabbro.Grammatik.Extraktion.stabilKette_invariante_gilt
#print axioms Gabbro.Grammatik.Extraktion.liesTreueMitVertrag
#print axioms Gabbro.Grammatik.Extraktion.liesTreueMitInv
#print axioms Gabbro.Grammatik.Extraktion.rahmenDecktLiesMitVertrag_aus_rahmen
#print axioms Gabbro.Grammatik.Extraktion.rahmenDecktLiesMitInv_aus_rahmen


end Gabbro.Grammatik.Extraktion
