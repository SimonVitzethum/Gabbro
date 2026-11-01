module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Geteilt.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Geteilt

/-- Tabellen-Träger als eigene Sorte, daneben `Carrier` (Schnitt C1, Entwurf:
    bindet die heutigen Beweise nicht um). -/
abbrev TabCarrier := Nat

/-- Global-Träger als eigene Sorte, daneben `Carrier` (Schnitt C1, Entwurf:
    bindet die heutigen Beweise nicht um). -/
abbrev GlobCarrier := Nat

/-- Faltung einer Seite: Tabelle nach zusammengelegtem Träger. -/
def carrierVonTab : TabCarrier → Carrier := fun t => t

/-- Faltung einer Seite: Global nach zusammengelegtem Träger. -/
def carrierVonGlob : GlobCarrier → Carrier := fun g => g

/-- Spiegel einer Seite: zusammengelegter Träger nach Tabelle. -/
def tabVonCarrier : Carrier → TabCarrier := fun c => c

/-- Spiegel einer Seite: zusammengelegter Träger nach Global. -/
def globVonCarrier : Carrier → GlobCarrier := fun c => c

/-- Faltung der geteilten Sorte in den zusammengelegten Träger. -/
def carrierVonSplit : TabCarrier ⊕ GlobCarrier → Carrier
  | .inl t => carrierVonTab t
  | .inr g => carrierVonGlob g

/-- Teilung des zusammengelegten Trägers in die geteilte Sorte; die
    Kennzeichnung `istTab` bleibt Behauptung der späteren Verdrahtung und wird
    hier nicht festgelegt. -/
def splitVonCarrier (istTab : Carrier → Bool) (c : Carrier) :
    TabCarrier ⊕ GlobCarrier :=
  if istTab c then .inl (tabVonCarrier c) else .inr (globVonCarrier c)

/-- Rundweg-Gestalt Tabelle: Spiegeln faltet zurück. -/
def tabRundweg (t : TabCarrier) : Prop :=
  tabVonCarrier (carrierVonTab t) = t

/-- Rundweg-Gestalt Global: Spiegeln faltet zurück. -/
def globRundweg (g : GlobCarrier) : Prop :=
  globVonCarrier (carrierVonGlob g) = g

/-- Rundweg-Gestalt Falten nach Teilen: Falten macht Teilen rückgängig. -/
def faltTeileForm (istTab : Carrier → Bool) (c : Carrier) : Prop :=
  carrierVonSplit (splitVonCarrier istTab c) = c

/-- Rundweg-Gestalt Teilen nach Falten, Tabellenseite. -/
def teileFaltFormTab (istTab : Carrier → Bool) (t : TabCarrier) : Prop :=
  splitVonCarrier istTab (carrierVonSplit (Sum.inl t)) = Sum.inl t

/-- Rundweg-Gestalt Teilen nach Falten, Globalseite. -/
def teileFaltFormGlob (istTab : Carrier → Bool) (g : GlobCarrier) : Prop :=
  splitVonCarrier istTab (carrierVonSplit (Sum.inr g)) = Sum.inr g

/-! ## 8. The split round-trips, proved (changes nothing above)

    The §7 shapes are Prop-defs; here they are discharged from the split
    types. `tabRundweg`/`globRundweg` hold for every carrier, `faltTeileForm`
    for every tag function (both branches fold back to `c`), and the two
    `teileFalt` forms hold under the matching tag premise -- the split can
    only return the injected side when the tag names it.

    The three `…Form` defs below mirror the `hinj`/`hdisj` premises that
    `Extraktion.lean` carries at `geteiltTab_trifft`/`geteiltGlob_trifft`/
    `geteiltAus_glob`: code injectivity per half and separation of the
    halves. Injectivity holds for the identity codes of cut C1 and is proved;
    separation does NOT hold in general (both halves fold through the same
    `Nat`) and stays a stated shape for downstream lanes to assume. -/

/-- Table round-trip: mirroring folds back. -/
theorem tabRundweg_holds (t : TabCarrier) : tabRundweg t := by rfl

/-- Global round-trip: mirroring folds back. -/
theorem globRundweg_holds (g : GlobCarrier) : globRundweg g := by rfl

/-- Fold after split is the identity, whatever the tag says: both branches
    fold back to `c`. -/
theorem faltTeile_holds (istTab : Carrier → Bool) (c : Carrier) :
    faltTeileForm istTab c := by
  unfold faltTeileForm splitVonCarrier
  by_cases h : istTab c = true
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    rfl

/-- Split after fold returns the table injection, provided the tag marks the
    folded code as a table. -/
theorem teileFaltTab_holds (istTab : Carrier → Bool) (t : TabCarrier)
    (h : istTab (carrierVonSplit (Sum.inl t)) = true) :
    teileFaltFormTab istTab t := by
  unfold teileFaltFormTab splitVonCarrier
  rw [if_pos h]
  rfl

/-- Split after fold returns the global injection, provided the tag marks the
    folded code as a global. -/
theorem teileFaltGlob_holds (istTab : Carrier → Bool) (g : GlobCarrier)
    (h : istTab (carrierVonSplit (Sum.inr g)) = false) :
    teileFaltFormGlob istTab g := by
  unfold teileFaltFormGlob splitVonCarrier
  have hne : ¬ istTab (carrierVonSplit (Sum.inr g)) = true := by
    rw [h]
    exact Bool.false_ne_true
  rw [if_neg hne]
  rfl

/-- Table-code injectivity as a shape: the `hinj` premise
    (`geteiltTab_trifft`) over the split table type. -/
def tabInjForm (tabs : List TabCarrier) : Prop :=
  ∀ t₁ ∈ tabs, ∀ t₂ ∈ tabs, carrierVonTab t₁ = carrierVonTab t₂ → t₁ = t₂

/-- Global-code injectivity as a shape: the `hinj` premise
    (`geteiltGlob_trifft`) over the split global type. -/
def globInjForm (globs : List GlobCarrier) : Prop :=
  ∀ g₁ ∈ globs, ∀ g₂ ∈ globs, carrierVonGlob g₁ = carrierVonGlob g₂ → g₁ = g₂

/-- Separation of the carrier halves as a shape: the `hdisj` premise
    (`geteiltAus_glob`) -- no table code meets a global code. Stated, not
    proved: under the identity codes of cut C1 it fails in general. -/
def halvesDisjointForm (tabs : List TabCarrier)
    (globs : List GlobCarrier) : Prop :=
  ∀ t ∈ tabs, ∀ g ∈ globs, carrierVonTab t ≠ carrierVonGlob g

/-- Table codes are injective: the codes ARE the carriers (cut C1). -/
theorem tabInj_all (tabs : List TabCarrier) : tabInjForm tabs := by
  intro t₁ _ t₂ _ h
  exact h

/-- Global codes are injective: the codes ARE the carriers (cut C1). -/
theorem globInj_all (globs : List GlobCarrier) : globInjForm globs := by
  intro g₁ _ g₂ _ h
  exact h

#print axioms Gabbro.Grammatik.Geteilt.tabRundweg_holds
#print axioms Gabbro.Grammatik.Geteilt.globRundweg_holds
#print axioms Gabbro.Grammatik.Geteilt.faltTeile_holds
#print axioms Gabbro.Grammatik.Geteilt.teileFaltTab_holds
#print axioms Gabbro.Grammatik.Geteilt.teileFaltGlob_holds
#print axioms Gabbro.Grammatik.Geteilt.tabInj_all
#print axioms Gabbro.Grammatik.Geteilt.globInj_all

/-! ## 9. World extension: the Seite partition over split carriers -/

/- C7 coordination: the Tab/Glob Bau -- which tables and globals exist
   and who writes them -- is owned by another wave. This section touches
   ONLY the World-partition defs: which side each split carrier sits on
   (`WeltSeiteBau`, `weltSeite`), what a cross-partition world step is
   (`WeltSchritt`, `quertWelt`, `weltRein`, `weltQuerSchritt`), and the
   discharge that separation forbids it
   (`getrennteWelt_keinQuerschritt`). The Adressraum side carries the
   region version (`Adressraum.WeltSeite`, `querSchritt`,
   `getrennteSeite_keinQuerschritt`); the fold between the two is
   `carrierVonSplit` (§7), whose round-trips §8 proves. -/

/-- The two sides, mirrored from `Adressraum.Seite` without the import:
    this file stays dependency-free (see the header mirror note). -/
inductive WSeite where
  | kern
  | user
  deriving DecidableEq, Repr

/-- The Seite partition over split world carriers: every table and every
    global sits on exactly one side. -/
def WeltSeiteBau :=
  TabCarrier ⊕ GlobCarrier → WSeite

/-- The side of one split world carrier under the partition. -/
def weltSeite (p : WeltSeiteBau) (c : TabCarrier ⊕ GlobCarrier) : WSeite :=
  p c

/-- A one-carrier world step: the carrier it touches and the side it
    runs on. An exec step runs ON one side; crossing is touching the
    other side's carrier. -/
structure WeltSchritt where
  traeger : TabCarrier ⊕ GlobCarrier
  seite : WSeite

/-- The step crosses the partition exactly when the touched carrier sits
    on the other side than the step runs on. -/
def quertWelt (p : WeltSeiteBau) (s : WeltSchritt) : Prop :=
  p s.traeger ≠ s.seite

/-- A step confined to its side: touched carrier and running side agree. -/
def weltRein (p : WeltSeiteBau) (s : WeltSchritt) : Prop :=
  p s.traeger = s.seite

/-- Confinement is the negation of crossing, by shape. -/
theorem weltRein_keinQueren (p : WeltSeiteBau) (s : WeltSchritt) :
    weltRein p s ↔ ¬ quertWelt p s := by
  unfold weltRein quertWelt
  constructor
  · intro h hc
    exact hc h
  · intro h
    by_cases heq : p s.traeger = s.seite
    · exact heq
    · exact absurd heq h

/-- A cross-partition world step: the same folded carrier touched once
    running user-side, once running kernel-side, both confined -- one
    carrier, both sides. `f` is the fold into the checked carrier
    (`carrierVonSplit`, §7); the Tab/Glob Bau behind it is owned
    elsewhere. -/
def weltQuerSchritt (p : WeltSeiteBau)
    (f : TabCarrier ⊕ GlobCarrier → Carrier) (a b : WeltSchritt) : Prop :=
  f a.traeger = f b.traeger ∧ a.seite = .user ∧ b.seite = .kern ∧
    weltRein p a ∧ weltRein p b

/-- **Discharge: separation entails no cross-partition world step.** If
    the partition factors through the fold -- the same folded code sits
    on the same side (the carrier-level separation premise; cf.
    `halvesDisjointForm`, stated where the codes collide and proved
    where they cannot) -- then no single folded carrier is touched
    confined from both sides at once. -/
theorem getrennteWelt_keinQuerschritt (p : WeltSeiteBau)
    (f : TabCarrier ⊕ GlobCarrier → Carrier)
    (hf : ∀ c₁ c₂, f c₁ = f c₂ → p c₁ = p c₂)
    (a b : WeltSchritt) (h : weltQuerSchritt p f a b) : False := by
  obtain ⟨hfold, ha, hb, hain, hbin⟩ := h
  unfold weltRein at hain hbin
  rw [ha] at hain
  rw [hb] at hbin
  have hsame : p a.traeger = p b.traeger := hf _ _ hfold
  rw [hain, hbin] at hsame
  simp only [reduceCtorEq] at hsame

/-- Speech probe: a single-sided partition factors through any fold, so
    the discharge applies. -/
example (f : TabCarrier ⊕ GlobCarrier → Carrier)
    (c₁ c₂ : TabCarrier ⊕ GlobCarrier) (_ : f c₁ = f c₂) :
    (fun _ => WSeite.user) c₁ = (fun _ => WSeite.user) c₂ :=
  by rfl

#print axioms Gabbro.Grammatik.Geteilt.weltRein_keinQueren
#print axioms Gabbro.Grammatik.Geteilt.getrennteWelt_keinQuerschritt
/-! ## 10. Owner marks on the producer path -- the sharing-level application

    `Syntax.lean:149` carries `eigner_nie_erzeugt` -- no signature produces an
    owner mark -- and `SYNTAX.md:1625` books it as true but unapplied. §5 of
    `Typen.lean` applies it to one call step; here it is applied to the closed
    world: along every call chain from the entries, the produced marks carry
    no owner mark, so an owner mark held anywhere in the world traces back to
    an entry's initial holdings. That entry context -- which linear value
    becomes the first mark, and at whose hands -- is the producer story `D026`
    waits for. Nothing below modifies `Bau` or the world-partition regions;
    the owner declaration stands beside them and reads the existing
    reachability (`schrittBis`, `geteilt_treu`) without touching it.
-/

/-- Owner marks, as numbers. Mirrors `D.Marke` cut down to identity. -/
abbrev OwnerMarke := Nat

/-- Who holds the first mark: the owner declaration beside the closed world.
    `eignerVon` folds `D.eigner` to the closed-world `Carrier`; `anfang` names
    the entry's initial holdings (the `Signaturkopf` story of `Marken.lean`
    cut C4); `erzeugtFn` mirrors `S.produziert` along the call graph. -/
structure OwnerAnfang where
  /-- Owner marks per carrier (`D.eigner`, folded). -/
  eignerVon : Carrier → List OwnerMarke
  /-- Initial holdings per entry function: the marks the entry starts with. -/
  anfang : Fn → List OwnerMarke
  /-- Produced marks per function (mirrors `S.produziert`). -/
  erzeugtFn : Fn → List OwnerMarke
  /-- The applied theorem: no function produces an owner mark
      (`eigner_nie_erzeugt`, `Syntax.lean:149`). A premise here, as `Bau`
      fields are premises above -- the wiring instantiates it. -/
  eigner_nie_erzeugt : ∀ f m, m ∈ erzeugtFn f → ¬ ∃ c, m ∈ eignerVon c

/-- Every mark produced along the reachable calls from entry `e`. -/
def weltErzeugt (W : OwnerAnfang) (ruft : Fn → List Fn) (fuel : Nat)
    (e : Fn) : List OwnerMarke :=
  (schrittBis ruft fuel e).flatMap W.erzeugtFn

/-- **The reachable producer path carries no owner mark.** Whatever the calls
    from the entries produce, no owner mark is among it. -/
theorem eigner_nie_in_welt (W : OwnerAnfang) (ruft : Fn → List Fn)
    (fuel : Nat) (e : Fn)
    (m : OwnerMarke) (hm : m ∈ weltErzeugt W ruft fuel e) :
    ¬ ∃ c, m ∈ W.eignerVon c := by
  unfold weltErzeugt at hm
  obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp hm
  exact W.eigner_nie_erzeugt g m hg

/-- **The first mark comes from the entry.** An owner mark held anywhere in
    the closed world -- initial holdings or produced along the calls -- was
    in the entry's initial holdings: the produced half cannot carry it. -/
theorem eigner_erster_aus_anfang (W : OwnerAnfang) (ruft : Fn → List Fn)
    (fuel : Nat) (e : Fn)
    (m : OwnerMarke) (_hmE : ∃ c, m ∈ W.eignerVon c)
    (hmem : m ∈ W.anfang e ++ weltErzeugt W ruft fuel e) :
    m ∈ W.anfang e := by
  rcases List.mem_append.mp hmem with h | h
  · exact h
  · exact absurd _hmE (eigner_nie_in_welt W ruft fuel e m h)

/-- **Owner-guarded and unshared means one thread.** An owner-guarded carrier
    that the declaration leaves unshared is reached by at most one thread --
    `geteilt_treu` applied to the owner case. The proof goes through
    unshared-ness; the owner premise selects the carriers this speaks about,
    and the two theorems above name where their first mark comes from. -/
theorem eigner_ungeteilt_ein_faden (B : Bau) (W : OwnerAnfang) (fuel : Nat)
    (h : pruefeUngeteilt B fuel = true)
    (c : Carrier) (hmem : c ∈ B.traeger) (hu : B.geteilt c = false)
    (m : OwnerMarke) (_hm : m ∈ W.eignerVon c)
    (f g : Nat) (hf : ErreichtBau B fuel f c) (hg : ErreichtBau B fuel g c) :
    f = g :=
  geteilt_treu B fuel h c hmem hu f g hf hg

#print axioms Gabbro.Grammatik.Geteilt.eigner_nie_in_welt
#print axioms Gabbro.Grammatik.Geteilt.eigner_erster_aus_anfang
#print axioms Gabbro.Grammatik.Geteilt.eigner_ungeteilt_ein_faden

/-! ## 11. Run-to-Bau wiring: the joint run over split carriers

    What §5 leaves open (cut C2, booked in the header): `ungeteilt_aus_baulauf`
    speaks about runs of folded carriers (`SchrittC = Nat × Carrier`). The (W5)
    shape downstream (`Gesittet.ungeteilt`, `ExecEng.ungeteilt`, `hungeteilt`)
    speaks about runs over the SPLIT sort (`D.Tab ⊕ D.Glob`): two accesses name
    the same split carrier `o`, and the flag is read through the fold. This
    section wires the joint run to the Bau: `ungeteilt_aus_lauf` lifts
    `geteilt_treu` from Bau-reachability to run-reachability over split
    carriers, discharging the `hungeteilt` shape for runs. `carrierVonSplit`
    (§7) is read, never rewritten; the §8 round-trips carry the tag-stable
    helpers (`faltLauf_split_stabil`, `laufTag_tab`, `laufTag_glob`).

    Narrowing, stated explicitly (no silent premise):

    N1. Entry discipline (cut C2, as in §5): the joint run is covered -- every
        access is reached statically (`BauLauf` over the fold: coverage plus
        only-declared-pairs-interleave). A run step outside static reachability
        is refused, not guessed.
    N2. Same split carrier: both steps name one split carrier `o`
        (`s₁.2 = s₂.2 = o`). Cross-side aliasing -- `inl t` vs `inr g` folding
        to one code -- is outside this section: ruling it out is
        `halvesDisjointForm` (§8), stated there and failing under the identity
        codes in general, so a downstream lane assumes it.
    No race-freedom is assumed: the conclusion holds for any two accesses,
    whether or not their threads interleave. -/

/-- A joint run over split carriers: thread and split carrier per access.
    Mirrors the `Lauf D` accesses behind `Gesittet.ungeteilt`, cut down to
    carrier identity (lock events play no role in (W5)). -/
abbrev LaufSplit := List (Nat × (TabCarrier ⊕ GlobCarrier))

/-- The fold of a joint run into the checked carrier run. -/
def faltLauf (l : LaufSplit) : List SchrittC :=
  l.map fun s => (s.1, carrierVonSplit s.2)

/-- Every split access folds into the folded run. -/
theorem mem_faltLauf (l : LaufSplit) (s : Nat × (TabCarrier ⊕ GlobCarrier))
    (h : s ∈ l) : (s.1, carrierVonSplit s.2) ∈ faltLauf l :=
  List.mem_map.mpr ⟨s, h, rfl⟩

/-- **Tag-stable fold.** Splitting a folded run carrier folds back to itself,
    under ANY tag -- `faltTeile_holds` (§8) applied to run carriers: the fold
    the checker reads is the fold the run touched, whichever side the tag
    names. -/
theorem faltLauf_split_stabil (istTab : Carrier → Bool)
    (o : TabCarrier ⊕ GlobCarrier) :
    carrierVonSplit (splitVonCarrier istTab (carrierVonSplit o)) =
      carrierVonSplit o :=
  faltTeile_holds istTab (carrierVonSplit o)

/-- **Per-side tag reading, table side.** Under the explicit tag-match premise
    the split of a folded table code returns the table injection --
    `teileFaltTab_holds` (§8) applied to run carriers. -/
theorem laufTag_tab (istTab : Carrier → Bool) (t : TabCarrier)
    (h : istTab (carrierVonSplit (Sum.inl t)) = true) :
    splitVonCarrier istTab (carrierVonSplit (Sum.inl t)) = Sum.inl t :=
  teileFaltTab_holds istTab t h

/-- **Per-side tag reading, global side.** Under the explicit tag-match premise
    the split of a folded global code returns the global injection --
    `teileFaltGlob_holds` (§8) applied to run carriers. -/
theorem laufTag_glob (istTab : Carrier → Bool) (g : GlobCarrier)
    (h : istTab (carrierVonSplit (Sum.inr g)) = false) :
    splitVonCarrier istTab (carrierVonSplit (Sum.inr g)) = Sum.inr g :=
  teileFaltGlob_holds istTab g h

/-- **Unshared from the joint run (`ungeteilt_aus_lauf`).** If the check passes
    and the folded joint run is covered (narrowing N1), two accesses naming the
    same split carrier `o` (narrowing N2) whose folded code is declared
    unshared are by the same thread -- `geteilt_treu` lifted from
    Bau-reachability to run-reachability, in the shape `hungeteilt` consumes. -/
theorem ungeteilt_aus_lauf (B : Bau) (fuel : Nat)
    (h : pruefeUngeteilt B fuel = true) (l : LaufSplit)
    (hl : BauLauf B fuel (faltLauf l))
    (o : TabCarrier ⊕ GlobCarrier)
    (hmem : carrierVonSplit o ∈ B.traeger)
    (hu : B.geteilt (carrierVonSplit o) = false)
    (s₁ s₂ : Nat × (TabCarrier ⊕ GlobCarrier))
    (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l)
    (hg : s₁.2 = s₂.2) (hc : s₁.2 = o) : s₁.1 = s₂.1 := by
  have e1 : (s₁.1, carrierVonSplit s₁.2) ∈ faltLauf l := mem_faltLauf l s₁ h₁
  have e2 : (s₂.1, carrierVonSplit s₂.2) ∈ faltLauf l := mem_faltLauf l s₂ h₂
  have hg' : carrierVonSplit s₁.2 = carrierVonSplit s₂.2 :=
    congrArg carrierVonSplit hg
  have hc' : carrierVonSplit s₁.2 = carrierVonSplit o :=
    congrArg carrierVonSplit hc
  exact ungeteilt_aus_baulauf B fuel h (faltLauf l) hl (carrierVonSplit o)
    hmem hu (s₁.1, carrierVonSplit s₁.2) (s₂.1, carrierVonSplit s₂.2)
    e1 e2 hg' hc'

/-- Speech probe: the checker computes over the split run's fold, and the
    theorem applies to the concrete declaration. -/
example (hl : BauLauf miniB 3 (faltLauf [(0, Sum.inl (7 : TabCarrier))])) :
    (0 : Nat) = 0 :=
  ungeteilt_aus_lauf miniB 3 rfl _ hl (Sum.inl (7 : TabCarrier))
    (by decide) rfl (0, Sum.inl (7 : TabCarrier)) (0, Sum.inl (7 : TabCarrier))
    (List.mem_cons.mpr (Or.inl rfl)) (List.mem_cons.mpr (Or.inl rfl)) rfl rfl

#print axioms Gabbro.Grammatik.Geteilt.mem_faltLauf
#print axioms Gabbro.Grammatik.Geteilt.faltLauf_split_stabil
#print axioms Gabbro.Grammatik.Geteilt.laufTag_tab
#print axioms Gabbro.Grammatik.Geteilt.laufTag_glob
#print axioms Gabbro.Grammatik.Geteilt.ungeteilt_aus_lauf

end Gabbro.Grammatik.Geteilt
