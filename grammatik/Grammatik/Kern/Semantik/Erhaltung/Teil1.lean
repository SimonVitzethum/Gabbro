module

public import Grammatik.Kern.Syntax.Ziel

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 1. Correspondence: exec-to-C, as data plus four Prop shapes -/

/-- One evaluation site on each side, joined by its form: the row of the
    per-run coverage certificate (`PROOF.md` §4). Sites are `Nat` ids;
    binding them to source spans is the recomputer's job (cut C1). -/
structure CorrSite where
  gabbroSite : Nat
  cSite : Nat
  form : CForm
  deriving DecidableEq, Repr

/-- The per-run certificate: the list of joined sites. -/
structure CorrCert where
  sites : List CorrSite
  deriving DecidableEq, Repr

/-- §4.1 Completeness: every Gabbro evaluation site appears at least once. -/
def corrComplete (gabbroSites : List Nat) (cert : CorrCert) : Prop :=
  ∀ g ∈ gabbroSites, ∃ s ∈ cert.sites, s.gabbroSite = g

/-- §4.2 Order: the C sites stand in the same order as the certificate. -/
def corrOrdered (cert : CorrCert) : Prop :=
  cert.sites.Pairwise fun a b => a.cSite ≤ b.cSite

/-- §4.3 Closure: every C form in the image stands in the ruled list.
    What "ruled" means is the table of §4 below (`entschieden`). -/
def corrClosed (cert : CorrCert) (ruled : CForm → Prop) : Prop :=
  ∀ s ∈ cert.sites, ruled s.form

/-- §4.4 No additional effect: no C site without a Gabbro preimage. -/
def corrNoExtra (gabbroSites : List Nat) (cert : CorrCert) : Prop :=
  ∀ s ∈ cert.sites, s.gabbroSite ∈ gabbroSites

/-! ## 2. Alias: no address arithmetic in the image, sites named -/

/-- The census number this obligation answers (`PROOF.md` C1, §2 row 2):
    491 `d->basis + 8` / `v->bytes + 4` sites against a row that promised
    none. Kept as data so the draft §19 can quote it, not as prose. -/
def ptrArithCensus : Nat := 491

/-- The two declaration shapes the 491 sites compute on: `basis` is
    `volatile uint8_t *`, `bytes` is `uint8_t *`. -/
inductive ArithSource where
  | basisPlus
  | bytesPlus
  deriving DecidableEq, Repr

/-- The obligation: the image carries its address-arithmetic sites openly.
    Fulfilled exactly when the list is empty; until then every entry is a
    named site id, not a residual risk of "none". -/
structure AliasObligation where
  arithSites : List Nat
  deriving DecidableEq, Repr

/-- Alias preserved: no address-arithmetic site in this image. -/
def aliasKept (o : AliasObligation) : Prop :=
  o.arithSites = []

/-! ## 3. Cost: CerCo preserves, production is measured -- as data -/

/-- Who carries the ops count from C to Asm. The distinction is DATA, not
    prose: only the `cerCo` carrier may be CLAIMED to preserve; the
    production compiler's count is MEASURED by witness pairs (`PROOF.md`
    §1b pattern), never proved here. -/
inductive CostCarrier where
  | cerCo
  | produktion
  deriving DecidableEq, Repr

/-- The cost claim of one compilation run: both counts plus who carries. -/
structure CostClaim where
  carrier : CostCarrier
  opsGabbro : Nat
  opsC : Nat
  deriving DecidableEq, Repr

/-- Cost preserved: under the CerCo carrier the C count IS the Gabbro
    count. For `produktion` this says nothing (it is the measured leg). -/
def costKept (k : CostClaim) : Prop :=
  k.carrier = .cerCo → k.opsC = k.opsGabbro

/-- Cost measured: under the production carrier, `paare` witness pairs ran
    green for this run. Zero pairs is not a measurement. -/
def costMeasured (k : CostClaim) (paare : Nat) : Prop :=
  k.carrier = .produktion → 0 < paare

/-- The lowering leg on the Gabbro side: one primitive becomes at most
    `proPrimitiv` C statements (premise P2, `Absenkung`). -/
def senkungBegrenzt (a : Absenkung) (cAnweisungen : Nat) : Prop :=
  cAnweisungen ≤ a.proPrimitiv

/-! ## 4. The ruling table: 19 named shapes, 30 census slots plus the
    syscall boundary, one status -/

/-- The status every slot carries. `aufListe` names the PRICE of the form's
    semantics; `ausErzeuger` names the REPLACEMENT the generator writes
    instead. `offen` is countable debt, not a shrug. -/
inductive RulingStatus where
  | offen
  | aufListe (preis : String)
  | ausErzeuger (ersatz : String)
  deriving DecidableEq, Repr

/-- The 30 census slots (`PROOF.md` §1a: C1 = 7, C2 = 19, C3 = 4),
    plus the syscall boundary slot below the census (lane S6,
    PLAN-SYSCALL.md item 1: generated, not found).
    Each doc line carries its site count, so the table quotes the census
    instead of restating it. -/
inductive OffeneForm where
  | zeigerArithmetik   -- C1: 491 sites; contradicts §2 row 2 as written
  | zeigerIndex        -- C1: 156 sites; `p[i]` IS `*(p+i)` by C's definition
  | cInclude           -- C1: 408 sites; preprocessor other than `#if`
  | cTypedef           -- C1: 240 sites; the list says typedef-free
  | cDefine            -- C1: 210 sites; "enum-free constants" plainly means it
  | cEnum              -- C1: 28 sites; the list says enum-free
  | bedingt            -- C1: 8 sites; RULED, the filled template below
  | voidTyp            -- C2: 930 sites; the type row never names it
  | cAttribut          -- C2: 766 sites
  | cInline            -- C2: 440 sites
  | cConst             -- C2: 419 sites
  | deref              -- C2: 141 sites
  | adressVon          -- C2: 111 sites
  | bitNicht           -- C2: 98 sites
  | abbruchStmt        -- C2: 51 sites (`break`)
  | schrittStmt        -- C2: 42 sites (`++`/`--`)
  | cSizeof            -- C2: 27 sites
  | logUndOder         -- C2: 23 sites; conditional like `?:`, second door
  | doubleTyp          -- C2: 18 sites; no float row at all, third door with `floatTyp`
  | schleifeStmt       -- C2: 11 sites (`while`)
  | typOfErw           -- C2: 9 sites (`__typeof__`)
  | floatTyp           -- C2: 8 sites; no float row at all
  | unerreichbarBuiltin-- C2: 5 sites; RULED once, kept at one site (`PROOF.md` §1b)
  | wennGnuC           -- C2: 5 sites; `#if defined(__GNUC__)` changes the program per compiler
  | fortStmt           -- C2: 3 sites (`continue`)
   | statikAssert       -- C2: 1 site (`_Static_assert`)
   | pfeilZugriff       -- C3: 704 sites; generous reading of "field access"
   | boolTyp            -- C3: 350 sites; `<stdbool.h>` for `_Bool`
   | boolLit            -- C3: 211 sites (`true`/`false`)
   | zusammZuweisung    -- C3: 24 sites; generous reading of "assignment"
   -- | syscallStub     -- NOT a census slot: the generated stub as an
   -- assumption boundary (lane S6, PLAN-SYSCALL.md item 1). The kernel
   -- behind the stub is the named assumption (`assume … falsifier …`);
   -- an unlisted errno or an out-of-range answer is the hardware outcome.
   | syscallStub
  deriving DecidableEq, Repr

/-- The filled template: the `?:` ruling the way every slot must be ruled.
    Generator wrong, not the list: all 8 sites are one line out of one
    emission site, and `if (v > z) { z = v; }` costs nothing at any level
    (`-O0`: 34 vs 34; `-O2`/`-Os`: byte-identical). The class stays open:
    `logUndOder` is the same conditional door, undecided. -/
def bedingtEntscheid : RulingStatus :=
  .ausErzeuger "if (v > z) { z = v; }"

/-- One row of the obligation table: either a named shape or a census
    slot, each WITH its status. The status field is what makes 30 holes
    countable instead of invisible. -/
inductive EntscheidZiel where
  | benannt (f : CForm) (s : RulingStatus)
  | luecke (u : OffeneForm) (s : RulingStatus)
  deriving DecidableEq, Repr

/-- Price of `beschraenkt` (`restrict`): a proof export into C's UB rules
    (`PROOF.md` row 11) -- priced option, never default (cut C3). -/
def beschraenktPreis : String :=
  "exports the effects-promise into C UB rules; only where the benchmark buys it"

/-- Price of `fluechtig` (`volatile`): weakly specified, MMIO practice --
    an axiom by name (cut C3). -/
def fluechtigPreis : String :=
  "axiom, named; seL4 excludes exactly this"

/-- The table: the 19 named shapes admitted with their price (template
    admissions per cut C5), the 30 census slots open -- except `bedingt`,
    which carries the filled template. -/
def tafel : List EntscheidZiel :=
  [.benannt .statisch (.aufListe "declaration header; no semantics beyond linkage"),
   .benannt .extern (.aufListe "foreign body; the null-spelling boundary lives here"),
   .benannt .zuweisung (.aufListe "E2: assignment is not an expression, one effect per statement"),
   .benannt .wenn (.aufListe "two-sided branch; no fall-through"),
   .benannt .schalter (.aufListe "exhaustive switch, no default"),
   .benannt .zaehlSchleife (.aufListe "counting loop over a bounded range"),
   .benannt .rueckgabe (.aufListe "single return of the declared type"),
   .benannt .sprungAlsSchleifenende (.aufListe "goto ONLY as a generated loop exit; counted, target unchecked"),
   .benannt .ruf (.aufListe "call to a declared or foreign body"),
   .benannt .literal (.aufListe "constant of a named type"),
   .benannt .name (.aufListe "identifier read; no implicit conversion at the read"),
   .benannt .feld (.aufListe "field access; padding bytes never read"),
   .benannt .index (.aufListe "index over the declared range; pointer-index is NOT this (see zeigerIndex)"),
   .benannt .wahlLesen (.aufListe "conditional read with the condition evaluated once"),
   .benannt .atomar (.aufListe "named ordering; orders under A10"),
   .benannt .beschraenkt (.aufListe beschraenktPreis),
   .benannt .fluechtig (.aufListe fluechtigPreis),
   .benannt .noreturn (.aufListe "proven non-return; the fall-through export needs D005 plus the tag invariant"),
   .benannt .asmEins (.aufListe "exactly one emission site; no downstream prover (16.2 (7))"),
   .luecke .zeigerArithmetik (.aufListe "no computed address outside place[expr]; unproven bound refused"),  -- ruled: LANGUAGE.md 5.2 + lane 142, re-decided over the scoped emitter map (withdrawn same-day on the unscoped one)
   .luecke .zeigerIndex (.aufListe "Adressrechnung; Pflicht je Stelle, in den Grenzen zu bleiben; UB-Zeile fuer den Aussenfall"),  -- ruled: messung/CFORM-REGEL-ZEIGERINDEX.md
    .luecke .cInclude (.aufListe "fixed four-header preamble; trust pinned by compile check, never proved"),  -- ruled: cut C3 (priced trust, carried never proved); preamble is emit.rs KOPF, byte-identical, cc -c -O0/-O2/-Os green
    .luecke .cTypedef (.aufListe "alias only; layout fixed once; unique names"),  -- ruled: messung/CFORM-REGEL-TYPEDEF.md
    .luecke .cDefine (.aufListe "object-like macro only; typed reads"),  -- ruled: messung/CFORM-REGEL-DEFINE.md
    .luecke .cEnum (.aufListe "closed alternative list as int"),  -- ruled: messung/CFORM-REGEL-ENUM.md
   .luecke .bedingt bedingtEntscheid,
   .luecke .voidTyp (.aufListe "empty result and parameter types as types; silence casts as deliberate"),  -- ruled: messung/CFORM-REGEL-VOID.md
   .luecke .cAttribut (.aufListe "truthful unused statement; checked pure/const effect promise; two-name section promise"),  -- ruled: messung/CFORM-REGEL-ATTRIBUT.md
   .luecke .cInline (.aufListe "non-binding inline request"),  -- ruled: messung/CFORM-REGEL-INLINE.md
   .luecke .cConst (.aufListe "read-only qualifier"),  -- ruled: messung/CFORM-REGEL-CONST.md
   .luecke .deref (.aufListe "plain dereference"),  -- ruled: messung/CFORM-REGEL-DEREF.md
   .luecke .adressVon (.aufListe "provenance-carrying address"),  -- ruled: messung/CFORM-REGEL-ADRESSE.md
   .luecke .bitNicht (.aufListe "double-cast width rule"),  -- ruled: messung/CFORM-REGEL-TILDE.md
   .luecke .abbruchStmt (.aufListe "Austritt aus dem Laufenskelett und Abschluss der Fallarme aus je zwei Emissionszeilen; kein Nutzerpfad; kein UB"),  -- ruled: messung/CFORM-REGEL-BREAK.md
   .luecke .schrittStmt (.aufListe "++ to += 1; exchange CAS untouched"),  -- ruled: messung/CFORM-REGEL-SENKUNG-142.md + ZULASSUNG-143 batch
   .luecke .cSizeof (.aufListe "layout-derived compile-time count; operands never evaluated"),  -- ruled: messung/CFORM-REGEL-SIZEOF.md
   .luecke .logUndOder (.aufListe "bedingte Auswertung mit Sequenzpunkt; Ergebnis 0 oder 1; Klammerpflicht beim Erzeuger"),  -- ruled: messung/CFORM-REGEL-LOGUNDODER.md
   .luecke .doubleTyp (.aufListe "f64 to double lowered; mixed-width refused"),  -- ruled: messung/CFORM-REGEL-SENKUNG-142.md + SENKUNG-144
   .luecke .schleifeStmt (.aufListe "retry skeleton only"),  -- ruled: messung/CFORM-REGEL-SENKUNG-142.md + SENKUNG-144
   .luecke .typOfErw (.aufListe "checked reference, single source"),  -- ruled: messung/CFORM-REGEL-SENKUNG-142.md + SENKUNG-144
   .luecke .floatTyp (.aufListe "f32 to float with suffix"),  -- ruled: messung/CFORM-REGEL-SENKUNG-144.md
   .luecke .unerreichbarBuiltin (.aufListe "kept at one site: D005 plus the tag invariant; four deletable sites out of the generator"),
   .luecke .wennGnuC (.aufListe "guard fires exactly when all arms return"),  -- ruled: messung/CFORM-REGEL-SENKUNG-144.md
   .luecke .fortStmt (.aufListe "Steuerung des Laufenskeletts aus einer Emissionszeile; kein Nutzerpfad; kein UB"),  -- ruled: messung/CFORM-REGEL-CONTINUE.md
   .luecke .statikAssert (.aufListe "declared spaces keep the assert"),  -- ruled: messung/CFORM-REGEL-SENKUNG-144.md
   .luecke .pfeilZugriff (.aufListe "generous reading of field access"),
   .luecke .boolTyp (.aufListe "generous reading: <stdbool.h> for _Bool"),
   .luecke .boolLit (.aufListe "generous reading: boolean literals"),
   .luecke .zusammZuweisung (.aufListe "generous reading of assignment"),
   -- The syscall stub as an assumption boundary (lane S6,
   -- PLAN-SYSCALL.md item 1): the stub is generated, so its shape is
   -- ruled here once instead of per site; the kernel behind it is the
   -- named assumption, and whatever the kernel answers outside the
   -- declared contract is the hardware outcome, never a value.
   .luecke .syscallStub (.aufListe "generated stub; the kernel behind it is the named assumption")]

/-- Decided: a named shape always counts as tabled; a slot counts exactly
    when its status stopped being `offen`. -/
def entschieden : EntscheidZiel → Prop
  | .benannt _ _ => True
  | .luecke _ .offen => False
  | .luecke _ _ => True

/-! ## 5. The sentences for later -- shapes only, no claims -/

/-- Later sentence 1 (correspondence): this run's certificate is complete,
    ordered, closed over the decided forms, and adds no effect. -/
def satz_korrespondenz (gabbroSites : List Nat) (cert : CorrCert) : Prop :=
  corrComplete gabbroSites cert ∧ corrOrdered cert ∧
    corrClosed cert (fun f => ∃ s : RulingStatus, .benannt f s ∈ tafel ∧ entschieden (.benannt f s)) ∧
    corrNoExtra gabbroSites cert

/-- Later sentence 2 (alias): this image carries no address arithmetic.
    Today `⟨List.replicate ptrArithCensus 0⟩` would be the honest witness,
    not the empty list -- the shape says which one the proof must take. -/
def satz_alias (o : AliasObligation) : Prop :=
  aliasKept o

/-- Later sentence 3 (cost): the CerCo leg preserves, the production leg
    is measured by `paare` pairs, and the lowering leg stays bounded. -/
def satz_kosten (k : CostClaim) (paare : Nat) (a : Absenkung) (cAnweisungen : Nat) : Prop :=
  costKept k ∧ costMeasured k paare ∧ senkungBegrenzt a cAnweisungen

/-- Later sentence 4 (table): every row of the table is decided. This is
    FALSE today (0 slots still `offen`) -- and that is the point: the
    shape counts the debt instead of hiding it. -/
def satz_tafel : Prop :=
  ∀ e ∈ tafel, entschieden e

/-- Later sentence 5 (the contract): correspondence, alias, cost, and the
    decided table, conjoined -- the SPECIFICATION the emitter must uphold,
    as one shape. -/
def satz_erzeugervertrag (gabbroSites : List Nat) (cert : CorrCert)
    (o : AliasObligation) (k : CostClaim) (paare : Nat)
    (a : Absenkung) (cAnweisungen : Nat) : Prop :=
  satz_korrespondenz gabbroSites cert ∧ satz_alias o ∧
    satz_kosten k paare a cAnweisungen ∧ satz_tafel

/-! ## 6. Correspondence, Lean side: recompute, then `decide` -/

/-- Recompute 1/4 (completeness, §4.1): every Gabbro site has a joined row.
    Boolean mirror of `corrComplete`, so a run's certificate can be CHECKED
    instead of believed. -/
def vollB (gabbroSites : List Nat) (cert : CorrCert) : Bool :=
  gabbroSites.all fun g => cert.sites.any fun s => decide (s.gabbroSite = g)

/-- Soundness 1/4: a successful recomputation IMPLIES completeness. -/
theorem vollB_sound (gabbroSites : List Nat) (cert : CorrCert)
    (h : vollB gabbroSites cert = true) : corrComplete gabbroSites cert := by
  have h' : gabbroSites.all (fun g => cert.sites.any fun s => decide (s.gabbroSite = g)) = true := by
    simpa only [vollB] using h
  have hall := List.all_eq_true.mp h'
  intro g hg
  have hmem := hall g hg
  have hex := List.any_eq_true.mp hmem
  obtain ⟨s, hs, heq⟩ := hex
  exact ⟨s, hs, of_decide_eq_true heq⟩

/-- Recompute 4/4 (no additional effect, §4.4): every row has a preimage. -/
def ohneExtraB (gabbroSites : List Nat) (cert : CorrCert) : Bool :=
  cert.sites.all fun s => decide (s.gabbroSite ∈ gabbroSites)

/-- Soundness 4/4: a successful recomputation IMPLIES no additional effect. -/
theorem ohneExtraB_sound (gabbroSites : List Nat) (cert : CorrCert)
    (h : ohneExtraB gabbroSites cert = true) : corrNoExtra gabbroSites cert := by
  have h' : cert.sites.all (fun s => decide (s.gabbroSite ∈ gabbroSites)) = true := by
    simpa only [ohneExtraB] using h
  have hall := List.all_eq_true.mp h'
  intro s hs
  exact of_decide_eq_true (hall s hs)

/-- Recompute 2/4 (order, §4.2) over the C-site ids. Adjacent check only;
    transitivity (`Nat.le_trans`) lifts it to every pair (`geordnetB_hilf`). -/
def geordnetB : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => if a ≤ b then geordnetB (b :: rest) else false

/-- The lift: a passing adjacent check bounds every later element. -/
theorem geordnetB_hilf : ∀ (l : List Nat) (a : Nat),
    geordnetB (a :: l) = true → ∀ y ∈ l, a ≤ y
  | [], _, _, y, hy => False.elim (List.not_mem_nil hy)
  | b :: rest, a, h, y, hy => by
    simp only [geordnetB] at h
    by_cases hab : a ≤ b
    · rw [if_pos hab] at h
      simp only [List.mem_cons] at hy
      cases hy with
      | inl heq => rw [heq]; exact hab
      | inr hin =>
        have hby : b ≤ y := geordnetB_hilf rest b h y hin
        exact Nat.le_trans hab hby
    · rw [if_neg hab] at h
      contradiction

/-- Soundness 2/4: a successful recomputation IMPLIES the order. -/
theorem geordnet_sound : ∀ (l : List Nat), geordnetB l = true → l.Pairwise (· ≤ ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.Pairwise.cons (fun _ hx => False.elim (List.not_mem_nil hx)) List.Pairwise.nil
  | a :: b :: rest, h => by
    have hunfold : geordnetB (a :: b :: rest) = (if a ≤ b then geordnetB (b :: rest) else false) := by
      simp only [geordnetB]
    by_cases hab : a ≤ b
    · have hrest : geordnetB (b :: rest) = true := by
        rw [hunfold, if_pos hab] at h
        exact h
      exact List.Pairwise.cons (geordnetB_hilf (b :: rest) a h) (geordnet_sound (b :: rest) hrest)
    · rw [hunfold, if_neg hab] at h
      contradiction

/-- Order over the certificate: project the C sites, then recompute. -/
def geordnetCertB (cert : CorrCert) : Bool :=
  geordnetB (cert.sites.map CorrSite.cSite)

/-- The projection preserves the order statement (`List.pairwise_map`). -/
theorem geordnetCertB_sound (cert : CorrCert) (h : geordnetCertB cert = true) :
    corrOrdered cert := by
  have hp := geordnet_sound _ (by simpa only [geordnetCertB] using h)
  have hm := List.pairwise_map.mp hp
  simpa only [corrOrdered] using hm

/-- Recompute 3/4 (closure, §4.3): the form's row is in the table. -/
def ruledB (f : CForm) : Bool :=
  tafel.any fun e => match e with
    | .benannt g _ => decide (g = f)
    | .luecke _ _ => false

/-- Soundness 3/4: a found row IS a decided table entry. -/
theorem ruledB_sound (f : CForm) (h : ruledB f = true) :
    ∃ s : RulingStatus, .benannt f s ∈ tafel ∧ entschieden (.benannt f s) := by
  have hex := List.any_eq_true.mp (by simpa only [ruledB] using h)
  obtain ⟨e, he, hb⟩ := hex
  cases e with
  | benannt g s =>
    have hgf : g = f := of_decide_eq_true hb
    subst hgf
    exact ⟨s, he, trivial⟩
  | luecke _ _ =>
    contradiction

/-- Every named shape has its row: all 19, one by one, each by `decide`. -/
theorem ruledB_voll : ∀ f, ruledB f = true := by
  intro f
  cases f <;> decide

/-! ## 4b. Witness pairs: the C2 linkage as a checked shape -/

/-- A witness pair: the probe file that exhibits a C form, the form itself,
    and the expected outcome. The probe lives under
    `messung/proben/zeugnis-c2/` and runs through `gabbro pruefe` (clean)
    plus `gabbro emit` (the named C fragment); the expectation here is data
    both sides recompute, not prose one side believes. -/
structure ZeugenPaar where
  probe : String
  form : CForm
  erwartetSauber : Bool
  deriving DecidableEq, Repr

/-- Linkage recomputation: the form is tabled (`ruledB`) and the probe name
    is non-empty. Boolean, so acceptance and rejection both close by
    `decide` -- the §6 pattern. -/
def zeugenPaarGueltig (p : ZeugenPaar) : Bool :=
  ruledB p.form && !p.probe.isEmpty

/-- Soundness: a valid pair IS a decided table entry for its form. -/
theorem zeugenPaar_sound (p : ZeugenPaar) (h : zeugenPaarGueltig p = true) :
    ∃ s : RulingStatus, .benannt p.form s ∈ tafel ∧ entschieden (.benannt p.form s) := by
  have h4 : ruledB p.form = true ∧ (!p.probe.isEmpty) = true := by
    simpa only [zeugenPaarGueltig, Bool.and_eq_true_iff] using h
  exact ruledB_sound _ h4.1

/-- The measured pairs: one row per probe in `messung/proben/zeugnis-c2/`.
    Each row names the C form the probe exhibits; `erwartetSauber` is true
    exactly when `gabbro pruefe` must report zero errors. -/
def c2Paare : List ZeugenPaar :=
  [{ probe := "c2-01-zuweisung", form := .zuweisung, erwartetSauber := true },
   { probe := "c2-02-wenn", form := .wenn, erwartetSauber := true },
   { probe := "c2-03-ruf", form := .ruf, erwartetSauber := true },
   { probe := "c2-04-rueckgabe", form := .rueckgabe, erwartetSauber := true },
   { probe := "c2-05-literal", form := .literal, erwartetSauber := true }]

/-- All pairs recompute green. -/
def c2AlleGueltig : Bool :=
  c2Paare.all zeugenPaarGueltig

/-- The linkage holds for every listed pair, by `decide`. -/
theorem c2Alle_decided : c2AlleGueltig = true := by decide

/-- Each listed pair names a tabled form -- the linkage the cut C2 owes. -/
theorem c2Paar_gedeckt (p : ZeugenPaar) (_h : p ∈ c2Paare)
    (hv : zeugenPaarGueltig p = true) :
    ∃ s : RulingStatus, .benannt p.form s ∈ tafel ∧ entschieden (.benannt p.form s) :=
  zeugenPaar_sound p hv

/-- Reject: an empty probe name is no witness, even over a tabled form. -/
example : zeugenPaarGueltig { probe := "", form := .literal, erwartetSauber := true } = false := by decide

#print axioms Gabbro.Grammatik.zeugenPaar_sound
#print axioms Gabbro.Grammatik.c2Alle_decided
end Gabbro.Grammatik
