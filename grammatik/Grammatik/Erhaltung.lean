/-
  File:       Grammatik/Erhaltung.lean
  Subject:    The PRODUCER CONTRACT as specification: what the emitter must
              uphold, written as Lean shapes. Design only.

  Claim (in one sentence):
    The emitter earns trust per run through a correspondence certificate
    (every Gabbro evaluation site exactly once, in order, over ruled forms
    only, with no C site lacking a Gabbro preimage), through an alias
    obligation (no address arithmetic in the image, the 491 census sites
    named), and through a cost obligation (CerCo preserves the ops count,
    the production compiler is only measured by witness pairs) -- and the
    per-form ruling table below names all 49 slots with their status, the
    `?:` ruling as the filled template.

  Mapping to the measured base (read-only, not imported as code):
    `Ziel.lean` `CForm`/`Absenkung` -- the 19 named shapes this table rules on,
      and the bounded lowering the cost shape rests on.
    `dokumente/BEWEIS.md` Gegenstand 2 -- the census (64 forms over 8001
      lines: 34 allowed-and-used, 30 undecided), the two rulings (`?:`,
      `__builtin_unreachable`), the UB inventory rows 2/5/11/12, and the
      per-run coverage certificate (§4: completeness, order, closure,
      no additional effect).
    `dokumente/SYNTAX.md` §18 -- the closed-list sentence this file turns
      into data; the prose for the new §19 stands in
      `messung/SYNTAX-ERHALTUNG-ENTWURF.md` (this lane does NOT edit it).

  Proven here: NOTHING. There is no `theorem`, `lemma`, or `example` in
    this file on purpose: the sentences below are `Prop`-valued `def`s --
    the SHAPES of what a later lane proves, once the form table and the
    witness pairs stand. The emitter stays the trust base throughout.

  Premises (trusted, not proved):
    P1  The 19 `CForm` shapes are the named target language (`Ziel.lean`).
    P2  Each Gabbro primitive lowers to at most `proPrimitiv` C statements
        (`Absenkung`; the number 4 is itself unmeasured -- see `Ziel.lean`).
    P3  The census counts are faithful (`zaehle-c-formen.py`, 2026-08-31:
        64 forms, 30 undecided, 491 pointer-arithmetic sites).

  Cuts (booked, not hidden):
    C1  No emitter verification: nothing here reads `crates/`, and no `def`
        below mentions `emit.rs`. The certificate is specified; the
        recomputer (a second program with its own pattern) is cut, not faked.
    C2  What a C form MEANS is not modelled: the hand-written table entry
        plus its executable witness pair carry the meaning, and the
        common-mode failure (both tables from one text) is named, not closed.
    C3  `restrict` and `volatile` stay trust: priced option and axiom,
        carried as data (`beschraenkt_Preis`, `fluechtig_Preis`), never
        proved.
    C4  Not wired into `Grammatik.lean`: lane scope forbids the index edit;
        check this file directly with `lake env lean Grammatik/Erhaltung.lean`.
    C5  The 19 admissions below are the TEMPLATE ruling, not 19 rulings:
        each named shape still owes its one-by-one decision the way `?:`
        got its (`bedingtEntscheid`); the status field is what makes the
        debt countable.

  No `mathlib`, no `sorry`, no `admit`, no `axiom`.
-/
import Grammatik.Ziel

namespace Gabbro.Grammatik

/-! ## 1. Correspondence: exec-to-C, as data plus four Prop shapes -/

/-- One evaluation site on each side, joined by its form: the row of the
    per-run coverage certificate (`BEWEIS.md` §4). Sites are `Nat` ids;
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

/-- The census number this obligation answers (`BEWEIS.md` C1, §2 row 2):
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
    production compiler's count is MEASURED by witness pairs (`BEWEIS.md`
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

/-! ## 4. The ruling table: 19 named shapes, 30 census slots, one status -/

/-- The status every slot carries. `aufListe` names the PRICE of the form's
    semantics; `ausErzeuger` names the REPLACEMENT the generator writes
    instead. `offen` is countable debt, not a shrug. -/
inductive RulingStatus where
  | offen
  | aufListe (preis : String)
  | ausErzeuger (ersatz : String)
  deriving DecidableEq, Repr

/-- The 30 census slots (`BEWEIS.md` §1a: C1 = 7, C2 = 19, C3 = 4).
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
  | unerreichbarBuiltin-- C2: 5 sites; RULED once, kept at one site (`BEWEIS.md` §1b)
  | wennGnuC           -- C2: 5 sites; `#if defined(__GNUC__)` changes the program per compiler
  | fortStmt           -- C2: 3 sites (`continue`)
  | statikAssert       -- C2: 1 site (`_Static_assert`)
  | pfeilZugriff       -- C3: 704 sites; generous reading of "field access"
  | boolTyp            -- C3: 350 sites; `<stdbool.h>` for `_Bool`
  | boolLit            -- C3: 211 sites (`true`/`false`)
  | zusammZuweisung    -- C3: 24 sites; generous reading of "assignment"
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
    (`BEWEIS.md` row 11) -- priced option, never default (cut C3). -/
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
   .luecke .zeigerArithmetik .offen,
   .luecke .zeigerIndex .offen,
   .luecke .cInclude .offen,
   .luecke .cTypedef .offen,
   .luecke .cDefine .offen,
   .luecke .cEnum .offen,
   .luecke .bedingt bedingtEntscheid,
   .luecke .voidTyp .offen,
   .luecke .cAttribut .offen,
   .luecke .cInline .offen,
   .luecke .cConst .offen,
   .luecke .deref .offen,
   .luecke .adressVon .offen,
   .luecke .bitNicht .offen,
   .luecke .abbruchStmt .offen,
   .luecke .schrittStmt .offen,
   .luecke .cSizeof .offen,
   .luecke .logUndOder .offen,
   .luecke .doubleTyp .offen,
   .luecke .schleifeStmt .offen,
   .luecke .typOfErw .offen,
   .luecke .floatTyp .offen,
   .luecke .unerreichbarBuiltin (.aufListe "kept at one site: D005 plus the tag invariant; four deletable sites out of the generator"),
   .luecke .wennGnuC .offen,
   .luecke .fortStmt .offen,
   .luecke .statikAssert .offen,
   .luecke .pfeilZugriff (.aufListe "generous reading of field access"),
   .luecke .boolTyp (.aufListe "generous reading: <stdbool.h> for _Bool"),
   .luecke .boolLit (.aufListe "generous reading: boolean literals"),
   .luecke .zusammZuweisung (.aufListe "generous reading of assignment")]

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
    FALSE today (29 slots still `offen`) -- and that is the point: the
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

#print axioms Gabbro.Grammatik.entschieden
#print axioms Gabbro.Grammatik.satz_tafel
#print axioms Gabbro.Grammatik.satz_erzeugervertrag

end Gabbro.Grammatik
