module

public import Grammatik.Kern.Syntax.Ziel
public import Grammatik.Kern.Semantik.Erhaltung.Teil1

@[expose] public section

namespace Gabbro.Grammatik

#print axioms Gabbro.Grammatik.c2Paar_gedeckt

/-- Closure over the certificate, from the row check. -/
def geschlossenB (cert : CorrCert) : Bool :=
  cert.sites.all fun s => ruledB s.form

/-- Soundness 3/4 over the certificate. -/
theorem geschlossenB_sound (cert : CorrCert) (h : geschlossenB cert = true) :
    corrClosed cert (fun f => ∃ s : RulingStatus, .benannt f s ∈ tafel ∧ entschieden (.benannt f s)) := by
  have h' : cert.sites.all (fun s => ruledB s.form) = true := by
    simpa only [geschlossenB] using h
  have hall := List.all_eq_true.mp h'
  intro s hs
  exact ruledB_sound _ (hall s hs)

/-- Closure holds for EVERY certificate: each of the 19 named shapes is
    tabled, so no image can fall outside the ruled list. (The SEMANTIC
    ruling -- what the row means -- stays cut C2.) -/
theorem geschlossen_immer (cert : CorrCert) :
    corrClosed cert (fun f => ∃ s : RulingStatus, .benannt f s ∈ tafel ∧ entschieden (.benannt f s)) :=
  geschlossenB_sound cert (List.all_eq_true.mpr (fun s _ => ruledB_voll s.form))

/-- Four passing legs ASSEMBLE the correspondence sentence. -/
theorem korrespondenz_aus_vieren (gabbroSites : List Nat) (cert : CorrCert)
    (hv : vollB gabbroSites cert = true) (hg : geschlossenB cert = true)
    (hn : ohneExtraB gabbroSites cert = true) (ho : geordnetCertB cert = true) :
    satz_korrespondenz gabbroSites cert :=
  ⟨vollB_sound _ _ hv, geordnetCertB_sound _ ho,
    geschlossenB_sound _ hg, ohneExtraB_sound _ _ hn⟩

/-- The per-run check, recomputed Lean-side: all four legs, right-nested so
    `Bool.and_eq_true_iff` splits it back into the four soundness premises. -/
def pruefeKorrespondenz (gabbroSites : List Nat) (cert : CorrCert) : Bool :=
  vollB gabbroSites cert && (geschlossenB cert && (ohneExtraB gabbroSites cert && geordnetCertB cert))

/-- Certificate validity: the recomputation SUCCEEDS. Decidable by
    construction, so acceptance and rejection both close by `decide` --
    the `Zeugnis.lean` (`GueltigAbleitung`) pattern. -/
abbrev GueltigKorrespondenz (gabbroSites : List Nat) (cert : CorrCert) : Prop :=
  pruefeKorrespondenz gabbroSites cert = true

/-- Soundness: a valid certificate IMPLIES the correspondence sentence.
    This file's direction, mirroring `zeugnis_sound`: the recomputer that
    would PRODUCE such a certificate stays cut (C1). -/
theorem korrespondenz_sound (gabbroSites : List Nat) (cert : CorrCert)
    (h : GueltigKorrespondenz gabbroSites cert) : satz_korrespondenz gabbroSites cert := by
  have hval : pruefeKorrespondenz gabbroSites cert = true := h
  have h4 : vollB gabbroSites cert = true ∧ geschlossenB cert = true ∧
      ohneExtraB gabbroSites cert = true ∧ geordnetCertB cert = true := by
    simpa only [pruefeKorrespondenz, Bool.and_eq_true_iff] using hval
  exact korrespondenz_aus_vieren _ _ h4.1 h4.2.1 h4.2.2.1 h4.2.2.2

/-- Accept: two sites, in order, over named forms, nothing more. -/
example : GueltigKorrespondenz [0, 1]
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal},
      {gabbroSite := 1, cSite := 1, form := .name}]⟩ := by decide

/-- Reject: Gabbro site 1 has no row (completeness fails loudly). -/
example : ¬ GueltigKorrespondenz [0, 1]
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal}]⟩ := by decide

/-- Reject: the C sites run backwards (order fails loudly). -/
example : ¬ GueltigKorrespondenz [0, 1]
    ⟨[{gabbroSite := 0, cSite := 1, form := .literal},
      {gabbroSite := 1, cSite := 0, form := .name}]⟩ := by decide

/-- Reject: a C site without a Gabbro preimage (no-extra fails loudly). -/
example : ¬ GueltigKorrespondenz [0]
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal},
      {gabbroSite := 5, cSite := 1, form := .name}]⟩ := by decide

/-- End to end: a valid certificate YIELDS the correspondence sentence. -/
example : satz_korrespondenz [0, 1]
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal},
      {gabbroSite := 1, cSite := 1, form := .name}]⟩ :=
  korrespondenz_sound _ _ (by decide)

/-- The empty run corresponds, vacuously: no site owes a row. -/
theorem korrespondenz_leer : satz_korrespondenz [] ⟨[]⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    exact False.elim (List.not_mem_nil hg)
  · exact List.Pairwise.nil
  · intro s hs
    exact False.elim (List.not_mem_nil hs)
  · intro s hs
    exact False.elim (List.not_mem_nil hs)

/-! ## 6b. The emitted witness: the C1 correspondence names its image -/

/-- The word the emitter writes into the image beside each emitted evaluation
    site (`crates/gabbro-check/src/emit.rs`, `emittiere_mit`, as the comment
    `/* gabbro-site <cSite> <form> */`). Naming the word is the C1 closure
    Lean-side: the recomputer (`instrumente/nachpruefer.py`) reads exactly
    this marker back. -/
def emittedMarker : String := "gabbro-site"

/-- The JSON field names of one certificate row, as the emitter writes them
    beside the C output (`CorrCert::to_json` in
    `crates/gabbro-check/src/corrcert.rs`). Machine-readable witness:
    `messung/proben/corrcert/korr-*.json` carry these names word for word. -/
def emittedRowFields : List String :=
  ["gabbroSite", "cSite", "form"]

/-- The word of one target shape: the `form` value a certificate row carries.
    Mirrors `CForm::as_str` in `crates/gabbro-check/src/corrcert.rs` one for
    one, so Lean rows, certificate JSON, and image markers spell every form
    with one word. -/
def cformWort : CForm → String
  | .statisch => "statisch"
  | .extern => "extern"
  | .zuweisung => "zuweisung"
  | .wenn => "wenn"
  | .schalter => "schalter"
  | .zaehlSchleife => "zaehlSchleife"
  | .rueckgabe => "rueckgabe"
  | .sprungAlsSchleifenende => "sprungAlsSchleifenende"
  | .ruf => "ruf"
  | .literal => "literal"
  | .name => "name"
  | .feld => "feld"
  | .index => "index"
  | .wahlLesen => "wahlLesen"
  | .atomar => "atomar"
  | .beschraenkt => "beschraenkt"
  | .fluechtig => "fluechtig"
  | .noreturn => "noreturn"
  | .asmEins => "asmEins"

/-- Marker agreement (the image direction of no-extra): every marked C site
    owns a certificate row in the same form word. The cert-only direction
    (`ohneExtraB`: every row has a preimage) cannot see an effect the image
    names but no row claims; this Boolean is what the recomputer checks the
    emitted construct against. -/
def markerStimmtB (cert : CorrCert) (marken : List (Nat × String)) : Bool :=
  marken.all fun m => cert.sites.any fun s =>
    decide (s.cSite = m.1) && decide (cformWort s.form = m.2)

/-- Accept: the marked image agrees with its rows, word for word. -/
example : markerStimmtB
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal},
      {gabbroSite := 1, cSite := 1, form := .name}]⟩
    [(0, "literal"), (1, "name")] = true := by decide

/-- Reject: the image marks C site 0 `name`, the row says `literal`. -/
example : markerStimmtB
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal}]⟩
    [(0, "name")] = false := by decide

/-! ## 7. Alias, Lean side: the dischargeable shape -/

/-- `aliasKept` is decidable: the obligation is CHECKABLE per image. -/
instance aliasKeptDec (o : AliasObligation) : Decidable (aliasKept o) :=
  inferInstanceAs (Decidable (o.arithSites = []))

/-- Discharge: the empty site list keeps the obligation, by `rfl`. -/
theorem alias_leer : aliasKept { arithSites := [] } := by rfl

/-- The census stands as data: 491 named sites (`PROOF.md` C1, §2 row 2). -/
theorem census_steht : ptrArithCensus = 491 := by rfl

/-- Accept: no address-arithmetic site in this image. -/
example : aliasKept ⟨[]⟩ := by decide

/-- Reject: one named site breaks the obligation. -/
example : ¬ aliasKept ⟨[0]⟩ := by decide

/-- Reject, honestly: today's image carries the whole census, not the empty
    list -- `⟨List.replicate ptrArithCensus 0⟩` is the witness the proof must
    one day TAKE, and it does not discharge. -/
example : ¬ aliasKept ⟨List.replicate ptrArithCensus 0⟩ := by decide

/-! ## 8. Cost, Lean side: who may claim, who must measure -/

/-- Both cost claims are decidable: per-run CHECKS, not prose. -/
instance costKeptDec (k : CostClaim) : Decidable (costKept k) :=
  inferInstanceAs (Decidable (k.carrier = .cerCo → k.opsC = k.opsGabbro))

instance costMeasuredDec (k : CostClaim) (paare : Nat) : Decidable (costMeasured k paare) :=
  inferInstanceAs (Decidable (k.carrier = .produktion → 0 < paare))

instance senkungDec (a : Absenkung) (n : Nat) : Decidable (senkungBegrenzt a n) :=
  inferInstanceAs (Decidable (n ≤ a.proPrimitiv))

/-- CerCo leg: under the CerCo carrier, equal counts ARE preservation. -/
theorem kosten_cerCo_gilt (k : CostClaim) (_hc : k.carrier = .cerCo)
    (heq : k.opsC = k.opsGabbro) : costKept k := by
  intro _
  exact heq

/-- Production leg, first half: under the production carrier `costKept`
    claims NOTHING -- diverging counts still satisfy it, vacuously. -/
theorem kosten_produktion_frei (k : CostClaim) (hc : k.carrier = .produktion) :
    costKept k := by
  intro hcontra
  rw [hc] at hcontra
  contradiction

/-- Production leg, second half: a measurement needs a carrier AND a pair. -/
theorem gemessen_produktion (k : CostClaim) (paare : Nat)
    (_hc : k.carrier = .produktion) (hpos : 0 < paare) :
    costMeasured k paare := by
  intro _
  exact hpos

/-- CerCo side of the measurement: nothing to measure, vacuously true. -/
theorem gemessen_cerCo_frei (k : CostClaim) (paare : Nat)
    (hc : k.carrier = .cerCo) : costMeasured k paare := by
  intro hcontra
  rw [hc] at hcontra
  contradiction

/-- The carrier distinction IS the data: every claim picks a side. -/
theorem traeger_trennt (k : CostClaim) :
    k.carrier = .cerCo ∨ k.carrier = .produktion := by
  cases k.carrier with
  | cerCo => exact Or.inl rfl
  | produktion => exact Or.inr rfl

/-- Bounded lowering from the measured bound: 17 per primitive
    (`messung/ABSENKUNG-MESSUNG.md`), so anything under 17 stays under. -/
theorem senkung_aus_schranke (cAnweisungen : Nat) (h : cAnweisungen ≤ 17) :
    senkungBegrenzt absenkung cAnweisungen := h

/-- Assemble the cost sentence from its three legs. -/
theorem kosten_satz_bauen (k : CostClaim) (paare : Nat) (a : Absenkung)
    (cAnweisungen : Nat) (h1 : costKept k) (h2 : costMeasured k paare)
    (h3 : senkungBegrenzt a cAnweisungen) :
    satz_kosten k paare a cAnweisungen :=
  ⟨h1, h2, h3⟩

/-- CerCo with equal counts: kept. -/
example : costKept ⟨.cerCo, 4, 4⟩ := by decide

/-- Production with DIVERGING counts: still `costKept` -- the claim lives
    on the CerCo leg only, and this is the measured leg. -/
example : costKept ⟨.produktion, 4, 9⟩ := by decide

/-- CerCo with diverging counts: NOT kept. -/
example : ¬ costKept ⟨.cerCo, 4, 9⟩ := by decide

/-- Production with two green pairs: measured. -/
example : costMeasured ⟨.produktion, 4, 9⟩ 2 := by decide

/-- Production with zero pairs: not a measurement. -/
example : ¬ costMeasured ⟨.produktion, 4, 9⟩ 0 := by decide

/-- The bound, both directions, at the measured number. -/
example : senkungBegrenzt absenkung 17 := by decide
example : ¬ senkungBegrenzt absenkung 18 := by decide

/-! ## 9. What stays cut: the debt, proved real -/

/-- `entschieden` is decidable: the table state is CHECKABLE per row, the way
    `aliasKept` (§7) and the cost claims (§8) carry their own instances. -/
instance entschiedenDec (e : EntscheidZiel) : Decidable (entschieden e) := by
  cases e with
  | benannt _ _ => exact isTrue trivial
  | luecke _ s =>
    cases s with
    | offen => exact isFalse (by simp only [entschieden, not_false_eq_true])
    | aufListe _ => exact isTrue trivial
    | ausErzeuger _ => exact isTrue trivial

/-- CLOSED 2026-09-11 (w01): was `¬ satz_tafel` witnessed by the open slot
    (formerly `tafel_nicht_geschlossen`). The last slot is now ruled with price --
    fixed four-header preamble, cut-C3 trust carried never proved -- so `decide`
    closes the table. The old witness `(.luecke .cInclude .offen) ∈ tafel` no
    longer typechecks; that failure IS the closure evidence. -/
theorem tafel_geschlossen : satz_tafel := by unfold satz_tafel; decide

/-- CLOSED-flip 2026-09-11 (w01): was `¬ satz_erzeugervertrag ...` via the open
    table (`vertrag_braucht_tafel`). The table now decides, so the link is the
    projection the name always named: the contract NEEDS the table. -/
theorem vertrag_braucht_tafel (gabbroSites : List Nat) (cert : CorrCert)
    (o : AliasObligation) (k : CostClaim) (paare : Nat)
    (a : Absenkung) (cAnweisungen : Nat) :
    satz_erzeugervertrag gabbroSites cert o k paare a cAnweisungen → satz_tafel :=
  fun h => h.2.2.2

#print axioms Gabbro.Grammatik.entschieden
#print axioms Gabbro.Grammatik.satz_tafel
#print axioms Gabbro.Grammatik.satz_erzeugervertrag
#print axioms Gabbro.Grammatik.korrespondenz_sound
#print axioms Gabbro.Grammatik.geschlossen_immer
#print axioms Gabbro.Grammatik.ruledB_voll
#print axioms Gabbro.Grammatik.korrespondenz_leer
#print axioms Gabbro.Grammatik.alias_leer
#print axioms Gabbro.Grammatik.kosten_produktion_frei
#print axioms Gabbro.Grammatik.gemessen_produktion
#print axioms Gabbro.Grammatik.senkung_aus_schranke
#print axioms Gabbro.Grammatik.tafel_geschlossen
#print axioms Gabbro.Grammatik.vertrag_braucht_tafel

/-! ## 10. The rechecker as program shape: run artefacts in, verdict out -/

/-- The rechecker input: everything a run leaves behind. The Gabbro sites
    and the certificate come from the producer run, the alias load from
    the image, the cost claim with its pairs from the measurement run,
    the statement count from the lowering. The second program that reads
    these artefacts out of the run stands outside this file (cut C6). -/
structure NachprueferEingabe where
  gabbroSites : List Nat
  cert : CorrCert
  o : AliasObligation
  k : CostClaim
  paare : Nat
  cAnweisungen : Nat
  deriving DecidableEq, Repr

/-- The rechecker: all legs recomputed. Correspondence over
    `pruefeKorrespondenz` (§6), the alias load over the empty site list
    (§7), the cost claim over its two decision instances (§8), and the
    statement count over the measured bound 17. Output is a verdict:
    `true` means accepted. -/
def nachpruefer (eingabe : NachprueferEingabe) : Bool :=
  pruefeKorrespondenz eingabe.gabbroSites eingabe.cert &&
    (decide (eingabe.o.arithSites = []) &&
      (decide (costKept eingabe.k) &&
        (decide (costMeasured eingabe.k eingabe.paare) &&
          decide (eingabe.cAnweisungen ≤ 17))))

/-- Validity: the recomputed verdict reads accepted. Decidable by
    construction, like `GueltigKorrespondenz` -- acceptance and rejection
    both close over the recomputation, not over belief. -/
def nachprueferGueltig (eingabe : NachprueferEingabe) : Prop :=
  nachpruefer eingabe = true

/-- The link to the producer, as a shape: a valid recomputed verdict
    means the issued certificate may be trusted -- correspondence over
    the run, alias load carried, cost kept and measured over `absenkung`.
    DRAFT, no theorem: the bridges from the single legs to the sentences
    stand outside this file (cut C6). -/
def satz_nachpruefung_vertrauen (eingabe : NachprueferEingabe) : Prop :=
  nachprueferGueltig eingabe →
    satz_korrespondenz eingabe.gabbroSites eingabe.cert ∧
    satz_alias eingabe.o ∧
    satz_kosten eingabe.k eingabe.paare absenkung eingabe.cAnweisungen

/-! ## 11. The five priced slots: price as data, no meaning claim -/

/-- The price of `logUndOder` (`messung/CFORM-REGEL-LOGUNDODER.md`, 23 sites):
    short-circuit evaluation with sequence point, result 0 or 1, mandatory
    parentheses at the emitter. Admission with price, no emitter change. -/
def logUndOderEntscheid : RulingStatus :=
  .aufListe "bedingte Auswertung mit Sequenzpunkt; Ergebnis 0 oder 1; Klammerpflicht beim Erzeuger"

/-- The price of `fortStmt` (`messung/CFORM-REGEL-CONTINUE.md`, 3 sites):
    control of the run skeleton from one emit line, no user path, no UB.
    Admission with price, no emitter change. -/
def fortEntscheid : RulingStatus :=
  .aufListe "Steuerung des Laufenskeletts aus einer Emissionszeile; kein Nutzerpfad; kein UB"

/-- The price of `abbruchStmt` (`messung/CFORM-REGEL-BREAK.md`, 51 sites):
    exit from the run skeleton and closing of the case arms from two emit
    lines each, no user path, no UB. Admission with price, no emitter
    change. -/
def abbruchEntscheid : RulingStatus :=
  .aufListe "Austritt aus dem Laufenskelett und Abschluss der Fallarme aus je zwei Emissionszeilen; kein Nutzerpfad; kein UB"

/-- The price of `zeigerIndex` (`messung/CFORM-REGEL-ZEIGERINDEX.md`,
    156 sites): address arithmetic, per-site duty to stay in bounds,
    UB row for the outside case. Admission with price, no emitter
    change. -/
def zeigerIndexEntscheid : RulingStatus :=
  .aufListe "Adressrechnung; Pflicht je Stelle, in den Grenzen zu bleiben; UB-Zeile fuer den Aussenfall"

/-- The five priced slots as a supplement: `bedingt` carries the filled
    template decision, the four admissions their prices from the ruling
    notes. Every other slot fails through (`none`) and keeps its old
    status. -/
def tafelPreisNachtrag : OffeneForm → Option RulingStatus
  | .bedingt => some bedingtEntscheid
  | .logUndOder => some logUndOderEntscheid
  | .fortStmt => some fortEntscheid
  | .abbruchStmt => some abbruchEntscheid
  | .zeigerIndex => some zeigerIndexEntscheid
  | _ => none

/-- The pure status change: where the supplement names a price, it takes
    the place of the old status; otherwise everything stays as it was. -/
def tafelStatusNeu (u : OffeneForm) (s : RulingStatus) : RulingStatus :=
  match tafelPreisNachtrag u with
  | some s' => s'
  | none => s

/-- The table with the five priced slots: the same rows as `tafel`,
    only the status field of the five slots decided with price. `tafel`
    itself stays frozen; this table carries the supplement as data, and the
    adequacy of every price stays owed (cut C7). -/
def tafelNeu : List EntscheidZiel :=
  tafel.map fun e => match e with
    | .benannt f s => .benannt f s
    | .luecke u s => .luecke u (tafelStatusNeu u s)

/-- The later sentence over the new table, as a shape: every row of
    `tafelNeu` is decided. DRAFT, no theorem -- as `satz_tafel` stays a
    SPECIFICATION until every slot is decided one by one. -/
def satz_tafelNeu : Prop :=
  ∀ e ∈ tafelNeu, entschieden e

/-
CUTS:
* No adequacy claim: `tafel_geschlossen` proves every table row is decided,
  not that any price is adequate (cut C5) -- including the new `syscallStub`
  row, whose price (the kernel keeps its contract under the named assumption)
  is an assumption, never a proved premise.
* No emitter linkage: nothing here proves the generated stub matches the
  `syscallStub` price -- the stub lives in `crates/gabbro-check/src/emit.rs`
  (`syscall_stumpf`), and adequacy of the decoding against `einpassen` is
  not stated anywhere in Lean.
* No pairing: a `kernel`-paired syscall needs no assumption by the
  PLAN-SYSCALL.md §2 pairing theorem, which is not stated here -- the row
  prices the `assume` shape only.
-/

end Gabbro.Grammatik
