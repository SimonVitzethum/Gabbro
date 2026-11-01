module

public import Grammatik.Parser.Elab.Uebersetze
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.GabbroV.GvZensus.Teil1

@[expose] public section

namespace Gabbro.Grammatik.GabbroV.GvZensus
open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

def zeigeZeilen : List String → String
  | [] => ""
  | [x] => x
  | x :: rest => x ++ " + " ++ zeigeZeilen rest

/-! ## Fixtures: emptiness on 104, exactness on a bad unit -/

/-- **104 yields no findings** (the census is empty on elaborated
    code; non-degenerate two-function program). -/
theorem zensus104_leer : befundeElab (uMembers items104) = [] := by
  decide

/-- **Synthetic two-blocker fixture**: a table with an unknown field
    type plus a function with a `match` body (real table, real body). -/
def wMultiItems : List SItemTief :=
  [.modT "beispiel::zeuge"
    [.tableT "T" .none (.some (.lit 1)) .none .none false
      [.tSlot [{ fname := "v", ftyp := .atom "Unbekannt",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
    .fnT
      { art := "impl", name := "f", params := [],
        res := .none, fehler := .none, klauseln := [] }
      (.block [.cases (.tru) []]
        (.some (.ret .none)))]]

/-- **Exactness on the fixture**: exactly the table finding and the
    `match`-statement finding, in stage order, nothing else. -/
theorem zensusMulti_exakt :
    befundeElab (uMembers wMultiItems) =
      [{ stufe := "tabelle", art := "tabelle", name := "T",
         meldung := "type unknown: Unbekannt" },
       { stufe := "rumpf", art := "match", name := "f",
         meldung := "stmt without G form" }] := by
  decide

#print axioms Gabbro.Grammatik.GabbroV.GvZensus.zensus104_leer
#print axioms Gabbro.Grammatik.GabbroV.GvZensus.zensusMulti_exakt

/-! ## Population: every corpus file -/

/-- Every `beispiele/*.gab` (157 files, `ls` order, 2026-10-07;
    single source for every census run). -/
def zensusDateien : List String :=
  ["01-tabelle.gab", "02-geraet.gab", "03-format.gab",
    "04-schleifen.gab", "05-nebenlaeufigkeit.gab", "06-annahmen.gab",
    "07-eintritt-und-boot.gab", "08-bereiche.gab", "09-ohne-zeiger.gab",
    "100-hardwareprofil.gab", "101-hardwareprofil-schluessel.gab",
    "104-referenz.gab", "106-summe-uebersetzt.gab",
    "107-summe-zwei-rufe.gab", "108-disjoint-start-locks.gab",
    "109-lockfree-entry-roots.gab", "10-geteilte-sperre.gab",
    "110-fussgarantie.gab", "1114-kind-handed-read.gab",
    "111-rufzulassung.gab", "1123-deklaration-laenge-ok.gab",
    "1124-verkettung-in-max-ok.gab", "1126-vergleich-ok.gab",
    "1127-literal-ok.gab", "112-register-traeger-bewacht.gab",
    "113-register-traeger-ungeschrieben.gab",
    "114-owner-with-producer.gab", "1159-index-unter-laenge-ok.gab",
    "115-owner-read-with-producer.gab", "116-payload-free-counter.gab",
    "117-message-passing-flag.gab", "118-sperrinvariante-erhaltung.gab",
    "119-sperrinvariante-bloecke.gab", "11a-divergenz-endet.gab",
    "11-grammatikbefunde.gab", "120-tagged-construction.gab",
    "121-tagged-static-init.gab", "122-matrix.gab", "123-const-matrix.gab",
    "124-two-threads-private.gab", "125-read-under-lock.gab",
    "126-vergleichssortierung.gab", "127-treiberrueckruf.gab",
    "12-umlaufendes-register.gab", "130-derived-contract-pure.gab",
    "131-derived-contract-call.gab", "132-raum-am-zeiger.gab",
    "133-nur-gruende-und-ein-format-am-arrow.gab",
    "134-holende-bitzuege.gab", "13-zeuge-mit-staerke.gab",
    "140-atomic-array-counter.gab", "141-atomic-array-pairing.gab",
    "146-sperrstreifen.gab", "147-ftp-alg-control.gab",
    "148-ftp-alg-daten.gab", "149-fd-offen.gab",
    "14-paarung-ueber-zwischenfunktion.gab", "150-fd-lesen.gab",
    "151-word-pool-discipline.gab", "152-byte-pool-cost.gab",
    "153-arena-waechst.gab", "154-arena-voll.gab",
    "155-kind-uebergabe.gab", "156-kind-verzweigt.gab",
    "157-worker-pool.gab", "158-arena-commit.gab",
    "159-laufzeit-start.gab", "15-own-traegt-beide-rechte.gab",
    "160-kind-liest-stapel.gab", "161-zeichenkette.gab",
    "162-geteilte-flagge.gab", "163-systemruf-variablen.gab",
    "164-eigener-kern.gab", "165-gp-eintritt.gab",
    "166-eintritt-irq-maskiert.gab",
    "167-reason-crosses-the-module-boundary.gab",
    "168-bytes-through-a-pointer.gab",
    "169-narrow-neben-einem-zeiger-desselben-namens.gab",
    "16-by-ops-am-feld.gab", "170-let-else-mit-typ.gab",
    "171-narrow-nach-eigener-deklaration.gab",
    "172-prozess-ohne-libc.gab", "173-abbruch-ohne-libc.gab",
    "174-tor-im-modell.gab", "175-puffer-gibt-seiten-zurueck.gab",
    "17-gruppe-ueber-zwei-sperren.gab",
    "180-zeigerindex-in-der-ausdehnung.gab",
    "181-gate-at-top-level.gab", "182-fallible-gate.gab",
    "183-region-vom-tor.gab", "184-code-vom-treiber.gab",
    "18-vorfahren.gab", "19-traversierung.gab", "20-falle-vier.gab",
    "21-verbundwert.gab", "22-bootstrecke.gab", "23-akkumulatoren.gab",
    "24-ip-kopf.gab", "25-entrust.gab", "26-gleitkomma.gab",
    "27-freiliste.gab", "28-reserve-und-hinterlegung.gab",
    "29-undurchsichtig.gab", "31-rcu.gab", "32-zeichenkette.gab",
    "33-rekursion.gab", "34-markierter-wert.gab", "35-tausch.gab",
    "36-asm.gab", "37-umlauf-rechnet.gab",
    "38-unveraenderlicher-zeiger.gab", "39-auftragsdienst.gab",
    "40-werte-und-griffe.gab", "41-handschlag.gab", "42-zaehlwerk.gab",
    "43-gegenprobe.gab", "44-register-einmal-lesen.gab",
    "45-gemischte-registerklasse.gab", "46-verneinung.gab",
    "47-ops-wortmenge.gab", "48-grund-mit-erzeuger.gab",
    "49-dispatch-tabelle.gab", "50-verfeinerung.gab",
    "51-abwesenheit-und-absage.gab", "52-baugatter.gab",
    "53-zwei-orte.gab", "54-divergenz-leckt-nicht.gab",
    "55-kindkette.gab", "56-auftragsring.gab", "57-faedenhalt.gab",
    "58-freiliste-zwei-formen.gab",
    "59-eintritt-nimmt-maskierte-sperre.gab",
    "60-annahme-mit-maschine.gab", "61-invertierung.gab",
    "62-grenzwort-im-ausdruck.gab", "63-druckt.gab",
    "64-writes-a-whole-buffer.gab", "65-port-space.gab",
    "66-transport-rueckgabe.gab", "67-befehlsebene.gab",
    "68-named-space-matches-itself.gab", "69-integer-conversion.gab",
    "70-kernel-namen.gab", "71-frist-und-zaehlung.gab",
    "72-fremdruf-unter-sperre.gab", "73-sugar-widths.gab",
    "74-syscall-schreiben.gab", "80-bibliothek-erklaert.gab",
    "90-syscall-errno.gab", "92-const-squares.gab",
    "93-const-scalars.gab", "94-uebersetzer-erklaert.gab",
    "95-uebersetzer-vertrag.gab", "96-buffered-writer.gab",
    "98-arena-erklaert.gab", "99-arena-grenze.gab", "halde.gab"]

/-
  CUTS (agent 02, V-02 census):
  1. PROVED here: the depth splitter with a decided 104 roundtrip
     (`spalte`, `parseStueck`, `ohneEnde`, `runde104`); finding and tag
     vocabulary (`Befund`, `artItem`, `artAnw`, `artEnde`, filters);
     collect-mode stages (`werte`, `sammleTabellen`, `sammleSperren`,
     `sammleKoepfe`, `sammleIdx` with `sammleIdx_laenge`); drivers
     (`zeigeLexFehler`, `befundeSrc`, `scanBelegt`, `wortKommtVor`,
     `arrayAnfang`, `merkmaleSrc`, renderers); fixtures
     (`zensus104_leer`, `wMultiItems`, `zensusMulti_exakt`); the
     population list (`zensusDateien`).
  2. KNOWN GAPS (by design, all documented for the report join):
     no `uRestFehler` replication (item-level blockers come from the
     tag probes, joined by hand); bodies of failed heads are hidden
     (as in `elabU`); per-chunk parse used only for the splitter
     proof, not per-file (whole-parse first errors stand);
     `arrayAnfang` is heuristic (bracket after `=`/`,`/`(`/`return`);
     the word scan covers English surface spellings observed in the
     corpus; `SAnw`-internal expression shapes are not descended
     (statement tags + messages carry those rows); multi-module files
     are opaque to the stage filters (items nested in `modT` show
     empty findings with modT tags, e.g. 29/59/60/167).
  3. Elaboration lesson: struct-instance `{...}` literals need a
     statically known expected type (`(...) : Befund` ascription) in
     lambdas and match arms; without it Lean reports "unexpected
     identifier; expected '}'" (multiline) or "invalid {...}
     notation" (single line).
-/

end Gabbro.Grammatik.GabbroV.GvZensus
