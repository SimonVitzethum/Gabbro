/-
  Datei:      Grammatik/Extraktion.lean
  Gegenstand: **DIE FUSSABDRUECKE ALS RECHNUNG** -- aus den Ruempfen gerechnet, nicht
              erklaert: die Rufkanten aus den Rufen im Rumpf (W-EXT), die
              Fussabdrucklisten aus den Effekten, die Paarliste aus der
              Nebenlauffassung; das Ergebnis IST `Geteilt.Bau` (kein Spiegel mehr),
              die Brennstoff-Rechnung IST `Geteilt.schrittBis`/`traegerBis`, die
              Paarform IST `Nebeneinander` (`Wettlauf.lean` §6), und die Anknuepfung
              steht als Satz daneben (die Treue-Saetze und die Einspeisung in
              `geteilt_treu`/`ungeteilt_aus_baulauf`).

  ZIEL (Bahn 38, Entwurf; Bahn 78 verdrahtet): Die Schnitte C2/C3 aus
  `Geteilt.lean` schliessen -- dort sind `schreibtFn` je Funktion und `neben`
  als Paarliste DEKLARIERT (getragen, nicht gerechnet). Hier steht die Rechnung:
  `ruftDirekt` traversiert `Programm.rumpf` (W-EXT, §2), `ruftNorm`/`kantenListe`
  schraenken auf die erklaerte Funktionsdomaene ein, `fussAus` liest die
  Effektpraedikate ueber der erklaerten Traegerdomaene, `nebenAus` schraenkt die
  erklaerte Paarliste auf die Eintritte ein, und `bauAus` baut daraus den
  `Geteilt.Bau`. Was der Pruefer heute per Hand schreibt (`H013`), rechnet
  kuenftig diese Datei aus dem Rumpf.

  VERDRAHTET (Bahn 78 -- kein Spiegel mehr):
    `Geteilt.Bau` statt `BauSpiegel` (Feld fuer Feld derselbe Typ, jetzt derselbe
      Term: `bauAus` liefert `Geteilt.Bau`);
    `Geteilt.schrittBis`/`traegerBis`/`ErreichtBau`/`BauLauf` statt der
      `…Spiegel`-Rechnungen (`laufGedeckt`/`nurPaareLaufen` sind die zwei
      Haelften von `Geteilt.BauLauf`, `bauLaufSpiegel_genau` ist `Iff.rfl`);
    `Nebeneinander` statt `Nat → Nat → Prop` (definitionell dasselbe:
      `Faden` IST `Nat`).

  SCHNITTE (gebucht, nicht versteckt):
  S1. Kodierung: `D.Fn`, `D.Tab`, `D.Glob` sind beliebige Typen, `Geteilt.Bau`
      spricht ueber Zahlen. Die Bruecke sind explizite Parameter
      (`fnCode`/`tabCode`/`globCode`); wo die Rechnung Eindeutigkeit braucht
      (Marken-Nachschlagen: `geteiltTab_trifft`, `geteiltAus_tab`), steht sie
      als Praemisse am Satz (`hinj`), nicht als Axiom im Baum. Die Trennung der
      Traegerhaelften leistet `hdisj` (kein Tab-Code trifft einen Glob-Code);
      `geteilt_treu` unterscheidet erst dort wieder Tabelle/Global.
  S2. W-EXT (die Traversierung, §2): `ruftDirekt` traversiert `Stmt`/`Block`/
      `Endblock`/`Arms`/`GrundArms` und sammelt `Stmt.call`, `Block.bindCall`,
      `Block.bindCallElse` als Kanten; `callInd` (Zeigerruf), `bindCallInd` und
      `axiomCall`/`bindAxiom` (fremder Rumpf) liefern KEINE Kante -- ein
      Zeigerruf faellt damit aus der Huelle, und der Pruefer muss ihn
      verweigern (fail-closed, wie `W003`), nicht raten. `kantenVoll` nennt
      diese Verweigerungspflicht beim Namen.
  S3. Lesen: `effects` erklaert nur Schreiben (`schreibt`/`gschreibt`); eine
      Lesehuelle (`slot`/`glob` in `Expr`) steht nirgends und fehlt hier -- fuer
      (W5) genuegt Schreiben (Erreichen heisst Beruehren zum Schreiben), fuer
      das Zwei-Faden-Modell (`Interferenz.lean`: disjunkte Rahmen) muss sie
      dazu.
  S4. Haengende Paare: `nebenAus` wirft Paare ausserhalb der Eintritte weg --
      `paarVoll_aus_bau` nennt die Pflicht des Pruefers als Praemissen
      (`hvoll`, `hbound`): was faellt, wird verweigert, nicht verschwiegen.
  S5. Unbekannt heisst geteilt: `geteiltAus` antwortet `true` ausserhalb der
      Tabellen -- fail-closed in die Richtung, in der ein Irrtum laut wird
      (`geteilt_treu` verlangt dann den Waechter statt der Einzigkeit);
      `geteiltAus_fremd` beweist es.

   Kern nur: kein `mathlib`, kein `sorry` -- nur `def` und `theorem`, und
   beides ueber den echten Typen (`Geteilt.Bau`, `Programm`, `Nebeneinander`).

   NACHTRAG (Bahn 84, Entwurf -- §12): Die Lesehuelle steht jetzt als Rechnung:
   `stmtOrte`/`blockOrte`/`endblockOrte`/`armsOrte`/`grundArmsOrte` tragen
   `Expr.orte` durch die Ruempfe, `liestDirekt`/`liestTab`/`liestGlob`/`liesAus`
   rechnen die Huelle je Rumpf und je Code, `liesTreue`/`liesVoll` sind die
   Treue-Formen zur Schreibseite (§8), und `rahmenDecktLies` knuepft die Huelle
   an die Rahmen von `Interferenz.lean`. Neu gebucht: S6 (Vertraege ausserhalb
   des Rumpfs), S7 (fremdes Rufziel wie S2). Nur `def`-Formen, als Entwurf: was
   die Rechnung dem Pruefer schuldet, steht als Form daneben, nicht als Satz.
-/


import Grammatik.Kern.Syntax.Extraktion.T1
import Grammatik.Kern.Syntax.Extraktion.T2
import Grammatik.Kern.Syntax.Extraktion.T3
import Grammatik.Kern.Syntax.Extraktion.T4
import Grammatik.Kern.Syntax.Extraktion.T5
import Grammatik.Kern.Syntax.Extraktion.T6
import Grammatik.Kern.Syntax.Extraktion.T7
import Grammatik.Kern.Syntax.Extraktion.T8
import Grammatik.Kern.Syntax.Extraktion.T9
