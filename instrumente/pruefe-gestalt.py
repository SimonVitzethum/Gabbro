#!/usr/bin/env python3
"""**Der Gestaltwaechter -- Saetze gegen Definitionen, je Datei.**

Am 2026-09-10 mass der Ordner `grammatik/Grammatik`: 23 Dateien, 372
`theorem`, 569 `def`-Formen -- und stellte fest, dass mehrere Dateien
ausdruecklich Gestalt sind und es auch sagen, die Dokumente darueber aber
Zahlen zitieren, die niemand nachrechnet (`ABSENKUNG-ZAEHLUNG.md` fuehrte
noch ` proPrimitiv <= 8` waehrend `Ziel.lean` laengst `<= 18` traegt).
*Zwei Register ueber einer Zahl, die aelteste Fehlerklasse des Ordners.*

Dieser Waechter zaehlt je Datei die Saetze (`theorem`/`lemma`) und Beispiele
(`example`) gegen die Definitionen (`def`/`abbrev`/`structure`/`inductive`/
`class`) und ratscht beide: jede Bewegung braucht einen Commit, der die
Tabelle unten mitbewegt. Was die Tabelle nicht erklaert, ist keine Messung.

**Zaehlt, was der Befehl zaehlt:** ein Konstrukt gilt, wenn es in Spalte 0
beginnt (`^theorem `, nicht eingerueckt); Kommentare (`--`, `/- -/`
geschachtelt) zaehlen nicht mit. Dieselbe Methode, mit der die 372/569
gemessen wurden -- ein Muster, das anders zaehlt als seine Quelle, misst
seine eigene Lesart (W16).
"""

import os
import re
import signal
import sys
import tempfile
from pathlib import Path

# **Vier statische Forderungen, wie jedes Instrument.** Pinned locale first:
# Fremdwerkzeuge melden in der Sprache des Benutzers, und ein `grep` auf den
# englischen Wortlaut trifft dann nichts.
os.environ.setdefault("LC_ALL", "C")

# **Frist, deklariert.** Reines Textzaehlen braucht sie nicht -- sie steht,
# damit ein Haenger, den es nicht geben kann, trotzdem keinen Zustand wuerde.
FRIST = 300

W = Path(__file__).resolve().parent.parent
GEGENSTAND = W / "grammatik" / "Grammatik"

# **Die Ratsche: je Datei (Saetze, Beispiele, Definitionen), gemessen am
# 2026-09-11 auf dem vereinten Baum (Bahn 100 eingeschlossen).** Eine Zeile
# bewegt sich nur mit einem Commit, der sie hier mitbewegt und den Grund
# daneben schreibt -- eine Marke, die man hochzieht, weil sie klemmt, ist
# keine (Rattenfaenger 2026-08-28: MARKE_EINGEFROREN blieb bei 31).
# Re-booked 2026-10-17: the Lean tree moved from one flat folder into sub-folders (the layout
# rule, at most 20 entries per folder), so the old per-name rows matched no file and the
# guardian counted nothing (ABBRUCH). Keys are now paths relative to `grammatik/Grammatik`;
# every row is the measured state of that day, a ratchet from here on.
ERWARTET = {
    "Bausteine/Arena/Arena.lean": (12, 0, 9),
    "Bausteine/Arena/ArenaDyn.lean": (40, 0, 27),
    "Bausteine/Arena/ArenaReset.lean": (3, 0, 2),
    "Bausteine/Arena/ArenaSeiten.lean": (3, 0, 4),
    "Bausteine/Arena/ArenaZucker.lean": (19, 0, 16),
    "Bausteine/Arena/Bibliothek.lean": (24, 0, 26),
    "Bausteine/Gleitkomma/GleitZeuge.lean": (9, 0, 14),
    "Bausteine/Gleitkomma/Gleitkomma.lean": (73, 0, 44),
    "Bausteine/Gleitkomma/GleitkommaBits.lean": (21, 0, 4),
    "Bausteine/Schablonen/SchablonenArena.lean": (18, 0, 8),
    "Bausteine/Schablonen/SchablonenFaden.lean": (12, 0, 12),
    "Bausteine/Schablonen/SchablonenMetall.lean": (20, 0, 13),
    "Bausteine/Schablonen/SchablonenMetallFaden.lean": (21, 0, 15),
    "Bausteine/Schablonen/SchablonenMetallIdt.lean": (10, 0, 15),
    "Bausteine/Schablonen/SchablonenMetallSperre.lean": (25, 0, 19),
    "Bausteine/Schablonen/SchablonenModul.lean": (26, 0, 15),
    "Bausteine/Schablonen/SchablonenOhneLibc.lean": (23, 0, 19),
    "Bausteine/Schablonen/SchablonenStapel.lean": (12, 0, 6),
    "Bausteine/Schablonen/SchablonenT5.lean": (52, 0, 19),
    "Bausteine/Schablonen/SchablonenT5Sem.lean": (22, 0, 7),
    "CBackend/Formen/CFormMatch.lean": (32, 0, 18),
    "CBackend/Formen/CFormNested.lean": (2, 0, 6),
    "CBackend/Formen/CFormen.lean": (19, 0, 54),
    "CBackend/Formen/CFormenDet.lean": (5, 0, 1),
    "CBackend/Formen/CFormenF.lean": (45, 0, 4),
    "CBackend/Formen/CFormenFZeuge.lean": (7, 0, 11),
    "CBackend/Formen/CFormenH.lean": (22, 0, 3),
    "CBackend/Formen/CFormenI.lean": (97, 0, 31),
    "CBackend/Formen/CFormenM.lean": (37, 0, 10),
    "CBackend/Formen/CFormenR.lean": (102, 0, 56),
    "CBackend/Formen/CFormenR2.lean": (8, 0, 1),
    "CBackend/Formen/CFormenR2Zeuge.lean": (5, 0, 6),
    "CBackend/Formen/CFormenRZeuge.lean": (23, 0, 46),
    "CBackend/Formen/CFormenRZeuge2.lean": (17, 0, 13),
    "CBackend/Formen/CFormenW.lean": (18, 0, 6),
    "CBackend/Formen/CFormenWZeuge.lean": (16, 0, 30),
    "CBackend/Formen/CFormenZeuge.lean": (25, 0, 27),
    "CBackend/Parser/Bruecke.lean": (4, 0, 2),
    "CBackend/Parser/CLexer.lean": (18, 0, 24),
    "CBackend/Parser/CParse.lean": (2, 0, 35),
    "CBackend/Parser/CProben.lean": (7, 0, 1),
    "CBackend/Semantik/CNebenlaeufig.lean": (23, 0, 51),
    "CBackend/Semantik/CSLInvariante.lean": (9, 0, 2),
    "CBackend/Semantik/CSLInvarianteC.lean": (11, 0, 0),
    "CBackend/Semantik/CSemantik.lean": (20, 0, 26),
    "CBackend/Semantik/CSpeicher.lean": (69, 0, 85),
    "CBackend/Semantik/CText104.lean": (2, 0, 2),
    "CBackend/Semantik/CText104Zeuge.lean": (3, 0, 6),
    "CBackend/Semantik/CText108.lean": (6, 0, 7),
    "CBackend/Semantik/CTicket.lean": (55, 0, 20),
    "CBackend/Semantik/CloneHandoff.lean": (41, 0, 31),
    "CBackend/Semantik/ZeichenfolgeC.lean": (8, 0, 10),
    "CBackend/Semantik/ZeichenfolgeGebunden.lean": (14, 0, 11),
    "CBackend/Semantik/ZeichenfolgeZelle.lean": (5, 6, 7),
    "GabbroV/GvAtomKoerper.lean": (43, 0, 10),
    "GabbroV/GvAtomRely.lean": (7, 0, 2),
    "GabbroV/GvBaum.lean": (20, 0, 12),
    "GabbroV/GvBruecke.lean": (3, 0, 2),
    "GabbroV/GvKetten.lean": (7, 0, 5),
    "GabbroV/GvLauf.lean": (8, 0, 2),
    "GabbroV/GvLuecken.lean": (7, 0, 1),
    "GabbroV/GvParserFragment.lean": (14, 0, 11),
    "GabbroV/GvParserFragment3.lean": (12, 0, 18),
    "GabbroV/GvParserFragment4.lean": (13, 0, 8),
    "GabbroV/GvSplits.lean": (11, 0, 8),
    "GabbroV/GvStartPflicht.lean": (13, 0, 7),
    "GabbroV/GvStore.lean": (11, 0, 8),
    "GabbroV/GvTraversal.lean": (16, 0, 13),
    "GabbroV/GvTreeParent.lean": (27, 0, 19),
    "GabbroV/GvVerkettung.lean": (22, 0, 9),
    "GabbroV/GvZensus.lean": (4, 0, 33),
    "Isabelle/Absenkung_Parametrisch.lean": (22, 0, 20),
    "Isabelle/AccumulatesMonoid.lean": (11, 0, 8),
    "Isabelle/Consuming.lean": (11, 0, 10),
    "Isabelle/DeviceKonstruktor.lean": (5, 0, 4),
    "Isabelle/FormatRoundtrip.lean": (7, 0, 10),
    "Isabelle/GruppeErhaltung.lean": (10, 0, 7),
    "Isabelle/Intervall_Aussen.lean": (10, 0, 4),
    "Isabelle/OptionSonderwert.lean": (5, 0, 4),
    "Isabelle/RestrictAlleinzugriff.lean": (5, 0, 6),
    "Isabelle/Table_Absenkung.lean": (4, 0, 2),
    "Isabelle/Table_Indexschranke.lean": (13, 0, 7),
    "Isabelle/Table_Induktion.lean": (13, 0, 6),
    "Isabelle/Table_Ops_Erhaltung.lean": (42, 0, 17),
    "Isabelle/Table_Zaehlung.lean": (19, 0, 4),
    "Isabelle/VerbundKonstruktor.lean": (5, 0, 4),
    "Kern/Semantik/Adressraum.lean": (37, 0, 49),
    "Kern/Semantik/Budget.lean": (37, 7, 24),
    "Kern/Semantik/Durchgaenge.lean": (12, 0, 6),
    "Kern/Semantik/Erhaltung.lean": (26, 18, 56),
    "Kern/Semantik/ErhaltungT4.lean": (35, 0, 0),
    "Kern/Semantik/Fristlauf.lean": (18, 7, 13),
    "Kern/Semantik/Geraet.lean": (31, 0, 24),
    "Kern/Semantik/Maschine.lean": (112, 0, 41),
    "Kern/Semantik/MaschinenKette.lean": (18, 0, 1),
    "Kern/Semantik/Semantik.lean": (8, 0, 83),
    "Kern/Semantik/Syscall.lean": (14, 0, 13),
    "Kern/Semantik/SyscallAllg.lean": (11, 0, 8),
    "Kern/Semantik/SyscallArm.lean": (21, 0, 38),
    "Kern/Semantik/SyscallArmLinux.lean": (7, 0, 11),
    "Kern/Semantik/SyscallArmPflicht.lean": (7, 0, 14),
    "Kern/Semantik/SyscallPaarung.lean": (17, 0, 18),
    "Kern/Semantik/Terminierung.lean": (14, 2, 2),
    "Kern/Semantik/Ueberlauf.lean": (13, 0, 5),
    "Kern/Syntax/Bits.lean": (58, 0, 25),
    "Kern/Syntax/Extraktion.lean": (87, 7, 77),
    "Kern/Syntax/Fehler.lean": (64, 0, 28),
    "Kern/Syntax/Geist.lean": (20, 0, 19),
    "Kern/Syntax/Koernung.lean": (33, 0, 11),
    "Kern/Syntax/Konstanten.lean": (12, 0, 19),
    "Kern/Syntax/Marken.lean": (28, 0, 20),
    "Kern/Syntax/MarkenInstanzA.lean": (18, 0, 10),
    "Kern/Syntax/Profil.lean": (16, 0, 30),
    "Kern/Syntax/Satz.lean": (125, 7, 39),
    "Kern/Syntax/Syntax.lean": (2, 0, 45),
    "Kern/Syntax/Typen.lean": (16, 0, 36),
    "Kern/Syntax/Ziel.lean": (35, 0, 6),
    "Kern/Syntax/Zucker.lean": (1, 2, 37),
    "Korrespondenz/Allgemein/KorrOkAdaequat.lean": (4, 0, 0),
    "Korrespondenz/Allgemein/KorrOkOhneLocks.lean": (4, 0, 0),
    "Korrespondenz/Allgemein/Korrespondenz.lean": (26, 0, 30),
    "Korrespondenz/Allgemein/Korrespondenz104.lean": (8, 0, 9),
    "Korrespondenz/Allgemein/KorrespondenzAllg.lean": (60, 0, 27),
    "Korrespondenz/Allgemein/KorrespondenzBlockZeuge.lean": (11, 0, 29),
    "Korrespondenz/Allgemein/KorrespondenzGeraetZeuge.lean": (12, 0, 31),
    "Korrespondenz/Allgemein/KorrespondenzWeitZeuge.lean": (18, 0, 22),
    "Korrespondenz/Allgemein/Pflicht104.lean": (25, 0, 3),
    "Korrespondenz/Allgemein/Pflicht108.lean": (27, 0, 1),
    "Korrespondenz/Allgemein/Referenz104.lean": (23, 0, 38),
    "Korrespondenz/Allgemein/Referenz104Rahmen.lean": (7, 0, 1),
    "Korrespondenz/Allgemein/ReferenzAR.lean": (29, 0, 23),
    "Korrespondenz/Allgemein/ReferenzB.lean": (67, 0, 47),
    "Korrespondenz/Allgemein/ReferenzZeuge.lean": (11, 0, 7),
    "Korrespondenz/Kette/Kette104.lean": (17, 0, 18),
    "Korrespondenz/Kette/Kette104Satz.lean": (16, 0, 7),
    "Korrespondenz/Kette/Kette108.lean": (27, 0, 23),
    "Korrespondenz/Kette/KetteMehrfadenC.lean": (6, 0, 3),
    "Korrespondenz/Kette/KetteVoll.lean": (34, 0, 23),
    "Korrespondenz/Kette/Schlusssatz.lean": (7, 0, 4),
    "Korrespondenz/Kette/Schlusssatz104.lean": (109, 1, 44),
    "Korrespondenz/Kette/Schlusssatz124.lean": (61, 0, 62),
    "Korrespondenz/Kette/Schlusssatz124Ticket.lean": (2, 0, 0),
    "Korrespondenz/Kette/SchlusssatzZeuge.lean": (4, 0, 4),
    "Korrespondenz/Korpus/Export104.lean": (7, 2, 19),
    "Korrespondenz/Korpus/Export108.lean": (5, 2, 22),
    "Korrespondenz/Korpus/GenOblig104.lean": (9, 4, 25),
    "Korrespondenz/Korpus/GenOblig108.lean": (8, 2, 23),
    "Korrespondenz/Korpus/Korpus07.lean": (4, 0, 8),
    "Korrespondenz/Korpus/Korpus109.lean": (31, 0, 35),
    "Korrespondenz/Korpus/Korpus124.lean": (32, 0, 41),
    "Korrespondenz/Korpus/Korpus125.lean": (26, 0, 23),
    "Korrespondenz/Korpus/Korpus59.lean": (31, 0, 36),
    "Korrespondenz/Korpus/TermIdent104.lean": (0, 12, 0),
    "Korrespondenz/Zeugnis/Zertifikate.lean": (0, 0, 0),
    "Korrespondenz/Zeugnis/Zeugnis.lean": (12, 70, 27),
    "Korrespondenz/Zeugnis/ZeugnisIdent.lean": (9, 0, 5),
    "Korrespondenz/Zeugnis/ZeugnisKorpus.lean": (0, 72, 69),
    "Korrespondenz/Zeugnis/ZeugnisStmt.lean": (8, 4, 19),
    "Korrespondenz/Zeugnis/ZeugnisStmt104.lean": (0, 14, 14),
    "Korrespondenz/Zeugnis/ZeugnisStmt104b.lean": (5, 7, 13),
    "Korrespondenz/Zeugnis/ZeugnisStmt2.lean": (26, 3, 18),
    "Korrespondenz/Zeugnis/ZeugnisStmt3.lean": (11, 2, 12),
    "Logik/Fortschritt/Folge.lean": (0, 0, 13),
    "Logik/Fortschritt/FolgeBeweis.lean": (19, 0, 2),
    "Logik/Fortschritt/FolgeZeuge.lean": (6, 0, 4),
    "Logik/Fortschritt/Fortschritt.lean": (27, 0, 14),
    "Logik/Fortschritt/FortschrittZeuge.lean": (4, 0, 2),
    "Logik/Fortschritt/KostenG.lean": (48, 0, 53),
    "Logik/Fortschritt/KostenGZeuge.lean": (17, 0, 1),
    "Logik/Fortschritt/Lebendigkeit.lean": (39, 0, 14),
    "Logik/Fortschritt/LebendigkeitZeuge.lean": (22, 0, 8),
    "Logik/Ruf/FremdRuf.lean": (56, 0, 38),
    "Logik/Ruf/HoareRegeln.lean": (18, 0, 7),
    "Logik/Ruf/HoareRuf.lean": (7, 0, 6),
    "Logik/Ruf/RufAdaequatG.lean": (232, 0, 72),
    "Logik/Ruf/RufAdaequatRufG.lean": (178, 0, 77),
    "Logik/Ruf/RufAtNachB.lean": (3, 0, 0),
    "Logik/Ruf/RufHaeltG.lean": (34, 0, 5),
    "Logik/Ruf/RufLogik.lean": (16, 0, 5),
    "Logik/Ruf/RufLogikZeuge.lean": (4, 0, 2),
    "Logik/Ruf/RufMaschineD.lean": (25, 0, 34),
    "Logik/Ruf/RufMaschineF.lean": (44, 0, 40),
    "Logik/Ruf/RufMaschineG.lean": (103, 0, 67),
    "Logik/Ruf/RufOhneHardware.lean": (15, 0, 7),
    "Logik/Ruf/RufOhneHardwareZeuge.lean": (12, 0, 1),
    "Logik/Ruf/RufTiefe.lean": (3, 0, 1),
    "Logik/Ruf/RufUmkehrRufG.lean": (81, 0, 23),
    "Logik/Vertraege/AntwortOrte.lean": (8, 0, 8),
    "Logik/Vertraege/AxiomVertrag.lean": (15, 0, 32),
    "Logik/Vertraege/EinpassenVoll.lean": (35, 0, 10),
    "Logik/Vertraege/Getrennt.lean": (11, 0, 6),
    "Logik/Vertraege/GetrenntZeuge.lean": (13, 0, 18),
    "Logik/Vertraege/HandlerKongruenz.lean": (19, 0, 9),
    "Logik/Vertraege/Komposition.lean": (19, 0, 44),
    "Logik/Vertraege/ObjektRahmen.lean": (45, 0, 30),
    "Logik/Vertraege/ObjektWurzel.lean": (15, 0, 14),
    "Logik/Vertraege/ObjektZeuge.lean": (20, 0, 29),
    "Logik/Vertraege/Objekte.lean": (9, 0, 4),
    "Logik/Vertraege/QLeer.lean": (4, 0, 9),
    "Logik/Vertraege/RahmenTreu.lean": (29, 0, 5),
    "Logik/Vertraege/Uebersetzung.lean": (3, 0, 3),
    "Logik/Vertraege/VertragOrtB.lean": (14, 0, 23),
    "Logik/Vertraege/VertragsFuss.lean": (8, 0, 2),
    "Nebenlaeufigkeit/Allgemein/DisziplinBedarf.lean": (26, 0, 12),
    "Nebenlaeufigkeit/Allgemein/FadenMaschine.lean": (8, 0, 6),
    "Nebenlaeufigkeit/Allgemein/FadenMerkmal.lean": (7, 0, 10),
    "Nebenlaeufigkeit/Allgemein/Geteilt.lean": (36, 4, 41),
    "Nebenlaeufigkeit/Allgemein/LesenStabil.lean": (20, 0, 8),
    "Nebenlaeufigkeit/Allgemein/MehrfadenLauf.lean": (15, 0, 1),
    "Nebenlaeufigkeit/Allgemein/MehrfadenZeuge.lean": (48, 0, 41),
    "Nebenlaeufigkeit/Allgemein/Schiebung.lean": (5, 0, 4),
    "Nebenlaeufigkeit/Allgemein/StabilBewacht.lean": (28, 0, 13),
    "Nebenlaeufigkeit/Allgemein/TravAwaitsLauf.lean": (15, 0, 7),
    "Nebenlaeufigkeit/Allgemein/TravAwaitsZeuge.lean": (25, 0, 47),
    "Nebenlaeufigkeit/Allgemein/Trennung.lean": (12, 1, 4),
    "Nebenlaeufigkeit/Allgemein/Unterbrechung.lean": (11, 0, 9),
    "Nebenlaeufigkeit/Allgemein/Verklemmung.lean": (27, 0, 16),
    "Nebenlaeufigkeit/Allgemein/Verschachtelt.lean": (12, 0, 12),
    "Nebenlaeufigkeit/Allgemein/WacheGlobal.lean": (10, 0, 10),
    "Nebenlaeufigkeit/Allgemein/Wettlauf.lean": (28, 0, 18),
    "Nebenlaeufigkeit/Rennfreiheit/EigenZustand.lean": (8, 0, 1),
    "Nebenlaeufigkeit/Rennfreiheit/EigenZustandD.lean": (46, 0, 13),
    "Nebenlaeufigkeit/Rennfreiheit/Interferenz.lean": (9, 0, 4),
    "Nebenlaeufigkeit/Rennfreiheit/InterferenzAllgemein.lean": (67, 0, 38),
    "Nebenlaeufigkeit/Rennfreiheit/RennfreiG.lean": (5, 0, 3),
    "Nebenlaeufigkeit/Rennfreiheit/RennfreiOrte.lean": (23, 0, 6),
    "Nebenlaeufigkeit/Rennfreiheit/RennfreiVoll.lean": (28, 0, 12),
    "Nebenlaeufigkeit/Sperren/ExportSperre.lean": (5, 6, 19),
    "Nebenlaeufigkeit/Sperren/FremdSperre.lean": (14, 0, 11),
    "Nebenlaeufigkeit/Sperren/MitRuhe.lean": (28, 0, 37),
    "Nebenlaeufigkeit/Sperren/MitRuheSemantik.lean": (83, 0, 8),
    "Nebenlaeufigkeit/Sperren/MitRuheSperre.lean": (28, 0, 10),
    "Nebenlaeufigkeit/Sperren/MitRuheStatisch.lean": (77, 0, 5),
    "Nebenlaeufigkeit/Sperren/RelySperre.lean": (28, 0, 20),
    "Nebenlaeufigkeit/Sperren/SperrImpl.lean": (25, 0, 3),
    "Nebenlaeufigkeit/Sperren/SperreBeweis.lean": (44, 0, 11),
    "Nebenlaeufigkeit/Sperren/SperreFuss.lean": (39, 0, 14),
    "Nebenlaeufigkeit/Sperren/SperreMaschine.lean": (14, 0, 4),
    "Nebenlaeufigkeit/Sperren/SperreSem.lean": (117, 0, 24),
    "Nebenlaeufigkeit/Sperren/Sperrstreifen.lean": (19, 0, 6),
    "Nichtinterferenz/Fluss.lean": (6, 0, 6),
    "Nichtinterferenz/Freigabe.lean": (5, 0, 4),
    "Nichtinterferenz/Grundlagen.lean": (14, 0, 14),
    "Nichtinterferenz/Invariante.lean": (24, 0, 2),
    "Nichtinterferenz/Korpus.lean": (5, 0, 5),
    "Nichtinterferenz/Lokal.lean": (14, 0, 10),
    "Nichtinterferenz/LokalSchritt.lean": (25, 0, 1),
    "Nichtinterferenz/Schritt.lean": (0, 0, 19),
    "Nichtinterferenz/SchrittTreu.lean": (4, 0, 0),
    "Nichtinterferenz/Zeuge.lean": (25, 0, 58),
    "Nichtinterferenz/ZeugeMehrfaden.lean": (5, 0, 6),
    "Parser/Anweisung.lean": (0, 0, 54),
    "Parser/AnweisungProben.lean": (134, 0, 67),
    "Parser/Ausdruck.lean": (6, 0, 45),
    "Parser/AusdruckProben.lean": (22, 0, 0),
    "Parser/Element.lean": (0, 0, 19),
    "Parser/ElementTief.lean": (0, 0, 191),
    "Parser/ElementTiefProben.lean": (120, 0, 60),
    "Parser/Lexer.lean": (36, 0, 48),
    "Parser/LexerVertrauen.lean": (12, 0, 17),
    "Parser/Rundlauf.lean": (59, 0, 33),
    "Parser/Rundlauf2.lean": (107, 0, 8),
    "Parser/Rundlauf3.lean": (84, 0, 17),
    "Parser/Rundlauf4.lean": (28, 0, 6),
    "Parser/Uebersetze.lean": (8, 0, 163),
    "Parser/UebersetzeAllg.lean": (17, 0, 51),
    "Parser/UebersetzeAllg2.lean": (33, 0, 56),
    "Parser/UebersetzeProben.lean": (35, 0, 36),
    "Parser/UebersetzeProben2.lean": (11, 0, 12),
    "Parser/WortStellung.lean": (7, 0, 3),
    "Proben/AuditFinal.lean": (12, 0, 0),
    "Proben/AuditW5.lean": (2, 0, 0),
    "Proben/AuditZiel.lean": (7, 0, 0),
    "Proben/BitVecProben.lean": (18, 0, 1),
    "Proben/BlattGegenbeispiel.lean": (8, 0, 10),
    "Proben/HelferZeuge.lean": (25, 0, 22),
    "Proben/InvZeuge.lean": (32, 0, 31),
    "Proben/ProbeD.lean": (25, 0, 13),
    "Proben/SimPruef.lean": (10, 0, 16),
    "Proben/SonstLeaveZeuge.lean": (4, 0, 9),
    "Speichermodell/Atomar/Atomar.lean": (35, 0, 6),
    "Speichermodell/Atomar/AtomarAkteur.lean": (1, 0, 0),
    "Speichermodell/Atomar/AtomarFortschritt.lean": (7, 0, 0),
    "Speichermodell/Atomar/AtomarInv.lean": (9, 0, 0),
    "Speichermodell/Atomar/AtomarLauf.lean": (12, 0, 3),
    "Speichermodell/Atomar/AtomarRec.lean": (20, 0, 8),
    "Speichermodell/Atomar/AtomarReplay.lean": (37, 0, 10),
    "Speichermodell/Atomar/AtomarRuhe.lean": (10, 0, 0),
    "Speichermodell/Atomar/AtomarSem.lean": (12, 0, 9),
    "Speichermodell/Atomar/AtomarW.lean": (8, 0, 1),
    "Speichermodell/Atomar/AtomarZeuge.lean": (26, 0, 3),
    "Speichermodell/Atomar/AtomarZiel.lean": (2, 0, 1),
    "Speichermodell/Darstellung.lean": (14, 11, 12),
    "Speichermodell/DarstellungTy.lean": (22, 0, 6),
    "Speichermodell/Fenster.lean": (14, 0, 3),
    "Speichermodell/Maschine/DRF.lean": (14, 0, 2),
    "Speichermodell/Maschine/GXMaschine.lean": (20, 0, 7),
    "Speichermodell/Maschine/MaschineW.lean": (26, 0, 18),
    "Speichermodell/Maschine/RMW.lean": (9, 0, 2),
    "Speichermodell/Maschine/Sicht.lean": (31, 0, 30),
    "Speichermodell/Maschine/SperreSemA.lean": (78, 0, 3),
    "Speichermodell/Maschine/Zaehler.lean": (6, 0, 9),
    "Speichermodell/Maschine/ZaehlerW.lean": (5, 0, 2),
    "Speichermodell/Maschine/Zeuge.lean": (14, 0, 6),
    "Speichermodell/OptBereich.lean": (13, 0, 3),
    "Speichermodell/RecordLage.lean": (18, 0, 10),
    "Speichermodell/Sprungtafel.lean": (16, 0, 8),
    "Speichermodell/Zaehlen.lean": (17, 0, 3),
    "Zertifikat/G1428_sperre_ohne_llvm.lean": (6, 4, 18),
    "Zertifikat/Reihe00/G15_own_traegt_beide_rechte.lean": (7, 1, 18),
    "Zertifikat/Reihe00/G16_by_ops_am_feld.lean": (8, 1, 23),
    "Zertifikat/Reihe00/G34_markierter_wert.lean": (7, 2, 28),
    "Zertifikat/Reihe00/G59_eintritt_nimmt_maskierte_sperre.lean": (10, 6, 36),
    "Zertifikat/Reihe00/G62_grenzwort_im_ausdruck.lean": (6, 2, 32),
    "Zertifikat/Reihe00/G69_integer_conversion.lean": (6, 2, 17),
    "Zertifikat/Reihe00/G73_sugar_widths.lean": (6, 2, 42),
    "Zertifikat/Reihe00/G93_const_scalars.lean": (6, 2, 17),
    "Zertifikat/Reihe01/G109_lockfree_entry_roots.lean": (10, 6, 36),
    "Zertifikat/Reihe01/G116_payload_free_counter.lean": (8, 1, 23),
    "Zertifikat/Reihe01/G118_sperrinvariante_erhaltung.lean": (10, 6, 24),
    "Zertifikat/Reihe01/G119_sperrinvariante_bloecke.lean": (7, 3, 19),
    "Zertifikat/Reihe01/G120_tagged_construction.lean": (6, 2, 22),
    "Zertifikat/Reihe01/G121_tagged_static_init.lean": (7, 2, 18),
    "Zertifikat/Reihe01/G124_two_threads_private.lean": (13, 3, 42),
    "Zertifikat/Reihe01/G130_derived_contract_pure.lean": (6, 2, 17),
    "Zertifikat/Reihe01/G157_worker_pool.lean": (8, 3, 26),
    "Zertifikat/Reihe01/G162_geteilte_flagge.lean": (8, 1, 23),
    "Zertifikat/Reihe01/G165_gp_eintritt.lean": (6, 2, 17),
    "Zertifikat/Reihe01/G166_eintritt_irq_maskiert.lean": (8, 4, 24),
    "Zertifikat/Reihe01/G174_tor_im_modell.lean": (7, 3, 26),
    "Zertifikat/Reihe01/G181_gate_at_top_level.lean": (7, 3, 26),
    "Zertifikat/Reihe01/G182_fallible_gate.lean": (6, 2, 19),
    "Zertifikat/Reihe01/G187_bool_statisch.lean": (8, 1, 23),
    "Zertifikat/Reihe01/G190_erster_treffer.lean": (7, 4, 18),
    "Zertifikat/Reihe01/G193_zwei_tabellen_kein_fehlablauf.lean": (9, 1, 24),
    "Zertifikat/Reihe02/G219_unaeres_minus.lean": (6, 2, 17),
    "Zertifikat/Reihe04/G414_tabellenspeicher_heisst_so.lean": (7, 2, 19),
    "Zertifikat/Reihe07/G700_lesen_ohne_klausel.lean": (7, 2, 18),
    "Zertifikat/Reihe07/G701_rein_ohne_klausel.lean": (6, 2, 17),
    "Zertifikat/Reihe07/G719_lock_taken_nowhere.lean": (6, 4, 18),
    "Zielsatz/Atomar/AtomarAkzeptiert.lean": (11, 0, 5),
    "Zielsatz/Atomar/AtomarAkzeptiertZeuge.lean": (25, 0, 14),
    "Zielsatz/Atomar/AtomarGoalZeuge.lean": (5, 0, 0),
    "Zielsatz/Atomar/AtomarInvarianten.lean": (10, 0, 0),
    "Zielsatz/Atomar/AtomarMasken.lean": (4, 0, 0),
    "Zielsatz/Atomar/AtomarPflicht.lean": (16, 0, 1),
    "Zielsatz/Atomar/AtomarRuheNutzer.lean": (10, 0, 1),
    "Zielsatz/Atomar/AtomarZertifikatZeuge.lean": (3, 0, 0),
    "Zielsatz/Atomar/AtomarZiel.lean": (7, 0, 2),
    "Zielsatz/Atomar/BeweisAtomar.lean": (24, 0, 0),
    "Zielsatz/BeweisAtomar.lean": (0, 0, 0),
    "Zielsatz/Eigenschaften/Divergenz.lean": (40, 0, 33),
    "Zielsatz/Eigenschaften/FolgeZiel.lean": (12, 0, 1),
    "Zielsatz/Eigenschaften/Invarianten.lean": (14, 0, 0),
    "Zielsatz/Eigenschaften/InvariantenZeuge.lean": (9, 0, 0),
    "Zielsatz/Eigenschaften/Masken.lean": (16, 0, 2),
    "Zielsatz/Eigenschaften/MaskenZeuge.lean": (13, 0, 12),
    "Zielsatz/Eigenschaften/NeverAsm.lean": (11, 0, 1),
    "Zielsatz/Eigenschaften/Schwach.lean": (4, 0, 0),
    "Zielsatz/Faeden/Faeden.lean": (5, 0, 0),
    "Zielsatz/Faeden/FaedenVor.lean": (7, 0, 6),
    "Zielsatz/Faeden/FaedenZeuge.lean": (37, 0, 25),
    "Zielsatz/Faeden/PoolSym.lean": (20, 0, 12),
    "Zielsatz/Faeden/PoolZeuge.lean": (15, 0, 4),
    "Zielsatz/Faeden/Ruhe.lean": (46, 0, 2),
    "Zielsatz/Faeden/RuheNutzer.lean": (31, 0, 1),
    "Zielsatz/Faeden/RuheZeuge.lean": (9, 0, 1),
    "Zielsatz/Faeden/Verbund.lean": (45, 0, 8),
    "Zielsatz/Faeden/VerbundZeuge.lean": (13, 0, 15),
    "Zielsatz/Kern/Akzeptiert.lean": (32, 0, 25),
    "Zielsatz/Kern/AkzeptiertZeuge.lean": (28, 0, 32),
    "Zielsatz/Kern/Beweis.lean": (6, 0, 0),
    "Zielsatz/Kern/Proben.lean": (34, 0, 0),
    "Zielsatz/Kern/ProbenG1.lean": (25, 0, 17),
    "Zielsatz/Kern/ProbenW1.lean": (12, 0, 14),
    "Zielsatz/Kern/Spec.lean": (0, 0, 85),
    "Zielsatz/Kern/SpecProben.lean": (1, 0, 20),
    "Zielsatz/ZielOrt/Geraet/ZielOrtBeweis.lean": (37, 0, 13),
    "Zielsatz/ZielOrt/Geraet/ZielOrtGeraet.lean": (7, 0, 0),
    "Zielsatz/ZielOrt/Geraet/ZielOrtGeraetAus.lean": (10, 0, 11),
    "Zielsatz/ZielOrt/Geraet/ZielOrtGeraetBeweis.lean": (11, 0, 5),
    "Zielsatz/ZielOrt/Geraet/ZielOrtGeraetSem.lean": (38, 0, 19),
    "Zielsatz/ZielOrt/Geraet/ZielOrtGeraetZeuge.lean": (33, 0, 31),
    "Zielsatz/ZielOrt/Geraet/ZielOrtSperre.lean": (12, 0, 0),
    "Zielsatz/ZielOrt/Geraet/ZielOrtSperreZeuge.lean": (56, 0, 33),
    "Zielsatz/ZielOrt/Grundlage/ZielOrt.lean": (37, 0, 29),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtGanz.lean": (30, 0, 10),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtGanzZeuge.lean": (40, 0, 15),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtGrund.lean": (11, 0, 4),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtRegister.lean": (24, 0, 30),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtSem.lean": (73, 0, 7),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtStart.lean": (11, 0, 6),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtVoll.lean": (14, 0, 1),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtVollBeweis.lean": (37, 0, 21),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtVollSem.lean": (96, 0, 14),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtVollZeuge.lean": (33, 0, 30),
    "Zielsatz/ZielOrt/Grundlage/ZielOrtZeuge.lean": (40, 0, 29),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtAx.lean": (6, 0, 0),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtAxBeweis.lean": (10, 0, 5),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtAxZeuge.lean": (13, 0, 7),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtEinfaden.lean": (6, 0, 3),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtEinfadenZeuge.lean": (24, 0, 20),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtInv.lean": (6, 0, 4),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtInvGrund.lean": (8, 0, 0),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtInvGrundZeuge.lean": (35, 0, 30),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtMehrfaden.lean": (14, 0, 11),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtRahmen.lean": (10, 0, 0),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtRahmenBeweis.lean": (16, 0, 7),
    "Zielsatz/ZielOrt/Rahmen/ZielOrtRahmenSem.lean": (21, 0, 9),
}

ZEILEN_SATZ = re.compile(r"^(theorem|lemma) ")
ZEILEN_BEISPIEL = re.compile(r"^example ")
ZEILEN_DEF = re.compile(r"^(def|abbrev|structure|inductive|class) ")


def ohne_kommentare(text):
    """Zeilen- (`--`) und geschachtelte Blockkommentare (`/- -/`) entfernen.

    Was in einem Kommentar steht, ist kein Konstrukt: `-- theorem spaet`
    und ein `theorem` im Blockkommentar duerfen nicht mitzaehlen -- sonst
    zaehlt eine auskommentierte Zeile als Satz (W16: das Werkzeug misst
    seine eigene Lesart).
    """
    out = []
    i, n, tiefe = 0, len(text), 0
    while i < n:
        if tiefe == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            tiefe += 1
            i += 2
        elif tiefe > 0 and text.startswith("-/", i):
            tiefe -= 1
            i += 2
        elif tiefe == 0:
            out.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(out)


def zaehle(pfad):
    """(Saetze, Beispiele, Definitionen) einer Datei, nach obiger Methode."""
    code = ohne_kommentare(pfad.read_text(encoding="utf-8"))
    saetze = beispiele = definitionen = 0
    for zeile in code.split("\n"):
        if ZEILEN_SATZ.match(zeile):
            saetze += 1
        elif ZEILEN_BEISPIEL.match(zeile):
            beispiele += 1
        elif ZEILEN_DEF.match(zeile):
            definitionen += 1
    return saetze, beispiele, definitionen


def pruefe(gegenstand):
    """Liste der Befunde; leer heisst: jede Datei steht auf ihrer Zeile."""
    befunde = []
    dateien = sorted(gegenstand.rglob("*.lean"))
    for pfad in dateien:
        name = pfad.relative_to(gegenstand).as_posix()
        if name not in ERWARTET:
            befunde.append(f"{name}: keine Zeile in der Ratsche -- neu, "
                           f"nicht gebucht")
            continue
        ist = zaehle(pfad)
        soll = ERWARTET[name]
        if ist != soll:
            befunde.append(f"{name}: steht als {soll}, gemessen {ist}")
    for name in ERWARTET:
        if not (gegenstand / name).is_file():
            befunde.append(f"{name}: Zeile ohne Datei -- entfernt, nicht Ausfall")
    return befunde, len(dateien)


def sprechprobe():
    """Sprechprobe in BEIDE Richtungen: was stimmt, besteht; was verstellt
    ist, faellt. Laeuft auf Wegwerf-Dateien im eigenen Kratzverzeichnis --
    nie im Baum (`CLAUDE.md`: fremde Dateien im Messverzeichnis verderben
    den Lauf, der sie liest)."""
    with tempfile.TemporaryDirectory(prefix="gestaltprobe-") as d:
        ort = Path(d)
        sauber = (
            "-- theorem spaet -- zaehlt nicht, Kommentar\n"
            "/- theorem tief -/\n"
            "/- aussen /- theorem tief2 -/ noch aussen -/\n"
            "theorem echt_a : True := trivial\n"
            "  theorem eingerueckt : True := trivial\n"
            "def d_a : Nat := 1\n"
            "abbrev A := Nat\n"
            "structure S where\n"
            "  x : Nat\n"
            "inductive I | a | b\n"
            "example e_a : True := trivial\n"
        )
        (ort / "sauber.lean").write_text(sauber, encoding="utf-8")
        if zaehle(ort / "sauber.lean") != (1, 1, 4):
            return False, "saubere Vorlage falsch gelesen"
        (ort / "verstellt.lean").write_text(sauber + "theorem spaet : True := trivial\n",
                                            encoding="utf-8")
        # Die verstellte Datei MUSS von der Ratsche abweichen: ein Eintrag
        # mit (1, 1, 4) daneben faellt auf (1, 1, 4) gegen (2, 1, 4).
        if zaehle(ort / "verstellt.lean") == (1, 1, 4):
            return False, "verstellte Datei kam durch"
    return True, ""


def main():
    signal.alarm(FRIST)
    ok, grund = sprechprobe()
    if not ok:
        print(f"ABBRUCH: Sprechprobe versagt ({grund}) -- NICHTS gemessen.")
        print("  Ein Waechter, der seine eigene Probe nicht besteht, misst")
        print("  einen Defekt an sich selbst, keinen am Gegenstand (R14).")
        return 2
    print("== Sprechprobe des Waechters ==")
    print("  saubere Vorlage gelesen, verstellte erkannt -- ok")
    if not GEGENSTAND.is_dir():
        print(f"ABBRUCH: {GEGENSTAND} fehlt -- NICHTS gemessen.")
        print("  Ueber einem fehlenden Gegenstand ist jede Zahl null, und null")
        print("  saehe aus wie ein sauberer Baum (W17).")
        return 2
    befunde, n = pruefe(GEGENSTAND)
    t = e = d = 0
    for name in sorted(ERWARTET):
        p = GEGENSTAND / name
        if p.is_file():
            st, be, de = zaehle(p)
            t, e, d = t + st, e + be, d + de
    # **Die Arbeitsmenge neben dem Urteil** (W17): ein Lauf, der null faehrt,
    # ist rot statt gruen.
    print(f"== Gestalt: {n} Dateien, {t} Saetze, {e} Beispiele, {d} Definitionen ==")
    if n == 0:
        print("ABBRUCH: keine Datei gezaehlt -- das ist kein sauberer Baum.")
        return 2
    if befunde:
        for b in befunde:
            print(f"  BEFUND  {b}")
        print("== GESTALT: ROT -- der Baum ist neben seiner Ratsche ==")
        return 1
    print("== GESTALT: GRUEN -- jede Datei steht auf ihrer Zeile ==")
    return 0


if __name__ == "__main__":
    sys.exit(main())
