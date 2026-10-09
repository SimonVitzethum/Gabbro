/-
  Grammatik -- die Grammatik von Gabbro als GETYPTE Grammatik, in Lean 4, ueber die GANZE
  Sprache.

  Der Satz: ein Satz dieser Grammatik hat eine totale Bedeutung, und seine Bedeutung kennt
  genau zwei Fehlerausgaenge -- die Logik des Schreibers (`requires`, `ensures`,
  `invariant`, `decreases`, ein `state`-Uebergang) und eine Hardwareannahme (fremder Rumpf,
  `progress`, IEEE, ein Register, sein Versprechen, das Speichermodell). Es gibt keinen
  dritten, weil der Ausgangstyp keinen dritten hat. Und ueber Verschraenkungen: zwei Faeden
  beruehren einen bewachten Traeger nie im Wettlauf (`Wettlauf.lean`).

  Kein `mathlib`, kein Import aus `programmlogik/` oder `passlogik/`: hier steht nur die
  Grammatik und was ihre Saetze bedeuten -- nichts ueber den Pruefer, nichts ueber den
  Erzeuger.

  | Datei               | Gegenstand                                                        |
  |---------------------|-------------------------------------------------------------------|
  | `Typen.lean`        | die Typen mit Bereich, ihre Werte, die Rechnung (auch mit Vorzeichen), Bytes |
  | `Syntax.lean`       | die GRAMMATIK: Ausdruecke und Anweisungen als getypte Familie      |
  | `Semantik.lean`     | was ein Satz bedeutet: `eval` total, `exec` mit zwei Ausgaengen, die Spur |
  | `Satz.lean`         | der Satz: Rahmen UND Spur in einer Induktion, die Inversionen, `#print axioms` |
  | `Wettlauf.lean`     | Faeden verschraenkt: kein Wettlauf, keine Ueberkreuzung der Sperrordnung |
  | `Zucker.lean`       | jede Schreibweise ohne eigenen Konstruktor, als Definition ueber dem Kern |
  | `ArenaZucker.lean`  | `alloc`/`reset` als Zucker ueber `narrow`+`assignSlot`+`assignGlob`, mit Bruecke zu `Arena.lean` |
| `Ziel.lean`         | DAS ZIEL als Satz ueber der Grammatik -- unabhaengig vom `.rs`-Code       |
  | `Interferenz.lean`  | das Verbundmodell deklarierter Paare: gueltige Vertraege ueberleben Verschraenkung |
  | `Koernung.lean`     | die Ereigniskoernung als benannte Praemisse: keine Zerreissung darunter, Bytes als n Ereignisse |
  | `Geteilt.lean`      | Erreichbarkeit als Konstruktion: ungeteilt heisst von hoechstens einem Faden erreichbar |
  | `Geraet.lean`       | das Geraet als Laufteilnehmer: Ordnung bewiesen, Inhalt benannte Annahme |
  | `Unterbrechung.lean`| der Handler als Faden: HB-Deckung ueber Sperrkante oder Maske            |
  | `Zeugnis.lean`      | die gedruckte Ableitung als Datum: gueltiges Zeugnis heisst Urteil        |
  | `Budget.lean`       | die ops-Frist als Rechnung: im Budget oder benannt erschoepft, nie still drueber |
  | `Terminierung.lean` | das Mass faellt heisst der Lauf endet: traversieren, Wiederholung, forever nie |
  | `InterferenzAllgemein.lean` | N Faeden, beliebig viele Schritte: Stabilitaet als Gestalt, Beweis spaeter |
  | `Komposition.lean` | Rufgraph und Schleifenregel als Gestalt: Ordnung ohne Mass, Zyklen mit |
  | `Fehler.lean`     | der Fehlerausgang als paralleles Modell: Klasse, Ergebnis, evalF-Gestalt |
  | `Erhaltung.lean`  | der Erzeugervertrag als Pflichtenheft: Entsprechung, Alias, Kosten, Tafel |
  | `Extraktion.lean` | berechnete Huellen: Kanten und Fuesse aus Ruempfen, Bau als Ergebnis     |
  | `Marken.lean`     | lineare Marken als Konstruktion: Besitz als Zustand, Einfaedigkeit als Gestalt |
  | `Fristlauf.lean`  | Fristablauf zwischen Pruefung und Lauf als benanntes Ergebnis, keine Wanduhr |
  | `Adressraum.lean` | Nutzerspeicher als Gestalt: gepruefte Kopie oder benannte Luecke          |
  | `LesenStabil.lean` | lesestabile Form: Vertragsgelesenes im Rahmen, Kette bis zum letzten Lauf |
-/
import Grammatik.Kern.Syntax.Typen
import Grammatik.Kern.Syntax.Syntax
import Grammatik.Kern.Semantik.Semantik
import Grammatik.Kern.Syntax.Satz
import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf
import Grammatik.Kern.Syntax.Zucker
import Grammatik.Kern.Syntax.Ziel
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.Interferenz
import Grammatik.Kern.Syntax.Koernung
import Grammatik.Nebenlaeufigkeit.Allgemein.Geteilt
import Grammatik.Kern.Semantik.Geraet
import Grammatik.Nebenlaeufigkeit.Allgemein.Unterbrechung
import Grammatik.Korrespondenz.Zeugnis.Zeugnis
import Grammatik.Kern.Semantik.Budget
import Grammatik.Kern.Semantik.Terminierung
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
import Grammatik.Logik.Vertraege.Komposition
import Grammatik.Kern.Syntax.Fehler
import Grammatik.Kern.Semantik.Erhaltung
import Grammatik.Kern.Syntax.Extraktion
import Grammatik.Kern.Syntax.Marken
import Grammatik.Kern.Semantik.Fristlauf
import Grammatik.Kern.Semantik.Adressraum
import Grammatik.Nebenlaeufigkeit.Allgemein.LesenStabil
import Grammatik.Kern.Semantik.Maschine
import Grammatik.Kern.Semantik.MaschinenKette
import Grammatik.Logik.Vertraege.QLeer
import Grammatik.Proben.BlattGegenbeispiel
import Grammatik.Logik.Vertraege.VertragOrtB
import Grammatik.Logik.Ruf.RufAtNachB
import Grammatik.Korrespondenz.Kette.KetteMehrfadenC
import Grammatik.Kern.Syntax.MarkenInstanzA
import Grammatik.Logik.Ruf.RufMaschineD
import Grammatik.Kern.Syntax.Geist
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD
import Grammatik.Korrespondenz.Allgemein.ReferenzB
import Grammatik.Logik.Ruf.HoareRegeln
import Grammatik.Logik.Ruf.RufMaschineF
import Grammatik.Kern.Semantik.Syscall
import Grammatik.Kern.Semantik.Ueberlauf
import Grammatik.Kern.Syntax.Profil
import Grammatik.Nebenlaeufigkeit.Allgemein.Schiebung
import Grammatik.Nebenlaeufigkeit.Sperren.FremdSperre
import Grammatik.Kern.Syntax.Bits
import Grammatik.CBackend.Semantik.CSLInvarianteC
import Grammatik.Bausteine.Arena.Arena
import Grammatik.Bausteine.Arena.ArenaZucker
import Grammatik.Logik.Ruf.HoareRuf
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustand
import Grammatik.Kern.Semantik.SyscallPaarung
import Grammatik.Logik.Ruf.RufMaschineG
import Grammatik.CBackend.Semantik.CSLInvariante
import Grammatik.Kern.Syntax.Konstanten
import Grammatik.Bausteine.Arena.Bibliothek
import Grammatik.Nebenlaeufigkeit.Allgemein.WacheGlobal
import Grammatik.Nebenlaeufigkeit.Allgemein.StabilBewacht
import Grammatik.Nebenlaeufigkeit.Allgemein.DisziplinBedarf
import Grammatik.Logik.Vertraege.VertragsFuss
import Grammatik.Nebenlaeufigkeit.Sperren.RelySperre
import Grammatik.Nebenlaeufigkeit.Allgemein.Trennung
import Grammatik.Proben.AuditW5
import Grammatik.Logik.Ruf.RufAdaequatG
import Grammatik.Logik.Ruf.RufAdaequatRufG
import Grammatik.Korrespondenz.Kette.KetteVoll
import Grammatik.Logik.Vertraege.Uebersetzung
import Grammatik.CBackend.Semantik.CSemantik
import Grammatik.CBackend.Semantik.CSpeicher
import Grammatik.Logik.Ruf.RufUmkehrRufG
import Grammatik.Logik.Ruf.RufHaeltG
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtZeuge
import Grammatik.Proben.AuditZiel
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiG
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtRegister
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetBeweis
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraet
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetAus
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetZeuge
import Grammatik.Logik.Fortschritt.KostenG
import Grammatik.Logik.Fortschritt.KostenGZeuge
import Grammatik.Proben.AuditFinal
import Grammatik.Korrespondenz.Zeugnis.ZeugnisStmt
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
import Grammatik.Nebenlaeufigkeit.Allgemein.TravAwaitsZeuge
import Grammatik.Nebenlaeufigkeit.Allgemein.TravAwaitsLauf
import Grammatik.Logik.Vertraege.AxiomVertrag
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxBeweis
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxZeuge
import Grammatik.Korrespondenz.Allgemein.Referenz104
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenSem
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmen
import Grammatik.Korrespondenz.Allgemein.Referenz104Rahmen
import Grammatik.Korrespondenz.Zeugnis.ZeugnisStmt2
import Grammatik.CBackend.Formen.CFormen
import Grammatik.CBackend.Formen.CFormenI
import Grammatik.CBackend.Formen.CFormenM
import Grammatik.CBackend.Formen.CFormenZeuge
import Grammatik.CBackend.Formen.CFormenH
import Grammatik.CBackend.Formen.CFormenDet
import Grammatik.Kern.Semantik.ErhaltungT4
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanzZeuge
import Grammatik.Korrespondenz.Korpus.Export104
import Grammatik.Korrespondenz.Korpus.Export108
import Grammatik.Korrespondenz.Allgemein.ReferenzAR
import Grammatik.Korrespondenz.Zeugnis.ZeugnisStmt3
import Grammatik.Parser.Lexer
import Grammatik.Parser.LexerVertrauen
import Grammatik.Parser.Ausdruck
import Grammatik.Parser.Anweisung
import Grammatik.Parser.Element
import Grammatik.Parser.AnweisungProben
import Grammatik.Parser.UebersetzeProben
import Grammatik.Parser.UebersetzeProben2
import Grammatik.Parser.AusdruckProben
import Grammatik.CBackend.Formen.CFormenW
import Grammatik.CBackend.Formen.CFormenWZeuge
import Grammatik.Korrespondenz.Allgemein.Korrespondenz104
import Grammatik.CBackend.Formen.CFormenR
import Grammatik.CBackend.Formen.CFormenRZeuge
import Grammatik.CBackend.Formen.CFormenRZeuge2
import Grammatik.CBackend.Formen.CFormenR2
import Grammatik.CBackend.Formen.CFormenR2Zeuge
import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss
import Grammatik.Nebenlaeufigkeit.Sperren.SperreBeweis
import Grammatik.Nebenlaeufigkeit.Sperren.SperreMaschine
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfaden
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfadenZeuge
import Grammatik.Bausteine.Schablonen.SchablonenT5
import Grammatik.Bausteine.Schablonen.SchablonenT5Sem
import Grammatik.Bausteine.Schablonen.SchablonenOhneLibc
import Grammatik.Bausteine.Schablonen.SchablonenArena
import Grammatik.Bausteine.Schablonen.SchablonenFaden
import Grammatik.Bausteine.Schablonen.SchablonenModul
import Grammatik.Bausteine.Schablonen.SchablonenMetall
import Grammatik.Bausteine.Schablonen.SchablonenMetallSperre
import Grammatik.Bausteine.Schablonen.SchablonenMetallIdt
import Grammatik.Bausteine.Schablonen.SchablonenMetallFaden
import Grammatik.Korrespondenz.Zeugnis.ZeugnisStmt104
import Grammatik.Korrespondenz.Zeugnis.ZeugnisIdent
import Grammatik.Korrespondenz.Zeugnis.ZeugnisStmt104b
import Grammatik.Korrespondenz.Korpus.TermIdent104
import Grammatik.Nebenlaeufigkeit.Sperren.ExportSperre
import Grammatik.Parser.ElementTief
import Grammatik.Parser.ElementTiefProben
import Grammatik.Parser.Uebersetze
import Grammatik.Korrespondenz.Zeugnis.ZeugnisKorpus
import Grammatik.Proben.HelferZeuge
import Grammatik.Proben.SonstLeaveZeuge
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInv
import Grammatik.Proben.InvZeuge
import Grammatik.Isabelle.Table_Induktion
import Grammatik.Isabelle.Table_Indexschranke
import Grammatik.Isabelle.Table_Absenkung
import Grammatik.Isabelle.Table_Zaehlung
import Grammatik.Isabelle.Table_Ops_Erhaltung
import Grammatik.Isabelle.Absenkung_Parametrisch
import Grammatik.Isabelle.Intervall_Aussen
import Grammatik.Isabelle.AccumulatesMonoid
import Grammatik.Isabelle.GruppeErhaltung
import Grammatik.Isabelle.FormatRoundtrip
import Grammatik.Isabelle.OptionSonderwert
import Grammatik.Isabelle.Consuming
import Grammatik.Isabelle.DeviceKonstruktor
import Grammatik.Isabelle.VerbundKonstruktor
import Grammatik.Isabelle.RestrictAlleinzugriff
import Grammatik.Korrespondenz.Kette.Schlusssatz104
import Grammatik.Korrespondenz.Allgemein.Korrespondenz
import Grammatik.Bausteine.Gleitkomma.Gleitkomma
import Grammatik.Bausteine.Gleitkomma.GleitZeuge
import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
import Grammatik.CBackend.Formen.CFormenF
import Grammatik.CBackend.Formen.CFormenFZeuge
import Grammatik.Nebenlaeufigkeit.Allgemein.Verschachtelt
import Grammatik.Parser.Rundlauf
import Grammatik.Parser.Rundlauf2
import Grammatik.Parser.Rundlauf3
import Grammatik.Parser.Rundlauf4
import Grammatik.Parser.UebersetzeAllg
import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMerkmal
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden
import Grammatik.Kern.Semantik.Durchgaenge
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtStart
import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung
import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenZeuge
import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenLauf
import Grammatik.Korrespondenz.Korpus.GenOblig104
import Grammatik.Korrespondenz.Allgemein.Pflicht104
import Grammatik.Korrespondenz.Korpus.GenOblig108
import Grammatik.Korrespondenz.Allgemein.Pflicht108
import Grammatik.Proben.ProbeD
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGrund
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuhe
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheStatisch
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSperre
import Grammatik.Zielsatz.Kern.Akzeptiert
import Grammatik.Zielsatz.Kern.AkzeptiertZeuge
import Grammatik.Zielsatz.Faeden.Ruhe
import Grammatik.Zielsatz.Faeden.RuheZeuge
import Grammatik.Zielsatz.Kern.Spec
import Grammatik.Zielsatz.Kern.SpecProben
import Grammatik.Zielsatz.Faeden.RuheNutzer
import Grammatik.Zielsatz.Kern.Beweis
import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMaschine
import Grammatik.Zielsatz.Faeden.Faeden
import Grammatik.Zielsatz.Eigenschaften.Invarianten
import Grammatik.Zielsatz.Eigenschaften.InvariantenZeuge
import Grammatik.Zielsatz.Faeden.FaedenVor
import Grammatik.Zielsatz.Faeden.FaedenZeuge
import Grammatik.Zielsatz.Kern.Proben
import Grammatik.Logik.Vertraege.EinpassenVoll
import Grammatik.Zielsatz.Kern.ProbenG1
import Grammatik.Zielsatz.Kern.ProbenW1
import Grammatik.Zielsatz.Eigenschaften.NeverAsm
import Grammatik.Parser.UebersetzeAllg2
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInvGrund
import Grammatik.Logik.Fortschritt.Fortschritt
import Grammatik.Logik.Fortschritt.FortschrittZeuge
import Grammatik.Logik.Fortschritt.Lebendigkeit
import Grammatik.Logik.Fortschritt.LebendigkeitZeuge
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInvGrundZeuge
import Grammatik.Nichtinterferenz.Freigabe
import Grammatik.Nichtinterferenz.Korpus
import Grammatik.Nichtinterferenz.ZeugeMehrfaden
import Grammatik.CBackend.Semantik.CNebenlaeufig
import Grammatik.Korrespondenz.Korpus.Korpus124
import Grammatik.CBackend.Semantik.CloneHandoff
import Grammatik.Korrespondenz.Kette.Schlusssatz124
import Grammatik.CBackend.Semantik.CTicket
import Grammatik.Korrespondenz.Kette.Schlusssatz124Ticket
import Grammatik.Logik.Ruf.RufOhneHardware
import Grammatik.Logik.Ruf.RufOhneHardwareZeuge
import Grammatik.Logik.Vertraege.RahmenTreu
import Grammatik.Logik.Vertraege.HandlerKongruenz
import Grammatik.Logik.Ruf.RufTiefe
import Grammatik.Logik.Ruf.RufLogik
import Grammatik.Korrespondenz.Allgemein.KorrespondenzAllg
import Grammatik.Korrespondenz.Allgemein.KorrOkAdaequat
import Grammatik.Korrespondenz.Allgemein.KorrOkOhneLocks
import Grammatik.Logik.Ruf.RufLogikZeuge
import Grammatik.Korrespondenz.Allgemein.KorrespondenzWeitZeuge
import Grammatik.Korrespondenz.Allgemein.ReferenzZeuge
import Grammatik.Korrespondenz.Allgemein.KorrespondenzBlockZeuge
import Grammatik.Korrespondenz.Allgemein.KorrespondenzGeraetZeuge
import Grammatik.Korrespondenz.Kette.Schlusssatz
import Grammatik.Korrespondenz.Kette.Kette104
import Grammatik.Korrespondenz.Kette.Kette104Satz
import Grammatik.Korrespondenz.Kette.Kette108
import Grammatik.Korrespondenz.Kette.SchlusssatzZeuge
import Grammatik.CBackend.Parser.CLexer
import Grammatik.CBackend.Parser.CParse
import Grammatik.CBackend.Parser.CProben
import Grammatik.CBackend.Parser.Bruecke
import Grammatik.CBackend.Semantik.CText104
import Grammatik.CBackend.Semantik.CText104Zeuge
import Grammatik.CBackend.Semantik.CText108
import Grammatik.Nebenlaeufigkeit.Sperren.Sperrstreifen
import Grammatik.Nebenlaeufigkeit.Sperren.SperrImpl
import Grammatik.CBackend.Formen.CFormNested
import Grammatik.Korrespondenz.Korpus.Korpus07
import Grammatik.Korrespondenz.Korpus.Korpus59
import Grammatik.Korrespondenz.Korpus.Korpus109
import Grammatik.Korrespondenz.Korpus.Korpus125
import Grammatik.Proben.SimPruef
import Grammatik.Bausteine.Arena.ArenaDyn
import Grammatik.Bausteine.Arena.ArenaReset
import Grammatik.Logik.Ruf.FremdRuf
import Grammatik.Zielsatz.Faeden.PoolSym
import Grammatik.Zielsatz.Eigenschaften.Masken
import Grammatik.Zielsatz.Eigenschaften.MaskenZeuge
import Grammatik.Zielsatz.Faeden.PoolZeuge
import Grammatik.CBackend.Formen.CFormMatch
import Grammatik.Zielsatz.Eigenschaften.Divergenz
import Grammatik.CBackend.Semantik.ZeichenfolgeGebunden
import Grammatik.Speichermodell.Maschine.Sicht
import Grammatik.Speichermodell.Maschine.MaschineW
import Grammatik.Speichermodell.Maschine.DRF
import Grammatik.Zielsatz.Eigenschaften.Schwach
import Grammatik.Speichermodell.Maschine.Zeuge
import Grammatik.Speichermodell.Darstellung
import Grammatik.CBackend.Semantik.ZeichenfolgeZelle
import Grammatik.Speichermodell.DarstellungTy
import Grammatik.Speichermodell.RecordLage
import Grammatik.Speichermodell.Sprungtafel
import Grammatik.Speichermodell.Fenster
import Grammatik.Speichermodell.Zaehlen
import Grammatik.Speichermodell.OptBereich
import Grammatik.Korrespondenz.Zeugnis.Zertifikate
import Grammatik.Speichermodell.Atomar.Atomar
import Grammatik.Speichermodell.Atomar.AtomarZeuge
import Grammatik.Speichermodell.Maschine.RMW
import Grammatik.Speichermodell.Atomar.AtomarSem
import Grammatik.Speichermodell.Maschine.SperreSemA
import Grammatik.Speichermodell.Atomar.AtomarRec
import Grammatik.Speichermodell.Atomar.AtomarReplay
import Grammatik.Speichermodell.Atomar.AtomarAkteur
import Grammatik.Speichermodell.Atomar.AtomarLauf
import Grammatik.Speichermodell.Atomar.AtomarW
import Grammatik.Speichermodell.Atomar.AtomarInv
import Grammatik.Speichermodell.Atomar.AtomarRuhe
import Grammatik.Speichermodell.Atomar.AtomarFortschritt
import Grammatik.Speichermodell.Atomar.AtomarZiel
import Grammatik.Zielsatz.Atomar.AtomarPflicht
import Grammatik.Zielsatz.Atomar.AtomarRuheNutzer
import Grammatik.Zielsatz.Atomar.AtomarInvarianten
import Grammatik.Zielsatz.Atomar.AtomarMasken
import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
import Grammatik.Zielsatz.Atomar.AtomarZiel
import Grammatik.Zielsatz.Atomar.AtomarAkzeptiertZeuge
import Grammatik.Speichermodell.Maschine.Zaehler
import Grammatik.CBackend.Semantik.ZeichenfolgeC
import Grammatik.Zielsatz.Faeden.Verbund
import Grammatik.Zielsatz.Faeden.VerbundZeuge
import Grammatik.Speichermodell.Maschine.GXMaschine
import Grammatik.Logik.Fortschritt.Folge
import Grammatik.Logik.Fortschritt.FolgeBeweis
import Grammatik.Logik.Fortschritt.FolgeZeuge
import Grammatik.Zielsatz.Eigenschaften.FolgeZiel
import Grammatik.Zielsatz.Atomar.AtomarGoalZeuge
import Grammatik.Zielsatz.Atomar.AtomarZertifikatZeuge
import Grammatik.Speichermodell.Maschine.ZaehlerW

import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.GabbroV.GvStartPflicht
import Grammatik.GabbroV.GvAtomRely
import Grammatik.GabbroV.GvTraversal
import Grammatik.GabbroV.GvTreeParent
import Grammatik.GabbroV.GvSplits
import Grammatik.GabbroV.GvParserFragment
import Grammatik.GabbroV.GvLuecken
import Grammatik.GabbroV.GvParserFragment3
import Grammatik.GabbroV.GvParserFragment4
import Grammatik.GabbroV.GvVerkettung
import Grammatik.GabbroV.GvKetten
import Grammatik.GabbroV.GvBruecke
import Grammatik.GabbroV.GvStore
import Grammatik.GabbroV.GvLauf
import Grammatik.GabbroV.GvBaum
import Grammatik.GabbroV.GvZensus
import Grammatik.GabbroV.GvAtomKoerper
import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.Kern.Semantik.SyscallArm
import Grammatik.Kern.Semantik.SyscallArmLinux
import Grammatik.Kern.Semantik.SyscallAllg
import Grammatik.Kern.Semantik.SyscallArmPflicht
