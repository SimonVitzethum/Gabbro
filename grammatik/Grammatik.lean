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
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.Satz
import Grammatik.Wettlauf
import Grammatik.Zucker
import Grammatik.Ziel
import Grammatik.Interferenz
import Grammatik.Koernung
import Grammatik.Geteilt
import Grammatik.Geraet
import Grammatik.Unterbrechung
import Grammatik.Zeugnis
import Grammatik.Budget
import Grammatik.Terminierung
import Grammatik.InterferenzAllgemein
import Grammatik.Komposition
import Grammatik.Fehler
import Grammatik.Erhaltung
import Grammatik.Extraktion
import Grammatik.Marken
import Grammatik.Fristlauf
import Grammatik.Adressraum
import Grammatik.LesenStabil
import Grammatik.Maschine
import Grammatik.MaschinenKette
import Grammatik.QLeer
import Grammatik.BlattGegenbeispiel
import Grammatik.VertragOrtB
import Grammatik.RufAtNachB
import Grammatik.KetteMehrfadenC
import Grammatik.MarkenInstanzA
import Grammatik.RufMaschineD
import Grammatik.Geist
import Grammatik.EigenZustandD
import Grammatik.ReferenzB
import Grammatik.HoareRegeln
import Grammatik.RufMaschineF
import Grammatik.Syscall
import Grammatik.Ueberlauf
import Grammatik.Profil
import Grammatik.Schiebung
import Grammatik.FremdSperre
import Grammatik.Bits
import Grammatik.CSLInvarianteC
import Grammatik.Arena
import Grammatik.ArenaZucker
import Grammatik.HoareRuf
import Grammatik.EigenZustand
import Grammatik.SyscallPaarung
import Grammatik.RufMaschineG
import Grammatik.CSLInvariante
import Grammatik.Konstanten
import Grammatik.Bibliothek
import Grammatik.WacheGlobal
import Grammatik.StabilBewacht
import Grammatik.DisziplinBedarf
import Grammatik.VertragsFuss
import Grammatik.RelySperre
import Grammatik.Trennung
import Grammatik.AuditW5
import Grammatik.RufAdaequatG
import Grammatik.RufAdaequatRufG
import Grammatik.KetteVoll
import Grammatik.Uebersetzung
import Grammatik.CSemantik
import Grammatik.CSpeicher
import Grammatik.RufUmkehrRufG
import Grammatik.RufHaeltG
import Grammatik.ZielOrt
import Grammatik.ZielOrtSem
import Grammatik.ZielOrtBeweis
import Grammatik.ZielOrtZeuge
import Grammatik.AuditZiel
import Grammatik.RennfreiG
import Grammatik.ZielOrtVollSem
import Grammatik.ZielOrtVollBeweis
import Grammatik.ZielOrtVoll
import Grammatik.ZielOrtVollZeuge
import Grammatik.ZielOrtRegister
import Grammatik.ZielOrtGeraetSem
import Grammatik.ZielOrtGeraetBeweis
import Grammatik.ZielOrtGeraet
import Grammatik.ZielOrtGeraetAus
import Grammatik.ZielOrtGeraetZeuge
import Grammatik.KostenG
import Grammatik.KostenGZeuge
import Grammatik.AuditFinal
import Grammatik.ZeugnisStmt
import Grammatik.RennfreiVoll
import Grammatik.TravAwaitsZeuge
import Grammatik.TravAwaitsLauf
import Grammatik.AxiomVertrag
import Grammatik.ZielOrtAxBeweis
import Grammatik.ZielOrtAx
import Grammatik.ZielOrtAxZeuge
import Grammatik.Referenz104
import Grammatik.ZielOrtRahmenSem
import Grammatik.ZielOrtRahmenBeweis
import Grammatik.ZielOrtRahmen
import Grammatik.Referenz104Rahmen
import Grammatik.ZeugnisStmt2
import Grammatik.CFormen
import Grammatik.CFormenI
import Grammatik.CFormenM
import Grammatik.CFormenZeuge
import Grammatik.CFormenH
import Grammatik.CFormenDet
import Grammatik.ErhaltungT4
import Grammatik.ZielOrtGanz
import Grammatik.ZielOrtGanzZeuge
import Grammatik.Export104
import Grammatik.Export108
import Grammatik.ReferenzAR
import Grammatik.ZeugnisStmt3
import Grammatik.Parser.Lexer
import Grammatik.Parser.LexerVertrauen
import Grammatik.Parser.Ausdruck
import Grammatik.Parser.Anweisung
import Grammatik.Parser.Element
import Grammatik.Parser.AnweisungProben
import Grammatik.Parser.AusdruckProben
import Grammatik.CFormenW
import Grammatik.CFormenWZeuge
import Grammatik.Korrespondenz104
import Grammatik.CFormenR
import Grammatik.CFormenRZeuge
import Grammatik.CFormenRZeuge2
import Grammatik.CFormenR2
import Grammatik.CFormenR2Zeuge
import Grammatik.SperreSem
import Grammatik.SperreFuss
import Grammatik.SperreBeweis
import Grammatik.SperreMaschine
import Grammatik.ZielOrtSperre
import Grammatik.ZielOrtSperreZeuge
import Grammatik.ZielOrtEinfaden
import Grammatik.ZielOrtEinfadenZeuge
import Grammatik.SchablonenT5
import Grammatik.SchablonenT5Sem
import Grammatik.ZeugnisStmt104
import Grammatik.ZeugnisIdent
import Grammatik.ZeugnisStmt104b
import Grammatik.TermIdent104
import Grammatik.ExportSperre
import Grammatik.Parser.ElementTief
import Grammatik.Parser.ElementTiefProben
import Grammatik.Parser.Uebersetze
import Grammatik.ZeugnisKorpus
import Grammatik.HelferZeuge
import Grammatik.SonstLeaveZeuge
import Grammatik.ZielOrtInv
import Grammatik.InvZeuge
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
import Grammatik.Schlusssatz104
import Grammatik.Korrespondenz
import Grammatik.Gleitkomma
import Grammatik.GleitZeuge
import Grammatik.GleitkommaBits
import Grammatik.CFormenF
import Grammatik.CFormenFZeuge
import Grammatik.Verschachtelt
import Grammatik.Parser.Rundlauf
import Grammatik.Parser.Rundlauf2
import Grammatik.Parser.Rundlauf3
import Grammatik.Parser.Rundlauf4
import Grammatik.Parser.UebersetzeAllg
import Grammatik.FadenMerkmal
import Grammatik.ZielOrtMehrfaden
import Grammatik.Durchgaenge
import Grammatik.ZielOrtStart
import Grammatik.Verklemmung
import Grammatik.MehrfadenZeuge
import Grammatik.MehrfadenLauf
import Grammatik.GenOblig104
import Grammatik.Pflicht104
import Grammatik.GenOblig108
import Grammatik.Pflicht108
import Grammatik.ProbeD
import Grammatik.ZielOrtGrund
import Grammatik.RennfreiOrte
import Grammatik.MitRuhe
import Grammatik.MitRuheStatisch
import Grammatik.MitRuheSemantik
import Grammatik.MitRuheSperre
import Grammatik.Zielsatz.Akzeptiert
import Grammatik.Zielsatz.AkzeptiertZeuge
import Grammatik.Zielsatz.Ruhe
import Grammatik.Zielsatz.RuheZeuge
import Grammatik.Zielsatz.Spec
import Grammatik.Zielsatz.SpecProben
import Grammatik.Zielsatz.RuheNutzer
import Grammatik.Zielsatz.Beweis
import Grammatik.FadenMaschine
import Grammatik.Zielsatz.Faeden
import Grammatik.Zielsatz.Invarianten
import Grammatik.Zielsatz.InvariantenZeuge
import Grammatik.Zielsatz.FaedenVor
import Grammatik.Zielsatz.FaedenZeuge
import Grammatik.Zielsatz.Proben
import Grammatik.EinpassenVoll
import Grammatik.Zielsatz.ProbenG1
import Grammatik.Zielsatz.ProbenW1
import Grammatik.Zielsatz.NeverAsm
import Grammatik.Parser.UebersetzeAllg2
import Grammatik.ZielOrtInvGrund
import Grammatik.Fortschritt
import Grammatik.FortschrittZeuge
import Grammatik.Lebendigkeit
import Grammatik.LebendigkeitZeuge
import Grammatik.ZielOrtInvGrundZeuge
import Grammatik.Nichtinterferenz.Freigabe
import Grammatik.Nichtinterferenz.Korpus
import Grammatik.Nichtinterferenz.ZeugeMehrfaden
import Grammatik.CNebenlaeufig
import Grammatik.Korpus124
import Grammatik.CloneHandoff
import Grammatik.Schlusssatz124
import Grammatik.CTicket
import Grammatik.Schlusssatz124Ticket
import Grammatik.RufOhneHardware
import Grammatik.RufOhneHardwareZeuge
import Grammatik.RahmenTreu
import Grammatik.HandlerKongruenz
import Grammatik.RufTiefe
import Grammatik.RufLogik
import Grammatik.KorrespondenzAllg
import Grammatik.KorrOkAdaequat
import Grammatik.KorrOkOhneLocks
import Grammatik.RufLogikZeuge
import Grammatik.KorrespondenzWeitZeuge
import Grammatik.ReferenzZeuge
import Grammatik.KorrespondenzBlockZeuge
import Grammatik.KorrespondenzGeraetZeuge
import Grammatik.Schlusssatz
import Grammatik.Kette104
import Grammatik.Kette104Satz
import Grammatik.Kette108
import Grammatik.SchlusssatzZeuge
import Grammatik.CParser.CLexer
import Grammatik.CParser.CParse
import Grammatik.CParser.CProben
import Grammatik.CParser.Bruecke
import Grammatik.CText104
import Grammatik.CText104Zeuge
import Grammatik.CText108
import Grammatik.Sperrstreifen
import Grammatik.SperrImpl
import Grammatik.CFormNested
import Grammatik.Korpus07
import Grammatik.Korpus59
import Grammatik.Korpus109
import Grammatik.Korpus125
import Grammatik.SimPruef
import Grammatik.ArenaDyn
import Grammatik.ArenaReset
import Grammatik.FremdRuf
import Grammatik.Zielsatz.PoolSym
import Grammatik.Zielsatz.Masken
import Grammatik.Zielsatz.MaskenZeuge
import Grammatik.Zielsatz.PoolZeuge
import Grammatik.CFormMatch
import Grammatik.Zielsatz.Divergenz
import Grammatik.ZeichenfolgeGebunden
import Grammatik.Speichermodell.Sicht
import Grammatik.Speichermodell.MaschineW
import Grammatik.Speichermodell.DRF
import Grammatik.Zielsatz.Schwach
import Grammatik.Speichermodell.Zeuge
import Grammatik.Zertifikate
import Grammatik.Speichermodell.Atomar
import Grammatik.Speichermodell.AtomarZeuge
import Grammatik.Speichermodell.RMW
import Grammatik.Speichermodell.AtomarSem
import Grammatik.Speichermodell.SperreSemA
import Grammatik.Speichermodell.AtomarRec
import Grammatik.Speichermodell.AtomarReplay
import Grammatik.Zielsatz.AtomarPflicht
import Grammatik.Speichermodell.Zaehler
import Grammatik.ZeichenfolgeC
