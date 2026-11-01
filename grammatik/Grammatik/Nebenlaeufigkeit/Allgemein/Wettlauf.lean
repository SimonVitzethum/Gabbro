/-
  Datei:      Grammatik/Wettlauf.lean
  Gegenstand: **Faeden, verschraenkt** -- und der Satz, dass zwei Faeden mit Spuren, wie die
              Grammatik sie hinterlaesst, einen bewachten Traeger nie im Wettlauf beruehren.

  ## Das Modell

  Ein LAUF ist eine Folge von Schritten (Faden, Ereignis), in Zeitfolge. Die Spur eines Fadens
  bis zum Zeitpunkt `j` ist, was `Semantik.lean` in `World.spur` schreibt: seine eigenen
  Ereignisse, neuestes zuerst. Was ein Faden HAELT, ist `offen` seiner Spur -- wie in der Welt.

  Ein Lauf ist GESITTET, wenn
    (W1) jede Fadenspur konsistent ist          -- `exec_spur`, Klausel 3
    (W2) jedes Ereignis gut ist                 -- `exec_spur`, Klausel 2
    (W3) Sperren einander AUSSCHLIESSEN: wer `L` nimmt, nimmt es, wenn kein anderer Faden
         `L` haelt                              -- was eine Sperre IST: die Zusage der
                                                   Sperrprimitive (ein fremder Rumpf), A_lock
    (W4) eine Marke ist in EINEM Faden          -- Linearitaet: keine Anweisung reicht eine
                                                   Marke an einen anderen Faden weiter, und
                                                   Eigentumsmarken erzeugt niemand
    (W5) ein ungeteilter Traeger gehoert EINEM Faden -- `geteilt`, die Erklaerung (`H013`)

  ## Der Satz

  `kein_wettlauf`: in einem gesitteten Lauf sind zwei Zugriffe verschiedener Faeden auf
  denselben Traeger durch HAPPENS-BEFORE geordnet -- Programmfolge im Faden, und `gibt L`
  vor `nimmt L`. Fuer ein Global: geordnet, oder das Global ist `atomic` -- und dann ordnet
  es die Maschine (A10, `Hardware.sichtbarkeit`). **Es gibt keinen dritten Fall**: das ist
  die Freiheit von Wettlaeufen als Satz ueber Verschraenkungen, nicht nur ueber Ableitungen.

  Der Beweis ist der klassische: beide Zugriffe tragen den Waechter des Traegers (W2); ist
  er eine Sperre, halten beide Faeden sie zu ihrer Zeit (W1); dann liegt zwischen dem
  ersten Zugriff und dem zweiten ein `gibt` des ersten Fadens und ein `nimmt` des zweiten
  (W3, und dass kein Faden eine Sperre zweimal nimmt -- `gut` am `nimmt`). Ist der Waechter
  eine Marke, sind es derselbe Faden (W4) -- kein zweiter Zugreifer.
-/
module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf.Teil1
public import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf.Teil2
