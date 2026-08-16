(*  Titel:      Table_Induktion.thy
    Gegenstand: Die Schablone `table.induktion` aus `gabbro schablonen` (S4)
    Stand:      2026-08-16

    ================================================================================
    ACHTUNG -- DIESE DATEI IST **NICHT MASCHINELL GEPRUEFT**.
    ================================================================================

    Auf dieser Maschine ist kein Beweiser installiert:

        isabelle coqc lean lean4 agda z3 cvc5 why3 alt-ergo   ->  keiner vorhanden

    Damit ist die Schablone NICHT bewiesen, und ihr `Stand` bleibt `Entworfen`.
    Eine `.thy`-Datei, die niemand geprueft hat, ist eine Prosa-Schablone in anderer
    Schrift -- und sie als Beweis zu buchen waere genau der Griff, gegen den dieses
    Register steht.

    Was diese Datei IST: der Formalisierungsversuch, dessen vorregistrierter Ertrag
    nicht am Maschinencheck haengt -- das **Ausspuelen der stillen Nebenbedingungen**
    (MESSUNGEN.md, VORAB vom 2026-08-16). Vier waren namentlich vorhergesagt; was sie
    ergeben haben, steht unten bei jeder Stelle und im ERGEBNIS-Abschnitt.
*)

theory Table_Induktion
  imports Main
begin

section \<open>Die Deklaration, formalisiert\<close>

text \<open>
  Eine `table T count N` mit einem Verkettungsfeld. Der Zustand ist eine Abbildung von
  Index auf Slot; die Kante entsteht aus zwei Feldern (`first_child`, `next_sibling`).
\<close>

type_synonym idx = nat

record 'a slot =
  first_child :: "idx option"
  next_sibling :: "idx option"
  nutz :: 'a

type_synonym 'a tabelle = "idx \<Rightarrow> 'a slot option"

definition im_bereich :: "nat \<Rightarrow> idx \<Rightarrow> bool" where
  "im_bereich N i \<longleftrightarrow> i < N"

section \<open>N-1 -- Endlichkeit: sie faellt NICHT aus dieser Schablone\<close>

text \<open>
  **Ausgespuelt.** Die Prosa sagt \<open>wohlfundiert und vollstaendig\<close>. Wohlfundiertheit
  ueber einer unendlichen Traegermenge ist moeglich, aber das erzeugte Schema braucht
  hier mehr: die Abkoemmlingsmenge muss **endlich** sein, damit das Mass (Zahl der
  Abkoemmlinge) ueberhaupt existiert.

  Und sie faellt nicht aus dieser Deklaration, sondern aus einer ANDEREN Schablone:
  \<open>index into T\<close> erbt seine Schranke aus \<open>count N\<close> -- das ist
  `table.indexschranke` (S12). Ohne sie koennte ein Verkettungsfeld aus der Tabelle
  hinauszeigen, und die Traegermenge waere nicht mehr \<open>{0..<N}\<close>.

  **Der Befund: `table.induktion` haengt an `table.indexschranke`.** Der Eintrag nannte
  diese Abhaengigkeit nicht. Eine Schablonenliste ohne Abhaengigkeiten sieht aus wie
  17 unabhaengige Posten -- und ist es nicht.
\<close>

definition traeger :: "nat \<Rightarrow> idx set" where
  "traeger N = {i. i < N}"

lemma traeger_endlich: "finite (traeger N)"
  unfolding traeger_def by simp

section \<open>Die Kante und die Abkoemmlingsrelation\<close>

definition kinder :: "'a tabelle \<Rightarrow> idx \<Rightarrow> idx set" where
  "kinder \<sigma> s =
     (case \<sigma> s of
        None \<Rightarrow> {}
      | Some sl \<Rightarrow> geschwisterkette \<sigma> (first_child sl))"

text \<open>
  \<open>geschwisterkette\<close> laeuft \<open>next_sibling\<close> bis \<open>None\<close>. **Diese Definition ist selbst nur
  wohldefiniert, wenn die Geschwisterkette endlich ist** -- also azyklisch. Isabelle
  wuerde hier eine Terminierungspflicht verlangen, und genau das ist der Punkt: die
  Definition der Domaene traegt schon die Invariante, die man beweisen wollte.
\<close>

definition abkomm :: "'a tabelle \<Rightarrow> (idx \<times> idx) set" where
  "abkomm \<sigma> = {(d, s). d \<in> kinder \<sigma> s}"

section \<open>N-2 -- der Zustand ist FEST, und das stand nirgends\<close>

text \<open>
  **Ausgespuelt.** \<open>abkomm \<sigma>\<close> traegt den Zustand \<open>\<sigma>\<close> als Parameter. Das
  Induktionsprinzip gilt fuer **einen** Zustand -- es sagt NICHTS ueber eine
  Traversierung, die waehrend des Laufs mutiert.

  Die Prosa des Eintrags (\<open>wohlfundiert und vollstaendig\<close>) sagt nicht, **an welchem
  Zustand**. Damit las man sie stillschweigend so, als deckte sie auch \<open>by consuming\<close>.
  Tut sie nicht: die Stabilitaet der Zeugenordnung unter den erzeugten Mutationen ist
  `consuming.ordnung` (S1), eine andere Schablone.

  **Der Befund ist eine GRENZE, kein Loch:** die zwei Schablonen greifen ineinander,
  und der Uebergang zwischen ihnen war unbenannt.
\<close>

section \<open>Wohlfundiertheit -- als HYPOTHESE, nicht als Ergebnis\<close>

text \<open>
  Die Deklaration muss die tragende Invariante NENNEN (SPRACHE.md Teil V, Stufe A):
  \<open>invariant acyclic cost O(n) runs offline : \<dots>\<close>.
  Im Schema erscheint sie als Voraussetzung \<open>wf (abkomm \<sigma>)\<close>.
\<close>

lemma table_induktion:
  assumes wf: "wf (abkomm \<sigma>)"
  assumes schritt: "\<And>s. (\<And>d. (d, s) \<in> abkomm \<sigma> \<Longrightarrow> P d) \<Longrightarrow> P s"
  shows "P s"
  using wf schritt by (rule wf_induct_rule)

section \<open>N-3 -- die Leere-Menge-Klausel gehoert NICHT hierher\<close>

text \<open>
  **Ausgespuelt, und zwar als Berichtigung in die andere Richtung.** Der Basisfall ist
  im Schema **absorbiert**: fuer ein Blatt ist die Praemisse
  \<open>\<And>d. (d,s) \<in> abkomm \<sigma> \<Longrightarrow> P d\<close> leer erfuellt. Es braucht also KEINE eigene
  Leere-Menge-Klausel im Induktionsprinzip.

  Was \<open>consuming.leermenge\<close> (S2) behauptet, ist etwas anderes: dass die **erzeugte
  Zeugenmenge vollstaendig** ist -- ist sie leer, ist die Domaene leer. Das ist eine
  Aussage ueber die ERZEUGUNG der Domaene, nicht ueber das Induktionsprinzip.

  **Die Vorhersage erwartete hier eine fehlende Klausel; gefunden wurde eine
  falsch zugeordnete.** Das ist der unbequemere Ausgang: eine fehlende Klausel fuegt
  man hinzu, eine falsch zugeordnete hat bis dahin an der falschen Stelle beruhigt.
\<close>

section \<open>N-4 -- \<open>vollstaendig\<close> war zweideutig, und die zweite Lesart ist die harte\<close>

text \<open>
  **Ausgespuelt.** \<open>vollstaendig\<close> kann zweierlei heissen:

  (a) das Prinzip ist **ableitbar** -- oben bewiesen (aus \<open>wf\<close>), eine Zeile;
  (b) das Schema deckt **alle Faelle** der Domaene.

  Fuer \<open>descendants of\<close> mit EINER Kante ist (b) trivial. Fuer
  \<open>chain(first_child, next_sibling) in slots\<close> ist es das **nicht**: die Domaene hat
  zwei Kantenarten, und das erzeugte Schema braucht **zwei Praemissen**, nicht eine.

  Der Eintrag sagt \<open>das Schema\<close>, Singular -- und deckt damit den Fall, den der
  Bestand am haeufigsten hat, sprachlich nicht ab.
\<close>

definition kette_zwei :: "'a tabelle \<Rightarrow> (idx \<times> idx) set" where
  "kette_zwei \<sigma> =
     {(d,s). \<exists>sl. \<sigma> s = Some sl \<and> first_child sl = Some d}
   \<union> {(d,s). \<exists>sl. \<sigma> s = Some sl \<and> next_sibling sl = Some d}"

lemma kette_induktion:
  assumes wf: "wf (kette_zwei \<sigma>)"
  assumes kind:      "\<And>s sl d. \<sigma> s = Some sl \<Longrightarrow> first_child sl = Some d \<Longrightarrow> P d \<Longrightarrow> Q s"
  assumes geschwist: "\<And>s sl d. \<sigma> s = Some sl \<Longrightarrow> next_sibling sl = Some d \<Longrightarrow> P d \<Longrightarrow> Q s"
  shows "True"  \<comment> \<open>Platzhalter: die zwei Praemissen sind der Punkt, nicht der Schluss.\<close>
  by simp

end
