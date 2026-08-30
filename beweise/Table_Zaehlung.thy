(*  Titel:      Table_Zaehlung.thy
    Gegenstand: «B13» -- die Aggregation `count(s in slots of A : P s)`, und der Beweis, der
                VOR der Grammatikzeile stehen muss (K100, zweites Tor)
    Stand:      2026-08-28

    WARUM DIESE THEORIE VOR DER FORM KOMMT

    `messung/AGGREGATION.md` misst «B13» aus und sagt die Form ab -- nicht mangels Bedarf
    (zwei saubere Korpusstellen, F1, und Caprocks K2, das `cap_space.rs` von Hand in Verus
    fuehrt), sondern weil der SCHWANZ laenger ist als die Form:

        1. eine Kostenregel -- sonst luegt `cost O(n)` bei geschachteltem `count`;
        2. eine Erzeugerschablone mit ihrer Erhaltungsfrage;
        3. das Isabelle-Gegenstueck.

    Und §5 desselben Dokuments legt die Reihenfolge fest: **der Beweis zuerst.** Das ist
    K100s zweites Tor, woertlich -- eine Schablone darf nicht von *entworfen* auf *getragen*
    wandern, ohne dass der Beweis vorher steht. Praezedenzfall `verbund.konstruktor`:
    *"so kam der Beweis zuerst"*.

    DIE FRAGE, DIE HIER BEANTWORTET WIRD

    Ein `count` in einer `runs offline`-Invariante wird vom Erzeuger als SCHLEIFE
    ausgeschrieben. Die Schablone schuldet damit zweierlei, und beides steht unten:

      I    dass die erzeugte Schleife wirklich die Zaehlung liefert -- und nicht etwas, das
           ihr in den Beispielen gleicht;
      II   die ERHALTUNGSFRAGE: was eine Mutation an der Zaehlung tut. Ohne sie muesste
           jede Operation die ganze Doppelschleife neu fahren, und die Invariante waere
           `runs offline` fuer immer.

    UND DIE GRENZE STEHT ALS GEGENBEISPIEL, NICHT ALS BEHAUPTUNG (Teil IV). Die
    Punktaenderung traegt die Zaehlung NUR unter `s0 < n`; ausserhalb der Schranke aendert
    der Speicher nichts an der Zaehlung, waehrend der erzeugte Zaehler mitliefe. *Das ist
    genau die Voraussetzung, die eine Schablone einem Rufer in Rechnung stellt* -- dieselbe
    Bauart wie `einfuegen_erhaelt` in `Table_Ops_Erhaltung.thy`.

    WAS DIESE THEORIE NICHT TUT

    Sie baut keine Grammatik und keinen Erzeuger. Sie sagt, WAS eine erzeugte Zaehlschleife
    liefert und unter welcher Voraussetzung eine Mutation sie erhaelt -- damit die Form,
    wenn sie kommt, nicht als Behauptung kommt. **Die Absage aus `AGGREGATION.md` §4 steht
    weiter**; was hier faellt, ist Punkt 3 ihrer Liste und die halbe Nummer 2.

    Und sie sagt NICHTS ueber die Kostenzeile ausser dem, was Teil III abzaehlt: die
    Schrittzahl. Dass `cost O(n)` an einer Invariante mit `count` falsch ist, ist damit
    nachrechenbar und nicht mehr nur behauptet -- die REGEL daraus zu machen ist Passarbeit.
*)

theory Table_Zaehlung
  imports Main
begin

section \<open>Teil I -- die erzeugte Schleife IST die Zaehlung\<close>

text \<open>
  Der Erzeuger schreibt kein \<open>card\<close>, er schreibt eine Schleife mit einem Akkumulator. Also
  steht hier die Schleife und nicht die Kardinalitaet -- und der erste Satz haelt die beiden
  gegeneinander. *Ein Beweis ueber \<open>card\<close> allein waere ein Beweis ueber etwas, das der
  Erzeuger nicht schreibt.*
\<close>

primrec zaehle :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
  "zaehle P 0 = 0"
| "zaehle P (Suc k) = zaehle P k + (if P k then 1 else 0)"

text \<open>
  \<open>Z-0\<close> -- die KONGRUENZ, und sie steht zuerst, weil jeder Satz darunter sie braucht: zwei
  Praedikate, die unterhalb der Schranke uebereinstimmen, werden gleich gezaehlt. Das ist
  die Rahmenaussage der Zaehlung -- was oberhalb von \<open>n\<close> steht, geht sie nichts an.
\<close>

lemma zaehle_kongruent:
  assumes "\<And>s. s < n \<Longrightarrow> P s = Q s"
  shows "zaehle P n = zaehle Q n"
  using assms by (induct n) auto

text \<open>
  \<open>Z-1\<close> -- die Schleife liefert die Kardinalitaet der Treffermenge unterhalb der Schranke.
  **Das ist die Aussage, die \<open>count(s in slots of A : P s)\<close> ueberhaupt erst zu einer
  Zaehlung macht**; ohne sie stuende im Register eine Zahl, die der Erzeuger ausrechnet,
  und daneben ein Wort, das etwas anderes bedeutet.
\<close>

lemma zaehle_ist_kardinalitaet:
  "zaehle P n = card {s. s < n \<and> P s}"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc k)
  have "{s. s < Suc k \<and> P s} = (if P k then insert k {s. s < k \<and> P s} else {s. s < k \<and> P s})"
    by (auto simp: less_Suc_eq)
  moreover have "finite {s. s < k \<and> P s}" by simp
  moreover have "k \<notin> {s. s < k \<and> P s}" by simp
  ultimately show ?case using Suc by simp
qed

text \<open>
  \<open>Z-2\<close> -- die Zaehlung ist durch die Schranke beschraenkt. Die Zeile, die eine
  Bereichszusage am Zaehlfeld traegt: ein \<open>u32\<close>-Zaehler ueber einer Tabelle mit \<open>count N\<close>
  laeuft nicht ueber, wenn \<open>N\<close> hineinpasst. *M104 braucht das, und ohne diesen Satz waere
  es eine Annahme.*
\<close>

lemma zaehle_beschraenkt: "zaehle P n \<le> n"
  by (induct n) auto

section \<open>Teil II -- die Erhaltungsfrage, und sie ist der Grund fuer die Schablone\<close>

text \<open>
  Eine \<open>runs offline\<close>-Invariante, die nach jeder Mutation neu gefahren werden muss, ist
  keine Buchfuehrung, sondern ein Pruefgang. **Die Schablone schuldet darum den Satz, der
  sagt, was EINE Aenderung an der Zaehlung tut** -- und zwar so, dass der Erzeuger daraus
  ein Dekrement und ein Inkrement schreiben darf statt zweier Schleifen.

  Modelliert wird die Bauform von «B13» woertlich: \<open>f\<close> ist \<open>Kappenraum.slots[s].objekt\<close>,
  also die Abbildung eines Platzes auf das Objekt, das er nennt. Eine Mutation setzt EINEN
  Platz um.
\<close>

text \<open>
  \<open>Z-3\<close> -- der Platz, dessen Nennung WEGGENOMMEN wird: die Zaehlung des alten Objekts
  faellt um genau eins. Geschrieben als \<open>Suc\<close> und nicht mit \<open>-\<close>, damit die Aussage nicht an
  der natuerlichen Subtraktion haengt.
\<close>

lemma zaehlung_faellt_um_eins:
  assumes "f s0 = a" and "b \<noteq> a"
  shows "s0 < n \<Longrightarrow> zaehle (\<lambda>s. f s = a) n = Suc (zaehle (\<lambda>s. (f(s0 := b)) s = a) n)"
  \<comment> \<open>Die Schranke steht IM Ziel und nicht unter \<open>assumes\<close>, damit die
      Induktionsvoraussetzung sie mitfuehrt und mit \<open>rule\<close> angewendet werden kann -- ohne
      eine der eingefrorenen Suchtaktiken, die \<open>instrumente/zaehle-theorien.py\<close> zaehlt.
      Am 2026-08-17 kosteten zwei davon zusammen 21 Minuten und 11 GB.\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases "s0 = k")
    case True
    have "zaehle (\<lambda>s. f s = a) k = zaehle (\<lambda>s. (f(s0 := b)) s = a) k"
      by (rule zaehle_kongruent) (simp add: True)
    with True assms show ?thesis by simp
  next
    case False
    with Suc.prems have "s0 < k" by simp
    then have "zaehle (\<lambda>s. f s = a) k = Suc (zaehle (\<lambda>s. (f(s0 := b)) s = a) k)"
      by (rule Suc.hyps)
    with False show ?thesis by simp
  qed
qed

text \<open>
  \<open>Z-4\<close> -- und die Gegenseite: die Zaehlung des NEUEN Objekts steigt um genau eins.
\<close>

lemma zaehlung_steigt_um_eins:
  assumes "f s0 = a" and "b \<noteq> a"
  shows "s0 < n \<Longrightarrow> zaehle (\<lambda>s. (f(s0 := b)) s = b) n = Suc (zaehle (\<lambda>s. f s = b) n)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases "s0 = k")
    case True
    have "zaehle (\<lambda>s. (f(s0 := b)) s = b) k = zaehle (\<lambda>s. f s = b) k"
      by (rule zaehle_kongruent) (simp add: True)
    with True assms show ?thesis by simp
  next
    case False
    with Suc.prems have "s0 < k" by simp
    then have "zaehle (\<lambda>s. (f(s0 := b)) s = b) k = Suc (zaehle (\<lambda>s. f s = b) k)"
      by (rule Suc.hyps)
    with False show ?thesis by simp
  qed
qed

text \<open>
  \<open>Z-5\<close> -- **der Rahmen, und er ist der teuerste der drei.** Jede andere Zaehlung bleibt
  unberuehrt. Ohne diesen Satz muesste eine Mutation JEDE Zaehlung neu rechnen, und die
  Schablone haette nichts gespart -- *die Erhaltungsfrage ist erst mit ihm beantwortet.*
\<close>

lemma zaehlung_bleibt_sonst:
  assumes "f s0 = a" and "c \<noteq> a" and "c \<noteq> b"
  shows "zaehle (\<lambda>s. (f(s0 := b)) s = c) n = zaehle (\<lambda>s. f s = c) n"
  by (rule zaehle_kongruent) (use assms in auto)

subsection \<open>Die Schablone, zusammengesetzt\<close>

text \<open>
  \<open>Z-6\<close> -- **die Erhaltungsaussage, die eine Erzeugerschablone tragen wuerde.** Gilt die
  Buchfuehrung vorher fuer jedes Objekt, und schreibt die Mutation das Dekrement und das
  Inkrement, so gilt sie nachher wieder. *Das ist der Satz, den «B13» braucht, damit die
  Invariante nicht bei jeder Aenderung offline geht.*

  \<open>z\<close> ist \<open>Objekte.slots[o].zaehler\<close>, \<open>f\<close> ist \<open>Kappenraum.slots[s].objekt\<close>.
\<close>

lemma buchfuehrung_erhaelt:
  assumes vorher: "\<And>ob. z ob = zaehle (\<lambda>s. f s = ob) n"
      and schranke: "s0 < n"
      and alt: "f s0 = a"
      and neu: "b \<noteq> a"
  shows "\<And>ob. (z(a := z a - 1, b := z b + 1)) ob = zaehle (\<lambda>s. (f(s0 := b)) s = ob) n"
proof -
  fix ob
  show "(z(a := z a - 1, b := z b + 1)) ob = zaehle (\<lambda>s. (f(s0 := b)) s = ob) n"
  proof (cases "ob = a")
    case True
    have "zaehle (\<lambda>s. f s = a) n = Suc (zaehle (\<lambda>s. (f(s0 := b)) s = a) n)"
      using alt neu schranke by (rule zaehlung_faellt_um_eins)
    with vorher True neu show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "ob = b")
      case True
      have "zaehle (\<lambda>s. (f(s0 := b)) s = b) n = Suc (zaehle (\<lambda>s. f s = b) n)"
        using alt neu schranke by (rule zaehlung_steigt_um_eins)
      with vorher True False show ?thesis by simp
    next
      case False
      \<comment> \<open>The frame step is applied as a RULE and not left to the simplifier: left to
          itself it rewrites the update and then owes exactly the fact that \<open>f s0 = a\<close>
          differs from \<open>ob\<close> -- which is the statement, not a step towards it.\<close>
      have "zaehle (\<lambda>s. (f(s0 := b)) s = ob) n = zaehle (\<lambda>s. f s = ob) n"
        using alt \<open>ob \<noteq> a\<close> False by (rule zaehlung_bleibt_sonst)
      then show ?thesis using vorher \<open>ob \<noteq> a\<close> False by simp
    qed
  qed
qed

section \<open>Teil III -- die KOSTEN, abgezaehlt statt geschaetzt\<close>

text \<open>
  \<open>AGGREGATION.md\<close> §3 nennt als schwersten Einwand gegen die Form: *"Die Kostenzeile wird
  falsch, und niemand merkt es."* \<open>cost O(n)\<close> an einer Invariante mit einem geschachtelten
  \<open>count\<close> ueber einen zweiten Traeger ist \<open>O(n\<cdot>m)\<close>.

  **Hier steht die Zahl statt der Behauptung.** \<open>schritte\<close> zaehlt, was die erzeugte
  Doppelschleife wirklich tut -- ein Schritt je betrachtetem Platz -- und die beiden Saetze
  darunter machen daraus eine nachrechenbare Aussage. *Damit ist die Kostenregel keine
  Meinung mehr, sondern eine Ableitung; sie zu einem PASS zu machen bleibt Arbeit.*
\<close>

primrec schritte :: "nat \<Rightarrow> nat" where
  "schritte 0 = 0"
| "schritte (Suc k) = schritte k + 1"

lemma schritte_der_inneren: "schritte n = n"
  by (induct n) auto

text \<open>
  \<open>Z-7\<close> -- die aeussere Schleife ueber \<open>m\<close> Objekte, die innere ueber \<open>n\<close> Plaetze.
\<close>

primrec doppelt :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "doppelt 0 n = 0"
| "doppelt (Suc k) n = doppelt k n + schritte n"

lemma doppelte_schleife_kostet_produkt: "doppelt m n = m * n"
  by (induct m) (auto simp: schritte_der_inneren)

text \<open>
  \<open>Z-8\<close> -- **und darum ist \<open>cost O(n)\<close> an so einer Invariante falsch**, sobald mehr als ein
  Objekt existiert und mehr als ein Platz. Als Gegenbeispiel und nicht als Behauptung: die
  Doppelschleife tut echt mehr Schritte als die einfache.
\<close>

lemma doppelt_ist_mehr_als_einfach:
  assumes "1 < m" and "0 < n"
  shows "schritte n < doppelt m n"
  using assms by (simp add: schritte_der_inneren doppelte_schleife_kostet_produkt)

section \<open>Teil IV -- die Grenzen, als GEGENBEISPIEL\<close>

text \<open>
  Zwei Stellen, an denen die Erhaltung NICHT gilt. Sie stehen als Gegenbeispiel da, weil ein
  Verbot, das niemand fallen sieht, eine Zierde ist -- dieselbe Bauart wie \<open>umhaengen_faellt\<close>
  in \<open>Table_Ops_Erhaltung.thy\<close>.
\<close>

text \<open>
  \<open>G-1\<close> -- **ohne \<open>s0 < n\<close> faellt die Erhaltung**, und sie faellt genau daran. Ein Platz
  ausserhalb der Schranke aendert die Zaehlung NICHT, waehrend der erzeugte Zaehler
  dekrementierte und inkrementierte. *Das ist die Voraussetzung, die die Schablone dem Rufer
  in Rechnung stellt* -- und \<open>Table_Indexschranke.thy\<close> ist der Ort, an dem sie faellt.
\<close>

lemma erhaltung_faellt_ohne_schranke:
  "zaehle (\<lambda>s. ((\<lambda>_. (0::nat))(1 := 1)) s = 0) 1 = zaehle (\<lambda>s. (\<lambda>_. (0::nat)) s = 0) 1"
  by simp

text \<open>
  Woertlich: die Tabelle hat EINEN Platz (\<open>n = 1\<close>), umgeschrieben wird Platz \<open>1\<close> -- ausserhalb.
  Die Zaehlung des Objekts \<open>0\<close> bleibt bei \<open>1\<close>, obwohl die Mutation ein Dekrement geschrieben
  haette. **Die Buchfuehrung waere danach um eins daneben, und kein Lauf der Schleife saehe es**,
  weil die Invariante \<open>runs offline\<close> ist.
\<close>

text \<open>
  \<open>G-2\<close> -- und die zweite Grenze: **die Zaehlung sagt nichts ueber die BELEGUNG.** Sie zaehlt
  jeden Platz, der das Objekt nennt, ob er benutzt ist oder nicht. Wer die Buchfuehrung ueber
  belegte Plaetze fuehren will, zaehlt ein anderes Praedikat -- und die beiden fallen
  auseinander, sobald ein freigegebener Platz seine Nennung behaelt.
\<close>

lemma belegung_ist_nicht_mitgezaehlt:
  "zaehle (\<lambda>s. (\<lambda>_. (0::nat)) s = 0) (Suc (Suc 0)) = 2
   \<and> zaehle (\<lambda>s. (\<lambda>_. (0::nat)) s = 0 \<and> (\<lambda>_. False) s) (Suc (Suc 0)) = 0"
  by simp

text \<open>
  *Das ist keine Schwaeche der Zaehlung, sondern eine Frage an die Deklaration:* zaehlt
  \<open>count(s in slots of A : …)\<close> ueber alle Plaetze oder nur ueber die belegten? `occupied`
  steht in der Tabellendeklaration, und die Form muesste sagen, ob sie es liest.
  **Solange sie das nicht sagt, ist sie zweideutig** -- und eine zweideutige Form ist genau
  das, was «B12» am 2026-08-20 entschieden bekommen hat, statt sie zu bauen.
\<close>

end
