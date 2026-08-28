(*  Titel:      Absenkung_Parametrisch.thy
    Gegenstand: DER ABSENKUNGSSATZ, parametrisch ueber der Zielsemantik
    Stand:      2026-08-28

    `PLAN-AUTONOM.md` §7 nennt die Luecke woertlich:

        "Dass `t->slots[s].elter = p;` die Funktion `umhaengen` IST, steht in keinem Satz."

    HIER STEHT ER -- und zwar so, dass er unter JEDEM der Wege durch §7 derselbe Satz ist.

    **Die Bewegung, um die es geht.** `Table_Absenkung.thy`:36 schiebt eine Voraussetzung aus
    dem Beweis heraus, indem sie sie zur Sprachdefinition erklaert: *"das ist die
    Sprachdefinition von C und keine Annahme dieses Beweises."* Das ist billig, solange die
    Zielsprache feststeht -- und es ist genau die Entscheidung, die §7 offenhaelt. Diese
    Theorie macht die Gegenbewegung: **jede solche Voraussetzung wird zu einer BENANNTEN
    Eigenschaft der Zielsemantik**, und der Satz gilt unter ihnen, gleich welche Zielsemantik
    sie einloest.

    **Der Riegel, unter dem diese Datei geschrieben ist.** Hier steht KEINE Semantik von C
    und KEINE Semantik einer Maschine. Es steht nicht da, in welcher Reihenfolge C
    auswertet, was C ein Objekt nennt, wann ein Zugriff undefiniert ist, was `volatile`
    heisst oder wie ein Ganzzahlueberlauf ausgeht. Wo eine solche Tatsache gebraucht wird,
    steht sie als `assumes`-Zeile mit einem Namen. *Eine Zielsemantik hinzuschreiben ist die
    Handlung, die die Entscheidung trifft; diese Datei trifft sie nicht.*

    DER GEGENSTAND ist die kleinste erzeugte Form, die den Kern trifft -- `ops relabel`.
    `emit.rs::ops` liefert dafuer heute EINEN Anweisungssatz (gemessen 2026-08-28 an
    `beispiele/47-ops-wortmenge.gab`):

        static void Ordner_relabel(Ordner *t, uint32_t s, uint32_t p) {
            t->slots[s].elter = p;
        }

    und `Table_Ops_Erhaltung.thy` haelt daneben `umhaengen \<sigma> s p = \<sigma>(s := Some \<lparr>elter = Some p\<rparr>)`.

    DER BEFUND, und er ist das Ergebnis dieser Theorie:

      **Der Satz "das Erzeugte berechnet die Modellfunktion" ist FALSCH, und zwar an einer
      benennbaren Stelle.** Er gilt am BELEGTEN Platz (`absenkung_am_belegten_platz`) und
      faellt am freien (`absenkung_geht_am_freien_platz_auseinander`) -- das Modell macht
      den Platz belegt, das erzeugte C laesst ihn frei. Was UNBEDINGT gilt, ist eine
      Fallunterscheidung mit zwei Zweigen (`absenkung_relabel`), und was der Erzeuger in
      seinem Kommentar behauptet, ist der schwaechere Satz ueber die INVARIANTE
      (`relabel_erhaelt_wohlgeformt`) -- der haelt, und er haelt aus einem anderen Grund als
      dem, den man erwartet.

      *Bis heute stand dieser Unterschied als Prosa in einem Erzeugerkommentar. Er ist jetzt
      ein Satz und ein Gegenbeispiel.*
*)

theory Absenkung_Parametrisch
  imports Table_Ops_Erhaltung
begin

section \<open>Das Abbild -- wie ein Zielzustand als Tabelle GELESEN wird\<close>

text \<open>
  **Eine Absenkung ist ohne Auslesung keine Aussage.** Das Modell redet ueber
  \<open>tabelle = idx \<Rightarrow> slot option\<close>, das Erzeugnis ueber einen Zustand irgendeiner Maschine.
  Zu sagen, das eine BERECHNE das andere, verlangt eine Abbildung vom Zielzustand auf das
  Modell -- und die ist selbst eine Behauptung, keine Definition der Zielsprache.

  \<open>abbild\<close> steht darum hier oben und nicht im Lokal darunter: **die Gegenbeispiele am Ende
  brauchen dieselbe Auslesung**, sonst zeigten sie an einem anderen Gegenstand vorbei.

  Die drei Stuecke, aus denen sie besteht, sind je eine eigene Behauptung:

    \<^item> \<open>i < N\<close> -- ausserhalb der Kapazitaet gibt es keinen Platz. *Das ist der Gegenstand von
      \<open>Table_Absenkung.thy\<close>, und dort steht die Bewegung, gegen die diese Theorie geschrieben
      ist.*
    \<^item> \<open>deutebelegt (lies z (belegtort i))\<close> -- ob ein Platz BELEGT ist, steht an einem eigenen
      Ort. `emit.rs` verlangt dafuer `occupied <feld>` (\<open>D011\<close>).
    \<^item> \<open>deute (lies z (ort i))\<close> -- der Elternzeiger, gedeutet. *Das ist \<open>option.sonderwert\<close>,
      und die Schablone steht GETRAGEN und UNBEWIESEN im Register.*
\<close>

definition abbild ::
  "('z \<Rightarrow> 'l \<Rightarrow> 'w) \<Rightarrow> (idx \<Rightarrow> 'l) \<Rightarrow> (idx \<Rightarrow> 'l) \<Rightarrow> ('w \<Rightarrow> idx option) \<Rightarrow> ('w \<Rightarrow> bool)
   \<Rightarrow> nat \<Rightarrow> 'z \<Rightarrow> tabelle" where
  "abbild lies ort belegtort deute deutebelegt N z =
     (\<lambda>i. if i < N \<and> deutebelegt (lies z (belegtort i))
          then Some \<lparr> elter = deute (lies z (ort i)) \<rparr>
          else None)"

section \<open>Die BENANNTEN Eigenschaften der Zielsemantik\<close>

text \<open>
  **Das hier ist der Ertrag der Theorie, noch vor jedem Satz.** §7 klagt an: es gibt
  *"eine Aufzaehlung dessen, worauf sie ruht"* statt eines Zeugnisses. Diese Aufzaehlung
  hat bis heute niemand geschrieben. Sie hat sechs Zeilen, und keine davon sagt, WELCHE
  Zielsprache gemeint ist.

  \<^descr>[\<open>E1\<close> RAHMEN] Ein Schreiben aendert genau einen Ort. *Hier wohnt das Aliasing -- unter
    einer C-Semantik faellt diese Zeile aus dem Objektmodell und der Regel ueber effektive
    Typen; unter einer Maschinensemantik faellt sie aus der Adressarithmetik. Die Zeile
    selbst weiss davon nichts.*

  \<^descr>[\<open>E2\<close> TREFFER] Was geschrieben wurde, liest sich zurueck. *Unter einer C-Semantik ist
    das die Zuweisung; unter einer Maschinensemantik der Speicherbefehl. Beide muessen es
    liefern, keiner von beiden bekommt es geschenkt: eine Breitenverkuerzung bricht es.*

  \<^descr>[\<open>E3\<close> ZUWEISUNG] Die eine Anweisung des Erzeugnisses IST das Schreiben an den Ort des
    Elternfeldes. **Das ist die Zeile, in der die Absenkung wohnt** -- und sie steht als
    Annahme da, weil sie einzuloesen genau der Schritt ist, den die Entscheidung waehlt.

  \<^descr>[\<open>E4\<close> GETRENNT] Verschiedene Plaetze haben verschiedene Elternorte.

  \<^descr>[\<open>E5\<close> GESCHIEDEN] Ein Elternort ist nie ein Belegungsort. *\<open>E4\<close> und \<open>E5\<close> zusammen sind
    die Trennungsforderung. Unter einer Maschinensemantik sind sie Arithmetik ueber der
    Feldgroesse; unter einer C-Semantik sind sie eine SPRACHREGEL. **Das ist die schaerfste
    Stelle, an der die Wege verschieden rechnen**, und sie steht im M-2-Abschnitt
    ausgeschrieben.*

  \<^descr>[\<open>E6\<close> DEUTUNGSTREU] Das Maschinenwort eines gueltigen Index liest sich als dieser Index
    zurueck. *Das ist \<open>option.sonderwert\<close> -- die Schablone, die das Register als GETRAGEN
    und UNBEWIESEN fuehrt. `sonderwert_bricht_die_absenkung` zeigt unten, dass sie hier
    wirklich gebraucht wird, und der Bruch ist der unangenehme von beiden.*

  **Zwei Lokale statt eines, und der Grund ist R11.** \<open>zielraum\<close> traegt nur \<open>E1\<close>--\<open>E3\<close>;
  \<open>zielsemantik\<close> legt \<open>E4\<close>--\<open>E6\<close> darauf. *Eine Voraussetzung, die man nie hat fehlen sehen,
  ist eine Zierde* -- und die beiden Gegenbeispiele am Ende wohnen im schwachen Lokal.
\<close>

locale zielraum =
  fixes lies        :: "'z \<Rightarrow> 'l \<Rightarrow> 'w"
    and schreib     :: "'z \<Rightarrow> 'l \<Rightarrow> 'w \<Rightarrow> 'z"
    and ort         :: "idx \<Rightarrow> 'l"
    and belegtort   :: "idx \<Rightarrow> 'l"
    and deute       :: "'w \<Rightarrow> idx option"
    and deutebelegt :: "'w \<Rightarrow> bool"
    and wort        :: "idx \<Rightarrow> 'w"
    and N           :: nat
    and wirkung     :: "idx \<Rightarrow> idx \<Rightarrow> 'z \<Rightarrow> 'z"
  assumes E1_rahmen:    "b \<noteq> a \<Longrightarrow> lies (schreib z a v) b = lies z b"
      and E2_treffer:   "lies (schreib z a v) a = v"
      and E3_zuweisung: "s < N \<Longrightarrow> p < N \<Longrightarrow> wirkung s p z = schreib z (ort s) (wort p)"
begin

abbreviation A :: "'z \<Rightarrow> tabelle" where
  "A z \<equiv> abbild lies ort belegtort deute deutebelegt N z"

end

locale zielsemantik = zielraum +
  assumes E4_getrennt:     "i < N \<Longrightarrow> j < N \<Longrightarrow> i \<noteq> j \<Longrightarrow> ort i \<noteq> ort j"
      and E5_geschieden:   "i < N \<Longrightarrow> j < N \<Longrightarrow> ort i \<noteq> belegtort j"
      and E6_deutungstreu: "i < N \<Longrightarrow> deute (wort i) = Some i"

section \<open>Was sich NICHT bewegt -- jeder andere Platz\<close>

text \<open>
  \<open>A-1\<close> -- der Kern beider Richtungen. **Ein Platz, der nicht \<open>s\<close> ist, liest sich nach dem
  Schreiben unveraendert**, in beiden Feldern. Er braucht \<open>E1\<close>, \<open>E4\<close> und \<open>E5\<close> und sonst
  nichts -- insbesondere weder \<open>E2\<close> noch \<open>E6\<close>, denn hier wird nichts gedeutet, was neu ist.
\<close>

lemma (in zielsemantik) anderer_platz_unberuehrt:
  assumes s_gueltig: "s < N"
      and p_gueltig: "p < N"
      and anders:    "i \<noteq> s"
  shows "A (wirkung s p z) i = A z i"
proof (cases "i < N")
  case False
  then show ?thesis unfolding abbild_def by simp
next
  case True
  have schritt: "wirkung s p z = schreib z (ort s) (wort p)"
    using s_gueltig p_gueltig by (rule E3_zuweisung)
  have b_anders: "belegtort i \<noteq> ort s"
    using E5_geschieden[OF s_gueltig True] by (rule not_sym)
  have belegung: "lies (wirkung s p z) (belegtort i) = lies z (belegtort i)"
    unfolding schritt using b_anders by (rule E1_rahmen)
  have o_anders: "ort i \<noteq> ort s"
    using E4_getrennt[OF True s_gueltig anders] .
  have elternfeld: "lies (wirkung s p z) (ort i) = lies z (ort i)"
    unfolding schritt using o_anders by (rule E1_rahmen)
  show ?thesis unfolding abbild_def using belegung elternfeld by simp
qed

text \<open>
  \<open>A-2\<close> -- und die BELEGUNG des umgehaengten Platzes bewegt sich auch nicht. *Das ist die
  Zeile, an der der Satz spaeter zerbricht:* das erzeugte C schreibt das Elternfeld und
  RUEHRT DIE BELEGUNG NICHT AN. Das Modell tut etwas anderes.
\<close>

lemma (in zielsemantik) belegung_von_s_unberuehrt:
  assumes s_gueltig: "s < N"
      and p_gueltig: "p < N"
  shows "deutebelegt (lies (wirkung s p z) (belegtort s))
         = deutebelegt (lies z (belegtort s))"
proof -
  have schritt: "wirkung s p z = schreib z (ort s) (wort p)"
    using s_gueltig p_gueltig by (rule E3_zuweisung)
  have "belegtort s \<noteq> ort s"
    using E5_geschieden[OF s_gueltig s_gueltig] by (rule not_sym)
  then have "lies (wirkung s p z) (belegtort s) = lies z (belegtort s)"
    unfolding schritt by (rule E1_rahmen)
  then show ?thesis by simp
qed

section \<open>Der Satz -- und er gilt nur am BELEGTEN Platz\<close>

text \<open>
  \<open>S-1\<close> -- **die Absenkung, in der Gestalt, die §7 verlangt:** *unter diesen benannten
  Eigenschaften der Zielsemantik gilt: das Erzeugte berechnet die Modellfunktion.*

  Und die dritte Voraussetzung ist der Befund. Sie steht NICHT in
  \<open>umhaengen_erhaelt\<close> (U-3), sie steht NICHT im erzeugten Kopf, und `D012` haelt sie an
  keiner Rufstelle. **Sie ist der Preis dafuer, dass die Aussage eine GLEICHHEIT ist und
  keine Erhaltung.**
\<close>

theorem (in zielsemantik) absenkung_am_belegten_platz:
  assumes s_gueltig: "s < N"
      and p_gueltig: "p < N"
      and belegt:    "deutebelegt (lies z (belegtort s))"
  shows "A (wirkung s p z) = umhaengen (A z) s p"
proof (rule ext)
  fix i
  show "A (wirkung s p z) i = umhaengen (A z) s p i"
  proof (cases "i = s")
    case False
    have "A (wirkung s p z) i = A z i"
      using s_gueltig p_gueltig False by (rule anderer_platz_unberuehrt)
    also have "\<dots> = umhaengen (A z) s p i"
      unfolding umhaengen_def using False by simp
    finally show ?thesis .
  next
    case True
    have schritt: "wirkung s p z = schreib z (ort s) (wort p)"
      using s_gueltig p_gueltig by (rule E3_zuweisung)
    have noch_belegt: "deutebelegt (lies (wirkung s p z) (belegtort s))"
      using belegung_von_s_unberuehrt[OF s_gueltig p_gueltig] belegt by simp
    have gelesen: "lies (wirkung s p z) (ort s) = wort p"
      unfolding schritt by (rule E2_treffer)
    have gedeutet: "deute (lies (wirkung s p z) (ort s)) = Some p"
      unfolding gelesen using p_gueltig by (rule E6_deutungstreu)
    have "A (wirkung s p z) s = Some \<lparr> elter = Some p \<rparr>"
      unfolding abbild_def using s_gueltig noch_belegt gedeutet by simp
    moreover have "umhaengen (A z) s p s = Some \<lparr> elter = Some p \<rparr>"
      unfolding umhaengen_def by simp
    ultimately show ?thesis using True by simp
  qed
qed

section \<open>Und er faellt am FREIEN Platz -- das ist der Befund\<close>

text \<open>
  \<open>S-2\<close> -- am freien Platz aendert das Erzeugnis das Modell **gar nicht**. Es schreibt das
  Elternfeld, und die Auslesung sieht es nicht an, weil der Platz unbelegt bleibt.

  *Das ist keine Nachlaessigkeit des Erzeugers, sondern seine ausdrueckliche Absicht:*
  `emit.rs::ops` schreibt daneben, der C-Zustand habe dann WENIGER belegte Plaetze als der
  Modellzustand, und \<open>wohlgeformt\<close> sei ein \<open>\<forall>\<close> ueber den belegten. Das Argument stimmt --
  und es ist ein Argument ueber eine ERHALTUNG und nicht ueber eine Gleichheit.
\<close>

theorem (in zielsemantik) relabel_am_freien_platz_ist_wirkungslos:
  assumes s_gueltig: "s < N"
      and p_gueltig: "p < N"
      and frei:      "\<not> deutebelegt (lies z (belegtort s))"
  shows "A (wirkung s p z) = A z"
proof (rule ext)
  fix i
  show "A (wirkung s p z) i = A z i"
  proof (cases "i = s")
    case False
    show ?thesis by (rule anderer_platz_unberuehrt[OF s_gueltig p_gueltig False])
  next
    case True
    have "\<not> deutebelegt (lies (wirkung s p z) (belegtort s))"
      using belegung_von_s_unberuehrt[OF s_gueltig p_gueltig] frei by simp
    then have "A (wirkung s p z) s = None" unfolding abbild_def by simp
    moreover have "A z s = None" unfolding abbild_def using frei by simp
    ultimately show ?thesis using True by simp
  qed
qed

text \<open>
  \<open>S-3\<close> -- **und damit gehen die beiden auseinander.** Das Modell macht \<open>s\<close> belegt, das
  Erzeugnis laesst ihn frei; ein \<open>Some\<close> gegen ein \<open>None\<close>, an genau einer Stelle.

  *Der Satz "das Erzeugte berechnet die Modellfunktion" ist also nicht bloss unbewiesen --
  er ist falsch, und diese Zeile sagt woran.*
\<close>

theorem (in zielsemantik) absenkung_geht_am_freien_platz_auseinander:
  assumes s_gueltig: "s < N"
      and p_gueltig: "p < N"
      and frei:      "\<not> deutebelegt (lies z (belegtort s))"
  shows "A (wirkung s p z) \<noteq> umhaengen (A z) s p"
proof -
  have vorher: "A z s = None" unfolding abbild_def using frei by simp
  have links: "A (wirkung s p z) s = None"
    using relabel_am_freien_platz_ist_wirkungslos[OF s_gueltig p_gueltig frei] vorher
    by simp
  have rechts: "umhaengen (A z) s p s = Some \<lparr> elter = Some p \<rparr>"
    unfolding umhaengen_def by simp
  show ?thesis
  proof
    assume "A (wirkung s p z) = umhaengen (A z) s p"
    then have "A (wirkung s p z) s = umhaengen (A z) s p s" by simp
    with links rechts show False by simp
  qed
qed

section \<open>Was UNBEDINGT gilt: zwei Zweige, nicht einer\<close>

text \<open>
  \<open>S-4\<close> -- die ehrliche Fassung. **Sie hat zwei Zweige, und der Ordner fuehrt bisher
  einen.** Genau diese Zeile gehoerte in eine Absenkungsspalte, und genau sie fehlt heute:
  \<open>A8\<close> zaehlt achtzehn Behauptungen, und eine Behauptung mit einem verschwiegenen zweiten
  Zweig ist teurer als eine offene Luecke.
\<close>

theorem (in zielsemantik) absenkung_relabel:
  assumes s_gueltig: "s < N"
      and p_gueltig: "p < N"
  shows "A (wirkung s p z)
         = (if deutebelegt (lies z (belegtort s)) then umhaengen (A z) s p else A z)"
proof (cases "deutebelegt (lies z (belegtort s))")
  case True
  then show ?thesis
    using absenkung_am_belegten_platz[OF s_gueltig p_gueltig] by simp
next
  case False
  then show ?thesis
    using relabel_am_freien_platz_ist_wirkungslos[OF s_gueltig p_gueltig] by simp
qed

text \<open>
  \<open>S-5\<close> -- **und die INVARIANTE senkt trotzdem unbedingt ab.** Das ist der Satz, den
  `emit.rs` in Prosa fuehrt, und er haelt: am belegten Platz ueber \<open>umhaengen_erhaelt\<close>
  (U-3), am freien, weil das Abbild sich gar nicht bewegt.

  **Die beiden Zweige halten aus VERSCHIEDENEN Gruenden, und das ist der Grund, warum die
  Erhaltung die Gleichheit nicht ersetzt.** Ein Erzeuger, der am freien Platz etwas voellig
  anderes schriebe, bekaeme denselben Satz -- die Erhaltung sieht dort nichts.
\<close>

corollary (in zielsemantik) relabel_erhaelt_wohlgeformt:
  assumes s_gueltig:     "s < N"
      and p_gueltig:     "p < N"
      and wf:            "wohlgeformt (A z)"
      and elter_da:      "erreicht (A z) p"
      and nicht_drunter: "\<not> ueber (A z) p s"
  shows "wohlgeformt (A (wirkung s p z))"
proof (cases "deutebelegt (lies z (belegtort s))")
  case True
  have "A (wirkung s p z) = umhaengen (A z) s p"
    using s_gueltig p_gueltig True by (rule absenkung_am_belegten_platz)
  moreover have "wohlgeformt (umhaengen (A z) s p)"
    using wf elter_da nicht_drunter by (rule umhaengen_erhaelt)
  ultimately show ?thesis by simp
next
  case False
  have "A (wirkung s p z) = A z"
    using s_gueltig p_gueltig False by (rule relabel_am_freien_platz_ist_wirkungslos)
  then show ?thesis using wf by simp
qed

section \<open>Zwei Gegenbeispiele -- die Eigenschaften sind keine Zierde\<close>

text \<open>
  **Eine Voraussetzung, die man nie hat fehlen sehen, ist eine Zierde** (R11). Die beiden
  Gegenbeispiele wohnen im SCHWACHEN Lokal \<open>zielraum\<close>: sie erfuellen \<open>E1\<close>--\<open>E3\<close>, verletzen
  je eine der drei uebrigen, und der Satz faellt.

  Beide arbeiten ueber einem denkbar einfachen Zielraum: ein Zustand ist eine Abbildung von
  Zahlen auf Zahlen. *Das ist KEINE Maschinensemantik -- es ist der duennste Traeger, an dem
  sich ein Gegenbeispiel hinschreiben laesst, und er sagt ueber keine Maschine etwas aus.*
\<close>

definition wlies :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "wlies z a = z a"

definition wschreib :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat)" where
  "wschreib z a v = z(a := v)"

definition wbelegtort :: "idx \<Rightarrow> nat" where
  "wbelegtort i = 10 + i"

definition wdeutebelegt :: "nat \<Rightarrow> bool" where
  "wdeutebelegt w = (w \<noteq> 0)"

definition wwort :: "idx \<Rightarrow> nat" where
  "wwort i = i"

subsection \<open>Ohne \<open>E4\<close>: zwei Plaetze teilen ihr Elternfeld\<close>

text \<open>
  **Der Alias-Bruch.** \<open>gort\<close> gibt jedem Platz DENSELBEN Elternort. Alles andere bleibt
  gesund: es wird an genau einen Ort geschrieben (\<open>E1\<close>), es liest sich zurueck (\<open>E2\<close>), und
  die Anweisung ist das Schreiben (\<open>E3\<close>). *Und trotzdem haengt das Erzeugnis ZWEI Plaetze
  um, wo das Modell einen umhaengt.*

  Diese Zeile ist die, an der die beiden Wege durch §7 wirklich verschieden rechnen: unter
  einer Maschinensemantik ist \<open>E4\<close> Arithmetik ueber der Slotgroesse und faellt aus
  \<open>i \<noteq> j\<close>; unter einer C-Semantik ist sie eine Sprachregel ueber Objekte und effektive Typen.
\<close>

definition gort :: "idx \<Rightarrow> nat" where
  "gort i = 0"

definition gdeute :: "nat \<Rightarrow> idx option" where
  "gdeute w = (if w = 2 then None else Some w)"

definition gwirkung :: "idx \<Rightarrow> idx \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)" where
  "gwirkung s p z = z(gort s := wwort p)"

interpretation aliasbruch:
  zielraum wlies wschreib gort wbelegtort gdeute wdeutebelegt wwort 2 gwirkung
proof
  fix z :: "nat \<Rightarrow> nat" and a b :: nat and v :: nat
  assume "b \<noteq> a"
  then show "wlies (wschreib z a v) b = wlies z b"
    unfolding wlies_def wschreib_def by simp
next
  fix z :: "nat \<Rightarrow> nat" and a v :: nat
  show "wlies (wschreib z a v) a = v"
    unfolding wlies_def wschreib_def by simp
next
  fix s p :: idx and z :: "nat \<Rightarrow> nat"
  show "gwirkung s p z = wschreib z (gort s) (wwort p)"
    unfolding gwirkung_def wschreib_def by simp
qed

lemma aliasbruch_verletzt_E4: "gort 0 = gort 1"
  unfolding gort_def by simp

text \<open>
  Der Anfangszustand ist ueberall \<open>1\<close>: beide Plaetze sind belegt (\<open>1 \<noteq> 0\<close>) und beide nennen
  \<open>1\<close> als Elter. Umgehaengt wird Platz \<open>0\<close> unter Platz \<open>0\<close> -- **und Platz \<open>1\<close> wandert mit.**
\<close>

lemma aliasbruch_bricht_die_absenkung:
  "abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (gwirkung 0 0 (\<lambda>_. 1))
     \<noteq> umhaengen (abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (\<lambda>_. 1)) 0 0"
proof -
  have vorher: "abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (\<lambda>_. 1) 1
                  = Some \<lparr> elter = Some 1 \<rparr>"
    unfolding abbild_def wlies_def wbelegtort_def wdeutebelegt_def gdeute_def by simp
  have nachher: "abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (gwirkung 0 0 (\<lambda>_. 1)) 1
                   = Some \<lparr> elter = Some 0 \<rparr>"
    unfolding abbild_def gwirkung_def wlies_def wbelegtort_def wdeutebelegt_def
              gdeute_def gort_def wwort_def by simp
  show ?thesis
  proof
    assume gleich: "abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (gwirkung 0 0 (\<lambda>_. 1))
                      = umhaengen (abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (\<lambda>_. 1)) 0 0"
    have "umhaengen (abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (\<lambda>_. 1)) 0 0 1
            = Some \<lparr> elter = Some 1 \<rparr>"
      unfolding umhaengen_def using vorher by simp
    with gleich nachher show False by simp
  qed
qed

subsection \<open>Ohne \<open>E6\<close>: der Sonderwert liegt IM Bereich\<close>

text \<open>
  **Der \<open>option.sonderwert\<close>-Bruch, und er ist der unangenehmere von beiden.** \<open>dgort\<close>
  trennt die Plaetze sauber, \<open>E4\<close> und \<open>E5\<close> halten also. Was faellt, ist die Deutung: der
  Sonderwert fuer \<open>None\<close> ist hier \<open>1\<close> und liegt damit INNERHALB der Indexdomaene
  \<open>{0, 1}\<close>. \<open>Option_Sonderwert.thy\<close> beweist, dass \<open>N\<close> ausserhalb liegt -- **die Schablone
  steht trotzdem als GETRAGEN und UNBEWIESEN im Register**, und hier steht, was sie kauft.

  *Und die Folge ist genau die Sorte, die eine Erhaltungsaussage nicht sieht:* der Platz
  wird still zur WURZEL. Der Baum ist danach ein anderer, \<open>wohlgeformt\<close> haelt weiter, und
  kein Satz ueber die Invariante sagt ein Wort dazu. **Das ist das Argument dafuer, dass die
  Gleichheit die Erhaltung nicht ersetzt.**
\<close>

definition dgort :: "idx \<Rightarrow> nat" where
  "dgort i = i"

definition dgdeute :: "nat \<Rightarrow> idx option" where
  "dgdeute w = (if w = 1 then None else Some w)"

definition dgwirkung :: "idx \<Rightarrow> idx \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)" where
  "dgwirkung s p z = z(dgort s := wwort p)"

interpretation sonderwert:
  zielraum wlies wschreib dgort wbelegtort dgdeute wdeutebelegt wwort 2 dgwirkung
proof
  fix z :: "nat \<Rightarrow> nat" and a b :: nat and v :: nat
  assume "b \<noteq> a"
  then show "wlies (wschreib z a v) b = wlies z b"
    unfolding wlies_def wschreib_def by simp
next
  fix z :: "nat \<Rightarrow> nat" and a v :: nat
  show "wlies (wschreib z a v) a = v"
    unfolding wlies_def wschreib_def by simp
next
  fix s p :: idx and z :: "nat \<Rightarrow> nat"
  show "dgwirkung s p z = wschreib z (dgort s) (wwort p)"
    unfolding dgwirkung_def wschreib_def by simp
qed

text \<open>
  \<open>E4\<close> und \<open>E5\<close> HALTEN hier -- das gehoert gezeigt, sonst braechen zwei Dinge auf einmal und
  das Gegenbeispiel sagte nichts ueber \<open>E6\<close>.
\<close>

lemma sonderwert_haelt_E4: "i < 2 \<Longrightarrow> j < 2 \<Longrightarrow> i \<noteq> j \<Longrightarrow> dgort i \<noteq> dgort j"
  unfolding dgort_def by simp

lemma sonderwert_haelt_E5: "i < 2 \<Longrightarrow> j < 2 \<Longrightarrow> dgort i \<noteq> wbelegtort j"
  unfolding dgort_def wbelegtort_def by simp

lemma sonderwert_verletzt_E6: "dgdeute (wwort 1) \<noteq> Some 1"
  unfolding dgdeute_def wwort_def by simp

text \<open>
  Der Anfangszustand ist ueberall \<open>5\<close>: beide Plaetze belegt, beide mit Elter \<open>Some 5\<close>.
  Umgehaengt wird Platz \<open>0\<close> unter Platz \<open>1\<close> -- **und Platz \<open>0\<close> wird zur Wurzel.**
\<close>

lemma sonderwert_bricht_die_absenkung:
  "abbild wlies dgort wbelegtort dgdeute wdeutebelegt 2 (dgwirkung 0 1 (\<lambda>_. 5))
     \<noteq> umhaengen (abbild wlies dgort wbelegtort dgdeute wdeutebelegt 2 (\<lambda>_. 5)) 0 1"
proof -
  have nachher: "abbild wlies dgort wbelegtort dgdeute wdeutebelegt 2 (dgwirkung 0 1 (\<lambda>_. 5)) 0
                   = Some \<lparr> elter = None \<rparr>"
    unfolding abbild_def dgwirkung_def wlies_def wbelegtort_def wdeutebelegt_def
              dgdeute_def dgort_def wwort_def by simp
  show ?thesis
  proof
    assume gleich: "abbild wlies dgort wbelegtort dgdeute wdeutebelegt 2 (dgwirkung 0 1 (\<lambda>_. 5))
                      = umhaengen (abbild wlies dgort wbelegtort dgdeute wdeutebelegt 2 (\<lambda>_. 5)) 0 1"
    have "umhaengen (abbild wlies dgort wbelegtort dgdeute wdeutebelegt 2 (\<lambda>_. 5)) 0 1 0
            = Some \<lparr> elter = Some 1 \<rparr>"
      unfolding umhaengen_def by simp
    with gleich nachher show False by simp
  qed
qed

section \<open>M-2 -- WORAN die Parametrisierung nicht durchhaelt\<close>

text \<open>
  **Das ist der wertvollste Abschnitt dieser Datei, und er enthaelt keinen Satz.** §7 sagt:
  wer an eine Stelle kommt, an der die Parametrisierung nicht durchhaelt, hat die erste beim
  Namen genannte Stelle gefunden, an der die Wege wirklich auseinandergehen. Hier stehen
  drei, und die dritte ist die harte.

  \<^item> **\<open>E4\<close>/\<open>E5\<close> sind auf den beiden Wegen VERSCHIEDENE Arten von Aussage** -- und das ist
    die Stelle, die man an \<open>alias_bricht_die_absenkung\<close> sehen kann. Unter einer
    Maschinensemantik ist \<open>ort i = basis + versatz + i * groesse\<close>, und \<open>E4\<close> faellt aus
    \<open>groesse > 0\<close> und \<open>i, j < N\<close> -- **es ist ein Lemma und keine Annahme.** Unter einer
    C-Semantik ist \<open>ort i\<close> gar keine Zahl: es ist ein Ort im Objektmodell, und dass zwei
    verschiedene Feldbezeichner verschiedene Orte bezeichnen, ist eine SPRACHREGEL. *Der
    eine Weg beweist \<open>E4\<close>, der andere erbt sie. Beide bekommen den Satz -- aber der Posten
    steht auf verschiedenen Seiten der Rechnung.*

  \<^item> **\<open>lies\<close> und \<open>schreib\<close> sind TOTAL, und das ueberlebt keine C-Semantik.** Hier ist
    \<open>schreib z a v\<close> fuer jeden Ort erklaert. Unter einer Maschinensemantik ist das nahezu
    richtig: ein Zugriff ausserhalb des Feldes trifft eine andere Adresse, und man kann
    HINSCHREIBEN, welche. Unter einer C-Semantik ist derselbe Zugriff **undefiniertes
    Verhalten**, und das ist kein Wert und kein Zustand, sondern die Auskunft, dass das
    ganze Programm keine Bedeutung hat -- rueckwirkend. *Ein partieller \<open>schreib\<close> waere
    darstellbar; was NICHT darstellbar ist, ist die Rueckwirkung.* **Damit ist die
    Signatur von \<open>schreib\<close> selbst schon eine halbe Entscheidung**, und sie ist hier so
    gewaehlt, dass \<open>s < N\<close> und \<open>p < N\<close> in jedem Satz als Voraussetzung dastehen muessen.
    *Die Parametrisierung haelt fuer die KORREKTHEIT und bricht an der DEFINIERTHEIT.*

  \<^item> **`restrict` hat auf der Maschinenseite kein Gegenstueck.** Der Erzeuger schreibt an
    anderen Stellen `T *restrict` (\<open>restrict.alleinzugriff\<close>, S1). Auf der Maschinenseite ist
    *"diese beiden Zeiger ueberlappen nicht"* eine PRAEMISSE, aus der man rechnen darf; in C
    ist es ein VERSPRECHEN des Programmierers, das der Uebersetzer ausnutzen darf, und
    dessen Bruch wieder undefiniertes Verhalten ist. **Dieselbe Zeile Quelltext ist auf dem
    einen Weg eine Annahme und auf dem anderen eine Lizenz.** *Diese Theorie beruehrt sie
    nicht -- \<open>relabel\<close> nimmt einen einzigen Zeiger --, und sie steht hier, weil sie die
    naechste Stelle derselben Sorte ist.*

  **Und was hier ausdruecklich NICHT steht:** keine Auswertungsreihenfolge, kein
  Speichermodell, kein Aliasingregelwerk, kein \<open>volatile\<close>, kein Ganzzahlueberlauf. Der
  Ueberlauf kommt nicht vor, weil \<open>relabel\<close> nicht rechnet; die anderen vier waeren die
  Handlung, die die Entscheidung trifft.
\<close>

section \<open>Was hier NICHT steht\<close>

text \<open>
  \<^item> **Kein Beweis, dass \<open>E3\<close> gilt.** Dass die eine C-Anweisung `t->slots[s].elter = p;`
    das Schreiben an \<open>ort s\<close> IST, ist hier Annahme und nirgends bewiesen. *Das ist die
    Luecke aus §7, und diese Theorie schliesst sie nicht -- sie schneidet sie auf eine
    Zeile zu.* Wer sie einloest, hat den Weg gewaehlt.

  \<^item> **Nur \<open>relabel\<close>.** \<open>insert\<close> und \<open>remove\<close> stehen nicht hier. \<open>insert\<close> schreibt ZWEI
    Anweisungen, und dafuer braucht es eine siebte Eigenschaft -- die
    Hintereinanderausfuehrung --, die \<open>relabel\<close> nicht braucht. \<open>remove\<close> schreibt je Feld eine. *Beide
    sind dieselbe Uebung eine Stufe groesser; keine ist gemacht.*

  \<^item> **Keine Aussage ueber den PRUEFER.** Dass `D012` die beiden Praemissen von U-3 an jeder
    Rufstelle haelt, ist eine Aussage ueber Rust und faellt in dieselbe Klasse wie die
    haengenden Praemissen des Registers (Zahn 3).

  \<^item> **Keine Kostenaussage.** \<open>costs\<close> kommt nicht vor.
\<close>

end
