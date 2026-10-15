(*  Titel:      Restrict_Alleinzugriff.thy
    Gegenstand: Die Schablone `restrict.alleinzugriff` -- wann der Erzeuger `restrict`
                schreiben DARF
    Stand:      2026-08-19

    Gemessen am selben Tag, `cc -O2`:

        Zeiger, deren Herkunft der C-Uebersetzer sieht      23,0 ms : 23,1 ms   1,00
        Zeiger aus einer anderen Uebersetzungseinheit       66,0 ms : 23,2 ms   2,85

    `restrict` ist damit der groesste ungenutzte Hebel des Erzeugers -- und zugleich der
    einzige, der etwas KAPUTT machen kann: eine falsche Alias-Zusicherung erzeugt Code, der
    bei `-O0` stimmt und bei `-O2` nicht.

    C11 6.7.3.1 sagt, was zugesichert wird: wird das Objekt X im Block B ueber den
    `restrict`-Zeiger P erreicht, so muss JEDER Zugriff auf X innerhalb von B ueber einen
    aus P abgeleiteten Zeiger laufen. Eine Verletzung ist undefiniertes Verhalten.

    Diese Theorie zeigt, unter WELCHEN Voraussetzungen Gabbro das behaupten darf -- und sie
    macht die Voraussetzungen zu Hypothesen, damit der Pruefer sie einzeln nachweisen muss.
    **Sie beweist NICHT, dass `own` Exklusivitaet bedeutet.** Das ist eine
    Sprachentscheidung und steht hier als benannte Annahme, nicht als Satz.
*)

theory Restrict_Alleinzugriff
  imports Main
begin

section \<open>Das Modell\<close>

text \<open>
  Ein Zugriff nennt zwei Dinge: die WURZEL, ueber die er laeuft (ein Parametername oder ein
  globaler Name), und den ORT, den er trifft. Mehr braucht der Satz nicht -- insbesondere
  keine Werte, keine Reihenfolge und keinen Zeitpunkt.

  \<^item> \<open>wurzeln\<close>  -- die Namen, die in einem Rumpf ueberhaupt als Wurzel auftreten koennen.
  \<^item> \<open>ort\<close>      -- welche Speicherstelle eine Wurzel bezeichnet.
  \<^item> \<open>zugriffe\<close> -- die Zugriffe des Rumpfes, als Menge von Wurzeln.
\<close>

type_synonym wurzel = string
type_synonym ort = nat

record rumpf =
  zugriffe :: "wurzel set"
  ort_von  :: "wurzel \<Rightarrow> ort"

text \<open>
  Die C-Bedingung, woertlich: jeder Zugriff, der den Ort von \<open>p\<close> trifft, laeuft ueber \<open>p\<close>.
\<close>

definition restrict_bedingung :: "rumpf \<Rightarrow> wurzel \<Rightarrow> bool" where
  "restrict_bedingung B p \<longleftrightarrow>
     (\<forall>w \<in> zugriffe B. ort_von B w = ort_von B p \<longrightarrow> w = p)"

section \<open>Die drei Hypothesen, die der Pruefer nachweisen muss\<close>

text \<open>
  \<^bold>\<open>H1 -- der Rahmen ist VOLLSTAENDIG.\<close> Jeder Zugriff des Rumpfes hat eine Wurzel aus der
  deklarierten Menge. Das haelt \<open>E008\<close> (kompositional ueber die Huelle) zusammen mit
  \<open>E010\<close> (Lesen gegen \<open>reads\<close>) -- und seit dem 2026-08-19 vergleicht \<open>E008\<close> den ORT und
  nicht mehr bloss die ART der Wirkung.

  \<^bold>\<open>H2 -- die anderen Wurzeln liegen woanders.\<close> Das ist die eigentliche Arbeit, und sie
  zerfaellt in zwei Faelle:

    \<^item> ein anderer ZEIGERPARAMETER mit demselben Traegertyp -- den schliesst der Pruefer
      aus, indem er verlangt, dass es keinen gibt;
    \<^item> ein GLOBALER Traeger desselben Typs -- den schliesst die SPRACHE aus: sie hat weder
      `cast` (G9) noch einen Adressoperator, also laesst sich ein Zeiger auf eine globale
      Tabelle in Gabbro gar nicht bilden.

  \<^bold>\<open>H3 -- \<open>p\<close> greift auf seinen eigenen Ort zu\<close> ist NICHT noetig. Der Satz gilt auch,
  wenn \<open>p\<close> ungenutzt bleibt: dann trifft kein Zugriff seinen Ort, und die Bedingung ist
  leer erfuellt. \<^emph>\<open>Eine Zusicherung ueber eine Menge, die leer ist, ist die staerkste.\<close>
\<close>

definition rahmen_vollstaendig :: "rumpf \<Rightarrow> wurzel set \<Rightarrow> bool" where
  "rahmen_vollstaendig B W \<longleftrightarrow> zugriffe B \<subseteq> W"

definition wurzeln_getrennt :: "rumpf \<Rightarrow> wurzel set \<Rightarrow> wurzel \<Rightarrow> bool" where
  "wurzeln_getrennt B W p \<longleftrightarrow> (\<forall>w \<in> W. w \<noteq> p \<longrightarrow> ort_von B w \<noteq> ort_von B p)"

section \<open>Der Satz\<close>

theorem restrict_gerechtfertigt:
  assumes voll: "rahmen_vollstaendig B W"
      and getrennt: "wurzeln_getrennt B W p"
    shows "restrict_bedingung B p"
  unfolding restrict_bedingung_def
proof (intro ballI impI)
  fix w assume "w \<in> zugriffe B" and gleich: "ort_von B w = ort_von B p"
  with voll have "w \<in> W" unfolding rahmen_vollstaendig_def by blast
  moreover have "w \<noteq> p \<Longrightarrow> ort_von B w \<noteq> ort_von B p"
    using getrennt \<open>w \<in> W\<close> unfolding wurzeln_getrennt_def by blast
  ultimately show "w = p" using gleich by blast
qed

section \<open>Die Gegenrichtung -- und sie ist die wichtigere\<close>

text \<open>
  \<^bold>\<open>Faellt eine der beiden Hypothesen, faellt der Satz.\<close> Das ist kein Schmuck: es sagt,
  dass der Pruefer BEIDE nachweisen muss und nicht eine davon "meistens" annehmen darf.
\<close>

lemma ohne_trennung_kein_restrict:
  assumes "ort_von B q = ort_von B p" and "q \<noteq> p" and "q \<in> zugriffe B"
  shows "\<not> restrict_bedingung B p"
  using assms unfolding restrict_bedingung_def by blast

text \<open>
  Und ein unvollstaendiger Rahmen hilft ebenso wenig: ein Zugriff ausserhalb von \<open>W\<close> kann
  den Ort von \<open>p\<close> treffen, ohne dass \<open>wurzeln_getrennt\<close> etwas darueber sagt.
\<close>

lemma unvollstaendiger_rahmen_traegt_nichts:
  assumes "wurzeln_getrennt B W p"
      and "q \<notin> W" and "q \<noteq> p" and "q \<in> zugriffe B" and "ort_von B q = ort_von B p"
  shows "\<not> restrict_bedingung B p"
  using assms unfolding restrict_bedingung_def by blast

section \<open>Was hier NICHT bewiesen wird\<close>

text \<open>
  \<^bold>\<open>Dass \<open>own\<close> Exklusivitaet bedeutet, ist eine SPRACHENTSCHEIDUNG und kein Satz.\<close> Sie
  wuerde \<open>wurzeln_getrennt\<close> auch fuer den Fall ZWEIER Zeigerparameter desselben
  Traegertyps liefern -- und genau das ist der Fall, in dem die Messung 2,85 ergab. Solange
  sie nicht getroffen ist, verlangt der Pruefer die staerkere, entscheidungsfreie Bedingung:
  \<^emph>\<open>hoechstens EIN Zeigerparameter je Traegertyp\<close>.

  Die Aussage, die dann noch bleibt, ist trotzdem keine leere: der C-Uebersetzer weiss
  \<^bold>\<open>nicht\<close>, dass eine globale Tabelle in Gabbro nicht adressierbar ist. Fuer ihn koennen
  \<^verbatim>\<open>Kappenraum *c\<close> und das globale \<^verbatim>\<open>Kappenraum\<close>-Objekt dasselbe sein; fuer Gabbro nicht.
  \<^emph>\<open>Das ist die Angabe, die C fehlt.\<close>
\<close>

end
