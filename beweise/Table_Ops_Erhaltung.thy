(*  Titel:      Table_Ops_Erhaltung.thy
    Gegenstand: Die Schablone `table.ops.erhaltung` (S5) -- Zuschnitt (c)
    Stand:      2026-08-19

    Der Eintrag lautet:

        "Je erzeugter Mutation bleibt jede `online`-Invariante DIESES TRAEGERS erhalten --
         einmal ueber der Deklaration, nicht je Aufrufstelle. Invarianten UEBER Traegern
         sind ausdruecklich nicht gedeckt; sie sind `gruppe.ops`."

    UND DER GEGENSTAND FEHLTE. Gemessen am 2026-08-19: `ops` steht an NULL Korpusstellen,
    und `opdecl = "ops" identlist ";"` nimmt beliebige Bezeichner. Nirgends steht, WAS eine
    erzeugte Mutation tut -- der Satz hatte kein Subjekt.

    Diese Theorie holt es aus dem Korpus statt es zu erfinden: `beispiele/01-tabelle.gab`
    schreibt `blatt_loeschen` mit `maintains baum_wohlgeformt`, und `aushaengen` daneben.
    Das sind zwei der vier Operationen, die `SPRACHE.md` 10.2 als Beispiel nennt
    (`insert, remove, relabel, delete_leaf`).

    DREI TEILE, und der mittlere ist der einzige mit Inhalt:

      I    das Amortisationsgesetz -- die Lizenz fuer "einmal je Operation, nicht je
           Aufrufstelle". Billig zu beweisen, und es ist die Aussage, auf der Zuschnitt (c)
           ruht.
      II   ZWEI konkrete erzeugte Mutationen gegen die konkrete Invariante des Korpus.
           Hier arbeitet der Beweis.
      III  zwei Grenzen als GEGENBEISPIEL statt als Behauptung: das Umhaengen faellt, und
           eine Verbindungsinvariante ist nicht gedeckt.

    WAS DIESE THEORIE NICHT TUT: sie stellt keinen Erzeuger her. Die Voraussetzung "jede
    erzeugte Operation erhaelt I" ist in Teil I HYPOTHESE und hat keinen Pass, der sie
    herstellt -- Zahn 3 bucht sie als solche. Teil II loest sie fuer zwei Operationen ein,
    von Hand, an einem Modell.
*)

theory Table_Ops_Erhaltung
  imports Main
begin

section \<open>Teil I -- das Amortisationsgesetz\<close>

text \<open>
  Der Plan sagt (M-Gold-1): \<open>faellt der Beweis EINMAL JE OPERATION im Erzeuger statt einmal
  je Aufrufstelle\<close>. Das ist keine Ergonomiebehauptung, sondern ein Satz, und er steht
  hier -- parametrisch in den Operationen, weil die Sprache sie noch nicht festlegt.
\<close>

locale traeger =
  fixes wirkung :: "'op \<Rightarrow> 'z \<Rightarrow> 'z"
    and online :: "('z \<Rightarrow> bool) set"
  assumes je_operation: "I \<in> online \<Longrightarrow> I z \<Longrightarrow> I (wirkung p z)"
begin

primrec laufen :: "'op list \<Rightarrow> 'z \<Rightarrow> 'z" where
  "laufen [] z = z"
| "laufen (p # ps) z = laufen ps (wirkung p z)"

text \<open>
  \<open>K-1\<close> -- eine FOLGE erzeugter Operationen erhaelt jede \<open>online\<close>-Invariante. Das ist die
  Lizenz: der Erzeuger zeigt es je Operation, der Programmierer benutzt sie beliebig oft.
\<close>

lemma folge_erhaelt:
  assumes "I \<in> online" and "I z"
  shows "I (laufen ps z)"
  using assms by (induct ps arbitrary: z) (auto simp: je_operation)

definition erreichbar :: "'z \<Rightarrow> 'z \<Rightarrow> bool" where
  "erreichbar z z' \<longleftrightarrow> (\<exists>ps. laufen ps z = z')"

text \<open>
  \<open>K-2\<close> -- und damit gilt sie in JEDEM erreichbaren Zustand. Das ist die Form, in der eine
  Tabelleninvariante gemeint ist: nicht \<open>irgendwann\<close>, sondern \<open>immer\<close>.
\<close>

theorem erreichbares_erhaelt:
  assumes "I \<in> online" and "I z" and "erreichbar z z'"
  shows "I z'"
  using assms folge_erhaelt unfolding erreichbar_def by auto

end

text \<open>
  **Die Grenze von Teil I, und sie ist der Grund fuer Teil II.** \<open>je_operation\<close> ist eine
  ANNAHME des Locales. Wer nur Teil I hat, hat bewiesen: *wenn* der Erzeuger je Operation
  liefert, dann gilt es ueberall. Er hat nicht gezeigt, dass irgendeine Operation liefert.

  Zahn 3 bucht genau das: eine Praemisse, die kein Pass herstellt.
\<close>

section \<open>Teil II -- zwei konkrete Mutationen, die konkrete Invariante des Korpus\<close>

text \<open>
  Das Modell ist \<open>beispiele/01-tabelle.gab\<close>: ein Kappenraum, jeder Platz mit einem
  Elternzeiger. \<open>baum_wohlgeformt\<close> heisst dort woertlich

      \<open>forall s in slots of c : c.slots[s] reaches WURZEL via elter\<close>
\<close>

type_synonym idx = nat

record slot = elter :: "idx option"

type_synonym tabelle = "idx \<Rightarrow> slot option"

inductive erreicht :: "tabelle \<Rightarrow> idx \<Rightarrow> bool" for \<sigma> where
  wurzel:   "\<sigma> s = Some sl \<Longrightarrow> elter sl = None \<Longrightarrow> erreicht \<sigma> s"
| aufstieg: "\<sigma> s = Some sl \<Longrightarrow> elter sl = Some p \<Longrightarrow> erreicht \<sigma> p \<Longrightarrow> erreicht \<sigma> s"

definition wohlgeformt :: "tabelle \<Rightarrow> bool" where
  "wohlgeformt \<sigma> \<longleftrightarrow> (\<forall>s sl. \<sigma> s = Some sl \<longrightarrow> erreicht \<sigma> s)"

text \<open>
  Ein Platz ist ein BLATT, wenn ihn niemand als Elter nennt. Genau das verlangt
  \<open>blatt_loeschen\<close> in seinem \<open>requires\<close> (\<open>ist_blatt(c, s)\<close>).
\<close>

definition blatt :: "tabelle \<Rightarrow> idx \<Rightarrow> bool" where
  "blatt \<sigma> s \<longleftrightarrow> (\<forall>t tl. \<sigma> t = Some tl \<longrightarrow> elter tl \<noteq> Some s)"

subsection \<open>Die erste Mutation: einen FRISCHEN Platz unter einen erreichbaren haengen\<close>

definition einfuegen :: "tabelle \<Rightarrow> idx \<Rightarrow> idx \<Rightarrow> tabelle" where
  "einfuegen \<sigma> n p = \<sigma>(n := Some \<lparr> elter = Some p \<rparr>)"

text \<open>
  \<open>M-1\<close> -- ein frischer Platz stoert keine vorhandene Erreichbarkeit. Der Grund ist
  scharf und nicht bloss plausibel: jede Kette besteht aus Plaetzen, die in \<open>\<sigma>\<close> BELEGT
  sind, und \<open>n\<close> ist es nicht.
\<close>

lemma erreicht_bleibt_bei_frischem:
  assumes frisch: "\<sigma> n = None"
  assumes "erreicht \<sigma> x"
  shows "erreicht (\<sigma>(n := sl0)) x"
  using assms(2)
proof (induct rule: erreicht.induct)
  case (wurzel s sl)
  then have "s \<noteq> n" using frisch by auto
  then show ?case using wurzel by (auto intro: erreicht.wurzel)
next
  case (aufstieg s sl p)
  then have "s \<noteq> n" using frisch by auto
  then show ?case using aufstieg by (auto intro: erreicht.aufstieg)
qed

text \<open>
  \<open>M-2\<close> -- und damit haelt die Invariante. **Die zwei Voraussetzungen sind genau die zwei
  Zeilen, die der Erzeuger schreiben muesste:** der Platz ist frisch, und der Elter ist
  erreichbar.
\<close>

theorem einfuegen_erhaelt:
  assumes wf: "wohlgeformt \<sigma>"
  assumes frisch: "\<sigma> n = None"
  assumes elter_da: "erreicht \<sigma> p"
  shows "wohlgeformt (einfuegen \<sigma> n p)"
proof -
  have p_neu: "erreicht (einfuegen \<sigma> n p) p"
    using elter_da frisch erreicht_bleibt_bei_frischem
    unfolding einfuegen_def by blast
  show ?thesis
  proof (unfold wohlgeformt_def, intro allI impI)
    fix s sl assume s: "einfuegen \<sigma> n p s = Some sl"
    show "erreicht (einfuegen \<sigma> n p) s"
    proof (cases "s = n")
      case True
      then show ?thesis
        using p_neu s unfolding einfuegen_def
        by (auto intro: erreicht.aufstieg)
    next
      case False
      then have "\<sigma> s = Some sl" using s unfolding einfuegen_def by auto
      then have "erreicht \<sigma> s" using wf unfolding wohlgeformt_def by blast
      then show ?thesis
        using frisch erreicht_bleibt_bei_frischem unfolding einfuegen_def by blast
    qed
  qed
qed

subsection \<open>Die zweite Mutation: ein BLATT loeschen\<close>

definition blatt_loeschen :: "tabelle \<Rightarrow> idx \<Rightarrow> tabelle" where
  "blatt_loeschen \<sigma> s = \<sigma>(s := None)"

text \<open>
  \<open>M-3\<close> -- eine Kette, die nicht bei \<open>s\<close> ANFAENGT, beruehrt \<open>s\<close> nicht, wenn \<open>s\<close> ein Blatt
  ist. *Sie muesste \<open>s\<close> ueber einen Elternzeiger betreten, und den gibt es nicht.*
\<close>

lemma erreicht_ohne_blatt:
  assumes ist_blatt: "blatt \<sigma> s"
  assumes "erreicht \<sigma> x"
  shows "x \<noteq> s \<longrightarrow> erreicht (\<sigma>(s := None)) x"
  using assms(2)
proof (induct rule: erreicht.induct)
  case (wurzel t tl)
  then show ?case by (auto intro: erreicht.wurzel)
next
  case (aufstieg t tl p)
  have "p \<noteq> s" using aufstieg ist_blatt unfolding blatt_def by blast
  then show ?case using aufstieg by (auto intro: erreicht.aufstieg)
qed

theorem blatt_loeschen_erhaelt:
  assumes wf: "wohlgeformt \<sigma>"
  assumes ist_blatt: "blatt \<sigma> s"
  shows "wohlgeformt (blatt_loeschen \<sigma> s)"
proof (unfold wohlgeformt_def, intro allI impI)
  fix x xl assume x: "blatt_loeschen \<sigma> s x = Some xl"
  then have ne: "x \<noteq> s" unfolding blatt_loeschen_def by auto
  then have "\<sigma> x = Some xl" using x unfolding blatt_loeschen_def by auto
  then have "erreicht \<sigma> x" using wf unfolding wohlgeformt_def by blast
  then show "erreicht (blatt_loeschen \<sigma> s) x"
    using ne ist_blatt erreicht_ohne_blatt unfolding blatt_loeschen_def by blast
qed

section \<open>Teil III -- zwei Grenzen, als Gegenbeispiel statt als Behauptung\<close>

subsection \<open>Das UMHAENGEN faellt, und darum ist S3 zu Recht offen\<close>

definition umhaengen :: "tabelle \<Rightarrow> idx \<Rightarrow> idx \<Rightarrow> tabelle" where
  "umhaengen \<sigma> s p = \<sigma>(s := Some \<lparr> elter = Some p \<rparr>)"

text \<open>
  Zwei Plaetze: \<open>0\<close> ist Wurzel, \<open>1\<close> haengt darunter. Haengt man \<open>0\<close> unter \<open>1\<close>, entsteht
  ein Zyklus, und **keiner der beiden** erreicht mehr eine Wurzel.
\<close>

definition zwei :: tabelle where
  "zwei = (\<lambda>i. if i = 0 then Some \<lparr> elter = None \<rparr>
               else if i = 1 then Some \<lparr> elter = Some 0 \<rparr>
               else None)"

lemma zwei_wohlgeformt: "wohlgeformt zwei"
proof (unfold wohlgeformt_def, intro allI impI)
  fix s sl assume "zwei s = Some sl"
  then have "s = 0 \<or> s = 1" unfolding zwei_def by (auto split: if_splits)
  moreover have "erreicht zwei 0"
    by (rule erreicht.wurzel[of zwei 0 "\<lparr> elter = None \<rparr>"]) (auto simp: zwei_def)
  ultimately show "erreicht zwei s"
    by (auto intro: erreicht.aufstieg simp: zwei_def)
qed

lemma zyklus_erreicht_nichts: "\<not> erreicht (umhaengen zwei 0 1) x"
proof
  assume "erreicht (umhaengen zwei 0 1) x"
  then show False
    by (induct rule: erreicht.induct) (auto simp: umhaengen_def zwei_def split: if_splits)
qed

theorem umhaengen_faellt: "\<not> wohlgeformt (umhaengen zwei 0 1)"
  using zyklus_erreicht_nichts unfolding wohlgeformt_def umhaengen_def
  by (auto simp: zwei_def)

text \<open>
  **Das ist der Satz, den der Schablonenregister-Eintrag \<open>consuming.umhaengen\<close> (S3) als
  \<open>entworfen\<close> fuehrt** -- und er ist hier nicht laenger eine Vermutung. Ein Erzeuger, der
  \<open>umhaengen\<close> ausliefert, schuldet eine Bedingung; \<open>einfuegen\<close> und \<open>blatt_loeschen\<close>
  schulden sie nicht.
\<close>

subsection \<open>Eine VERBINDUNGSinvariante ist nicht gedeckt -- und das steht im Eintrag\<close>

text \<open>
  Der Eintrag sagt: \<open>Invarianten UEBER Traegern sind ausdruecklich nicht gedeckt; sie sind
  gruppe.ops\<close>. Auch das ist beweisbar statt behauptbar: es gibt eine Operation, die
  **jede Invariante ihres eigenen Traegers erhaelt** und eine verbindende bricht.
\<close>

definition setze_eins :: "nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "setze_eins z = (1, snd z)"

definition eigen :: "nat \<times> nat \<Rightarrow> bool" where
  "eigen z \<longleftrightarrow> fst z \<le> 1"

definition verbindend :: "nat \<times> nat \<Rightarrow> bool" where
  "verbindend z \<longleftrightarrow> fst z = snd z"

lemma eigen_bleibt: "eigen z \<Longrightarrow> eigen (setze_eins z)"
  unfolding eigen_def setze_eins_def by simp

lemma zweiter_traeger_unberuehrt: "snd (setze_eins z) = snd z"
  unfolding setze_eins_def by simp

theorem verbindung_nicht_gedeckt:
  "verbindend (0, 0) \<and> \<not> verbindend (setze_eins (0, 0))"
  unfolding verbindend_def setze_eins_def by simp

text \<open>
  \<open>f\<close> ruehrt den zweiten Traeger nicht an (zweite Zeile) und erhaelt die Invariante des
  ersten (erste Zeile) -- und die verbindende faellt trotzdem. **Damit ist \<open>gruppe.ops\<close>
  keine Bequemlichkeit, sondern notwendig**, und der Eintrag von S5 darf seine Grenze
  nennen, ohne sich klein zu machen.
\<close>

section \<open>Was hier NICHT steht\<close>

text \<open>
  \<^item> **Kein Erzeuger.** \<open>einfuegen\<close> und \<open>blatt_loeschen\<close> sind hier von Hand definiert;
    dass \<open>gabbro\<close> genau diese Ruempfe emittiert, ist unbewiesen und heute unwahr -- es
    gibt keinen Erzeuger fuer \<open>ops\<close>. *Bewiesen ist die MATHEMATIK der Schablone, nicht
    ihre Auslieferung* -- derselbe Satz wie bei \<open>table.induktion\<close>.
  \<^item> **Keine Kostenaussage.** \<open>SPRACHE.md\<close> 10.2 verlangt, dass eine \<open>online\<close>-Invariante in
    die \<open>costs\<close> der Mutation passt. Das ist eine Pruefervorschrift, kein Satz ueber
    Zustaende.
  \<^item> **Kein \<open>offline\<close>.** Teil I quantifiziert ueber \<open>online\<close>. Ueber \<open>offline\<close> folgt
    NICHTS -- und das ist die Absicht: \<open>offline\<close> ist Diagnose und laeuft im Pruefgeschirr.
\<close>

end
