(*  Titel:      Table_Ops_Erhaltung.thy
    Gegenstand: Die Schablone `table.ops.erhaltung` (S5) -- Zuschnitt (c)
    Stand:      2026-08-28 (Teil II hat seit heute DREI Mutationen -- `umhaengen` traegt
                eine Bedingung statt eines Verbots)

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
      II   DREI konkrete erzeugte Mutationen gegen die konkrete Invariante des Korpus.
           Hier arbeitet der Beweis.
      III  zwei Grenzen als GEGENBEISPIEL statt als Behauptung: das Umhaengen faellt OHNE
           seine Bedingung, und eine Verbindungsinvariante ist nicht gedeckt.

    DIE DRITTE MUTATION KAM AM 2026-08-28, und sie kam als Bedingung statt als Verbot.
    `relabel` war bis dahin ein Wort der geschlossenen `ops`-Wortmenge, das der Erzeuger
    ABSAGTE -- unter Berufung auf `umhaengen_faellt` aus Teil III. Ein Wort, das nichts
    erzeugt und niemand rufen kann, ist eine Klausel ohne Einloeser (`N037`, `H007`/`H008`),
    und der Bedarf ist gemessen: 127 Korpusstellen.

    Die Frage, die davor niemand gestellt hatte, war nicht OB das Umhaengen faellt, sondern
    WORAN. `U-3` (`umhaengen_erhaelt`) beantwortet sie: `\<not> ueber \<sigma> p s` -- der neue Elter
    liegt nicht unter dem umgehaengten Platz, dieser selbst eingeschlossen. `G-1`/`G-2`
    zeigen, dass das Gegenbeispiel von Teil III GENAU an dieser Voraussetzung scheitert und
    an keiner anderen.

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

section \<open>Teil II -- drei konkrete Mutationen, die konkrete Invariante des Korpus\<close>

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

subsection \<open>Die dritte Mutation: das UMHAENGEN -- und es traegt eine Bedingung\<close>

text \<open>
  \<open>relabel\<close> haengt einen VORHANDENEN Platz unter einen neuen Elter. Bis zum 2026-08-28
  stand dazu in dieser Theorie nur das Gegenbeispiel von Teil III, und der Erzeuger sagte
  das Wort deshalb ab -- **ein Wort einer geschlossenen Wortmenge, das nichts erzeugt und
  niemand rufen kann.** Dieselbe Stellung, die \<open>ensures\<close> am Zeigertyp gekostet hat
  (\<open>N037\<close>) und \<open>beispiele/05\<close> seine \<open>protects\<close>-Klausel (\<open>H007\<close>/\<open>H008\<close>).

  Und der Bedarf ist gemessen: \<open>umhaengen\<close> steht an 127 Stellen des zweiten Korpus
  (\<open>kernel/\<close> + \<open>mm/\<close>, 2026-08-19). *"Kein gemessener Bedarf" war hier also nie der Ausweg.*

  Die Frage, die vorher niemand gestellt hat, lautet daher: **unter WELCHER Bedingung
  erhaelt das Umhaengen die Wohlgeformtheit?**
\<close>

definition umhaengen :: "tabelle \<Rightarrow> idx \<Rightarrow> idx \<Rightarrow> tabelle" where
  "umhaengen \<sigma> s p = \<sigma>(s := Some \<lparr> elter = Some p \<rparr>)"

text \<open>
  \<open>ueber \<sigma> x s\<close> -- **\<open>s\<close> liegt auf \<open>x\<close>s Elternkette, \<open>x\<close> selbst eingeschlossen.** Das ist
  die reflexiv-transitive Huelle der Elternkante.

  **Die Reflexivitaet ist keine Bequemlichkeit, sondern die Haelfte der Aussage.**
  \<open>umhaengen \<sigma> s s\<close> macht \<open>s\<close> zu seinem eigenen Elter -- eine Schlinge, und die bricht
  \<open>wohlgeformt\<close> genauso wie der Zweislotzyklus des Gegenbeispiels. Eine STRIKTE
  Vorfahrenrelation liesse genau diesen Fall durch; *sie waere fail-open an der Stelle, an
  der der Satz der ganze Ertrag ist.* Und sie ist genau das, was Gabbros \<open>ancestors of\<close>
  ist -- siehe \<open>messung/OPS-RELABEL.md\<close>.
\<close>

inductive ueber :: "tabelle \<Rightarrow> idx \<Rightarrow> idx \<Rightarrow> bool" for \<sigma> where
  hier:   "ueber \<sigma> s s"
| hoeher: "\<sigma> x = Some xl \<Longrightarrow> elter xl = Some q \<Longrightarrow> ueber \<sigma> q s \<Longrightarrow> ueber \<sigma> x s"

text \<open>
  \<open>U-1\<close> -- **eine Kette, die \<open>s\<close> nicht beruehrt, ueberlebt das Umhaengen unveraendert.**
  Der Grund ist derselbe wie bei \<open>M-1\<close> und \<open>M-3\<close>: \<open>umhaengen\<close> aendert \<open>\<sigma>\<close> an genau einer
  Stelle, und wessen Kette diese Stelle nie betritt, den geht die Aenderung nichts an.
\<close>

lemma umhaengen_ausserhalb:
  assumes "erreicht \<sigma> x"
  shows "\<not> ueber \<sigma> x s \<longrightarrow> erreicht (umhaengen \<sigma> s p) x"
  using assms
proof (induct rule: erreicht.induct)
  case (wurzel y yl)
  show ?case
  proof
    assume nu: "\<not> ueber \<sigma> y s"
    have ne: "y \<noteq> s"
    proof
      assume "y = s"
      then have "ueber \<sigma> y s" by (simp add: ueber.hier)
      with nu show False ..
    qed
    then have "umhaengen \<sigma> s p y = Some yl"
      using wurzel unfolding umhaengen_def by simp
    then show "erreicht (umhaengen \<sigma> s p) y"
      using wurzel by (auto intro: erreicht.wurzel)
  qed
next
  case (aufstieg y yl q)
  show ?case
  proof
    assume nu: "\<not> ueber \<sigma> y s"
    have ne: "y \<noteq> s"
    proof
      assume "y = s"
      then have "ueber \<sigma> y s" by (simp add: ueber.hier)
      with nu show False ..
    qed
    have "\<not> ueber \<sigma> q s"
    proof
      assume "ueber \<sigma> q s"
      from ueber.hoeher[OF aufstieg(1) aufstieg(2) this] have "ueber \<sigma> y s" .
      with nu show False ..
    qed
    then have q_da: "erreicht (umhaengen \<sigma> s p) q" by (rule mp[OF aufstieg(4)])
    have "umhaengen \<sigma> s p y = Some yl"
      using ne aufstieg unfolding umhaengen_def by simp
    then show "erreicht (umhaengen \<sigma> s p) y"
      using aufstieg q_da by (auto intro: erreicht.aufstieg)
  qed
qed

text \<open>
  \<open>U-2\<close> -- **und wer \<open>s\<close> ueberhaupt erreicht, kommt hinterher ueber \<open>s\<close> weiter.** Der Satz
  braucht \<open>ueber\<close> gar nicht: entweder laeuft \<open>x\<close>s Kette durch \<open>s\<close>, dann endet sie dort und
  laeuft von da weiter, wohin \<open>s\<close> jetzt zeigt -- oder sie laeuft nicht durch \<open>s\<close> und ist
  unveraendert. **Beides steht in derselben Induktion.**

  *Der erste Anlauf hatte hier zwei Lemmata (\<open>ueber\<close> bleibt erhalten; Erreichbarkeit wandert
  die Kette abwaerts), und beide sind an derselben Stelle gefallen:* in
  \<open>ueber \<sigma> x s \<Longrightarrow> ueber (umhaengen \<sigma> s p) x s\<close> traegt \<open>s\<close> ZWEI Rollen -- Induktionsargument
  und Parameter des Ergebnisses -- und \<open>induct\<close> verallgemeinert dann nur \<open>x\<close>. Die Fassung
  hier hat \<open>s\<close> nur als Parameter.
\<close>

lemma umhaengen_durch_s:
  assumes "erreicht \<sigma> x"
  shows "erreicht (umhaengen \<sigma> s p) s \<longrightarrow> erreicht (umhaengen \<sigma> s p) x"
  using assms
proof (induct rule: erreicht.induct)
  case (wurzel y yl)
  show ?case
  proof
    assume s_da: "erreicht (umhaengen \<sigma> s p) s"
    show "erreicht (umhaengen \<sigma> s p) y"
    proof (cases "y = s")
      case True
      then show ?thesis using s_da by simp
    next
      case False
      then have "umhaengen \<sigma> s p y = Some yl"
        using wurzel unfolding umhaengen_def by simp
      then show ?thesis using wurzel by (auto intro: erreicht.wurzel)
    qed
  qed
next
  case (aufstieg y yl q)
  show ?case
  proof
    assume s_da: "erreicht (umhaengen \<sigma> s p) s"
    show "erreicht (umhaengen \<sigma> s p) y"
    proof (cases "y = s")
      case True
      then show ?thesis using s_da by simp
    next
      case False
      then have wert: "umhaengen \<sigma> s p y = Some yl"
        using aufstieg unfolding umhaengen_def by simp
      have "erreicht (umhaengen \<sigma> s p) q" by (rule mp[OF aufstieg(4) s_da])
      then show ?thesis using wert aufstieg by (auto intro: erreicht.aufstieg)
    qed
  qed
qed

text \<open>
  \<open>U-3\<close> -- **der Satz.** Drei Voraussetzungen, und die dritte ist die neue:

    \<^item> \<open>wohlgeformt \<sigma>\<close> -- wie bei den anderen beiden Mutationen;
    \<^item> \<open>erreicht \<sigma> p\<close> -- der NEUE Elter erreicht eine Wurzel. Wortgleich zur zweiten
      Voraussetzung von \<open>einfuegen_erhaelt\<close>;
    \<^item> \<open>\<not> ueber \<sigma> p s\<close> -- **\<open>s\<close> liegt nicht auf \<open>p\<close>s Elternkette.** Das ist die Bedingung,
      die \<open>relabel\<close> schuldet und die \<open>insert\<close> nicht schuldet: dort ist der Platz FRISCH,
      und ueber einem frischen Platz kann nichts haengen.

  Der Beweis in drei Zuegen: \<open>p\<close>s Kette laeuft nicht durch \<open>s\<close>, ueberlebt also unveraendert
  (\<open>U-1\<close>) -- **das ist die einzige Stelle, an der die neue Bedingung gebraucht wird, und sie
  wird dort ganz gebraucht.** Damit erreicht \<open>s\<close> ueber seinen neuen Elter
  (\<open>erreicht.aufstieg\<close>); und jeder uebrige belegte Platz kommt mit \<open>U-2\<close> nach.
\<close>

theorem umhaengen_erhaelt:
  assumes wf: "wohlgeformt \<sigma>"
  assumes elter_da: "erreicht \<sigma> p"
  assumes nicht_drunter: "\<not> ueber \<sigma> p s"
  shows "wohlgeformt (umhaengen \<sigma> s p)"
proof -
  have p_neu: "erreicht (umhaengen \<sigma> s p) p"
    by (rule mp[OF umhaengen_ausserhalb[OF elter_da] nicht_drunter])
  have s_wert: "umhaengen \<sigma> s p s = Some \<lparr> elter = Some p \<rparr>"
    unfolding umhaengen_def by simp
  have s_elter: "elter \<lparr> elter = Some p \<rparr> = Some p" by simp
  have s_neu: "erreicht (umhaengen \<sigma> s p) s"
    by (rule erreicht.aufstieg[OF s_wert s_elter p_neu])
  show ?thesis
  proof (unfold wohlgeformt_def, intro allI impI)
    fix x xl assume x: "umhaengen \<sigma> s p x = Some xl"
    show "erreicht (umhaengen \<sigma> s p) x"
    proof (cases "x = s")
      case True
      then show ?thesis using s_neu by simp
    next
      case False
      then have "\<sigma> x = Some xl" using x unfolding umhaengen_def by simp
      then have "erreicht \<sigma> x"
        using wf[unfolded wohlgeformt_def, rule_format] by simp
      then show ?thesis by (rule mp[OF umhaengen_durch_s s_neu])
    qed
  qed
qed

text \<open>
  **Was der Satz NICHT verlangt, und es war im Zuschnitt vorgesehen:** \<open>\<sigma> s = Some sl\<close>.
  Die Voraussetzung *"der umgehaengte Platz ist belegt"* ist entbehrlich -- \<open>umhaengen\<close>
  SETZT den Platz, und auf einem freien \<open>s\<close> ist es dasselbe wie \<open>einfuegen\<close>. Sie steht
  darum nicht bei den Annahmen, sondern hier; die vorgeschlagene Fassung faellt aus der
  bewiesenen heraus:
\<close>

corollary umhaengen_erhaelt_am_belegten_platz:
  assumes "wohlgeformt \<sigma>" and "\<sigma> s = Some sl"
      and "erreicht \<sigma> p" and "\<not> ueber \<sigma> p s"
  shows "wohlgeformt (umhaengen \<sigma> s p)"
  using umhaengen_erhaelt[OF assms(1) assms(3) assms(4)] .

section \<open>Teil III -- zwei Grenzen, als Gegenbeispiel statt als Behauptung\<close>

subsection \<open>Das UMHAENGEN faellt OHNE die Bedingung -- und darum ist sie noetig\<close>

text \<open>
  Zwei Plaetze: \<open>0\<close> ist Wurzel, \<open>1\<close> haengt darunter. Haengt man \<open>0\<close> unter \<open>1\<close>, entsteht
  ein Zyklus, und **keiner der beiden** erreicht mehr eine Wurzel.

  **Dieses Gegenbeispiel bleibt stehen, und seine Rolle hat sich am 2026-08-28 gedreht:**
  bis dahin war es der Grund, \<open>relabel\<close> gar nicht erst zu erzeugen; jetzt ist es der Beleg,
  dass \<open>U-4\<close> keine Aussage ueber etwas Leichtes ist. *Ein Satz, dessen Voraussetzung nie
  verletzt sein kann, ist eine Zierde.*
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

  **Und seit \<open>U-3\<close> ist die Bedingung benannt** -- womit dieses Gegenbeispiel eine zweite
  Pflicht bekommt: es muss GENAU an ihr scheitern. Ein Gegenbeispiel, das schon an
  \<open>wohlgeformt \<sigma>\<close> oder an \<open>erreicht \<sigma> p\<close> stuerbe, wuerde ueber die neue Voraussetzung
  nichts sagen.
\<close>

text \<open>
  \<open>G-1\<close> -- die ersten beiden Voraussetzungen von \<open>U-3\<close> HALTEN am Gegenbeispiel:
  \<open>zwei\<close> ist wohlgeformt, und der neue Elter \<open>1\<close> erreicht eine Wurzel.
\<close>

lemma gegenbeispiel_erfuellt_die_alten:
  "wohlgeformt zwei \<and> erreicht zwei 1"
proof -
  have "erreicht zwei 0"
    by (rule erreicht.wurzel[of zwei 0 "\<lparr> elter = None \<rparr>"]) (auto simp: zwei_def)
  then have "erreicht zwei 1"
    by (rule erreicht.aufstieg[of zwei 1 "\<lparr> elter = Some 0 \<rparr>" 0, rotated 2])
       (auto simp: zwei_def)
  then show ?thesis using zwei_wohlgeformt by simp
qed

text \<open>
  \<open>G-2\<close> -- **und die dritte faellt, und nur sie.** \<open>umhaengen zwei 0 1\<close> haengt \<open>s = 0\<close>
  unter \<open>p = 1\<close>, und \<open>0\<close> liegt auf \<open>1\<close>s Elternkette. *Damit ist die Voraussetzung von
  \<open>U-3\<close> nicht bloss hinreichend hingeschrieben, sondern an der einen bekannten Bruchstelle
  gemessen.*
\<close>

lemma gegenbeispiel_verletzt_die_neue: "ueber zwei 1 0"
proof (rule ueber.hoeher[of zwei 1 "\<lparr> elter = Some 0 \<rparr>" 0 0])
  show "zwei 1 = Some \<lparr> elter = Some 0 \<rparr>" by (simp add: zwei_def)
  show "elter \<lparr> elter = Some (0::idx) \<rparr> = Some 0" by simp
  show "ueber zwei 0 0" by (rule ueber.hier)
qed

text \<open>
  Zusammen: \<open>U-3\<close> und \<open>umhaengen_faellt\<close> sind kein Widerspruch, sondern die zwei Haelften
  einer Aussage. **Die Bedingung ist noetig** (dieses Gegenbeispiel erfuellt alles ausser
  ihr und bricht) **und sie ist hinreichend** (\<open>U-3\<close>). *Das ist genau der Stand, den
  \<open>relabel\<close> brauchte, um vom abgesagten Wort zur erzeugten Operation zu werden.*
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
  \<^item> **Kein Beweis der ABSENKUNG.** \<open>einfuegen\<close>, \<open>blatt_loeschen\<close> und \<open>umhaengen\<close> sind
    hier von Hand definiert; dass die C-Ruempfe aus \<open>emit.rs::ops\<close> genau diese Funktionen
    sind, ist NICHT bewiesen. *Bewiesen ist die MATHEMATIK der Schablone, nicht ihre
    Auslieferung* -- dieselbe Luecke, die \<open>Table_Absenkung.thy\<close> mit eigenen Worten nennt.
    (Bis zum 2026-08-28 stand hier *"es gibt keinen Erzeuger fuer \<open>ops\<close>"*; seit dem
    Vormittag gibt es einen, und seit dem Nachmittag ruft ihn \<open>D012\<close> zur Rechenschaft.)
  \<^item> **Keine Kostenaussage.** \<open>SPRACHE.md\<close> 10.2 verlangt, dass eine \<open>online\<close>-Invariante in
    die \<open>costs\<close> der Mutation passt. Das ist eine Pruefervorschrift, kein Satz ueber
    Zustaende.
  \<^item> **Kein \<open>offline\<close>.** Teil I quantifiziert ueber \<open>online\<close>. Ueber \<open>offline\<close> folgt
    NICHTS -- und das ist die Absicht: \<open>offline\<close> ist Diagnose und laeuft im Pruefgeschirr.
\<close>

end
