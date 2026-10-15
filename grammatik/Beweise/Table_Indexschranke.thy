(*  Titel:      Table_Indexschranke.thy
    Gegenstand: Die Schablone `table.indexschranke` (S12)
    Stand:      2026-08-16

    Der Eintrag lautet:

        "Der erzeugte Indextyp `0 ..< N` deckt genau die belegten Slots, und die
         Absenkung legt N Slots an."

    Diese Schablone wird ZUERST gefahren, weil der Beweis von S4 auf ihr ruht:
    `traeger_endlich` in Table_Induktion.thy nimmt `im_bereich N \<sigma>` an, und das ist
    woertlich, was hier geschuldet wird. Eine bewiesene Schablone, die auf einer
    unbewiesenen ruht, hat die Vertrauensbasis verschoben, nicht verkleinert.
*)

theory Table_Indexschranke
  imports Main
begin

section \<open>Der Indextyp\<close>

text \<open>
  \<open>table T count N\<close> erzeugt \<open>index into T\<close>. Die Behauptung: dieser Typ ist \<open>{i. i < N}\<close>.
\<close>

type_synonym idx = nat

definition indextyp :: "nat \<Rightarrow> idx set" where
  "indextyp N = {i. i < N}"

lemma indextyp_endlich: "finite (indextyp N)"
  unfolding indextyp_def by simp

lemma indextyp_schranke: "i \<in> indextyp N \<Longrightarrow> i < N"
  unfolding indextyp_def by simp

section \<open>M-1 -- \<open>deckt genau die belegten Slots\<close> ist FALSCH, wie es dasteht\<close>

text \<open>
  **Ausgespuelt.** Der Eintrag sagt \<open>deckt genau die belegten Slots\<close>. Das ist zu stark und
  waere, woertlich genommen, eine andere Zusage:

    \<open>indextyp N = {i. belegt \<sigma> i}\<close>

  Das gilt **nicht** -- eine Tabelle mit \<open>count 80256\<close>, von der drei Slots belegt sind, hat
  einen Indextyp mit 80256 Werten. Was wirklich gilt, ist die eine Richtung:
\<close>

definition belegt :: "(idx \<Rightarrow> 'a option) \<Rightarrow> idx \<Rightarrow> bool" where
  "belegt \<sigma> i \<longleftrightarrow> \<sigma> i \<noteq> None"

definition wohlgeformt :: "nat \<Rightarrow> (idx \<Rightarrow> 'a option) \<Rightarrow> bool" where
  "wohlgeformt N \<sigma> \<longleftrightarrow> (\<forall>i. belegt \<sigma> i \<longrightarrow> i \<in> indextyp N)"

lemma belegt_liegt_im_indextyp:
  assumes "wohlgeformt N \<sigma>"
  assumes "belegt \<sigma> i"
  shows "i \<in> indextyp N"
  using assms unfolding wohlgeformt_def by blast

text \<open>
  **Die Gegenrichtung gilt nicht, und der Beweis dafuer steht hier**, damit die Zusage nicht
  weiter zu gross gelesen wird: ein Index im Typ muss nicht belegt sein.
\<close>

lemma indextyp_deckt_nicht_nur_belegte:
  assumes "N > 0"
  shows "\<exists>\<sigma> i. wohlgeformt N \<sigma> \<and> i \<in> indextyp N \<and> \<not> belegt \<sigma> i"
proof -
  have "wohlgeformt N (\<lambda>_. None :: 'a option)"
    unfolding wohlgeformt_def belegt_def by simp
  moreover have "(0::idx) \<in> indextyp N" using assms unfolding indextyp_def by simp
  moreover have "\<not> belegt (\<lambda>_. None :: 'a option) 0"
    unfolding belegt_def by simp
  ultimately show ?thesis by blast
qed

section \<open>M-2 -- die Schranke ist eine Zusage ueber SCHREIBSTELLEN, nicht ueber den Typ\<close>

text \<open>
  **Ausgespuelt.** Dass \<open>indextyp N\<close> nur Werte \<open>< N\<close> enthaelt, ist trivial (eine Zeile oben).
  Der Gehalt der Schablone liegt woanders: **jede erzeugte Schreibstelle bleibt darin.**

  Ohne diese Haelfte ist die Schranke eine Aussage ueber eine Menge, nicht ueber ein
  Programm -- und genau die Haelfte ist es, die S4 gebraucht hat.
\<close>

definition schreibstellen_im_typ ::
    "nat \<Rightarrow> (idx \<Rightarrow> 'a option) \<Rightarrow> (idx \<Rightarrow> idx option) \<Rightarrow> bool" where
  "schreibstellen_im_typ N \<sigma> feld \<longleftrightarrow>
     (\<forall>i d. belegt \<sigma> i \<longrightarrow> feld i = Some d \<longrightarrow> d \<in> indextyp N)"

lemma kette_bleibt_im_typ:
  assumes "schreibstellen_im_typ N \<sigma> feld"
  assumes "belegt \<sigma> i"
  assumes "feld i = Some d"
  shows "d < N"
  using assms unfolding schreibstellen_im_typ_def by (simp add: indextyp_def)

section \<open>M-3 -- \<open>die Absenkung legt N Slots an\<close> ist NICHT beweisbar, und zwar aus einem Grund\<close>

text \<open>
  **Ausgespuelt, als GRENZE.** Der zweite Halbsatz des Eintrags ist eine Aussage ueber die
  **Emission**: dass der erzeugte C-Code \<open>N\<close> Slots anlegt.

  **Es gibt keinen Erzeuger.** \<open>mutiere-pruefer.py\<close> weist die Emissionsflaechen mit 0
  Mutationen aus. Eine Formalisierung dieses Halbsatzes waere eine Formalisierung meiner
  Absicht, nicht eines Gegenstands -- und wuerde danach wie Deckung aussehen.

  **Die ehrliche Fassung: die Schablone hat ZWEI Haelften, und nur die erste ist heute
  beweisbar.** Der Eintrag fuehrte sie in einem Satz, als waeren sie eine.
\<close>

section \<open>Was S4 von hier bekommt\<close>

text \<open>
  Der Anschluss an \<open>Table_Induktion.thy\<close>: dort steht \<open>im_bereich N \<sigma>\<close> als Annahme. Sie ist
  genau \<open>schreibstellen_im_typ\<close>, ueber zwei Felder statt einem.
\<close>

lemma im_bereich_folgt_aus_indexschranke:
  assumes fc: "schreibstellen_im_typ N \<sigma> erstes"
  assumes ns: "schreibstellen_im_typ N \<sigma> naechstes"
  assumes "belegt \<sigma> i"
  shows "(\<forall>d. erstes i = Some d \<longrightarrow> d < N) \<and> (\<forall>d. naechstes i = Some d \<longrightarrow> d < N)"
  using assms kette_bleibt_im_typ by blast

end
