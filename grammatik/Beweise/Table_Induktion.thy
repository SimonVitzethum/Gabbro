(*  Titel:      Table_Induktion.thy
    Gegenstand: Die Schablone `table.induktion` (S4) aus `gabbro schablonen`
    Stand:      2026-08-16

    Diese Datei formalisiert, was der Schablonen-Eintrag behauptet -- und zwar in der
    geschaerften Fassung, die aus dem ersten (ungeprueften) Anlauf entstanden ist:
    die vier Nebenbedingungen N-1 bis N-4 stehen einzeln da, statt in den zwei Woertern
    "wohlfundiert und vollstaendig" zu verschwinden.

    Der Pruefstand steht im Kopf jedes Abschnitts: was Isabelle hier ANNIMMT, ist das,
    was die Schablone dem Erzeuger als Pflicht auferlegt. Was sie BEWEIST, ist das, was
    der Erzeuger daraus bekommt.
*)

theory Table_Induktion
  imports Main
begin

section \<open>Die Deklaration\<close>

text \<open>
  Eine \<open>table T count N\<close> mit zwei Verkettungsfeldern. Der Zustand bildet einen Index auf
  einen Slot ab; \<open>None\<close> heisst "der Platz ist nicht belegt".
\<close>

type_synonym idx = nat

record slot =
  first_child :: "idx option"
  next_sibling :: "idx option"

type_synonym tabelle = "idx \<Rightarrow> slot option"

text \<open>
  **Die primitive Kante, und sie hat ZWEI Arten.** Das ist bereits N-4: die Domaene
  \<open>chain(first_child, next_sibling) in slots\<close> laeuft ueber zwei verschiedene Felder, und
  wer nur eine Kantenart formalisiert, formalisiert eine andere Domaene.
\<close>

definition kante :: "tabelle \<Rightarrow> (idx \<times> idx) set" where
  "kante \<sigma> =
     {(d, s). \<exists>sl. \<sigma> s = Some sl \<and> first_child sl = Some d} \<union>
     {(d, s). \<exists>sl. \<sigma> s = Some sl \<and> next_sibling sl = Some d}"

section \<open>N-2 -- der Zustand ist ein PARAMETER, und das ist die Grenze zu \<open>consuming.ordnung\<close>\<close>

text \<open>
  \<open>kante\<close> nimmt \<open>\<sigma>\<close>. Jedes Ergebnis dieser Theorie gilt fuer **einen** Zustand.

  Ueber eine Traversierung, die waehrend des Laufs mutiert (\<open>by consuming\<close>), sagt hier
  nichts etwas aus -- das ist Schablone \<open>consuming.ordnung\<close> (S1). Die alte Prosa-Fassung
  ("wohlfundiert und vollstaendig") nannte keinen Zustand und wurde deshalb gelesen, als
  deckte sie beides.
\<close>

section \<open>Das erzeugte Schema -- die eine Zeile, die der Erzeuger bekommt\<close>

text \<open>
  **Wohlfundiertheit ist HYPOTHESE, nicht Ergebnis.** Sie folgt nicht aus der Deklaration;
  die Deklaration muss die tragende Invariante nennen (\<open>invariant acyclic\<close>). Im Schema
  erscheint sie als Voraussetzung.
\<close>

lemma table_induktion:
  assumes wf: "wf (kante \<sigma>)"
  assumes schritt: "\<And>s. (\<And>d. (d, s) \<in> kante \<sigma> \<Longrightarrow> P d) \<Longrightarrow> P s"
  shows "P s"
  using wf schritt by (rule wf_induct_rule)

text \<open>
  **N-3 -- der Basisfall ist ABSORBIERT.** Fuer ein Blatt ist die Praemisse leer erfuellt;
  eine eigene Leere-Menge-Klausel braucht dieses Prinzip nicht. Der Beweis unten ist die
  Probe darauf: er benutzt \<open>schritt\<close> mit einer Voraussetzung, die nie eingeloest wird.
\<close>

lemma blatt_ohne_eigene_klausel:
  assumes wf: "wf (kante \<sigma>)"
  assumes schritt: "\<And>s. (\<And>d. (d, s) \<in> kante \<sigma> \<Longrightarrow> P d) \<Longrightarrow> P s"
  assumes blatt: "\<And>d. (d, s) \<notin> kante \<sigma>"
  shows "P s"
proof -
  have "\<And>d. (d, s) \<in> kante \<sigma> \<Longrightarrow> P d" using blatt by simp
  thus "P s" by (rule schritt)
qed

section \<open>N-4 -- die zwei Praemissen, ausgeschrieben\<close>

text \<open>
  Der Erzeuger schreibt aus \<open>kante\<close> nicht eine Praemisse, sondern zwei -- eine je Feld.
  Das folgende Lemma ist die Form, die er zu erzeugen hat; es faellt aus dem allgemeinen
  Schema, aber die ZERLEGUNG ist der Punkt: wer "das Schema" im Singular sagt, deckt sie
  sprachlich nicht ab.
\<close>

lemma table_induktion_zwei_kanten:
  assumes wf: "wf (kante \<sigma>)"
  assumes kind:
    "\<And>s sl. \<sigma> s = Some sl \<Longrightarrow>
       (\<And>d. first_child sl = Some d \<Longrightarrow> P d) \<Longrightarrow>
       (\<And>d. next_sibling sl = Some d \<Longrightarrow> P d) \<Longrightarrow> P s"
  assumes leer: "\<And>s. \<sigma> s = None \<Longrightarrow> P s"
  shows "P s"
proof (induct s rule: table_induktion[OF wf])
  case (1 s)
  show "P s"
  proof (cases "\<sigma> s")
    case None
    thus ?thesis by (rule leer)
  next
    case (Some sl)
    have "\<And>d. first_child sl = Some d \<Longrightarrow> P d"
      using 1 Some by (simp add: kante_def)
    moreover have "\<And>d. next_sibling sl = Some d \<Longrightarrow> P d"
      using 1 Some by (simp add: kante_def)
    ultimately show ?thesis using Some by (rule_tac kind, auto)
  qed
qed

section \<open>N-1 -- Endlichkeit faellt NICHT aus dieser Deklaration\<close>

text \<open>
  Die Traegermenge ist \<open>{i. i < N}\<close> -- **aber nur, wenn die Verkettungsfelder in der
  Tabelle bleiben.** Ein Feld, das hinauszeigt, verlaesst sie.

  Das ist die Pflicht einer ANDEREN Schablone: \<open>table.indexschranke\<close> (S12), \<open>index into T\<close>
  erbt seine Schranke aus \<open>count N\<close>. **Ohne sie ist die Endlichkeit nicht gegeben, und
  ohne Endlichkeit gibt es kein Mass** (Zahl der Abkoemmlinge), auf das sich die
  Wohlfundiertheit stuetzen liesse.

  Der Eintrag nannte diese Abhaengigkeit nicht.
\<close>

definition im_bereich :: "nat \<Rightarrow> tabelle \<Rightarrow> bool" where
  "im_bereich N \<sigma> \<longleftrightarrow>
     (\<forall>s sl. \<sigma> s = Some sl \<longrightarrow>
        (\<forall>d. first_child sl = Some d \<longrightarrow> d < N) \<and>
        (\<forall>d. next_sibling sl = Some d \<longrightarrow> d < N))"

lemma kante_bleibt_im_bereich:
  assumes "im_bereich N \<sigma>"
  assumes "(d, s) \<in> kante \<sigma>"
  shows "d < N"
  using assms by (auto simp: im_bereich_def kante_def)

lemma traeger_endlich:
  assumes "im_bereich N \<sigma>"
  shows "finite {d. \<exists>s. (d, s) \<in> kante \<sigma>}"
proof -
  have "{d. \<exists>s. (d, s) \<in> kante \<sigma>} \<subseteq> {i. i < N}"
    using assms kante_bleibt_im_bereich by blast
  moreover have "finite {i. i < N}" by simp
  ultimately show ?thesis by (rule finite_subset)
qed

end
