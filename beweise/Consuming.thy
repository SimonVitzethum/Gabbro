(*  Titel:      Consuming.thy
    Gegenstand: Die Schablonen `consuming.ordnung` (S1) und `consuming.leermenge` (S2)
    Stand:      2026-08-16

    Beide gehoeren zum selben Konstrukt (`traverse … by consuming`) und stehen deshalb in
    einer Theorie. S1 haengt an S4 (`table.induktion`) -- der Zyklus, der am 2026-08-16
    gebucht wurde: die Ordnung braucht das Schema, das Schema braucht die Ordnung fuer den
    mutierenden Fall.

    S1: "Die Domaene liefert ihre Zeugen in der erzeugten wohlfundierten Ordnung, und die
         Ordnung bleibt unter der erzeugten Mutation erhalten. Daraus faellt die Blattheit
         zum Verbrauchszeitpunkt."
    S2: "Die erzeugte Zeugenmenge ist VOLLSTAENDIG: ist sie leer, ist die Domaene leer."
*)

theory Consuming
  imports Table_Induktion
begin

section \<open>Die Mutation, die \<open>by consuming\<close> erzeugt\<close>

text \<open>
  Der Rumpf verbraucht den gerade besuchten Zeugen. Als Zustandsuebergang: der Platz wird
  frei.
\<close>

definition verbrauche :: "tabelle \<Rightarrow> idx \<Rightarrow> tabelle" where
  "verbrauche \<sigma> v = (\<lambda>i. if i = v then None else \<sigma> i)"

section \<open>K-1 -- \<open>die Ordnung bleibt erhalten\<close> haelt fuer das ENTFERNEN, und nur dafuer\<close>

text \<open>
  Die eine Haelfte ist leicht, und sie steht hier, damit die andere sichtbar wird: entfernt
  man einen Platz, wird die Kantenmenge **kleiner**, und eine Teilmenge einer wohlfundierten
  Relation ist wohlfundiert.
\<close>

lemma verbrauche_verkleinert:
  "kante (verbrauche \<sigma> v) \<subseteq> kante \<sigma>"
  unfolding kante_def verbrauche_def by auto

lemma ordnung_bleibt_unter_entfernen:
  assumes "wf (kante \<sigma>)"
  shows "wf (kante (verbrauche \<sigma> v))"
  using assms verbrauche_verkleinert by (rule wf_subset)

text \<open>
  **K-1, ausgespuelt.** Der Eintrag sagt \<open>unter der erzeugten Mutation\<close> -- Singular, ohne zu
  nennen, WELCHE. Der Beweis oben deckt genau eine: das **Entfernen**. Er deckt nicht das
  **Umhaengen**.

  Und das ist kein Randfall: der Bestand macht beides in einem Zug. \<open>delete_leaf\<close> ruft
  \<open>unlink\<close>, und \<open>unlink\<close> schreibt die Geschwisterzeiger der NACHBARN um (B3, Marke Nb2:
  \<open>space.rs:1044\<close>). **Eine Mutation, die Kanten HINZUFUEGT, ist von \<open>wf_subset\<close> nicht
  gedeckt** -- sie kann einen Zyklus erzeugen.

  Der naechste Abschnitt zeigt, dass die Zusage dort wirklich faellt.
\<close>

section \<open>K-2 -- Umhaengen ist NICHT gedeckt, und hier ist das Gegenbeispiel\<close>

definition haenge_um :: "tabelle \<Rightarrow> idx \<Rightarrow> idx \<Rightarrow> tabelle" where
  "haenge_um \<sigma> i d =
     (\<lambda>j. if j = i
          then (case \<sigma> j of None \<Rightarrow> None
                | Some sl \<Rightarrow> Some (sl \<lparr> next_sibling := Some d \<rparr>))
          else \<sigma> j)"

lemma umhaengen_kann_zyklus_erzeugen:
  "\<exists>\<sigma> i d. wf (kante \<sigma>) \<and> \<not> wf (kante (haenge_um \<sigma> i d))"
proof -
  define sl0 where "sl0 = \<lparr> first_child = None, next_sibling = None \<rparr>"
  define \<sigma> where "\<sigma> = (\<lambda>j. if j = (0::idx) then Some sl0 else None)"
  have leer: "kante \<sigma> = {}"
    unfolding kante_def \<sigma>_def sl0_def by auto
  hence wf0: "wf (kante \<sigma>)" by simp
  \<comment> \<open>Jetzt haengt der Platz 0 auf sich selbst um: eine Schlinge.\<close>
  have "(0, 0) \<in> kante (haenge_um \<sigma> 0 0)"
    unfolding kante_def haenge_um_def \<sigma>_def sl0_def by simp
  hence "\<not> wf (kante (haenge_um \<sigma> 0 0))"
    by (meson wf_not_refl)
  with wf0 show ?thesis by blast
qed

text \<open>
  **Damit ist die Zusage in ihrer Wortfassung widerlegt.** \<open>die Ordnung bleibt unter der
  erzeugten Mutation erhalten\<close> gilt fuer das Entfernen und **nicht** fuer das Umhaengen --
  und der Bestand tut beides in derselben Operation.

  Die tragfaehige Fassung nennt die Mutationen einzeln und verlangt fuer die
  hinzufuegenden einen **eigenen** Erhaltungsbeweis.
\<close>

section \<open>K-3 -- \<open>daraus faellt die Blattheit\<close> faellt NICHT daraus\<close>

text \<open>
  Blattheit zum Verbrauchszeitpunkt: der verbrauchte Platz hat keine Kinder mehr.
\<close>

definition ist_blatt :: "tabelle \<Rightarrow> idx \<Rightarrow> bool" where
  "ist_blatt \<sigma> v \<longleftrightarrow> (\<forall>d. (d, v) \<notin> kante \<sigma>)"

text \<open>
  **Ausgespuelt.** Aus \<open>wf\<close> allein folgt sie nicht. \<open>wf\<close> sagt, dass **minimale Elemente
  existieren** -- nicht, dass die Traversierung eines davon **nimmt**. Eine Traversierung,
  die einen inneren Knoten zuerst verbraucht, ist mit \<open>wf\<close> vertraeglich und laesst
  Abkoemmlinge verwaist zurueck.

  Die fehlende Bedingung hat einen Namen: die Auswahl ist **minimal**.
\<close>

definition waehlt_minimal :: "tabelle \<Rightarrow> idx \<Rightarrow> bool" where
  "waehlt_minimal \<sigma> v \<longleftrightarrow> (\<forall>d. (d, v) \<notin> kante \<sigma>)"

lemma blattheit_braucht_minimale_auswahl:
  assumes "waehlt_minimal \<sigma> v"
  shows "ist_blatt \<sigma> v"
  using assms unfolding waehlt_minimal_def ist_blatt_def by simp

text \<open>
  Der Satz oben ist **eine Umbenennung, kein Beweis** -- und genau das ist der Befund: die
  Blattheit ist keine FOLGE der Wohlfundiertheit, sondern eine **zusaetzliche Pflicht an die
  Erzeugung der Zeugenreihenfolge**. Der Eintrag sagte \<open>daraus faellt\<close>; sie faellt nicht,
  sie ist zu zeigen.
\<close>

section \<open>S2 -- \<open>consuming.leermenge\<close>\<close>

text \<open>
  \<open>Ist die erzeugte Zeugenmenge leer, ist die Domaene leer.\<close> Als Aussage ueber die Kante:
  liefert die Erzeugung keinen Zeugen, gibt es auch keine Kante.
\<close>

definition zeugen :: "tabelle \<Rightarrow> idx \<Rightarrow> idx set" where
  "zeugen \<sigma> s = {d. (d, s) \<in> kante \<sigma>}"

lemma leermenge:
  "zeugen \<sigma> s = {} \<longleftrightarrow> (\<forall>d. (d, s) \<notin> kante \<sigma>)"
  unfolding zeugen_def by blast

text \<open>
  **S2 geht glatt durch, und das war vorhergesagt** (0--1). Die Aussage ist eine
  Aequivalenz und faellt in einer Zeile.

  **Eine Nebenbedingung faellt trotzdem ab, und sie ist dieselbe wie N-2 bei S4:** \<open>zeugen\<close>
  nimmt den Zustand als Parameter. Der Eintrag sagt \<open>ist sie leer, ist die Domaene leer\<close>
  ohne Zustand -- und in einer VERBRAUCHENDEN Traversierung ist genau das die Frage: leer
  **wann**? Vor dem Zug, oder nach dem letzten Verbrauch?
\<close>

lemma leermenge_ist_zustandsabhaengig:
  "\<exists>\<sigma> v s. zeugen \<sigma> s \<noteq> {} \<and> zeugen (verbrauche \<sigma> v) s = {}"
proof -
  define sl_kind where "sl_kind = \<lparr> first_child = None, next_sibling = None \<rparr>"
  define sl_eltern where "sl_eltern = \<lparr> first_child = Some (1::idx), next_sibling = None \<rparr>"
  define \<sigma> where
    "\<sigma> = (\<lambda>j. if j = (0::idx) then Some sl_eltern else if j = 1 then Some sl_kind else None)"
  have "(1, 0) \<in> kante \<sigma>"
    unfolding kante_def \<sigma>_def sl_eltern_def by simp
  hence a: "zeugen \<sigma> 0 \<noteq> {}" unfolding zeugen_def by blast
  have "kante (verbrauche \<sigma> 0) = {}"
    unfolding kante_def verbrauche_def \<sigma>_def sl_eltern_def sl_kind_def by auto
  hence b: "zeugen (verbrauche \<sigma> 0) 0 = {}" unfolding zeugen_def by simp
  from a b show ?thesis by blast
qed

end
