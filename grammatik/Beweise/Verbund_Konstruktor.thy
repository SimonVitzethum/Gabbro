(*  Titel:      Verbund_Konstruktor.thy
    Gegenstand: Die Schablone `verbund.konstruktor` (S18)
    Stand:      2026-08-17

    Der Eintrag lautet:

        "Der aus der Felderliste erzeugte Konstruktor setzt jedes Feld genau einmal
         und laesst keins uninitialisiert."

    **Warum sie VOR dem Konstrukt bewiesen wird und nicht danach.** K100 traegt zwei Tore:
    `H -> 0` und `L <= 4` (lebend unbewiesene Schablonen). Das Verbundliteral («B7») zu bauen
    macht diesen Eintrag von `Entworfen` zu `Getragen` -- der Uebersetzer stuetzt sich dann
    darauf -- und damit ginge `L` auf 5.

    > *Ein Plan, der nur `H` verfolgt, erreicht 100 % und ist danach schlechter dran.*
*)

theory Verbund_Konstruktor
  imports Main
begin

section \<open>Die Felderliste und der erzeugte Konstruktor\<close>

text \<open>
  Ein `structty` ist eine Liste benannter Felder. Der Konstruktor bekommt je Feld einen
  Ausdruck -- als Zuordnung \<open>Feldname \<rightarrow> Wert\<close>. Die Zusage besteht aus zwei Haelften, und
  der Eintrag fuehrt sie in einem Satz:

    1. \<open>setzt jedes Feld genau einmal\<close>
    2. \<open>laesst keins uninitialisiert\<close>
\<close>

type_synonym feld = string

definition wohlgeformt :: "feld list \<Rightarrow> bool" where
  "wohlgeformt fs \<longleftrightarrow> distinct fs"

definition deckt :: "feld list \<Rightarrow> (feld \<times> 'v) list \<Rightarrow> bool" where
  "deckt fs zs \<longleftrightarrow> map fst zs = fs"

section \<open>M-1 -- die zwei Haelften sind EINE, sobald die Deklaration wohlgeformt ist\<close>

text \<open>
  **Ausgespuelt.** Der Eintrag liest sich wie zwei Pflichten. Sie fallen zusammen: wenn die
  Zuordnungsliste genau die Feldliste als Schluesselfolge hat, ist beides zugleich erfuellt --
  *keins doppelt* und *keins fehlend*.

  **Das ist keine Trivialitaet, sondern die Aussage, warum ein ERZEUGTER Konstruktor sicherer
  ist als ein geschriebener:** der Erzeuger legt \<open>map fst zs = fs\<close> per Bau fest, waehrend ein
  Mensch beides einzeln falsch machen kann.
\<close>

lemma deckt_setzt_jedes_genau_einmal:
  assumes "wohlgeformt fs"
  assumes "deckt fs zs"
  shows "distinct (map fst zs) \<and> set (map fst zs) = set fs"
  using assms unfolding wohlgeformt_def deckt_def by simp

text \<open>
  **Die zwei Schritte hier standen zuerst als \<open>metis\<close> da, und einer von beiden ist
  divergiert** -- der Poly/ML-Prozess lief neun Minuten und stand bei 6,3 GB, bevor ich ihn
  angehalten habe. *Ein Beweisschritt, der ohne Schranke sucht, ist dieselbe Bauart wie eine
  Schleife ohne \<open>bounded\<close>* -- und der Ordner hat dafuer drei Schleifenformen.

  Ersetzt durch strukturierte Schritte: sie sagen, WELCHER Weg genommen wird, statt einen
  suchen zu lassen.
\<close>

lemma deckt_laesst_keins_aus:
  assumes dk: "deckt fs zs"
  assumes drin: "f \<in> set fs"
  shows "\<exists>v. (f, v) \<in> set zs"
proof -
  from dk drin have "f \<in> set (map fst zs)" unfolding deckt_def by simp
  then have "f \<in> fst ` set zs" by simp
  then obtain p where p1: "p \<in> set zs" and p2: "fst p = f" by auto
  show ?thesis
  proof (cases p)
    case (Pair a b)
    with p1 p2 show ?thesis by auto
  qed
qed

section \<open>Die Ablesung ist eindeutig -- und DAS ist der Gehalt\<close>

text \<open>
  Der eigentliche Satz: unter der Deckung liefert die Ablesung eines Feldes **genau den Wert,
  den der Konstruktor dort hingeschrieben hat**. Ohne ihn waere \<open>setzt jedes Feld\<close> eine
  Aussage ueber eine Liste statt ueber einen Verbund.
\<close>

definition liest :: "(feld \<times> 'v) list \<Rightarrow> feld \<Rightarrow> 'v option" where
  "liest zs f = map_of zs f"

lemma ablesung_ist_eindeutig:
  assumes wf: "wohlgeformt fs"
  assumes dk: "deckt fs zs"
  assumes drin: "(f, v) \<in> set zs"
  shows "liest zs f = Some v"
proof -
  from wf dk have "distinct (map fst zs)"
    unfolding wohlgeformt_def deckt_def by simp
  with drin show ?thesis
    unfolding liest_def by (simp add: map_of_is_SomeI)
qed

lemma jedes_feld_hat_einen_wert:
  assumes "wohlgeformt fs"
  assumes "deckt fs zs"
  assumes "f \<in> set fs"
  shows "\<exists>v. liest zs f = Some v"
proof -
  from assms(2,3) have "f \<in> set (map fst zs)"
    unfolding deckt_def by simp
  then have "f \<in> fst ` set zs" by simp
  then have "map_of zs f \<noteq> None" by (simp add: map_of_eq_None_iff)
  then show ?thesis unfolding liest_def by auto
qed

section \<open>M-2 -- was die Schablone NICHT deckt, und es gehoert dazugesagt\<close>

text \<open>
  **Ausgespuelt, als GRENZE.** Gezeigt ist: *wenn* die Zuordnungsliste die Feldliste deckt,
  ist der Verbund vollstaendig und eindeutig belegt.

  **Nicht gezeigt ist, dass der ERZEUGER \<open>deckt\<close> herstellt.** Das ist eine Aussage ueber
  `emit.rs` und `parse.rs` -- dieselbe Lage wie bei \<open>option.sonderwert\<close>, M-2. Sie faellt in
  die Bruecke, die \<open>PLAN.md\<close> unter PL.3 fuehrt: **je Satz eine Sprechprobe, die den Rust
  gegen das Modell faehrt.**

  Konkret heisst das hier: eine Mutation, die ein Feld **doppelt** oder **gar nicht** setzt,
  muss fallen. *Der Satz sagt, welche Beschaedigung das ist -- und ohne ihn wusste es niemand.*

  **Zweitens, und es ist eine Entwurfsfrage, keine Luecke:** \<open>deckt\<close> verlangt die
  REIHENFOLGE der Deklaration (\<open>map fst zs = fs\<close>), nicht bloss dieselbe Menge. Das ist die
  strengere Fassung. Sie ist hier gewaehlt, weil eine Felderliste in einem `format` ohnehin
  eine Reihenfolge IST -- und weil eine Zuordnung, die nur die Menge trifft, beim Leser
  aussieht wie die Deklaration und es nicht ist.
\<close>

end
