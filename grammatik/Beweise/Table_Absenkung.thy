(*  Titel:      Table_Absenkung.thy
    Gegenstand: Die Schablone `table.absenkung` (S15)
    Stand:      2026-08-17, K11.3.2

    Der Eintrag lautet:

        "Die Absenkung legt genau N Slots an -- nicht weniger (dann waere ein Index im
         Typ ohne Speicher) und nicht mehr (dann waere Speicher ohne Index, den keine
         Schranke deckt)."

    **Warum dieser zuerst.** Er ist einer von vier LEBEND getragenen Saetzen: der
    Uebersetzer stuetzt sich JETZT darauf, und ist er falsch, ist das erzeugte C falsch --
    ab dem naechsten Lauf. Von den vieren ist er der, auf dem die anderen aufsitzen:
    `option.sonderwert` braucht die Laenge, um den Sonderwert zu setzen, und
    `table.induktion` braucht die Schranke, um zu terminieren.

    **Und er haengt an `table.indexschranke`** (dort bewiesen, 2026-08-14). Dieser Beweis
    setzt dessen Ergebnis als Voraussetzung ein, statt es zu wiederholen -- eine
    Schablonenliste ohne Abhaengigkeiten sieht aus wie unabhaengige Posten und ist es nicht.
*)

theory Table_Absenkung
  imports Main
begin

section \<open>Der Indextyp und das erzeugte Feld\<close>

text \<open>
  `table T count N` erzeugt zweierlei: den Indextyp \<open>{i. i < N}\<close> (das ist
  `table.indexschranke`, dort bewiesen) und ein C-Feld \<open>T_slot slots[N]\<close>.

  **Der Gegenstand hier ist die ZAHL, und nur sie.** Was in einem Slot steht, ist die Sache
  der Felder; dass es *ihn* gibt, ist die Sache dieser Schablone.

  Ein C-Feld der Laenge \<open>m\<close> hat die gueltigen Indizes \<open>{i. i < m}\<close> -- das ist die
  Sprachdefinition von C und keine Annahme dieses Beweises.
\<close>

definition indextyp :: "nat \<Rightarrow> nat set" where
  "indextyp N = {i. i < N}"

definition feldindizes :: "nat \<Rightarrow> nat set" where
  "feldindizes m = {i. i < m}"

section \<open>M-1 -- die beiden Haelften, und sie sind wirklich zwei\<close>

text \<open>
  Der Eintrag nennt zwei Fehlrichtungen, und der Beweis nimmt sie einzeln:

    1. \<open>m < N\<close> -- ein Index im Typ ohne Speicher. **Das ist der gefaehrliche.**
    2. \<open>m > N\<close> -- Speicher ohne Index. Harmloser, aber nicht harmlos.

  *Sie zusammen als \<open>m = N\<close> hinzuschreiben waere richtig und wuerde verschweigen, dass die
  beiden Richtungen verschieden teuer sind.*
\<close>

lemma zu_kurz_laesst_einen_index_ohne_speicher:
  assumes "m < N"
  shows "\<exists>i \<in> indextyp N. i \<notin> feldindizes m"
proof -
  from assms have "m \<in> indextyp N" unfolding indextyp_def by simp
  moreover have "m \<notin> feldindizes m" unfolding feldindizes_def by simp
  ultimately show ?thesis by blast
qed

lemma zu_lang_laesst_speicher_ohne_index:
  assumes "N < m"
  shows "\<exists>i \<in> feldindizes m. i \<notin> indextyp N"
proof -
  from assms have "N \<in> feldindizes m" unfolding feldindizes_def by simp
  moreover have "N \<notin> indextyp N" unfolding indextyp_def by simp
  ultimately show ?thesis by blast
qed

text \<open>
  Und die Zusage selbst: **genau \<open>N\<close> heisst, dass die beiden Mengen zusammenfallen** --
  jeder Index hat Speicher und jeder Speicher hat einen Index.
\<close>

theorem absenkung_deckt_genau:
  "feldindizes m = indextyp N \<longleftrightarrow> m = N"
proof
  assume "feldindizes m = indextyp N"
  then have gleich: "{i. i < m} = {i. i < N}"
    unfolding feldindizes_def indextyp_def by simp
  show "m = N"
  proof (rule ccontr)
    assume "m \<noteq> N"
    then consider "m < N" | "N < m" by linarith
    then show False
    proof cases
      case 1
      from 1 have "m \<in> {i. i < N}" by simp
      with gleich have "m \<in> {i. i < m}" by simp
      then show False by simp
    next
      case 2
      from 2 have "N \<in> {i. i < m}" by simp
      with gleich have "N \<in> {i. i < N}" by simp
      then show False by simp
    qed
  qed
next
  assume "m = N"
  then show "feldindizes m = indextyp N"
    unfolding feldindizes_def indextyp_def by simp
qed

section \<open>Der Gehalt: JEDER Zugriff des erzeugten C liegt im Feld\<close>

text \<open>
  Der Eintrag liest sich wie eine Aussage ueber eine Zahl. **Der Gehalt liegt eine Stufe
  weiter**, und ohne ihn waere die Zahl Buchhaltung: aus \<open>m = N\<close> und der Indexschranke
  faellt, dass **kein** Zugriff des erzeugten Programms aus dem Feld laeuft.

  \<open>M103\<close> stellt sicher, dass jeder Index im Typ liegt (das ist `table.indexschranke`,
  Voraussetzung hier). Diese Schablone stellt sicher, dass der Typ ins Feld passt. *Erst
  beide zusammen sind die Aussage, um derentwillen die Absenkung ein festes Feld nimmt und
  keinen Zeiger mit Laenge.*
\<close>

theorem kein_zugriff_laeuft_aus_dem_feld:
  assumes laenge: "m = N"
  assumes m103:   "i \<in> indextyp N"      \<comment> \<open>aus \<open>table.indexschranke\<close>\<close>
  shows "i \<in> feldindizes m"
  using assms absenkung_deckt_genau by blast

text \<open>
  **Und die Umkehrung gilt NICHT, und das gehoert dazugesagt:** aus \<open>i \<in> feldindizes m\<close>
  folgt nicht, dass der Slot BELEGT ist. Das ist genau die Grenze, die
  `table.indexschranke` unter M-2 fuehrt -- *der Typ enthaelt jeden belegten Slot und deckt
  ihn nicht genau.*
\<close>

section \<open>M-2 -- was diese Schablone NICHT deckt\<close>

text \<open>
  **Erstens, und es ist dieselbe Grenze wie bei \<open>option.sonderwert\<close>:** gezeigt ist, dass
  eine Absenkung mit \<open>m = N\<close> genau deckt. **Nicht gezeigt ist, dass der ERZEUGER \<open>m = N\<close>
  herstellt.** Das ist eine Aussage ueber `emit.rs`, und sie faellt in die Bruecke
  (\<open>PLAN.md\<close>, PL.3).

  Konkret heisst das hier: **eine Mutation, die die Feldlaenge von der Kapazitaet loest,
  muss fallen.** Der Satz sagt, welche Beschaedigung das ist.

  **Zweitens, und es ist eine PRAEMISSE und keine Luecke:** \<open>N\<close> muss in eine
  C-Feldlaenge passen. Der Erzeuger weigert sich fuer eine `table` ohne `count`
  (*„the array would have no size"*), und `option.sonderwert` fuehrt die verwandte
  Praemisse \<open>N < 2^32\<close> fuer den Sonderwert. **Hier ist sie schwaecher und steht
  trotzdem da**: ohne sie waere \<open>feldindizes m\<close> eine Menge ueber einer Zahl, die keine
  Maschine hinschreibt.

  **Drittens:** ueber die BELEGUNG sagt diese Schablone nichts, ueber den INHALT eines
  Slots nichts, und ueber die Ausrichtung des C-Feldes nichts. *Wer eine Layoutzusage
  braucht, braucht ein `format` -- und das ist ein anderer Eintrag.*
\<close>

end
