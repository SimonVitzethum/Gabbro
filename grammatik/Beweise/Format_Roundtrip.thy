(*  Titel:      Format_Roundtrip.thy
    Gegenstand: Die Schablone `format.roundtrip` (S11)
    Stand:      2026-08-17, K11.3.2

    Der Eintrag lautet:

        "(1) `lesen(schreiben(x)) == x` fuer jedes darstellbare x.
         (2) Der Leser prueft die Pufferlaenge einmal am Eintritt -- das gilt nur fuer
             FESTE Laengen. Bei variablen faellt die Schranke erst aus dem Inhalt, und
             dann ist je Feld zu pruefen."

    **Der zweite Satz ist keine Nebenbedingung, sondern die halbe Schablone**, und er ist
    der Grund, warum sie hier in zwei Teilen steht: die Rundreise ist eine Aussage ueber
    WERTE, die Einmalpruefung eine ueber ZUGRIFFE.

    **Und der Erzeuger senkt ein `format` bewusst NICHT zu einem C-Verbund ab** (`emit.rs`):
    ein Format ist eine Zusage ueber BYTES, ein C-Verbund waere eine ueber ein Layout, das
    die Deklaration nicht macht. Dieser Beweis handelt darum von einer Bytefolge und einer
    Ablesefunktion, nicht von einem Verbund.
*)

theory Format_Roundtrip
  imports Main
begin

section \<open>Der feste Fall: Feld an Versatz, Breite aus der Deklaration\<close>

text \<open>
  Ein `format` mit festen Laengen ist eine Liste von Feldern, jedes mit Versatz und Breite.
  \<open>lesen\<close> schneidet die Bytes heraus, \<open>schreiben\<close> legt sie hin.

  **Modelliert wird die Bytefolge als Abbildung \<open>nat \<Rightarrow> byte\<close> mit einer Laenge** -- nicht
  als Liste, weil der erzeugte C-Leser einen Zeiger und eine Laenge bekommt und genau so
  darauf zugreift.
\<close>

type_synonym byte = nat
type_synonym puffer = "nat \<Rightarrow> byte"

record feld =
  versatz :: nat
  breite  :: nat

definition liest :: "puffer \<Rightarrow> feld \<Rightarrow> byte list" where
  "liest p f = map p [versatz f ..< versatz f + breite f]"

definition schreibt :: "puffer \<Rightarrow> feld \<Rightarrow> byte list \<Rightarrow> puffer" where
  "schreibt p f bs = (\<lambda>i. if versatz f \<le> i \<and> i < versatz f + breite f
                          then bs ! (i - versatz f) else p i)"

section \<open>(1) Die Rundreise\<close>

lemma roundtrip:
  assumes "length bs = breite f"
  shows "liest (schreibt p f bs) f = bs"
proof -
  have entpackt: "liest (schreibt p f bs) f
        = map (\<lambda>i. bs ! (i - versatz f)) [versatz f ..< versatz f + breite f]"
    unfolding liest_def schreibt_def by simp
  \<comment> \<open>**Der Schritt steht geschrieben, statt gesucht zu werden.** Ein \<open>metis\<close> ist an
      dieser Stelle schon einmal divergiert (\<open>Verbund_Konstruktor.thy\<close>, neun Minuten,
      6,3 GB) -- *ein Beweisschritt ohne Schranke ist dieselbe Bauart wie eine Schleife
      ohne \<open>bounded\<close>.*\<close>
  show ?thesis
  proof (subst entpackt, rule nth_equalityI)
    show "length (map (\<lambda>i. bs ! (i - versatz f))
                      [versatz f ..< versatz f + breite f]) = length bs"
      using assms by simp
  next
    fix k
    assume k: "k < length (map (\<lambda>i. bs ! (i - versatz f))
                                [versatz f ..< versatz f + breite f])"
    then have kn: "k < breite f" by simp
    have "map (\<lambda>i. bs ! (i - versatz f)) [versatz f ..< versatz f + breite f] ! k
          = bs ! ([versatz f ..< versatz f + breite f] ! k - versatz f)"
      using kn by simp
    also have "[versatz f ..< versatz f + breite f] ! k = versatz f + k"
      using kn by simp
    finally show "map (\<lambda>i. bs ! (i - versatz f))
                      [versatz f ..< versatz f + breite f] ! k = bs ! k"
      by simp
  qed
qed

text \<open>
  **Und die Rundreise ruht auf der LAENGE, nicht auf dem Wohlwollen.** Passt der Wert nicht
  in die deklarierte Breite, ist \<open>bs ! k\<close> fuer \<open>k \<ge> length bs\<close> unbestimmt -- genau der
  Fall, den M1 an der Schreibstelle abfaengt (`M101`) und den diese Schablone deshalb als
  PRAEMISSE fuehrt statt ihn zu behaupten.
\<close>

section \<open>Die Trennung der Felder -- ohne sie waere die Rundreise wertlos\<close>

text \<open>
  Ein Format hat mehr als ein Feld. **Die Rundreise oben gilt je Feld; dass ein Schreiben in
  das eine das andere nicht zerstoert, ist eine eigene Aussage** -- und sie ist die, die ein
  Erzeuger falsch machen kann, indem er zwei Versaetze ueberlappen laesst.
\<close>

definition trennt :: "feld \<Rightarrow> feld \<Rightarrow> bool" where
  "trennt f g \<longleftrightarrow> versatz f + breite f \<le> versatz g \<or> versatz g + breite g \<le> versatz f"

lemma schreiben_stoert_getrennte_felder_nicht:
  assumes "trennt f g"
  shows "liest (schreibt p f bs) g = liest p g"
proof -
  have "\<forall>i \<in> set [versatz g ..< versatz g + breite g].
          schreibt p f bs i = p i"
  proof
    fix i assume "i \<in> set [versatz g ..< versatz g + breite g]"
    then have i: "versatz g \<le> i" "i < versatz g + breite g" by auto
    \<comment> \<open>Der Widerspruch wird GEFUEHRT, nicht gesucht: liegt \<open>i\<close> in beiden Feldern, sind
        sie nicht getrennt.\<close>
    have "\<not> (versatz f \<le> i \<and> i < versatz f + breite f)"
    proof
      assume a: "versatz f \<le> i \<and> i < versatz f + breite f"
      from assms show False unfolding trennt_def using i a by linarith
    qed
    then show "schreibt p f bs i = p i" unfolding schreibt_def by auto
  qed
  then show ?thesis unfolding liest_def by simp
qed

section \<open>(2) Die Einmalpruefung -- und WARUM sie nur fuer feste Laengen gilt\<close>

text \<open>
  Der erzeugte Leser prueft die Pufferlaenge **einmal am Eintritt**: passt das letzte Byte des
  letzten Feldes hinein, passen alle. *Das ist eine Rechnung ueber Konstanten, und genau
  deshalb faellt sie zur Uebersetzungszeit.*
\<close>

definition passt :: "feld list \<Rightarrow> nat \<Rightarrow> bool" where
  "passt fs n \<longleftrightarrow> (\<forall>f \<in> set fs. versatz f + breite f \<le> n)"

lemma eintrittspruefung_deckt_jeden_zugriff:
  assumes "passt fs n"
  assumes "f \<in> set fs"
  assumes "i \<in> set [versatz f ..< versatz f + breite f]"
  shows "i < n"
proof -
  from assms(3) have "i < versatz f + breite f" by simp
  moreover from assms(1,2) have "versatz f + breite f \<le> n" unfolding passt_def by simp
  ultimately show ?thesis by linarith
qed

text \<open>
  **Und hier liegt die Grenze, die der Eintrag selbst nennt.** Die Pruefung oben quantifiziert
  ueber eine FESTE Felderliste. Haengt ein Versatz vom INHALT ab -- ein Laengenfeld, das die
  Lage des naechsten bestimmt --, ist \<open>fs\<close> keine Konstante mehr, und \<open>passt fs n\<close> laesst sich
  am Eintritt nicht auswerten.

  *Formal: die Praemisse waere \<open>passt (fs p) n\<close> mit \<open>fs\<close> als Funktion des Puffers -- und dann
  ist sie keine Eintrittspruefung, sondern je Feld eine.*

  **Solange variable Laengen offen sind, deckt diese Schablone nur den festen Fall**, und der
  Erzeuger weigert sich fuer alles andere.
\<close>

section \<open>M-2 -- was NICHT gezeigt ist\<close>

text \<open>
  **Erstens, und es ist dieselbe Grenze wie ueberall in diesem Register:** gezeigt ist, dass
  eine Absenkung mit getrennten Feldern und geprueftem Puffer die Rundreise haelt. **Nicht
  gezeigt ist, dass der ERZEUGER die Felder getrennt legt.** Das ist eine Aussage ueber
  `emit.rs`, und sie faellt in die Bruecke (\<open>PLAN.md\<close>, PL.3).

  Konkret: **eine Mutation, die zwei Versaetze ueberlappen laesst, muss fallen** --
  \<open>schreiben_stoert_getrennte_felder_nicht\<close> sagt, welche Beschaedigung das ist.

  **Zweitens: die BYTEREIHENFOLGE steht hier nicht.** \<open>liest\<close> gibt eine Byteliste; ob aus
  ihr `little` oder `big` ein Wort wird, ist die Sache der erzeugten Wortleser. *Sie
  hierhineinzuziehen wuerde den Satz vergroessern, ohne ihn zu staerken -- die Rundreise gilt
  fuer jede feste Abbildung Byteliste \<open>\<rightarrow>\<close> Wort, solange sie umkehrbar ist.*

  **Drittens: Bitlagen sind ABGELEHNT, nicht ungeprueft** («B24»). Was eine Bitposition
  jenseits der Wortbreite bedeutet und wie sie mit `endian` zusammenwirkt, sagt die
  Spezifikation nicht -- und der Erzeuger weigert sich benannt, statt es zu raten.
\<close>

end
