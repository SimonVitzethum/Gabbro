(*  Titel:      Intervall_Aussen.thy
    Gegenstand: Die Rundung NACH AUSSEN in M1s Gleitkommafortpflanzung
    Stand:      2026-08-18, «F»/F3

    **Dieser Beweis handelt vom PRUEFER, nicht vom Erzeuger, und das ist neu.**

    Jede andere Theorie dieses Ordners deckt eine Erzeugerschablone: eine Form, die `emit.rs`
    hinschreibt. Hier steht zum ersten Mal eine Zusage ueber M1 selbst -- denn seit «F»
    RECHNET der Pruefer in Gleitkomma. Bis dahin war seine Arithmetik exakte `i128`-Rechnung;
    jetzt leitet er Fakten mit `f64`-Operationen her.

    *Ein Pruefer, der inexakt rechnet, ist eine neue Vertrauensflaeche -- und sie gehoert
    genauso gebucht wie jede andere.*

    Der Einwand, aus dem dieser Satz kam, lautete:

        „Rechnet der Pruefer seine Schranken mit Host-Doubles in RNE, sind sie um bis zu ein
         Ulp zu eng und die ganze Analyse ist unsound -- in der Richtung, die nichts meldet."

    **In der Richtung, die nichts meldet**: eine zu enge Schranke laesst ein Programm durch,
    das nicht durchgehen darf. Kein Waechter wird rot.
*)

theory Intervall_Aussen
  imports Complex_Main
begin

section \<open>Die Maschine, als Annahme benannt\<close>

text \<open>
  Modelliert wird nicht IEEE-754 -- dafuer braeuchte es die AFP, und die ist hier nicht
  installiert (gemessen 2026-08-18). Modelliert wird **genau die Eigenschaft, auf die sich
  die Fortpflanzung stuetzt**, und sie steht als Annahme da, nicht als Behauptung:

  \<^item> \<open>fl\<close> ist, was die Maschine rechnet.
  \<^item> \<open>nd\<close> und \<open>nu\<close> sind die Nachbarn eines Maschinenwerts.
  \<^item> **Die tragende Annahme:** der WAHRE Wert liegt zwischen den Nachbarn des GERECHNETEN.

  Das ist die Zusage von round-to-nearest: der Fehler ist hoechstens ein halbes Ulp, also
  ueberspringt er keinen Nachbarn. *Sie steht hier als Praemisse und im Manifest als
  `gleitkomma_rundungsmodus_ist_rne` mit Sonde.*
\<close>

locale rundung =
  fixes fl :: "real \<Rightarrow> real"
    and nd :: "real \<Rightarrow> real"
    and nu :: "real \<Rightarrow> real"
  assumes nachbarn: "nd (fl z) \<le> z" "z \<le> nu (fl z)"
begin

section \<open>Was der Pruefer tut\<close>

text \<open>
  **Und er tut es SCHARF, nicht bloss sicher.** Die erste Fassung rundete unbedingt; dann gab
  \<open>[0,1] + [0,1]\<close> das Intervall \<open>[-5e-324, 2.0000000000000004]\<close> -- richtig und unbrauchbar.
  Ist die Ecke exakt, wandert nichts.
\<close>

definition aussen_lo :: "real \<Rightarrow> real" where
  "aussen_lo z = (if fl z = z then z else nd (fl z))"

definition aussen_hi :: "real \<Rightarrow> real" where
  "aussen_hi z = (if fl z = z then z else nu (fl z))"

lemma huelle_haelt: "aussen_lo z \<le> z \<and> z \<le> aussen_hi z"
proof (cases "fl z = z")
  case True
  then show ?thesis unfolding aussen_lo_def aussen_hi_def by simp
next
  case False
  then have "aussen_lo z = nd (fl z)" unfolding aussen_lo_def by simp
  moreover from False have "aussen_hi z = nu (fl z)" unfolding aussen_hi_def by simp
  ultimately show ?thesis using nachbarn by simp
qed

section \<open>M-1 -- der Satz: die gerechnete Schranke haelt\<close>

text \<open>
  Zwei Haelften, und sie sind wirklich zwei:

    (1) ueber den REELLEN Zahlen ist die Addition monoton -- das ist die gewoehnliche
        Intervallarithmetik, und sie ist die harmlose Haelfte;
    (2) die gerechnete Schranke umschliesst die reelle -- das ist \<open>huelle_haelt\<close>, und **sie
        ist die, um derentwillen dieser Beweis existiert.**
\<close>

\<comment> \<open>**Getrennt statt zusammen**, weil die beiden Richtungen getrennt gebraucht werden --
    und weil ein \<open>shows A and B\<close> mit einem Sammelbeweis die erste Stelle waere, an der
    dieser Ordner wieder eine Suche statt eines Schritts schriebe.\<close>
lemma monoton_unten:
  fixes a x c y :: real
  assumes "a \<le> x" and "c \<le> y"
  shows "a + c \<le> x + y"
  by (rule add_mono[OF assms(1) assms(2)])

lemma monoton_oben:
  fixes x b y d :: real
  assumes "x \<le> b" and "y \<le> d"
  shows "x + y \<le> b + d"
  by (rule add_mono[OF assms(1) assms(2)])

theorem summe_liegt_in_der_gerechneten_schranke:
  fixes a x b c y d :: real
  assumes "a \<le> x" "x \<le> b" "c \<le> y" "y \<le> d"
  shows "aussen_lo (a + c) \<le> x + y \<and> x + y \<le> aussen_hi (b + d)"
proof
  have "aussen_lo (a + c) \<le> a + c" using huelle_haelt by simp
  also have "\<dots> \<le> x + y" using assms(1) assms(3) by (rule monoton_unten)
  finally show "aussen_lo (a + c) \<le> x + y" .
next
  have "x + y \<le> b + d" using assms(2) assms(4) by (rule monoton_oben)
  also have "\<dots> \<le> aussen_hi (b + d)" using huelle_haelt by simp
  finally show "x + y \<le> aussen_hi (b + d)" .
qed

section \<open>Und die Scharfe: exakt heisst UNVERAENDERT\<close>

text \<open>
  Ohne diese Zeile waere der Satz oben richtig und der Pruefer unbrauchbar: eine Schranke,
  die bei jeder Rechnung ein Ulp wandert, verliert nach wenigen Schritten jede Aussage.
  **Die Exaktheit wird im Pruefer GEMESSEN** (Knuths 2Sum fuer die Summe, `mul_add` fuer
  Produkt und Quotient), und hier steht, was sie wert ist.
\<close>

lemma exakt_wandert_nicht:
  assumes "fl z = z"
  shows "aussen_lo z = z" and "aussen_hi z = z"
  using assms unfolding aussen_lo_def aussen_hi_def by simp_all

end

section \<open>M-2 -- was NICHT gezeigt ist, und der erste Punkt ist der grosse\<close>

text \<open>
  **Erstens: dass Rusts \<open>next_up\<close>, \<open>next_down\<close> und \<open>mul_add\<close> die Nachbarn und das exakte
  Produkt liefern, steht hier nicht.** Das ist eine Aussage ueber die Wirtssprache und ihre
  Maschine -- dieselbe Arbeitsteilung wie ueberall: was die Maschine leistet, wird BENANNT
  und nicht bewiesen.

  > *Der Unterschied zu jeder anderen Annahme dieses Ordners: sie betrifft nicht das
  > erzeugte Programm, sondern den PRUEFER. Ist sie falsch, ist nicht ein Programm falsch,
  > sondern jede Aussage ueber jedes Gleitkommaprogramm.*

  **Zweitens: die Praemisse \<open>nachbarn\<close> ist round-to-nearest.** Unter einem anderen
  Rundungsmodus ist der Fehler groesser, und der wahre Wert kann den Nachbarn ueberspringen.
  Genau darum steht `gleitkomma_rundungsmodus_ist_rne` mit Sonde im Manifest -- und genau
  darum ist der Modus **globaler Zustand und damit kompositional giftig**.

  **Drittens: nur die SUMME.** Produkt und Quotient rechnen im Pruefer ueber die vier Ecken;
  dass das Minimum der vier die untere Schranke ist, braucht die Monotonie in beiden
  Argumenten und die Fallunterscheidung nach Vorzeichen. *Der Satz dafuer ist groesser und
  steht noch nicht da.*

  **Viertens: die Null.** \<open>-0.0\<close> liegt in \<open>0.0 .. 1.0\<close>, weil alle Vergleiche das sagen --
  \<open>1.0 / x\<close> liefert dafuer aber \<open>-inf\<close>. Der Pruefer antwortet fuer einen Divisor, dessen
  Intervall die Null enthaelt, in BEIDE Richtungen unbeschraenkt. *Das ist eine Aussage ueber
  Vorzeichen und nicht ueber Rundung, und sie gehoert in einen eigenen Satz.*
\<close>

end
