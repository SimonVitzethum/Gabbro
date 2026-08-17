(*  Titel:      Option_Sonderwert.thy
    Gegenstand: Die Schablone `option.sonderwert` (S1)
    Stand:      2026-08-17

    Der Eintrag lautet:

        "Der Sonderwert `N` liegt AUSSERHALB der Indexdomaene `0 ..< N`, und keine
         erzeugte Rechnung erreicht ihn. Damit ist die Absenkung von
         `option index into T` auf ein blankes Maschinenwort verlustfrei: jeder
         gueltige Index ist von `None` unterscheidbar. **Zu zeigen ist beides** --
         die Disjunktheit UND dass keine Operation den Sonderwert erzeugen kann."

    Die Schablone ist am 2026-08-17 entstanden, als der Erzeuger F8 absenkte und fuer
    `option index into T` eine Darstellung waehlen musste. Sie steht als GETRAGEN im
    Register -- der Uebersetzer stuetzt sich JETZT darauf, nicht irgendwann.
*)

theory Option_Sonderwert
  imports Main
begin

section \<open>Die Kodierung\<close>

text \<open>
  \<open>table T count N\<close> erzeugt \<open>index into T\<close> mit dem Wertebereich \<open>{i. i < N}\<close>
  (\<open>Table_Indexschranke.thy\<close>). \<open>option index into T\<close> senkt der Erzeuger auf DASSELBE
  Maschinenwort ab und schreibt \<open>N\<close> selbst als \<open>None\<close>:

    \<^verbatim>\<open>#define T_NONE (N)\<close>

  Die Behauptung \<open>verlustfrei\<close> heisst genau: diese Kodierung ist injektiv.
\<close>

type_synonym idx = nat

definition indextyp :: "nat \<Rightarrow> idx set" where
  "indextyp N = {i. i < N}"

definition kodiere :: "nat \<Rightarrow> idx option \<Rightarrow> nat" where
  "kodiere N x = (case x of None \<Rightarrow> N | Some i \<Rightarrow> i)"

section \<open>Die erste Haelfte: Disjunktheit -- und sie ist trivial\<close>

text \<open>
  **Das gehoert gesagt, statt es als Ergebnis zu verkaufen.** Dass \<open>N \<notin> {i. i < N}\<close> gilt,
  ist eine Zeile. Der Eintrag fuehrt es als halbe Pflicht, und als Pflicht ist es zu klein.
\<close>

lemma sonderwert_ausserhalb: "N \<notin> indextyp N"
  unfolding indextyp_def by simp

text \<open>Der Gehalt liegt eine Stufe weiter: die Kodierung ist auf dem gueltigen Bereich injektiv.\<close>

lemma kodiere_injektiv:
  assumes "\<forall>i. x = Some i \<longrightarrow> i \<in> indextyp N"
  assumes "\<forall>i. y = Some i \<longrightarrow> i \<in> indextyp N"
  assumes "kodiere N x = kodiere N y"
  shows "x = y"
proof (cases x)
  case None
  then show ?thesis
  proof (cases y)
    case (Some j)
    then have "j < N" using assms(2) unfolding indextyp_def by simp
    moreover from None Some assms(3) have "N = j" unfolding kodiere_def by simp
    ultimately show ?thesis by simp
  qed (simp add: None)
next
  case (Some i)
  then have "i < N" using assms(1) unfolding indextyp_def by simp
  then show ?thesis
  proof (cases y)
    case None
    from Some None assms(3) have "i = N" unfolding kodiere_def by simp
    with \<open>i < N\<close> show ?thesis by simp
  next
    case (Some j)
    with \<open>x = Some i\<close> assms(3) show ?thesis unfolding kodiere_def by simp
  qed
qed

section \<open>M-1 -- die PRAEMISSE, die der Eintrag nicht nennt: das Maschinenwort\<close>

text \<open>
  **Ausgespuelt, und es ist der Ertrag dieser Formalisierung.**

  Der Eintrag redet ueber \<open>N\<close> und die Menge \<open>{i. i < N}\<close> -- also ueber natuerliche Zahlen.
  Der Erzeuger schreibt aber ein \<^verbatim>\<open>uint32_t\<close>, und dort rechnet alles modulo \<open>2^w\<close>.

  **Ist \<open>N = 2^w\<close>, faellt der Sonderwert auf null** -- und null ist der ERSTE gueltige Slot.
  Die Kodierung ist dann nicht mehr injektiv: \<open>None\<close> und \<open>Some 0\<close> sind dasselbe Wort.
\<close>

definition kodiere_wort :: "nat \<Rightarrow> nat \<Rightarrow> idx option \<Rightarrow> nat" where
  "kodiere_wort w N x = (kodiere N x) mod (2 ^ w)"

lemma sonderwert_kollidiert_bei_vollem_wort:
  assumes "N = 2 ^ w"
  assumes "N > 0"
  shows "kodiere_wort w N None = kodiere_wort w N (Some 0)"
  using assms unfolding kodiere_wort_def kodiere_def by simp

text \<open>
  **Und mit der Praemisse gilt die Zusage.** Sie lautet \<open>N < 2^w\<close> -- die Tabelle muss ECHT
  kuerzer sein als das Maschinenwort, das ihren Index traegt.
\<close>

lemma kodiere_wort_injektiv:
  assumes klein: "N < 2 ^ w"
  assumes gx: "\<forall>i. x = Some i \<longrightarrow> i \<in> indextyp N"
  assumes gy: "\<forall>i. y = Some i \<longrightarrow> i \<in> indextyp N"
  assumes gleich: "kodiere_wort w N x = kodiere_wort w N y"
  shows "x = y"
proof -
  have schranke: "kodiere N z < 2 ^ w"
    if "\<forall>i. z = Some i \<longrightarrow> i \<in> indextyp N" for z
    using that klein unfolding kodiere_def indextyp_def
    by (cases z) auto
  from schranke[OF gx] schranke[OF gy] gleich
  have "kodiere N x = kodiere N y"
    unfolding kodiere_wort_def by simp
  with gx gy show ?thesis by (rule kodiere_injektiv)
qed

text \<open>
  > **Die Praemisse stand nirgends.** Weder im Registereintrag noch im Erzeuger noch in
  > \<open>SPRACHE.md\<close>. Sie ist in der Praxis erfuellt -- \<open>count 80256\<close> gegen \<open>2^32\<close> -- aber
  > *erfuellt* und *geprueft* sind zwei verschiedene Zustaende, und der Ordner hat fuer den
  > Unterschied schon bezahlt.
\<close>

section \<open>M-2 -- die zweite Haelfte ist NICHT bewiesen, und sie ist die eigentliche\<close>

text \<open>
  **Ausgespuelt, als GRENZE.** Der Eintrag verlangt zweierlei, und nur das erste steht oben:

    1. die Disjunktheit -- hier, mit der ausgespuelten Praemisse \<open>N < 2^w\<close>;
    2. **dass keine erzeugte Rechnung den Sonderwert erreicht.**

  Das zweite ist eine Aussage ueber \<open>emit.rs\<close>, nicht ueber eine Menge. Sie laesst sich hier
  hinschreiben, aber nicht beweisen -- ihr Gegenstand ist ein Programm, das in Rust steht:

    \<open>\<forall>Operation o des Erzeugers. \<forall>x. x \<in> Bild(kodiere N) \<longrightarrow> o(x) \<in> Bild(kodiere N)\<close>

  **Was sich HEUTE sagen laesst, und es ist mehr als am 2026-08-16:** die Flaeche ist klein
  und aufzaehlbar. Der Erzeuger gibt fuer einen \<open>option\<close>-Wert genau zwei Formen aus --
  den Vergleich gegen \<open>T_NONE\<close> und die Bindung des \<open>Some\<close>-Zweigs -- und **weigert sich
  (\<open>C001\<close>) fuer \<open>None\<close> als Ausdruck**, weil er dafuer die Zieltabelle nicht kennt.

  *Solange er sich weigert, kann keine Rechnung den Sonderwert HERSTELLEN.* Das ist keine
  Beweisfuehrung, sondern eine Beobachtung ueber eine heute enge Flaeche -- und sie faellt
  in dem Augenblick, in dem \<open>None\<close> als Wert abgesenkt wird.
\<close>

section \<open>Was daraus folgt\<close>

text \<open>
  Die Schablone bleibt **unbewiesen**, und zwar mit Grund: eine Haelfte ist gezeigt (mit einer
  neuen Praemisse), die andere hat ihren Gegenstand ausserhalb von Isabelle.

  **Zu tun, in dieser Reihenfolge:**

    * \<open>N < 2^w\<close> als Pruefung in den Erzeuger -- heute prueft es niemand;
    * den Eintrag im Register um die Praemisse ergaenzen;
    * die zweite Haelfte offen fuehren, statt sie mit der ersten zu verrechnen.
\<close>

end
