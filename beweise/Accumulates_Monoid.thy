(*  Titel:      Accumulates_Monoid.thy
    Gegenstand: Die Schablone `accumulates.monoid` (S9)
    Stand:      2026-08-17, K11.3.2

    Der Eintrag lautet:

        "Die Merge-Menge ist ein kommutatives Monoid (mechanisch pruefbar).
         **Die Absenkung ergibt denselben Wert wie ein atomares RMW nur an einem
         RUHEPUNKT** -- nebenlaeufig gelesen tut sie es nicht, und das ist keine
         Ungenauigkeit, sondern der Preis der Absenkung."

    **Der zweite Satz ist der wichtigere**, und er ist der Grund, dass dieser Beweis den
    ersten nicht bloss abhakt: `accumulates x : u64 merge max` senkt zu EINER ZELLE JE KERN
    ab, und das Lesen faltet sie. Ohne CAS, ohne unbegrenzte Schleife -- und ohne die
    Gleichheit mit einem atomaren RMW zu jedem Zeitpunkt.

    *Was gezeigt wird: dass die Faltung wohldefiniert ist, in beliebiger Reihenfolge
    dasselbe liefert, und dass sie am Ruhepunkt mit der sequentiellen Fassung
    uebereinstimmt.*
*)

theory Accumulates_Monoid
  imports Main "HOL-Library.Multiset"
begin

section \<open>Die vier erlaubten Verknuepfungen\<close>

text \<open>
  `merge` nimmt genau \<open>max\<close>, \<open>min\<close>, \<open>add\<close>, \<open>or\<close> oder \<open>and\<close>. **Der Wortschatz ist
  geschlossen, und das ist der Grund, warum die Eigenschaft mechanisch pruefbar IST:** eine
  offene Menge von Verknuepfungen waere eine Zusage ueber etwas, das der Nutzer erst noch
  hinschreibt.

  Modelliert wird die gemeinsame Struktur, nicht jede einzeln: **kommutatives Monoid** --
  assoziativ, kommutativ, mit neutralem Element.
\<close>

locale merge_monoid =
  fixes verknuepft :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70)
    and neutral :: 'a
  assumes assoz: "(a \<oplus> b) \<oplus> c = a \<oplus> (b \<oplus> c)"
      and komm:  "a \<oplus> b = b \<oplus> a"
      and links: "neutral \<oplus> a = a"
begin

lemma rechts: "a \<oplus> neutral = a"
  using komm links by simp

section \<open>Die Faltung ueber den Kernen\<close>

text \<open>
  Die Absenkung legt je Kern eine Zelle an; das Lesen faltet sie mit \<open>\<oplus>\<close>. **Die Zahl der
  Kerne ist beschraenkt (`NCORES`), also ist die Schleife beschraenkt** -- genau der Grund,
  warum `accumulates` ohne CAS auskommt.
\<close>

primrec faltet :: "'a list \<Rightarrow> 'a" where
  "faltet [] = neutral"
| "faltet (x # xs) = x \<oplus> faltet xs"

lemma faltet_anhaengen: "faltet (xs @ ys) = faltet xs \<oplus> faltet ys"
proof (induct xs)
  case Nil
  show ?case by (simp add: links)
next
  case (Cons x xs)
  have "faltet ((x # xs) @ ys) = x \<oplus> faltet (xs @ ys)" by simp
  also have "\<dots> = x \<oplus> (faltet xs \<oplus> faltet ys)" using Cons by simp
  also have "\<dots> = (x \<oplus> faltet xs) \<oplus> faltet ys" using assoz by simp
  finally show ?case by simp
qed

section \<open>Der Satz: die REIHENFOLGE der Kerne ist gleichgueltig\<close>

text \<open>
  **Das ist die Zusage, um derentwillen `merge` eine geschlossene Menge ist.** Die Zellen
  werden in irgendeiner Reihenfolge gelesen -- der erzeugte Code laeuft von 0 bis NCORES,
  aber welcher Kern wann geschrieben hat, steht nicht fest.

  *Waere \<open>\<oplus>\<close> nicht kommutativ, haenge das Ergebnis an der Leserichtung, und die Absenkung
  waere von der Deklaration nicht mehr gedeckt.*
\<close>

lemma faltet_vertauschen: "faltet (x # y # xs) = faltet (y # x # xs)"
proof -
  have "faltet (x # y # xs) = x \<oplus> (y \<oplus> faltet xs)" by simp
  also have "\<dots> = (x \<oplus> y) \<oplus> faltet xs" using assoz by simp
  also have "\<dots> = (y \<oplus> x) \<oplus> faltet xs" using komm by simp
  also have "\<dots> = y \<oplus> (x \<oplus> faltet xs)" using assoz by simp
  finally show ?thesis by simp
qed

theorem faltung_ist_reihenfolgeunabhaengig:
  assumes "mset xs = mset ys"
  shows "faltet xs = faltet ys"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  \<comment> \<open>\<open>mset [] = mset ys\<close> heisst \<open>ys = []\<close> -- der Schritt wird GEFUEHRT statt gesucht.\<close>
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a as)
    \<comment> \<open>Ein Element auf der einen Seite, keines auf der anderen -- ueber die TRAEGERMENGE.\<close>
    from \<open>mset [] = mset ys\<close> have "set ([] :: 'a list) = set ys"
      by (rule mset_eq_setD)
    with Cons have False by simp
    then show ?thesis ..
  qed
next
  case (Cons x xs)
  from Cons.prems have "x \<in> set ys"
  proof -
    have "x \<in># mset (x # xs)" by simp
    with Cons.prems have "x \<in># mset ys" by simp
    then show ?thesis by simp
  qed
  then obtain as bs where ys: "ys = as @ x # bs" by (meson split_list)
  from Cons.prems ys have "mset xs = mset (as @ bs)" by simp
  with Cons.hyps have ih: "faltet xs = faltet (as @ bs)" by simp
  have "faltet ys = faltet as \<oplus> (x \<oplus> faltet bs)"
    using ys faltet_anhaengen by simp
  also have "\<dots> = x \<oplus> (faltet as \<oplus> faltet bs)"
    using assoz komm by metis
  also have "\<dots> = x \<oplus> faltet (as @ bs)" using faltet_anhaengen by simp
  finally show ?case using ih by simp
qed

section \<open>M-1 -- der Ruhepunkt, und er ist die eigentliche Aussage\<close>

text \<open>
  Am **Ruhepunkt** -- kein Kern schreibt mehr -- liefert die Faltung dasselbe wie eine
  sequentielle Kette atomarer RMW-Schritte auf einer einzigen Zelle. *Das ist die Gleichung,
  die die Absenkung rechtfertigt.*
\<close>

primrec rmw_kette :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "rmw_kette z [] = z"
| "rmw_kette z (x # xs) = rmw_kette (z \<oplus> x) xs"

lemma rmw_kette_zieht_heraus: "rmw_kette z xs = z \<oplus> faltet xs"
proof (induct xs arbitrary: z)
  case Nil
  show ?case by (simp add: rechts)
next
  case (Cons x xs)
  have "rmw_kette z (x # xs) = rmw_kette (z \<oplus> x) xs" by simp
  also have "\<dots> = (z \<oplus> x) \<oplus> faltet xs" using Cons by simp
  also have "\<dots> = z \<oplus> (x \<oplus> faltet xs)" using assoz by simp
  finally show ?case by simp
qed

theorem am_ruhepunkt_gleich_dem_atomaren_rmw:
  "rmw_kette neutral xs = faltet xs"
  using rmw_kette_zieht_heraus links by simp

end

section \<open>Die vier Verknuepfungen sind wirklich Monoide\<close>

text \<open>
  **Eine Struktur zu behaupten und keine Instanz zu zeigen, waere eine Zusage ueber die leere
  Menge.** Darum steht hier je Verknuepfung der Nachweis -- und `min` ist die interessante:
  ihr Neutrales ist das MAXIMUM des Typs, nicht die Null.

  *An genau der Stelle wuerde ein Erzeuger, der `0` als Startwert nimmt, jedes `min` auf null
  ziehen.*
\<close>

interpretation acc_max: merge_monoid "max :: nat \<Rightarrow> nat \<Rightarrow> nat" 0
  by unfold_locales (auto simp: max.assoc max.commute)

interpretation acc_add: merge_monoid "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat" 0
  by unfold_locales auto

interpretation acc_or: merge_monoid "(\<or>)" False
  by unfold_locales auto

interpretation acc_and: merge_monoid "(\<and>)" True
  by unfold_locales auto

text \<open>
  \<open>min\<close> ueber \<open>nat\<close> hat kein neutrales Element -- es gaebe keine groesste Zahl. **Ueber
  einem Maschinenwort hat es eines: das Vollbild.** Hier steht es an einem endlichen Typ,
  und das ist genau die Lage in Gabbro (`u8`…`u64`).
\<close>

lemma min_ist_monoid_mit_top:
  fixes a b c :: "'a::{linorder, order_top}"
  shows assoz: "min (min a b) c = min a (min b c)"
    and komm:  "min a b = min b a"
    and links: "min top a = a"
proof -
  show "min (min a b) c = min a (min b c)" by (auto simp: min_def)
  show "min a b = min b a" by (auto simp: min_def)
  \<comment> \<open>**Der letzte Fall ist der, um dessentwillen dieser Satz an einem BESCHRAENKTEN Typ
      steht.** \<open>min top a = a\<close> braucht, dass \<open>top\<close> obere Schranke ist -- und genau diese
      Eigenschaft fehlt \<open>nat\<close>. *Ein Erzeuger, der `min` mit `0` anfangen laesst, zieht
      jedes Ergebnis auf null.*\<close>
  \<comment> \<open>**Hier ist der Ordner zum zweiten Mal in eine Suche gelaufen** -- ein \<open>blast\<close>
      ueber \<open>top_unique\<close>, 12 Minuten, 4,8 GB. Der Schritt steht jetzt geschrieben:
      \<open>top_unique\<close> ist eine UMSCHREIBUNG (\<open>top \<le> a \<longleftrightarrow> a = top\<close>), keine Suchaufgabe.\<close>
  show "min top a = a"
  proof (cases "top \<le> a")
    case True
    then have "a = top" by (simp add: top_unique)
    with True show ?thesis by (simp add: min_def)
  next
    case False
    then show ?thesis by (simp add: min_def)
  qed
qed

section \<open>M-2 -- was NICHT gezeigt ist, und der Eintrag nennt es selbst\<close>

text \<open>
  **Nebenlaeufig gelesen stimmt die Faltung NICHT mit einem atomaren RMW ueberein.** Der Satz
  oben hat den Ruhepunkt als Praemisse (\<open>xs\<close> ist eine feste Liste), und das ist keine
  Ungenauigkeit dieses Beweises, sondern **der Preis der Absenkung**: wer waehrend des Lesens
  schreibt, wird beim naechsten Lesen gezaehlt und nicht bei diesem.

  > *Der Eintrag sagt es, und dieser Beweis macht es formal sichtbar, statt es zu verstecken.*

  **Zweitens:** nicht gezeigt ist, dass der ERZEUGER je Kern eine Zelle anlegt und mit dem
  richtigen Neutralen anfaengt. Dieselbe Bruecke wie ueberall (\<open>PLAN.md\<close>, PL.3) -- und hier
  hat sie eine benannte Falle: **`min` mit `0` als Startwert zieht jedes Ergebnis auf null.**
  Die Mutation, die das tut, muss fallen.

  **Drittens:** die Zahl der Kerne ist hier eine Listenlaenge. Dass sie beschraenkt IST,
  faellt aus `NCORES` und gehoert dem Kostenpass, nicht dieser Schablone.
\<close>

end
