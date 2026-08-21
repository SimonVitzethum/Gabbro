(*  Titel:      Gruppe_Erhaltung.thy
    Gegenstand: Die Schablonen `gruppe.ops` (S19) und `gruppe.sperrabdruck` (S20)
    Stand:      2026-08-19

    Beide gehoeren zum selben Konstrukt (`group N over { A, B }`) und stehen deshalb in
    EINER Theorie -- wie `Consuming.thy` fuer S1/S2.

    S20 fuehrt seine Pflicht bereits in drei benannten Teilen, und genau die werden hier
    Saetze:

        (a) die Reihenfolge ist die deklarierte -- sonst ist die DEADLOCKFREIHEIT des
            Bestands verloren, nicht bloss die Invariante
        (b) die Verbindungs-Invariante gilt am ANFANG und am ENDE des Zuges, NICHT
            zwischendrin -- der Zwischenzustand ist genau der Grund, warum es eine
            Gruppenoperation gibt
        (c) kein Zwischenaustritt verlaesst den Zug im Zwischenzustand

    S19 setzt S20 voraus (`haengt_an`) und sagt: die Verbindungs-Invariante bleibt unter
    jeder Gruppenoperation erhalten.

    WARUM DIESE THEORIE JETZT KOMMT: `Table_Ops_Erhaltung.thy` hat am selben Tag
    `verbindung_nicht_gedeckt` bewiesen -- eine Operation erhaelt jede Invariante IHRES
    Traegers und bricht die verbindende. Damit ist `gruppe.ops` NOTWENDIG und nicht bequem,
    und die Frage ist nicht mehr ob, sondern unter welcher Bedingung sie traegt.

    DER KERN, in einem Satz: die Invariante darf INNEN gebrochen sein. Was zaehlt, ist,
    dass sie an jeder Stelle gilt, an der sie BEOBACHTET werden kann -- und der Sperrabdruck
    ist genau das, was die Beobachtungsstellen auf Anfang und Ende einschraenkt.
*)

theory Gruppe_Erhaltung
  imports Main
begin

section \<open>Teil (a) -- die Rangordnung, und sie traegt mehr als die Invariante\<close>

text \<open>
  Der Eintrag sagt: *„sonst ist die Deadlockfreiheit des BESTANDS verloren, nicht bloss die
  Invariante."* Das ist die schaerfere Haelfte, und sie ist ein Satz ueber die Wartekanten.

  Eine Wartekante \<open>(r, s)\<close> heisst: jemand haelt eine Sperre mit Rang \<open>r\<close> und wartet auf
  eine mit Rang \<open>s\<close>. Nimmt jeder in aufsteigender Rangordnung, liegt jede Kante in
  \<open>less_than\<close>.
\<close>

theorem rangordnung_azyklisch:
  assumes "W \<subseteq> less_than"
  shows "acyclic W"
proof -
  have "wf W" using assms wf_less_than wf_subset by blast
  then show ?thesis by (rule wf_acyclic)
qed

text \<open>
  \<open>K-a1\<close> -- und die Gegenrichtung, damit der Satz nicht groesser aussieht als er ist:
  **eine einzige Kante gegen die Ordnung genuegt fuer einen Zyklus.**
\<close>

theorem eine_kante_gegen_die_ordnung_reicht:
  "\<not> acyclic {(0::nat, 1), (1, 0)}"
proof -
  have "(0::nat, 0) \<in> {(0::nat, 1), (1, 0)}\<^sup>+"
    by (rule trancl_into_trancl[of 0 1]) (auto intro: r_into_trancl)
  then show ?thesis unfolding acyclic_def by blast
qed

section \<open>Teil (b) -- der Zug: innen gebrochen, aussen ganz\<close>

text \<open>
  Ein Zug ist eine nichtleere Folge von Zustaenden. \<open>voll i\<close> heisst: in Schritt \<open>i\<close> haelt der
  Zieher den GANZEN Sperrabdruck der Gruppe -- und dann kann niemand sonst die Traeger
  ansehen.

  **Die Modellierung ist die Aussage:** die Invariante wird NICHT ueberall verlangt. Sie
  wird dort verlangt, wo jemand hinsehen kann.
\<close>

locale zug =
  fixes zs :: "'z list"
    and I :: "'z \<Rightarrow> bool"
    and voll :: "nat \<Rightarrow> bool"
  assumes nichtleer: "zs \<noteq> []"
      and anfang: "I (zs ! 0)"
      and ende:   "I (zs ! (length zs - 1))"
      and abdruck_innen: "\<lbrakk> 0 < i; i < length zs - 1 \<rbrakk> \<Longrightarrow> voll i"
begin

text \<open>
  Beobachtbar ist ein Schritt genau dann, wenn der Abdruck NICHT ganz gehalten wird --
  dann kann ein anderer Kern die Sperren nehmen und die Traeger zusammen ansehen.
\<close>

definition beobachtbar :: "nat \<Rightarrow> bool" where
  "beobachtbar i \<longleftrightarrow> i < length zs \<and> \<not> voll i"

text \<open>
  \<open>K-b1\<close> -- **der Hauptsatz.** An jeder beobachtbaren Stelle gilt die Invariante. Der
  Zwischenzustand ist erlaubt, weil er unsichtbar ist.
\<close>

theorem beobachtbares_gilt:
  assumes "beobachtbar i"
  shows "I (zs ! i)"
proof -
  from assms have grenze: "i < length zs" and offen: "\<not> voll i"
    unfolding beobachtbar_def by auto
  have "i = 0 \<or> i = length zs - 1"
    using offen abdruck_innen grenze by force
  then show ?thesis using anfang ende by auto
qed

end

text \<open>
  **Was der Satz NICHT sagt, und es steht hier statt in einer Fussnote:** dass der
  Sperrabdruck TATSAECHLICH gehalten wird. \<open>abdruck_innen\<close> ist eine Annahme des Locales,
  und sie herzustellen ist Sache des Pruefers -- \<open>U001\<close>-\<open>U005\<close> im Gruppenpass. *Bewiesen
  ist: WENN der Abdruck steht, dann ist der Zwischenzustand folgenlos.*

  **Und die zweite Haelfte, die bis zum 2026-08-21 gar keinen Ort hatte.** \<open>U001\<close>-\<open>U005\<close>
  stellen her, dass der Zieher die Sperren HAELT. Dass ein gehaltener Abdruck einen fremden
  Kern wirklich fernhaelt, stellen sie nicht her -- das ist eine Aussage ueber das
  SPEICHERMODELL, und keine Regel dieser Sprache kann sie pruefen.

  Sie heisst jetzt

    \<^item> \<open>sperrabdruck_haelt_fremde_kerne_fern\<close> -- Annahme der Axiomschicht, NICHT
      FALSIFIZIERBAR, mit Grund.

  und \<open>gabbro annahmen\<close> druckt sie, sobald eine \<open>group\<close> im Baum steht (\<open>manifest.rs\<close>,
  \<open>sperrabdruckannahme\<close>). *Damit sieht ein Leser dieses Beweises die Praemisse, statt sie zu
  unterstellen* -- vorher stand sie in \<open>gabbro schablonen\<close> als haengende Praemisse von
  \<open>gruppe.ops\<close> mit der Adresse \<^emph>\<open>braeuchte: die AXIOMSCHICHT\<close>, und die Adresse ist damit
  eingeloest.

  **Nicht falsifizierbar, und der Grund ist derselbe wie bei
  \<open>release_stellt_sichtbarkeit_her\<close>:** eine Sonde, die den Abdruck haelt und nachsieht, ob
  jemand hingesehen hat, zeigt nur, dass DIESMAL niemand hingesehen hat. Ein Speichermodell
  ist durch Ausfuehrung nicht widerlegbar. *Das macht die Annahme nicht kleiner -- es macht
  sie sichtbar, und genau das ist der Unterschied.*
\<close>

section \<open>Teil (c) -- der Zwischenaustritt, als Gegenbeispiel\<close>

text \<open>
  Der Eintrag verlangt: *kein Zwischenaustritt verlaesst den Zug im Zwischenzustand.* Warum
  das keine Vorsichtsmassnahme ist, sondern notwendig, zeigt ein Zug mit zwei Traegern.

  Die Verbindungs-Invariante ist \<open>fst = snd\<close>. Der Zug setzt erst den ersten Traeger, dann
  den zweiten. Bricht er nach dem ersten Schritt ab, endet er GEBROCHEN -- und die Stelle
  ist beobachtbar, weil ein Austritt die Sperren freigibt.
\<close>

definition paarig :: "nat \<times> nat \<Rightarrow> bool" where
  "paarig z \<longleftrightarrow> fst z = snd z"

definition ganzer_zug :: "(nat \<times> nat) list" where
  "ganzer_zug = [(0, 0), (1, 0), (1, 1)]"

definition abgebrochen :: "(nat \<times> nat) list" where
  "abgebrochen = [(0, 0), (1, 0)]"

lemma ganzer_zug_ist_einer: "zug ganzer_zug paarig (\<lambda>i. i = 1)"
proof (unfold_locales)
  show "ganzer_zug \<noteq> []" unfolding ganzer_zug_def by simp
  show "paarig (ganzer_zug ! 0)" unfolding ganzer_zug_def paarig_def by simp
  show "paarig (ganzer_zug ! (length ganzer_zug - 1))"
    unfolding ganzer_zug_def paarig_def by simp
  show "\<And>i. \<lbrakk> 0 < i; i < length ganzer_zug - 1 \<rbrakk> \<Longrightarrow> i = 1"
    unfolding ganzer_zug_def by simp
qed

text \<open>
  \<open>K-c1\<close> -- der abgebrochene Zug ist **kein** Zug: seine letzte Stelle verletzt die
  Invariante, und `ende` ist genau die Bedingung, die das ausschliesst.
\<close>

theorem zwischenaustritt_bricht:
  "\<not> paarig (abgebrochen ! (length abgebrochen - 1))"
  unfolding abgebrochen_def paarig_def by simp

theorem abgebrochener_ist_kein_zug:
  "\<not> zug abgebrochen paarig f"
proof
  assume "zug abgebrochen paarig f"
  then have "paarig (abgebrochen ! (length abgebrochen - 1))"
    by (rule zug.ende)
  with zwischenaustritt_bricht show False by simp
qed

section \<open>Teil S20 -- ZWEI Sperren sind nicht eine, und das ist die eigentliche Pflicht\<close>

text \<open>
  Der Eintrag begruendet, warum \<open>gruppe.sperrabdruck\<close> eine ZWEITE Schablone ist: *„unter
  einer Sperre ist die Erhaltung ein sequenzielles Argument, unter zweien haengt sie an der
  Ordnung und daran, dass zwischen den zwei Nahmen kein fremder Schreiber dazwischenkommt."*

  Formal: haelt der Zieher im Zwischenschritt nur EINEN Teil des Abdrucks, ist der Schritt
  nach obiger Definition beobachtbar -- und dann greift \<open>beobachtbares_gilt\<close> nicht mehr,
  sondern verlangt die Invariante genau dort, wo sie gebrochen ist.
\<close>

theorem halber_abdruck_ist_kein_zug:
  "\<not> zug ganzer_zug paarig (\<lambda>i. False)"
proof
  assume z: "zug ganzer_zug paarig (\<lambda>i. False)"
  have "(0::nat) < 1" and "(1::nat) < length ganzer_zug - 1"
    unfolding ganzer_zug_def by simp_all
  from zug.abdruck_innen[OF z this] show False by simp
qed

text \<open>
  **Die Lesart, und sie ist der Grund fuer S20:** ein Zug ueber Traegern mit VERSCHIEDENEN
  Sperren hat einen Zwischenschritt, in dem nur ein Teil des Abdrucks steht. Das Locale
  laesst sich dann nicht erfuellen -- nicht weil der Beweis schwerer waere, sondern weil die
  Voraussetzung falsch ist.

  \<^item> Unter EINER Sperre: der Abdruck steht ab dem ersten Nehmen, \<open>abdruck_innen\<close> gilt.
  \<^item> Unter ZWEIEN: zwischen den beiden Nahmen steht er nicht.

  *Deshalb verlangt (a) die aufsteigende Rangordnung UND das Halten ueber den ganzen Zug --
  zwei Forderungen, nicht eine, und der Satz oben zeigt, dass die zweite unabhaengig ist.*
\<close>

section \<open>Was hier NICHT steht\<close>

text \<open>
  \<^item> **Kein Erzeuger.** Es gibt keine Gruppen-\<open>ops\<close>; \<open>U001\<close>-\<open>U007\<close> pruefen die FORM, in der
    die Frage gestellt werden kann, und nicht die Erhaltung. *Bewiesen ist die Mathematik
    der Schablone, nicht ihre Auslieferung* -- derselbe Satz wie bei \<open>table.induktion\<close> und
    \<open>table.ops.erhaltung\<close>.
  \<^item> **Kein Speichermodell.** \<open>voll i\<close> heisst hier \<open>der Abdruck ist gehalten\<close>. Dass ein
    gehaltener Abdruck einen fremden Kern wirklich fernhaelt, ist eine Aussage der
    Axiomschicht und faellt nicht in diesen Satz. **Seit dem 2026-08-21 hat sie dort einen
    NAMEN** -- \<open>sperrabdruck_haelt_fremde_kerne_fern\<close> -- und steht in der Annahmenmenge
    jedes Erzeugnisses mit einer \<open>group\<close>. *Der Satz sagt sie weiterhin nicht; er
    unterstellt sie nur nicht mehr stillschweigend.*
  \<^item> **Keine Aussage ueber die Zahl der Traeger.** Die Gegenbeispiele nehmen zwei; das
    Locale nimmt beliebige Zustaende.
\<close>

end
