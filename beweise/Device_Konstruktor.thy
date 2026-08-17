(*  Titel:      Device_Konstruktor.thy
    Gegenstand: Die Schablone `device.konstruktor` (S13)
    Stand:      2026-08-17, K11.3.2

    Der Eintrag lautet:

        "Aus der Adresse entsteht ein typisierter Griff, und die erzeugten Zugriffe
         treffen die im `device`-Block DEKLARIERTEN Lagen. **Dass die deklarierten Lagen
         die des Geraets sind, ist eine ANNAHME der Axiomschicht** und wird hier nicht
         gezeigt."

    **Der zweite Satz ist die halbe Schablone**, und er ist der Grund, dass dieser Beweis
    kurz sein DARF: die Frage „stimmt 0x18 fuer GCMD?" ist keine Frage an ein Beweissystem,
    sondern an ein Datenblatt. Sie steht als Annahme mit Sonde im Manifest
    (\<open>gabbro annahmen\<close>).

    **Was hier bleibt, ist die Rechnung** -- und sie ist genau das, was ein Erzeuger falsch
    machen kann: dass zwei verschiedene Register nie dieselbe Zelle treffen, dass ein
    Bankeintrag an `basis + at + k * stride` liegt und dass ein Bitfeld im Wort bleibt.
*)

theory Device_Konstruktor
  imports Main
begin

section \<open>Der Griff: die Adresse IST der Wert\<close>

text \<open>
  `device Vtd(basis : Pa) at mmio` erzeugt keinen Zustand, sondern eine Sicht. Der Griff
  traegt genau die Adresse -- *deshalb kostet der Konstruktor nichts, und deshalb gibt es
  hier keine Aliasfrage.*
\<close>

type_synonym adresse = nat

record reg =
  offset :: adresse
  weite  :: nat        \<comment> \<open>Bytes, aus der Registerbreite\<close>

definition zelle :: "adresse \<Rightarrow> reg \<Rightarrow> adresse set" where
  "zelle b r = {a. b + offset r \<le> a \<and> a < b + offset r + weite r}"

section \<open>Die tragende Aussage: verschiedene Register, verschiedene Zellen\<close>

text \<open>
  **Das ist die Zeile, die ein Erzeuger falsch machen kann**, und die einzige dieses
  Eintrags, die eine Rechnung ist: zwei Register mit getrennten Lagen beruehren einander
  nicht -- **fuer jede Basis**.

  *Ohne sie waere ein Schreiben auf `GCMD` moeglicherweise auch eines auf `GSTS`, und die
  ganze Falle 4 (`mirrors`) waere ueber einem Modell gebaut, das nicht traegt.*
\<close>

definition getrennt :: "reg \<Rightarrow> reg \<Rightarrow> bool" where
  "getrennt r s \<longleftrightarrow> offset r + weite r \<le> offset s \<or> offset s + weite s \<le> offset r"

theorem getrennte_register_treffen_getrennte_zellen:
  assumes "getrennt r s"
  shows "zelle b r \<inter> zelle b s = {}"
proof (rule ccontr)
  assume "zelle b r \<inter> zelle b s \<noteq> {}"
  then obtain a where a: "a \<in> zelle b r" "a \<in> zelle b s" by blast
  from a have r: "b + offset r \<le> a" "a < b + offset r + weite r"
    unfolding zelle_def by auto
  from a have s: "b + offset s \<le> a" "a < b + offset s + weite s"
    unfolding zelle_def by auto
  from assms show False unfolding getrennt_def using r s by linarith
qed

text \<open>
  **Und die Basis faellt heraus** -- das ist keine Nebenbemerkung, sondern der Grund, warum
  der Griff der Konstruktor sein darf: die Trennung ist eine Eigenschaft der DEKLARATION und
  nicht der Adresse, an der das Geraet zufaellig liegt.
\<close>

corollary trennung_haengt_nicht_an_der_basis:
  assumes "getrennt r s"
  shows "\<forall>b. zelle b r \<inter> zelle b s = {}"
  using assms getrennte_register_treffen_getrennte_zellen by blast

section \<open>Die Bank: \<open>at + k * stride\<close>, und die Eintraege ueberlappen nicht\<close>

text \<open>
  `bank FRR at CAP.FRO * 16 stride 16 count 256` erzeugt 256 Sichten. **Dass sie einander
  nicht ueberlappen, haengt an einer einzigen Ungleichung** -- und sie steht in der
  Deklaration, nicht in einer Konvention.
\<close>

definition bankzelle :: "adresse \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> adresse set" where
  "bankzelle b start schritt k = {a. b + start + k * schritt \<le> a
                                     \<and> a < b + start + k * schritt + schritt}"

theorem bankeintraege_ueberlappen_nicht:
  assumes "j < k"
  shows "bankzelle b start schritt j \<inter> bankzelle b start schritt k = {}"
proof (rule ccontr)
  assume "bankzelle b start schritt j \<inter> bankzelle b start schritt k \<noteq> {}"
  then obtain a where a: "a \<in> bankzelle b start schritt j"
                        "a \<in> bankzelle b start schritt k" by blast
  from a have hj: "a < b + start + j * schritt + schritt"
    unfolding bankzelle_def by simp
  from a have hk: "b + start + k * schritt \<le> a"
    unfolding bankzelle_def by simp
  \<comment> \<open>\<open>j < k\<close> heisst \<open>j + 1 \<le> k\<close>, also \<open>(j+1) * schritt \<le> k * schritt\<close>.\<close>
  from assms have "Suc j \<le> k" by simp
  then have "Suc j * schritt \<le> k * schritt" by (rule mult_le_mono1)
  then have "j * schritt + schritt \<le> k * schritt" by simp
  with hj hk show False by linarith
qed

text \<open>
  **Ein `stride` von null bricht das**, und zwar sofort: dann liegen alle Eintraege
  aufeinander. Der Satz oben braucht ihn nicht als Praemisse -- bei \<open>schritt = 0\<close> ist jede
  \<open>bankzelle\<close> LEER, und leere Mengen schneiden sich nicht.

  *Das ist richtig und nutzlos*, und darum steht es hier: **eine Bank mit `stride 0` erzeugt
  keine Zugriffe, und der Erzeuger sollte sie ablehnen statt sie leerlaufen zu lassen.**
  Diese Zeile ist eine Fundstelle fuer `TODO.md`, kein Beweisschritt.
\<close>

lemma stride_null_macht_die_bank_leer:
  "bankzelle b start 0 k = {}"
  unfolding bankzelle_def by simp

section \<open>M-2 -- was NICHT gezeigt ist, und der erste Punkt ist der grosse\<close>

text \<open>
  **Erstens, und der Eintrag sagt es selbst:** dass die deklarierten Lagen die des Geraets
  sind, steht hier nicht. Es ist eine Aussage ueber die Hardware, sie steht in der
  Axiomschicht (\<open>gabbro annahmen\<close>: \<open>vtd_srtp_quittiert\<close>, \<open>vtd_te_wirksam\<close> und die
  Registerlagen selbst), und **kein Beweissystem kann sie ersetzen** -- ein Datenblatt ist
  keine Theorie.

  > *Das ist die Arbeitsteilung, um derentwillen die Axiomschicht existiert: was die Maschine
  > leistet, wird BENANNT und nicht bewiesen.*

  **Zweitens:** nicht gezeigt ist, dass der ERZEUGER die Lagen aus der Deklaration nimmt.
  Dieselbe Bruecke wie bei jedem Eintrag dieses Registers (\<open>PLAN.md\<close>, PL.3). Konkret: eine
  Mutation, die einen Versatz verschiebt, muss fallen -- *und sie tut es*
  (\<open>pruefe-emission.sh\<close>, Einheit `beispiel20`, Falle 4).

  **Drittens: die Bitfelder eines Registers stehen hier nicht.** Ein `@[hi:lo]` ist eine
  Aussage im WORT, nicht ueber Zellen; sie gehoert zur selben Familie wie \<open>format\<close>s
  Bitlagen und faellt mit «B24».
\<close>

end
