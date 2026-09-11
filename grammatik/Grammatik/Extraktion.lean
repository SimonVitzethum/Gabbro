/-
  Datei:      Grammatik/Extraktion.lean
  Gegenstand: **DIE FUSSABDRUECKE ALS RECHNUNG** -- aus den Ruempfen gerechnet, nicht
              erklaert: die Rufkanten aus den Rufen im Rumpf (W-EXT), die
              Fussabdrucklisten aus den Effekten, die Paarliste aus der
              Nebenlauffassung; das Ergebnis IST `Geteilt.Bau` (kein Spiegel mehr),
              die Brennstoff-Rechnung IST `Geteilt.schrittBis`/`traegerBis`, die
              Paarform IST `Nebeneinander` (`Wettlauf.lean` §6), und die Anknuepfung
              steht als Satz daneben (die Treue-Saetze und die Einspeisung in
              `geteilt_treu`/`ungeteilt_aus_baulauf`).

  ZIEL (Bahn 38, Entwurf; Bahn 78 verdrahtet): Die Schnitte C2/C3 aus
  `Geteilt.lean` schliessen -- dort sind `schreibtFn` je Funktion und `neben`
  als Paarliste DEKLARIERT (getragen, nicht gerechnet). Hier steht die Rechnung:
  `ruftDirekt` traversiert `Programm.rumpf` (W-EXT, §2), `ruftNorm`/`kantenListe`
  schraenken auf die erklaerte Funktionsdomaene ein, `fussAus` liest die
  Effektpraedikate ueber der erklaerten Traegerdomaene, `nebenAus` schraenkt die
  erklaerte Paarliste auf die Eintritte ein, und `bauAus` baut daraus den
  `Geteilt.Bau`. Was der Pruefer heute per Hand schreibt (`H013`), rechnet
  kuenftig diese Datei aus dem Rumpf.

  VERDRAHTET (Bahn 78 -- kein Spiegel mehr):
    `Geteilt.Bau` statt `BauSpiegel` (Feld fuer Feld derselbe Typ, jetzt derselbe
      Term: `bauAus` liefert `Geteilt.Bau`);
    `Geteilt.schrittBis`/`traegerBis`/`ErreichtBau`/`BauLauf` statt der
      `…Spiegel`-Rechnungen (`laufGedeckt`/`nurPaareLaufen` sind die zwei
      Haelften von `Geteilt.BauLauf`, `bauLaufSpiegel_genau` ist `Iff.rfl`);
    `Nebeneinander` statt `Nat → Nat → Prop` (definitionell dasselbe:
      `Faden` IST `Nat`).

  SCHNITTE (gebucht, nicht versteckt):
  S1. Kodierung: `D.Fn`, `D.Tab`, `D.Glob` sind beliebige Typen, `Geteilt.Bau`
      spricht ueber Zahlen. Die Bruecke sind explizite Parameter
      (`fnCode`/`tabCode`/`globCode`); wo die Rechnung Eindeutigkeit braucht
      (Marken-Nachschlagen: `geteiltTab_trifft`, `geteiltAus_tab`), steht sie
      als Praemisse am Satz (`hinj`), nicht als Axiom im Baum. Die Trennung der
      Traegerhaelften leistet `hdisj` (kein Tab-Code trifft einen Glob-Code);
      `geteilt_treu` unterscheidet erst dort wieder Tabelle/Global.
  S2. W-EXT (die Traversierung, §2): `ruftDirekt` traversiert `Stmt`/`Block`/
      `Endblock`/`Arms`/`GrundArms` und sammelt `Stmt.call`, `Block.bindCall`,
      `Block.bindCallElse` als Kanten; `callInd` (Zeigerruf), `bindCallInd` und
      `axiomCall`/`bindAxiom` (fremder Rumpf) liefern KEINE Kante -- ein
      Zeigerruf faellt damit aus der Huelle, und der Pruefer muss ihn
      verweigern (fail-closed, wie `W003`), nicht raten. `kantenVoll` nennt
      diese Verweigerungspflicht beim Namen.
  S3. Lesen: `effects` erklaert nur Schreiben (`schreibt`/`gschreibt`); eine
      Lesehuelle (`slot`/`glob` in `Expr`) steht nirgends und fehlt hier -- fuer
      (W5) genuegt Schreiben (Erreichen heisst Beruehren zum Schreiben), fuer
      das Zwei-Faden-Modell (`Interferenz.lean`: disjunkte Rahmen) muss sie
      dazu.
  S4. Haengende Paare: `nebenAus` wirft Paare ausserhalb der Eintritte weg --
      `paarVoll_aus_bau` nennt die Pflicht des Pruefers als Praemissen
      (`hvoll`, `hbound`): was faellt, wird verweigert, nicht verschwiegen.
  S5. Unbekannt heisst geteilt: `geteiltAus` antwortet `true` ausserhalb der
      Tabellen -- fail-closed in die Richtung, in der ein Irrtum laut wird
      (`geteilt_treu` verlangt dann den Waechter statt der Einzigkeit);
      `geteiltAus_fremd` beweist es.

   Kern nur: kein `mathlib`, kein `sorry` -- nur `def` und `theorem`, und
   beides ueber den echten Typen (`Geteilt.Bau`, `Programm`, `Nebeneinander`).

   NACHTRAG (Bahn 84, Entwurf -- §12): Die Lesehuelle steht jetzt als Rechnung:
   `stmtOrte`/`blockOrte`/`endblockOrte`/`armsOrte`/`grundArmsOrte` tragen
   `Expr.orte` durch die Ruempfe, `liestDirekt`/`liestTab`/`liestGlob`/`liesAus`
   rechnen die Huelle je Rumpf und je Code, `liesTreue`/`liesVoll` sind die
   Treue-Formen zur Schreibseite (§8), und `rahmenDecktLies` knuepft die Huelle
   an die Rahmen von `Interferenz.lean`. Neu gebucht: S6 (Vertraege ausserhalb
   des Rumpfs), S7 (fremdes Rufziel wie S2). Nur `def`-Formen, als Entwurf: was
   die Rechnung dem Pruefer schuldet, steht als Form daneben, nicht als Satz.
-/

import Grammatik.Geteilt
import Grammatik.Syntax
import Grammatik.Wettlauf
import Grammatik.Semantik
import Grammatik.Interferenz
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

/-! ## 1. W-EXT -- die Traversierung: Rufe aus den Ruempfen

    Jeder Konstruktor steht explizit da -- gerade die, die KEINE Kante liefern
    (`callInd`, `bindCallInd`, `axiomCall`, `bindAxiom`): ein Zeigerruf und ein
    fremder Rumpf fallen aus der Huelle (Schnitt S2). -/

mutual

/-- Die direkten Rufe einer Anweisung. -/
def stmtKanten {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List D.Fn
  | .assignSlot _ _ _ _ _ _ => []
  | .assignDurch _ _ _ _ _ _ _ _ => []
  | .assignGlob _ _ _ _ => []
  | .schreibBytes _ _ _ _ _ _ _ _ _ _ => []
  | .assignVar _ _ => []
  | .uebergang _ _ _ _ _ _ _ _ _ _ => []
  | .ite _ t e => blockKanten t ++ blockKanten e
  | .onOption _ p a => blockKanten p ++ blockKanten a
  | .onTag _ arms => armsKanten arms
  | .onGrund _ arms => grundArmsKanten arms
  | .call f _ _ _ => [f]
  | .callInd _ _ _ _ => []
  | .locks _ _ body => blockKanten body
  | .breaking _ body => blockKanten body
  | .traverse _ _ body => blockKanten body
  | .retry _ _ body ueber => blockKanten body ++ blockKanten ueber
  | .forever _ _ body => blockKanten body
  | .axiomCall _ _ _ _ _ => []
  | .regSchreib _ _ _ => []
  | .transition _ _ _ _ _ _ _ => []
  | .publish _ _ _ _ _ _ => []
  | .advances _ _ _ _ => []
  | .retires _ _ _ _ => []
  | .ret _ _ => []
  | .retGrund _ _ => []
  | .leave _ => []
  | .next _ => []

/-- Die direkten Rufe eines Blocks. `bindCall` und `bindCallElse` tragen ihre
    Kante; `bindCallInd` (Zeiger) und `bindAxiom` (fremd) tragen keine. -/
def blockKanten {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List D.Fn
  | .nil => []
  | .cons s rest => stmtKanten s ++ blockKanten rest
  | .bind _ rest => blockKanten rest
  | .bindCall f _ _ _ _ rest => f :: blockKanten rest
  | .bindCallInd _ _ _ _ _ rest => blockKanten rest
  | .bindCallElse f _ _ _ _ err rest =>
      f :: endblockKanten err ++ blockKanten rest
  | .bindAxiom _ _ _ _ _ rest => blockKanten rest
  | .regLies _ _ rest => blockKanten rest
  | .regLiesElse _ _ _ sonst rest =>
      endblockKanten sonst ++ blockKanten rest
  | .awaits _ _ _ _ rest => blockKanten rest
  | .exchange _ _ _ _ rest => blockKanten rest
  | .narrow _ _ _ sonst rest =>
      endblockKanten sonst ++ blockKanten rest
  | .pruefung _ sonst rest =>
      endblockKanten sonst ++ blockKanten rest
  | .gleit _ _ _ _ _ rest => blockKanten rest
  | .gleitLit _ _ _ rest => blockKanten rest
  | .gleitVon _ _ _ rest => blockKanten rest
  | .gleitNarrow _ _ _ sonst rest =>
      endblockKanten sonst ++ blockKanten rest

/-- Die direkten Rufe eines nicht abfallenden Blocks. -/
def endblockKanten {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List D.Fn
  | .ret _ _ => []
  | .retGrund _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => stmtKanten s ++ endblockKanten rest
  | .bind _ rest => endblockKanten rest

/-- Die direkten Rufe der Fallunterscheidung. -/
def armsKanten {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → List D.Fn
  | .nil => []
  | .cons b rest => blockKanten b ++ armsKanten rest

/-- Die direkten Rufe der Grund-Fallunterscheidung. -/
def grundArmsKanten {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → List D.Fn
  | .nil => []
  | .cons b rest => blockKanten b ++ grundArmsKanten rest

end

/-- Die direkten Rufe des Rumpfs von `f`: W-EXT am `Programm.rumpf`. -/
def ruftDirekt (P : Programm D) (f : D.Fn) : List D.Fn :=
  endblockKanten (P.rumpf f)

/-! ## 2. Die Kantenrechnung: aus den Rufen, ueber der Domaene -/

/-- Die normierte Kante: nur Rufe in die erklaerte Funktionsdomaene ueberleben
    (als Codes -- `D.Fn` braucht kein `DecidableEq`). Ein Ruf ins Unerklaerte
    faellt hier weg -- und `kantenVoll` (§5) verlangt ihn dort zurueck: was
    faellt, verweigert der Pruefer. -/
def ruftNorm (P : Programm D) (fns : List D.Fn) (fnCode : D.Fn → Nat)
    (f : D.Fn) : List Nat :=
  ((ruftDirekt P f).map fnCode).filter fun c => decide (c ∈ fns.map fnCode)

/-- Die Kantenliste der Einheit: je erklaerter Funktion ihre normierten Ziele
    (die Sicht des Pruefers auf `Bau.ruft`). -/
def kantenListe (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat) : List (Nat × Nat) :=
  fns.flatMap fun f => (ruftNorm P fns fnCode f).map fun g => (fnCode f, g)

/-- Die Rufhuelle als Bau-Feld: zu Code `n` alle normierten Ziele aller
    Funktionen mit diesem Code. -/
def ruftAus (P : Programm D) (fns : List D.Fn) (fnCode : D.Fn → Nat) :
    Nat → List Nat :=
  fun n =>
    ((fns.filter fun f => decide (fnCode f = n)).flatMap
      (ruftNorm P fns fnCode))

/-! ## 3. Die Fussabdruckrechnung: aus den Effekten, ueber der Domaene -/

/-- Der Fussabdruck je Code: was die Effekte (`D.schreibt`/`D.gschreibt`)
    nennen, aus der erklaerten Domaene herausgefiltert, als Codes. Ein Effekt
    ausserhalb der Domaene faellt weg -- wie die Kante: was faellt, verweigert
    der Pruefer (`fussTreue`, §8). -/
def fussAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) : Nat → List Nat :=
  fun n =>
    ((fns.filter fun f => decide (fnCode f = n)).flatMap fun f =>
      ((tabs.filter (D.schreibt f)).map tabCode ++
        (globs.filter (D.gschreibt f)).map globCode))

/-! ## 4. Die Markenrechnung: Domaene und Markierung aus einer Quelle -/

/-- Die Traegerdomaene: Tabellen-Codes vor Glob-Codes. -/
def traegerAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat) : List Nat :=
  tabs.map tabCode ++ globs.map globCode

/-- Nachschlagen in der Tabellenhaelfte: der erste Treffer gewinnt. -/
def geteiltTab (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (c : Nat) : Option Bool :=
  match tabs with
  | [] => none
  | t :: ts =>
      if tabCode t = c then some (D.geteilt t)
      else geteiltTab ts tabCode c

/-- Nachschlagen in der Glob-Haelfte. -/
def geteiltGlob (globs : List D.Glob) (globCode : D.Glob → Nat)
    (c : Nat) : Option Bool :=
  match globs with
  | [] => none
  | g :: gs =>
      if globCode g = c then some (D.ggeteilt g)
      else geteiltGlob gs globCode c

/-- Die Markierungsfunktion: Tabellen zuerst, dann Globs, ausserhalb `true` --
    unbekannt heisst geteilt (Schnitt S5: fail-closed zur lauten Seite). -/
def geteiltAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat) : Nat → Bool :=
  fun c =>
    match geteiltTab tabs tabCode c with
    | some b => b
    | none =>
        match geteiltGlob globs globCode c with
        | some b => b
        | none => true

/-- Treffer in der Tabellenhaelfte: unter Eindeutigkeit der Codes (`hinj`)
    steht am Code von `t` genau die Marke von `t`. -/
theorem geteiltTab_trifft (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (hinj : ∀ t₁ ∈ tabs, ∀ t₂ ∈ tabs, tabCode t₁ = tabCode t₂ → t₁ = t₂)
    (t : D.Tab) (ht : t ∈ tabs) :
    geteiltTab tabs tabCode (tabCode t) = some (D.geteilt t) := by
  induction tabs with
  | nil => simp at ht
  | cons x xs ih =>
      simp only [geteiltTab]
      by_cases hxc : tabCode x = tabCode t
      · rw [if_pos hxc]
        have hx : x = t :=
          hinj x List.mem_cons_self t (by simpa using ht) hxc
        rw [hx]
      · rw [if_neg hxc]
        rcases List.mem_cons.mp ht with rfl | hmem
        · exact absurd rfl hxc
        · exact ih
            (fun t₁ h₁ t₂ h₂ h => hinj t₁ (List.mem_cons_of_mem _ h₁)
              t₂ (List.mem_cons_of_mem _ h₂) h)
            hmem

/-- Treffer in der Glob-Haelfte. -/
theorem geteiltGlob_trifft (globs : List D.Glob) (globCode : D.Glob → Nat)
    (hinj : ∀ g₁ ∈ globs, ∀ g₂ ∈ globs, globCode g₁ = globCode g₂ → g₁ = g₂)
    (g : D.Glob) (hg : g ∈ globs) :
    geteiltGlob globs globCode (globCode g) = some (D.ggeteilt g) := by
  induction globs with
  | nil => simp at hg
  | cons x xs ih =>
      simp only [geteiltGlob]
      by_cases hxc : globCode x = globCode g
      · rw [if_pos hxc]
        have hx : x = g :=
          hinj x List.mem_cons_self g (by simpa using hg) hxc
        rw [hx]
      · rw [if_neg hxc]
        rcases List.mem_cons.mp hg with rfl | hmem
        · exact absurd rfl hxc
        · exact ih
            (fun g₁ h₁ g₂ h₂ h => hinj g₁ (List.mem_cons_of_mem _ h₁)
              g₂ (List.mem_cons_of_mem _ h₂) h)
            hmem

/-- Daneben in der Tabellenhaelfte: kein Code trifft `c`. -/
theorem geteiltTab_fremd (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (c : Nat) (h : ∀ t ∈ tabs, tabCode t ≠ c) :
    geteiltTab tabs tabCode c = none := by
  induction tabs with
  | nil => rfl
  | cons x xs ih =>
      simp only [geteiltTab]
      rw [if_neg (h x List.mem_cons_self)]
      exact ih fun t ht => h t (List.mem_cons_of_mem _ ht)

/-- Daneben in der Glob-Haelfte. -/
theorem geteiltGlob_fremd (globs : List D.Glob) (globCode : D.Glob → Nat)
    (c : Nat) (h : ∀ g ∈ globs, globCode g ≠ c) :
    geteiltGlob globs globCode c = none := by
  induction globs with
  | nil => rfl
  | cons x xs ih =>
      simp only [geteiltGlob]
      rw [if_neg (h x List.mem_cons_self)]
      exact ih fun g hg => h g (List.mem_cons_of_mem _ hg)

/-- Die Marke am Tab-Code ist die erklaerte Marke (Schnitt S1: mit `hinj`). -/
theorem geteiltAus_tab (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (hinj : ∀ t₁ ∈ tabs, ∀ t₂ ∈ tabs, tabCode t₁ = tabCode t₂ → t₁ = t₂)
    (t : D.Tab) (ht : t ∈ tabs) :
    geteiltAus tabs tabCode globs globCode (tabCode t) = D.geteilt t := by
  unfold geteiltAus
  rw [geteiltTab_trifft tabs tabCode hinj t ht]

/-- Die Marke am Glob-Code ist die erklaerte Marke (mit `hinj` und der
    Haelftentrennung `hdisj`: kein Tab-Code darf ihn treffen). -/
theorem geteiltAus_glob (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (hinj : ∀ g₁ ∈ globs, ∀ g₂ ∈ globs, globCode g₁ = globCode g₂ → g₁ = g₂)
    (hdisj : ∀ t ∈ tabs, ∀ g ∈ globs, tabCode t ≠ globCode g)
    (g : D.Glob) (hg : g ∈ globs) :
    geteiltAus tabs tabCode globs globCode (globCode g) = D.ggeteilt g := by
  unfold geteiltAus
  rw [geteiltTab_fremd tabs tabCode _ (fun t ht => hdisj t ht g hg)]
  rw [geteiltGlob_trifft globs globCode hinj g hg]

/-- Unbekannt heisst geteilt (Schnitt S5, bewiesen): ausserhalb der erklaerten
    Domaene antwortet die Markierung `true`. -/
theorem geteiltAus_fremd (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (c : Nat) (ht : ∀ t ∈ tabs, tabCode t ≠ c)
    (hg : ∀ g ∈ globs, globCode g ≠ c) :
    geteiltAus tabs tabCode globs globCode c = true := by
  unfold geteiltAus
  rw [geteiltTab_fremd tabs tabCode c ht]
  rw [geteiltGlob_fremd globs globCode c hg]

/-! ## 5. Die Paarrechnung: aus der Fassung, ueber den Eintritten -/

/-- Die Nebenlaufpaare: nur Paare innerhalb der Eintritte ueberleben. Ein Paar
    mit haengender Nummer faellt weg -- und `paarVoll_aus_bau` (§6) verlangt es
    zurueck: was faellt, verweigert der Pruefer (Schnitt S4). -/
def nebenAus (fadenZahl : Nat) (paare : List (Nat × Nat)) :
    List (Nat × Nat) :=
  paare.filter fun p => decide (p.1 < fadenZahl ∧ p.2 < fadenZahl)

/-! ## 6. Der Zusammenbau: der Bau als Rechnung -- ein `Geteilt.Bau` -/

/-- **Der Bau aus der Rechnung.** Jede Stelle nennt ihre Herkunft: die Eintritte
    getragen (als Codes), die Kanten aus den Rufen (§1-2), die Fuesse aus den
    Effekten (§3), Markierung und Domaene aus einer Quelle (§4), die Paare aus
    der Fassung (§5). Das Ergebnis hat den Typ `Geteilt.Bau`. -/
def bauAus (P : Programm D) (fns : List D.Fn) (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat)) : Geteilt.Bau where
  eintritt := eintritt.map fnCode
  ruft := ruftAus P fns fnCode
  schreibtFn := fussAus tabs tabCode globs globCode fns fnCode
  geteilt := geteiltAus tabs tabCode globs globCode
  traeger := traegerAus tabs tabCode globs globCode
  neben := nebenAus eintritt.length paare

/-! ## 7. Die Lauf-Form: die `BauLauf`-Gestalt ueber dem errechneten Bau -/

/-- **Deckung als Form.** Jeder Zugriff des Laufs ist statisch gedeckt -- die
    erste Haelfte von `Geteilt.BauLauf`, ueber dem errechneten Bau (die
    Koerper-Extraktionspflicht aus `Geteilt.lean` C2 ist hier die Rechnung
    selbst). -/
def laufGedeckt (B : Geteilt.Bau) (fuel : Nat)
    (l : List (Nat × Nat)) : Prop :=
  ∀ s ∈ l, Geteilt.ErreichtBau B fuel s.1 s.2

/-- **Nur Paare als Form.** Zwei Schritte verschiedener Faeden nennen ein
    erklaertes Paar -- die zweite Haelfte von `Geteilt.BauLauf`, ueber der
    gerechneten Paarliste. -/
def nurPaareLaufen (B : Geteilt.Bau) (l : List (Nat × Nat)) : Prop :=
  ∀ s₁ ∈ l, ∀ s₂ ∈ l,
    s₁.1 = s₂.1 ∨ (s₁.1, s₂.1) ∈ B.neben ∨ (s₂.1, s₁.1) ∈ B.neben

/-- **Die Lauf-Form.** Deckung UND nur Paare -- Satz fuer Satz `Geteilt.BauLauf`,
    ausgewertet am errechneten Bau statt am erklaerten. -/
def bauLaufSpiegel (B : Geteilt.Bau) (fuel : Nat)
    (l : List (Nat × Nat)) : Prop :=
  laufGedeckt B fuel l ∧ nurPaareLaufen B l

/-- Die Lauf-Form IST `Geteilt.BauLauf` -- die Verdrahtung als `Iff.rfl`. -/
theorem bauLaufSpiegel_genau (B : Geteilt.Bau) (fuel : Nat)
    (l : List (Nat × Nat)) :
    bauLaufSpiegel B fuel l ↔ Geteilt.BauLauf B fuel l :=
  Iff.rfl

/-! ## 8. Die Treue-Formen: was die Rechnung dem Pruefer schuldet -/

/-- **Kantentreue.** Kein direkter Ruf faellt aus der Rechnung: was der Rumpf
    ruft, steht -- in der Domaene -- in `B.ruft`. Die Richtung ist Absicht --
    die Rechnung darf MEHR sehen (Uebernaeherung), nie weniger. -/
def kantenTreue (B : Geteilt.Bau) (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat) : Prop :=
  ∀ f ∈ fns, ∀ g ∈ ruftDirekt P f,
    fnCode g ∈ fns.map fnCode → fnCode g ∈ B.ruft (fnCode f)

/-- **Kantenvollstaendigkeit (die Pflicht des Pruefers).** Kein direkter Ruf
    haengt ausserhalb der Domaene -- sonst duerfte die Rechnung weniger sehen,
    als der Rumpf ruft, und `ruftNorm` haette still verschwiegen, was es warf.
    Unbewiesen (Obligation, kein Satz): der Pruefer verweigert, was faellt. -/
def kantenVoll (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat) : Prop :=
  ∀ f ∈ fns, ∀ g ∈ ruftDirekt P f, fnCode g ∈ fns.map fnCode

/-- **Fusstreue.** Kein Effekt faellt aus der Rechnung: was die Signatur
    schreibt, steht -- als Code -- in `B.schreibtFn`, je Haelfte. -/
def fussTreue (B : Geteilt.Bau) (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) : Prop :=
  (∀ f ∈ fns, ∀ t ∈ tabs,
    D.schreibt f t = true → tabCode t ∈ B.schreibtFn (fnCode f)) ∧
  (∀ f ∈ fns, ∀ g ∈ globs,
    D.gschreibt f g = true → globCode g ∈ B.schreibtFn (fnCode f))

/-- **Paartreue.** Jedes gerechnete Paar ist ein deklariertes: aus der Liste in
    die `Nebeneinander`-Form (`Wettlauf.lean` §6; `Faden` ist `Nat`, also ist
    `Nebeneinander` genau diese Gestalt). -/
def paarTreue (B : Geteilt.Bau) (Nb : Nebeneinander) : Prop :=
  ∀ i j, (i, j) ∈ B.neben → Nb i j

/-- **Paarvollstaendigkeit (die Pflicht des Pruefers).** Jedes deklarierte Paar
    steht in der Liste -- sonst duerfte der Lauf weniger, als die Fassung
    verspricht, und `nebenAus` haette still verschwiegen, was es warf
    (Schnitt S4). Unbewiesen als Form; `paarVoll_aus_bau` nennt die Praemissen,
    unter denen der errechnete Bau sie erfuellt. -/
def paarVoll (B : Geteilt.Bau) (Nb : Nebeneinander) : Prop :=
  ∀ i j, Nb i j → (i, j) ∈ B.neben ∨ (j, i) ∈ B.neben

/-- Die Kantenrechnung ist kantentreu: was in der Domaene liegt, ueberlebt. -/
theorem kantenTreue_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat)) :
    kantenTreue (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare)
      P fns fnCode := by
  intro f hf g hg hdom
  show fnCode g ∈ ruftAus P fns fnCode (fnCode f)
  unfold ruftAus ruftNorm
  exact List.mem_flatMap.mpr
    ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
      List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨g, hg, rfl⟩, decide_eq_true hdom⟩⟩

/-- Die Fussrechnung ist fusstreu: jeder erklaerte Effekt steht im Bau. -/
theorem fussTreue_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat)) :
    fussTreue (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare)
      tabs tabCode globs globCode fns fnCode := by
  constructor
  · intro f hf t ht hw
    show tabCode t ∈ fussAus tabs tabCode globs globCode fns fnCode (fnCode f)
    unfold fussAus
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inl (List.mem_map.mpr
          ⟨t, List.mem_filter.mpr ⟨ht, hw⟩, rfl⟩))⟩
  · intro f hf g hg hw
    show globCode g ∈ fussAus tabs tabCode globs globCode fns fnCode (fnCode f)
    unfold fussAus
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inr (List.mem_map.mpr
          ⟨g, List.mem_filter.mpr ⟨hg, hw⟩, rfl⟩))⟩

/-- Die Paarrechnung ist paartreu: was sie behielt, war deklariert. -/
theorem paarTreue_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (Nb : Nebeneinander) (hpaar : ∀ p ∈ paare, Nb p.1 p.2) :
    paarTreue (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare)
      Nb := by
  intro i j hmem
  have hmem' : (i, j) ∈ nebenAus eintritt.length paare := hmem
  obtain ⟨hm, _⟩ := List.mem_filter.mp hmem'
  exact hpaar _ hm

/-- Die Paarrechnung ist paarvollstaendig, sobald die Fassung es ist (`hvoll`)
    und kein deklariertes Paar ausserhalb der Eintritte haengt (`hbound`). -/
theorem paarVoll_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (Nb : Nebeneinander)
    (hvoll : ∀ i j, Nb i j → (i, j) ∈ paare ∨ (j, i) ∈ paare)
    (hbound : ∀ i j, Nb i j → i < eintritt.length ∧ j < eintritt.length) :
    paarVoll (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare)
      Nb := by
  intro i j hnb
  obtain ⟨hi, hj⟩ := hbound i j hnb
  rcases hvoll i j hnb with h | h
  · left
    have h' : (i, j) ∈ nebenAus eintritt.length paare :=
      List.mem_filter.mpr ⟨h, decide_eq_true ⟨hi, hj⟩⟩
    exact h'
  · right
    have h' : (j, i) ∈ nebenAus eintritt.length paare :=
      List.mem_filter.mpr ⟨h, decide_eq_true ⟨hj, hi⟩⟩
    exact h'

/-! ## 9. Die Einspeisung: der errechnete Bau in `geteilt_treu` -/

/-- **Geteilt, errechnet.** Der Pruefer `pruefeUngeteilt` laeuft ueber dem
    errechneten Bau; ein ungeteilter Traeger darin gehoert einem Faden. -/
theorem geteilt_treu_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (fuel : Nat)
    (h : Geteilt.pruefeUngeteilt
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare)
      fuel = true)
    (c : Nat)
    (hmem : c ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).traeger)
    (hu : (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).geteilt c = false)
    (f g : Nat)
    (hf : Geteilt.ErreichtBau
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare) fuel f c)
    (hg : Geteilt.ErreichtBau
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare) fuel g c) :
    f = g :=
  Geteilt.geteilt_treu _ fuel h c hmem hu f g hf hg

/-- **(W5) ueber errechneten Laeufen**, die Form, die `kein_wettlauf`
    verbraucht. -/
theorem ungeteilt_aus_baulauf_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (fuel : Nat) (l : List (Nat × Nat))
    (h : Geteilt.pruefeUngeteilt
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare)
      fuel = true)
    (hl : bauLaufSpiegel
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare) fuel l)
    (c : Nat)
    (hmem : c ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).traeger)
    (hu : (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).geteilt c = false)
    (s₁ s₂ : Nat × Nat) (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l)
    (hg : s₁.2 = s₂.2) (hc : s₁.2 = c) : s₁.1 = s₂.1 :=
  Geteilt.ungeteilt_aus_baulauf _ fuel h l
    ((bauLaufSpiegel_genau _ fuel l).mp hl) c hmem hu s₁ s₂ h₁ h₂ hg hc

#print axioms Gabbro.Grammatik.Extraktion.kantenTreue_aus_bau
#print axioms Gabbro.Grammatik.Extraktion.fussTreue_aus_bau
#print axioms Gabbro.Grammatik.Extraktion.geteilt_treu_aus_bau
#print axioms Gabbro.Grammatik.Extraktion.ungeteilt_aus_baulauf_aus_bau

/-! ## 10. Die Probe-Deklaration: zwei Faeden, zwei Traeger, echt

    Eine konkrete `Deklaration` (`miniD`) mit zwei Funktionen (`Bool`), zwei
    Tabellen (`Bool`), sonst leeren Sorten -- und einem `Programm` (`miniP`)
    aus zwei leeren Ruempfen. Funktion `true` schreibt Tabelle `true`,
    Funktion `false` schreibt Tabelle `false`; beide Tabellen sind ungeteilt.
    Die Codes trennen clean (`fnCode`: wahr/falsch auf 0/1, `tabCode` auf
    7/9); `miniB` ist der daraus errechnete `Geteilt.Bau`. -/

/-- Signatur von `true`: schreibt nur Tabelle `true`. -/
def miniSigA : Signatur Bool Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun | true => true | false => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Signatur von `false`: schreibt nur Tabelle `false`. -/
def miniSigB : Signatur Bool Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun | true => false | false => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Die Probe-Deklaration: `Fn = Bool`, `Tab = Bool`, alles andere leer. -/
def miniD : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some true | 1 => some false | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun | 0 => miniSigA | _ => miniSigB
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- Die Probe-Ruempfe: je ein leeres `return` (keine Rufe -- die Kantenliste
    ist leer, und `kantenVoll` gilt per Fallunterscheidung). -/
def miniRumpf : ∀ f : miniD.Fn,
    Endblock miniD (vertragVon miniD f) false (miniD.params f)
      (Signatur.anfang miniD (miniD.signatur f))
  | true => .ret .keine (List.Perm.refl [])
  | false => .ret .keine (List.Perm.refl [])

/-- Das Probe-Programm ueber `miniD`. -/
def miniP : Programm miniD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf := miniRumpf

/-- Die Probe-Eingaben: Domaenen, Codes, Eintritte, Paare. -/
def miniFns : List miniD.Fn := [true, false]

def miniFnCode : miniD.Fn → Nat
  | true => 0
  | false => 1

def miniTabs : List miniD.Tab := [true, false]

def miniTabCode : miniD.Tab → Nat
  | true => 7
  | false => 9

def miniGlobs : List miniD.Glob := []

def miniGlobCode : miniD.Glob → Nat := fun e => nomatch e

def miniEintritt : List miniD.Fn := [true, false]

def miniPaare : List (Nat × Nat) := [(0, 1)]

def miniNb : Nebeneinander := fun i j => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)

/-- Der Probenbau: `bauAus` ueber dem echten Programm -- ein `Geteilt.Bau`. -/
def miniB : Geteilt.Bau :=
  bauAus miniP miniFns miniFnCode miniTabs miniTabCode
    miniGlobs miniGlobCode miniEintritt miniPaare

/-! ## 11. Sprechprobe: die Rechnung rechnet Ende zu Ende -/

/-- Der Pruefer entscheidet per Rechnung: eine falsche Marke liesse dieses
    `rfl` zur Elaborationszeit scheitern -- der laute Bruch. -/
example : Geteilt.pruefeUngeteilt miniB 3 = true := rfl

/-- Faden 0 erreicht Traeger 7 wirklich -- durch den errechneten Bau. -/
theorem mini_errecht : Geteilt.ErreichtBau miniB 3 0 7 :=
  ⟨0, 0, rfl, Geteilt.RuftStarN.refl _ _, by decide⟩

/-- Nichts haengt aus der Domaene: beide Ruempfe rufen nichts. -/
example : kantenVoll miniP miniFns miniFnCode := by
  intro f _ g hg
  have h1 : ruftDirekt miniP true = [] := rfl
  have h2 : ruftDirekt miniP false = [] := rfl
  cases f with
  | true => rw [h1] at hg; simp at hg
  | false => rw [h2] at hg; simp at hg

/-- Die Treue-Saetze greifen am errechneten Bau. -/
example := kantenTreue_aus_bau miniP miniFns miniFnCode miniTabs miniTabCode
  miniGlobs miniGlobCode miniEintritt miniPaare

example := fussTreue_aus_bau miniP miniFns miniFnCode miniTabs miniTabCode
  miniGlobs miniGlobCode miniEintritt miniPaare

example : paarTreue miniB miniNb :=
  paarTreue_aus_bau miniP miniFns miniFnCode miniTabs miniTabCode
    miniGlobs miniGlobCode miniEintritt miniPaare miniNb
    (by intro p hp
        simp only [miniPaare, List.mem_singleton] at hp
        subst hp
        exact Or.inl ⟨rfl, rfl⟩)

/-- Die Einspeisung greift am errechneten Bau: zwei Griffe auf den ungeteilten
    Traeger 7 sind vom selben Faden. -/
example (h : Geteilt.ErreichtBau miniB 3 0 7) : (0 : Nat) = 0 :=
  geteilt_treu_aus_bau miniP miniFns miniFnCode miniTabs miniTabCode
    miniGlobs miniGlobCode miniEintritt miniPaare 3 rfl 7 (by decide) rfl
    0 0 mini_errecht h

#print axioms Gabbro.Grammatik.Extraktion.mini_errecht
#print axioms Gabbro.Grammatik.Extraktion.paarTreue_aus_bau
#print axioms Gabbro.Grammatik.Extraktion.paarVoll_aus_bau

/-! ## 12. Die Lesehuelle als Rechnung -- aus den Ausdruecken, ueber den Ruempfen

    Schnitt S3 nannte die Luecke: `effects` erklaert nur Schreiben, und die
    `slot`/`glob`-Lesungen in `Expr` standen nirgends als Huelle. Hier steht die
    Rechnung, Zug fuer Zug die Anordnung der Schreibseite (§1-§3, §8):

    * die Ausdrucksgestalten liefert `Expr.orte` (`Semantik.lean` §2: jedes
      `slot`/`durch`/`altSlot`/`leseBytes`/`forallSlots`/`existsSlots`/`reaches`
      nennt seinen Traeger, jedes `glob`/`altGlob` sein Global -- als
      Ueberdeckung, nie weniger);
    * `stmtOrte`/`blockOrte`/`endblockOrte`/`armsOrte`/`grundArmsOrte` tragen
      diese Gestalten durch die Ruempfe (derselbe Gang wie `stmtKanten` in §1,
      jeder Konstruktor steht explizit da);
    * `liestDirekt` ist der Rumpf als Huelle (`ruftDirekt` in §1);
    * `liestTab`/`liestGlob` teilen die Huelle in beide Haelften;
    * `liesAus` rechnet die Codes ueber der erklaerten Domaene (`fussAus`
      in §3: was ausserhalb liegt, faellt -- und `liesVoll` verlangt es zurueck);
    * `liesTreue` ist die Treue-Form (`fussTreue`/`kantenTreue` in §8: die
      Rechnung darf MEHR sehen, nie weniger);
    * `rahmenDecktLies` ist die Anknuepfung ans Zwei-Faden-Modell: was der
      Rumpf liest, liegt im genannten Rahmen -- die Gestalt, die
      `Interferenz.lean` als `W`/`G` traegt (`Rahmen`, `HaengtAb`, `Disjunkt`
      nehmen genau solche Prädikate).

    Zwei Zugriffe ohne Ausdrucksgestalt nennt die Rechnung beim Namen: `awaits`
    und `exchange` lesen das Global, an dem sie haengen (`Semantik.lean`:
    `execBlock` legt `σ.globs g` auf den Binder) -- darum traegt ihre Zeile
    das `g` direkt, nicht ueber `Expr.orte`. Registerlesungen (`regLies`,
    `transition` ueber den Spiegel) betreffen weder Traeger noch Globale und
    fallen hier nicht unter die Huelle: ausserhalb des Modells, nicht
    verschwiegen -- der Rahmen von `Interferenz.lean` spricht nur ueber
    `slots`/`globs`.

    Gebucht, nicht versteckt (vgl. S1-S5 oben):
    S6. Vertraege ausserhalb: `liestDirekt` traversiert nur `Programm.rumpf`;
        `requires`/`ensures`/`invariante` sind Ausdruecke mit denselben
        Lesungen (`Expr.orte` greift dort unmittelbar), aber kein
        Rumpf-Durchgang deckt sie -- wer die Huelle schliesst, fuehrt sie
        derselben Rechnung zu.
    S7. Fremde Ruempfe wie in S2: `callInd` und der fremde Rumpf liefern keine
        Huelle ihres Ziels; `liesVoll` deckt nur die Domaene, nicht das Ziel.
        Der Pruefer verweigert, was faellt.

    NACHTRAG (Bahn 100, Satz -- §13): Der Schlussstein (R1) steht als Satz:
    `eval_liest_nur_orte`/`eval_liest_orte` beweisen den Fussabdruck am
    Ausdruck (jede Lesung waehrend der Auswertung ist in `Expr.orte` genannt),
    `QRequires`/`QEnsures`/`QInvariante` sind die Vertraege als
    Welt-Praedikate, `haengtAb_requires`/`haengtAb_ensures`/
    `haengtAb_invariante` loesen `HaengtAb` aus den gerechneten Huellen ein
    (sobald sie im Rahmen liegen), und `liestVertrag`/`liestVertragMitInv`
    fuehren die Vertraege derselben §12-Rechnung zu (`liesAusMitVertrag`/
    `liesAusMitInv`, `liesTreueMitVertrag`/`liesTreueMitInv`,
    `rahmenDecktLiesMitVertrag`/`rahmenDecktLiesMitInv`): S6 ist geschlossen,
    soweit die Gestalt reicht. Gebucht bleibt: R1a (`old(…)` faellt als
    Ein-Welt-Praedikat in die Gegenwart -- dieselbe Huelle, anderer Zeitpunkt;
    die Zwei-Welt-Lesung steht in `exec`), R1b (`Q` spricht nur ueber die Welt:
    jede Umgebung zaehlt, `∀ ρ` -- kein Faden teilt sie, wie G7 in
    `InterferenzAllgemein.lean`), R1c (S7 bleibt: kein Ziel fremder Rufe).
-/

mutual

/-- Die gelesenen Orte einer Anweisung: jede Ausdruckstelle meldet ihre
    `Expr.orte`-Gestalt; Rufe melden ihre Argumente (`Args.orte`), die Rueckgabe
    ihre `ErgExpr.orte`-Gestalt. Was keinen Ort liest (Marken, Register, blosse
    Verzweigung), meldet nichts. -/
def stmtOrte {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .assignSlot _ _ i e _ _ => i.orte ++ e.orte
  | .assignDurch p _ _ _ i e _ _ => p.orte ++ i.orte ++ e.orte
  | .assignGlob _ e _ _ => e.orte
  | .schreibBytes _ _ _ _ i _ _ e _ _ => i.orte ++ e.orte
  | .assignVar _ e => e.orte
  | .uebergang _ _ _ i _ _ _ _ _ _ => i.orte
  | .ite c t e => c.orte ++ blockOrte t ++ blockOrte e
  | .onOption o p a => o.orte ++ blockOrte p ++ blockOrte a
  | .onTag v arms => v.orte ++ armsOrte arms
  | .onGrund r arms => r.orte ++ grundArmsOrte arms
  | .call _ args _ _ => args.orte
  | .callInd p args _ _ => p.orte ++ args.orte
  | .locks _ _ body => blockOrte body
  | .breaking _ body => blockOrte body
  | .traverse _ inv body => inv.orte ++ blockOrte body
  | .retry _ bis body ueber => bis.orte ++ blockOrte body ++ blockOrte ueber
  | .forever _ inv body => inv.orte ++ blockOrte body
  | .axiomCall _ args _ _ _ => args.orte
  | .regSchreib _ _ e => e.orte
  | .transition _ _ _ _ _ _ _ => []
  | .publish _ e _ _ _ _ => e.orte
  | .advances _ _ _ _ => []
  | .retires _ _ _ _ => []
  | .ret e _ => e.orte
  | .retGrund _ _ => []
  | .leave _ => []
  | .next _ => []

/-- Die gelesenen Orte eines Blocks. `awaits` und `exchange` lesen das Global,
    an dem sie haengen -- darum nennt ihre Zeile das `g` direkt (keine
    Ausdrucksgestalt, aber ein Lesezugriff der Bedeutung). -/
def blockOrte {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons s rest => stmtOrte s ++ blockOrte rest
  | .bind e rest => e.orte ++ blockOrte rest
  | .bindCall _ args _ _ _ rest => args.orte ++ blockOrte rest
  | .bindCallInd p args _ _ _ rest => p.orte ++ args.orte ++ blockOrte rest
  | .bindCallElse _ args _ _ _ err rest =>
      args.orte ++ endblockOrte err ++ blockOrte rest
  | .bindAxiom _ args _ _ _ rest => args.orte ++ blockOrte rest
  | .regLies _ _ rest => blockOrte rest
  | .regLiesElse _ _ zusage sonst rest =>
      zusage.orte ++ endblockOrte sonst ++ blockOrte rest
  | .awaits g _ _ _ rest => .inr g :: blockOrte rest
  | .exchange g neu _ _ rest => .inr g :: neu.orte ++ blockOrte rest
  | .narrow e _ _ sonst rest =>
      e.orte ++ endblockOrte sonst ++ blockOrte rest
  | .pruefung c sonst rest =>
      c.orte ++ endblockOrte sonst ++ blockOrte rest
  | .gleit _ a b _ _ rest => a.orte ++ b.orte ++ blockOrte rest
  | .gleitLit _ _ _ rest => blockOrte rest
  | .gleitVon e _ _ rest => e.orte ++ blockOrte rest
  | .gleitNarrow e _ _ sonst rest =>
      e.orte ++ endblockOrte sonst ++ blockOrte rest

/-- Die gelesenen Orte eines nicht abfallenden Blocks. -/
def endblockOrte {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (D.Tab ⊕ D.Glob)
  | .ret e _ => e.orte
  | .retGrund _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => stmtOrte s ++ endblockOrte rest
  | .bind e rest => e.orte ++ endblockOrte rest

/-- Die gelesenen Orte der Fallunterscheidung. -/
def armsOrte {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons b rest => blockOrte b ++ armsOrte rest

/-- Die gelesenen Orte der Grund-Fallunterscheidung. -/
def grundArmsOrte {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons b rest => blockOrte b ++ grundArmsOrte rest

end

/-- Die gelesenen Orte des Rumpfs von `f`: die Lesehuelle am `Programm.rumpf`. -/
def liestDirekt (P : Programm D) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  endblockOrte (P.rumpf f)

/-- Die gelesene Traegerhaelfte je Rumpf: nur die `slot`-Seite der Huelle. -/
def liestTab (P : Programm D) (f : D.Fn) : List D.Tab :=
  (liestDirekt P f).filterMap fun o => match o with
    | .inl t => some t
    | .inr _ => none

/-- Die gelesene Globalhaelfte je Rumpf: nur die `glob`-Seite der Huelle. -/
def liestGlob (P : Programm D) (f : D.Fn) : List D.Glob :=
  (liestDirekt P f).filterMap fun o => match o with
    | .inl _ => none
    | .inr g => some g

/-- Die Lesehuelle je Code: was die Ruempfe lesen, aus der erklaerten Domaene
    herausgefiltert, als Codes. Eine Lesung ausserhalb der Domaene faellt
    weg -- wie die Kante, wie der Fuss: was faellt, verweigert der Pruefer
    (`liesVoll`). -/
def liesAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D) :
    Nat → List Nat :=
  fun n =>
    ((fns.filter fun f => decide (fnCode f = n)).flatMap fun f =>
      (((liestTab P f).map tabCode).filter fun c => decide (c ∈ tabs.map tabCode)) ++
      (((liestGlob P f).map globCode).filter fun c => decide (c ∈ globs.map globCode)))

/-- **Lesetreue.** Keine Lesung faellt aus der Rechnung: was der Rumpf liest,
    steht -- in der Domaene -- in `B.schreibtFn`. Die Richtung ist Absicht --
    die Rechnung darf MEHR sehen (Uebernaeherung), nie weniger. Die gelesenen
    Traeger fahren im Beruehrfeld des Baus: was gelesen wird, wird beruehrt. -/
def liesTreue (B : Geteilt.Bau) (P : Programm D)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) : Prop :=
  (∀ f ∈ fns, ∀ t ∈ liestTab P f,
    tabCode t ∈ tabs.map tabCode → tabCode t ∈ B.schreibtFn (fnCode f)) ∧
  (∀ f ∈ fns, ∀ g ∈ liestGlob P f,
    globCode g ∈ globs.map globCode → globCode g ∈ B.schreibtFn (fnCode f))

/-- **Lesevollstaendigkeit (die Pflicht des Pruefers).** Keine Lesung haengt
    ausserhalb der Domaene -- sonst duerfte die Rechnung weniger sehen, als
    der Rumpf liest, und `liesAus` haette still verschwiegen, was es warf.
    Unbewiesen als Form: der Pruefer verweigert, was faellt. -/
def liesVoll (P : Programm D) (fns : List D.Fn)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat) : Prop :=
  (∀ f ∈ fns, ∀ t ∈ liestTab P f, tabCode t ∈ tabs.map tabCode) ∧
  (∀ f ∈ fns, ∀ g ∈ liestGlob P f, globCode g ∈ globs.map globCode)

/-- **Die Huelle im Rahmen.** Was die Ruempfe lesen, liegt im genannten Rahmen
    -- je Haelfte. Das ist die Gestalt, die das Zwei-Faden-Modell verbraucht:
    `Interferenz.lean` nimmt genau solche `W`/`G`-Rahmen (`Rahmen`,
    `HaengtAb`, `Disjunkt`); die Trennung der Faeden entscheidet sich dort,
    die Deckung steht hier. -/
def rahmenDecktLies (P : Programm D) (fns : List D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool) : Prop :=
  (∀ f ∈ fns, ∀ t ∈ liestTab P f, W t = true) ∧
  (∀ f ∈ fns, ∀ g ∈ liestGlob P f, G g = true)

/-! ## 13. Der Schlussstein (R1): `eval` liest nur `Expr.orte`

    `Interferenz.lean` (S1) nahm es an, §12 (S6) buchte die Luecke: ein
    Vertragsausdruck ist ein `Expr` mit denselben Lesungen, und was er liest,
    steht in `Expr.orte`. Hier steht der Satz, eine Stufe tiefer als §12 (am
    Ausdruck statt am Rumpf): stimmen Eintritt und Gegenwart auf den Orten
    von `e` ueberein, liefert `eval` denselben Wert. `durch` wertet den Zeiger
    nicht einmal aus (reine Faehigkeit, M3) -- seine Orte zaehlen als
    Ueberdeckung mit. -/

/-- `bytesAb` liest nur die Spalte von `t`: gleiche Spalte, gleiche Bytes. -/
theorem bytesAb_gleich {t : D.Tab} {f : D.Feld t} {hf : D.typ t f = .int 0 255}
    {σ σ' : World D}
    (h : ∀ k f', σ.slots t k f' = σ'.slots t k f')
    (n : Nat) (k : Int) :
    σ.bytesAb t f hf n k = σ'.bytesAb t f hf n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      simp only [World.bytesAb]
      rw [h k f, ih]

/-- `kette` liest nur ihre `weiter`-Spalte: gleiche Spalte, gleiche
    Erreichbarkeit. -/
theorem kette_gleich {n : Int} {weiter weiter' : Int → Option (Zahl 0 (n - 1))}
    (fuel : Nat) (k ziel : Int)
    (h : ∀ k, weiter k = weiter' k) :
    kette weiter fuel k ziel = kette weiter' fuel k ziel := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
      show (if k = ziel then true
          else match weiter k with
          | none => false
          | some m => kette weiter fuel m.n ziel) =
        (if k = ziel then true
          else match weiter' k with
          | none => false
          | some m => kette weiter' fuel m.n ziel)
      by_cases hk : k = ziel
      · simp [hk]
      · simp only [if_neg hk]
        rw [h k]
        cases hm : weiter' k with
        | none => rfl
        | some m => exact ih _

/-- Punktweise gleiche Praedikate zaehlen gleich (`all`). -/
theorem list_all_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : p x = q x := h x List.mem_cons_self
      have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp [List.all_cons, hx, ih']

/-- Punktweise gleiche Praedikate zaehlen gleich (`any`). -/
theorem list_any_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : p x = q x := h x List.mem_cons_self
      have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp [List.any_cons, hx, ih']

mutual

/-- **Der Fussabdruck-Schlussstein (R1, Ausdruck):** `eval` liest nur
    `Expr.orte`. Stimmen zwei Welten -- Eintritt wie Gegenwart -- auf allen
    Orten von `os` ueberein, und deckt `os` die Orte von `e`, so liefert
    `eval` denselben Wert. Die Liste `os` bleibt durch die Induktion
    unveraendert stehen; nur die Deckung (`hsub`) wandert zu den
    Teilausdruecken. -/
theorem eval_liest_nur_orte {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (os : List (D.Tab ⊕ D.Glob))
    (hsub : ∀ o ∈ e.orte, o ∈ os)
    (σ₀ σ₀' σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, .inl t ∈ os → ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hSG : ∀ g : D.Glob, .inr g ∈ os → σ.globs g = σ'.globs g)
    (h0T : ∀ t : D.Tab, .inl t ∈ os → ∀ k f, σ₀.slots t k f = σ₀'.slots t k f)
    (h0G : ∀ g : D.Glob, .inr g ∈ os → σ₀.globs g = σ₀'.globs g) :
    eval σ₀ e σ ρ = eval σ₀' e σ' ρ := by
  match e with
  | .lit _ => rfl
  | .wahr => rfl
  | .falsch => rfl
  | .var _ => rfl
  | .ptrOf _ _ _ _ => rfl
  | .fnref _ _ _ => rfl
  | .none _ => rfl
  | .grund _ _ => rfl
  | .glob g _ =>
      simp only [eval]
      exact hSG g (hsub _ (by simp [Expr.orte]))
  | .altGlob g _ =>
      simp only [eval]
      exact h0G g (hsub _ (by simp [Expr.orte]))
  | .slot t f i _ =>
      have hi := eval_liest_nur_orte i os
        (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval, hi]
      exact hS t (hsub _ (by simp [Expr.orte])) _ _
  | .altSlot t f i _ =>
      have hi := eval_liest_nur_orte i os
        (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval, hi]
      exact h0T t (hsub _ (by simp [Expr.orte])) _ _
  | .durch _ t _ f i _ =>
      have hi := eval_liest_nur_orte i os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ho))))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval, hi]
      exact hS t (hsub _ (by simp [Expr.orte])) _ _
  | .weiter _ _ e =>
      have h := eval_liest_nur_orte e os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [h]
  | .neg a =>
      have h := eval_liest_nur_orte a os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [h]
  | .nicht a =>
      have h := eval_liest_nur_orte a os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [h]
  | .some e =>
      have h := eval_liest_nur_orte e os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [h]
  | .istSome e =>
      have h := eval_liest_nur_orte e os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [h]
  | .fall _ _ nutz =>
      have hn := evalNutz_liest_nur_orte nutz os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [hn]
  | .add a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .sub a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .mul a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .div _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .rem _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .sdiv _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .srem _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .band _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .bor _ _ _ _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .bxor _ _ _ _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .shl _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .shr _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .lt a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .le a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .eq a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .fllt a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .flle a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .und a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .oder a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .leseBytes t f hf n i _ _ _ =>
      have hmemT : .inl t ∈ os := hsub _ (by simp [Expr.orte])
      have hi := eval_liest_nur_orte i os
        (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb : σ.bytesAb t f hf n (eval σ₀' i σ' ρ).n =
          σ'.bytesAb t f hf n (eval σ₀' i σ' ρ).n :=
        bytesAb_gleich (fun k f' => hS t hmemT k f') n _
      -- `simp only` rewrites under the dependent tuple proofs (where `rw`
      -- fails the motive check) but leaves the proof-irrelevant rest: `rfl`.
      simp only [eval, hi, hb]
      rfl
  | .forallSlots t body _ =>
      have hbody : ∀ k : Wert D (.index (D.count t)),
          k ∈ alleIndizes (D.count t) →
          wahr? (eval σ₀ body σ (.cons k ρ)) =
            wahr? (eval σ₀' body σ' (.cons k ρ)) := by
        intro k _
        exact congrArg wahr? (eval_liest_nur_orte body os
          (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
          σ₀ σ₀' σ σ' (.cons k ρ) hS hSG h0T h0G)
      simp only [eval]
      exact list_all_congr hbody
  | .existsSlots t body _ =>
      have hbody : ∀ k : Wert D (.index (D.count t)),
          k ∈ alleIndizes (D.count t) →
          wahr? (eval σ₀ body σ (.cons k ρ)) =
            wahr? (eval σ₀' body σ' (.cons k ρ)) := by
        intro k _
        exact congrArg wahr? (eval_liest_nur_orte body os
          (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
          σ₀ σ₀' σ σ' (.cons k ρ) hS hSG h0T h0G)
      simp only [eval]
      exact list_any_congr hbody
  | .reaches t f hf a b _ =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl ho))))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr ho))))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hw : ∀ k, (fun k => hf ▸ σ.slots t k f) k =
          (fun k => hf ▸ σ'.slots t k f) k := by
        intro k
        show (hf ▸ σ.slots t k f) = (hf ▸ σ'.slots t k f)
        rw [hS t (hsub _ (by simp [Expr.orte])) k f]
      simp only [eval]
      rw [ha, hb]
      exact kette_gleich _ _ _ hw

/-- Die Nutzlast liest nur ihre Orte: die zweite Haelfte des Schlusssteins. -/
theorem evalNutz_liest_nur_orte {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)}
    (nutz : NutzlastExpr D Γ Λ c) (os : List (D.Tab ⊕ D.Glob))
    (hsub : ∀ o ∈ nutz.orte, o ∈ os)
    (σ₀ σ₀' σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, .inl t ∈ os → ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hSG : ∀ g : D.Glob, .inr g ∈ os → σ.globs g = σ'.globs g)
    (h0T : ∀ t : D.Tab, .inl t ∈ os → ∀ k f, σ₀.slots t k f = σ₀'.slots t k f)
    (h0G : ∀ g : D.Glob, .inr g ∈ os → σ₀.globs g = σ₀'.globs g) :
    evalNutz σ₀ nutz σ ρ = evalNutz σ₀' nutz σ' ρ := by
  match nutz with
  | .keine => rfl
  | .zahl e =>
      have h := eval_liest_nur_orte e os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [evalNutz]
      rw [h]

end

/-- **Der Fussabdruck-Schlussstein (R1):** `eval` liest nur `Expr.orte` --
    die Form ohne Deckungsliste: die Orte des Ausdrucks selbst genuegen. -/
theorem eval_liest_orte {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ)
    (σ₀ σ₀' σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, .inl t ∈ e.orte → ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hSG : ∀ g : D.Glob, .inr g ∈ e.orte → σ.globs g = σ'.globs g)
    (h0T : ∀ t : D.Tab, .inl t ∈ e.orte → ∀ k f, σ₀.slots t k f = σ₀'.slots t k f)
    (h0G : ∀ g : D.Glob, .inr g ∈ e.orte → σ₀.globs g = σ₀'.globs g) :
    eval σ₀ e σ ρ = eval σ₀' e σ' ρ :=
  eval_liest_nur_orte e _ (fun _ ho => ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G

/-! ## 14. Vertraege als Welt-Praedikate: `HaengtAb` aus der gerechneten Huelle

    Ein Vertragsausdruck ist ein `Expr`; `vertragW`/`vertragG` lesen seine
    Huelle aus `Expr.orte`, und `QRequires`/`QEnsures`/`QInvariante` sind die
    Vertraege als Welt-Praedikate (je Umgebung -- kein Faden teilt sie, R1b;
    `old` faellt als Ein-Welt-Praedikat in die Gegenwart, R1a). `haengtAb_expr`
    loest `HaengtAb` aus der Huelle ein (`eval_aus_rahmen` ist die eine
    Zeile, die arbeitet); `haengtAb_weitet` traegt die Richtung in den
    Signaturrahmen, und `haengtAb_requires`/`haengtAb_ensures`/
    `haengtAb_invariante` benennen die Einloesung je Vertrag. Was in
    `InterferenzAllgemein.lean` als Praemisse getragen wird -- :211
    (`StabilSchritt`), :220 (`StabilKette`), :387 (`allgemeinStabil`, `hAb`),
    :431 (`allgemeinStabil_invariant`, `hAb`) -- loest sich hier ein, wo die
    Gestalt passt: `haengtAb_vertrag_gesamt` reicht die vereinte
    Vertrags-Huelle an :387 weiter, die `stabilKette_…_gilt`-Saetze schliessen
    :220 fuer vertragsgestaltiges `Q`. Fuer abstraktes `Q` bleiben die Stellen
    Praemissen -- das ist kein Rest, sondern die Aussage: was keinen
    gerechneten Fussabdruck hat, wird angenommen, nicht abgeleitet. -/

/-- The table half of a contract expression's footprint: named in `e.orte`
    (`List.any`, not `decide` over membership: only `DecidableEq` per side is
    needed, and `vertragW_mem` is the bridge back to `∈`). -/
def vertragW {Γ : Ctx} {Λ : List (Res D)} (e : Expr D Γ Λ .bool) :
    D.Tab → Bool :=
  fun t => e.orte.any fun o => match o with
    | .inl t' => decide (t' = t)
    | .inr _ => false

/-- The global half of a contract expression's footprint. -/
def vertragG {Γ : Ctx} {Λ : List (Res D)} (e : Expr D Γ Λ .bool) :
    D.Glob → Bool :=
  fun g => e.orte.any fun o => match o with
    | .inl _ => false
    | .inr g' => decide (g' = g)

/-- The table half names exactly the `.inl` members of `e.orte`. -/
theorem vertragW_mem {Γ : Ctx} {Λ : List (Res D)}
    (e : Expr D Γ Λ .bool) (t : D.Tab) :
    vertragW e t = true ↔ (.inl t : D.Tab ⊕ D.Glob) ∈ e.orte := by
  simp only [vertragW, List.any_eq_true]
  constructor
  · rintro ⟨o, ho, hpo⟩
    cases o with
    | inl t' =>
        simp only at hpo
        have heq : t' = t := of_decide_eq_true hpo
        subst heq
        exact ho
    | inr _ =>
        simp at hpo
  · intro h
    exact ⟨.inl t, h, by simp⟩

/-- The global half names exactly the `.inr` members of `e.orte`. -/
theorem vertragG_mem {Γ : Ctx} {Λ : List (Res D)}
    (e : Expr D Γ Λ .bool) (g : D.Glob) :
    vertragG e g = true ↔ (.inr g : D.Tab ⊕ D.Glob) ∈ e.orte := by
  simp only [vertragG, List.any_eq_true]
  constructor
  · rintro ⟨o, ho, hpo⟩
    cases o with
    | inl _ =>
        simp at hpo
    | inr g' =>
        simp only at hpo
        have heq : g' = g := of_decide_eq_true hpo
        subst heq
        exact ho
  · intro h
    exact ⟨.inr g, h, by simp⟩

/-- A contract expression as a world predicate: holds for every environment. -/
def QExpr {Γ : Ctx} {Λ : List (Res D)} (e : Expr D Γ Λ .bool) :
    World D → Prop :=
  fun σ => ∀ ρ : Env D Γ, wahr? (eval σ e σ ρ) = true

/-- `requires` as a world predicate (every parameter environment). -/
def QRequires (P : Programm D) (f : D.Fn) : World D → Prop :=
  QExpr (P.requires f)

/-- `ensures` as a world predicate (every return value, every parameter
    environment). -/
def QEnsures (P : Programm D) (f : D.Fn) : World D → Prop :=
  fun σ => ∀ (v : ErgVal D (D.erg f)) (ρ : Env D (D.params f)),
    wahr? (eval σ (P.ensures f) σ (ergEnv (D.erg f) v ρ)) = true

/-- An invariant as a world predicate (empty environment -- R1b). -/
def QInvariante (P : Programm D) (i : D.Inv) : World D → Prop :=
  fun σ => wahr? (eval σ (P.invariante i) σ .nil) = true

/-- A single environment: frame agreement makes `eval` agree. The workhorse
    behind every `HaengtAb` below. -/
theorem eval_aus_rahmen {Γ : Ctx} {Λ : List (Res D)}
    (e : Expr D Γ Λ .bool) {σ σ' : World D}
    (hRR : RahmenGleichAuf (vertragW e) (vertragG e) σ σ')
    (ρ : Env D Γ) :
    eval σ e σ ρ = eval σ' e σ' ρ :=
  eval_liest_orte e σ σ' σ σ' ρ
    (fun t ht k f => (hRR.1 t ((vertragW_mem e t).mpr ht) k f).symm)
    (fun g hg => (hRR.2 g ((vertragG_mem e g).mpr hg)).symm)
    (fun t ht k f => (hRR.1 t ((vertragW_mem e t).mpr ht) k f).symm)
    (fun g hg => (hRR.2 g ((vertragG_mem e g).mpr hg)).symm)

/-- **Contracts hang on their computed footprint:** what `e` reads decides
    what `QExpr e` sees. -/
theorem haengtAb_expr {Γ : Ctx} {Λ : List (Res D)}
    (e : Expr D Γ Λ .bool) :
    HaengtAb (vertragW e) (vertragG e) (QExpr e) := by
  intro σ σ' hRR
  constructor
  · intro h ρ
    have he := eval_aus_rahmen e hRR ρ
    rw [← he]
    exact h ρ
  · intro h ρ
    have he := eval_aus_rahmen e hRR ρ
    rw [he]
    exact h ρ

/-- `ensures` hangs on its computed footprint (return value and parameters). -/
theorem haengtAb_ensures_shape (P : Programm D) (f : D.Fn) :
    HaengtAb (vertragW (P.ensures f)) (vertragG (P.ensures f))
      (QEnsures P f) := by
  intro σ σ' hRR
  constructor
  · intro h v ρ
    have he := eval_aus_rahmen (P.ensures f) hRR (ergEnv (D.erg f) v ρ)
    rw [← he]
    exact h v ρ
  · intro h v ρ
    have he := eval_aus_rahmen (P.ensures f) hRR (ergEnv (D.erg f) v ρ)
    rw [he]
    exact h v ρ

/-- An invariant hangs on its computed footprint (empty environment). -/
theorem haengtAb_invariante_shape (P : Programm D) (i : D.Inv) :
    HaengtAb (vertragW (P.invariante i)) (vertragG (P.invariante i))
      (QInvariante P i) := by
  intro σ σ' hRR
  constructor
  · intro h
    show wahr? (eval σ' (P.invariante i) σ' .nil) = true
    have he := eval_aus_rahmen (P.invariante i) hRR .nil
    rw [← he]
    exact h
  · intro h
    show wahr? (eval σ (P.invariante i) σ .nil) = true
    have he := eval_aus_rahmen (P.invariante i) hRR .nil
    rw [he]
    exact h

/-- A frame may only grow: what hangs on the narrow frame hangs on the wide
    one. -/
theorem haengtAb_weitet {W W' : D.Tab → Bool} {G G' : D.Glob → Bool}
    {Q : World D → Prop}
    (hW : ∀ t, W t = true → W' t = true)
    (hG : ∀ g, G g = true → G' g = true)
    (h : HaengtAb W G Q) : HaengtAb W' G' Q := by
  intro σ σ' hRR
  apply h
  constructor
  · intro t ht k f
    exact hRR.1 t (hW t ht) k f
  · intro g hg
    exact hRR.2 g (hG g hg)

/-- The `requires` footprint discharges `HaengtAb` at the signature frame --
    the :387 premise for `requires`-shaped assertions. -/
theorem haengtAb_requires (P : Programm D) (f : D.Fn)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.requires f).orte → D.schreibt f t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.requires f).orte → D.gschreibt f g = true) :
    HaengtAb (D.schreibt f) (D.gschreibt f) (QRequires P f) :=
  haengtAb_weitet (fun t ht => hT t ((vertragW_mem _ t).mp ht))
    (fun g hg => hG g ((vertragG_mem _ g).mp hg))
    (haengtAb_expr (P.requires f))

/-- The `ensures` footprint discharges `HaengtAb` at the signature frame. -/
theorem haengtAb_ensures (P : Programm D) (f : D.Fn)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.ensures f).orte → D.schreibt f t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.ensures f).orte → D.gschreibt f g = true) :
    HaengtAb (D.schreibt f) (D.gschreibt f) (QEnsures P f) :=
  haengtAb_weitet (fun t ht => hT t ((vertragW_mem _ t).mp ht))
    (fun g hg => hG g ((vertragG_mem _ g).mp hg))
    (haengtAb_ensures_shape P f)

/-- An invariant footprint discharges `HaengtAb` at any covering frame --
    the :431 premise wherever the invariant is expression-shaped. -/
theorem haengtAb_invariante (P : Programm D) (i : D.Inv)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.invariante i).orte → W t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.invariante i).orte → G g = true) :
    HaengtAb W G (QInvariante P i) :=
  haengtAb_weitet (fun t ht => hT t ((vertragW_mem _ t).mp ht))
    (fun g hg => hG g ((vertragG_mem _ g).mp hg))
    (haengtAb_invariante_shape P i)

/-- `HaengtAb` distributes over conjunction: the combined contract hangs on
    one frame. -/
theorem haengtAb_konjunktion {W : D.Tab → Bool} {G : D.Glob → Bool}
    {Q₁ Q₂ : World D → Prop}
    (h₁ : HaengtAb W G Q₁) (h₂ : HaengtAb W G Q₂) :
    HaengtAb W G (fun σ => Q₁ σ ∧ Q₂ σ) := by
  intro σ σ' hRR
  show (Q₁ σ ∧ Q₂ σ) ↔ (Q₁ σ' ∧ Q₂ σ')
  rw [h₁ σ σ' hRR, h₂ σ σ' hRR]

/-- The :387 premise for contract-shaped assertions: `requires` and `ensures`
    together hang on the signature frame once both footprints lie inside. -/
theorem haengtAb_vertrag_gesamt (P : Programm D) (f : D.Fn)
    (hReqT : ∀ t : D.Tab, .inl t ∈ (P.requires f).orte → D.schreibt f t = true)
    (hReqG : ∀ g : D.Glob, .inr g ∈ (P.requires f).orte → D.gschreibt f g = true)
    (hEnsT : ∀ t : D.Tab, .inl t ∈ (P.ensures f).orte → D.schreibt f t = true)
    (hEnsG : ∀ g : D.Glob, .inr g ∈ (P.ensures f).orte → D.gschreibt f g = true) :
    HaengtAb (D.schreibt f) (D.gschreibt f)
      (fun σ => QRequires P f σ ∧ QEnsures P f σ) :=
  haengtAb_konjunktion
    (haengtAb_requires P f hReqT hReqG)
    (haengtAb_ensures P f hEnsT hEnsG)

/-- The :220 site for `requires`-shaped assertions: `StabilKette` from the
    computed footprint, no `HaengtAb` premise left. -/
theorem stabilKette_requires_gilt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (P : Programm D) (f : D.Fn)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.requires f).orte → D.schreibt f t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.requires f).orte → D.gschreibt f g = true) :
    StabilKette Nb J (D.schreibt f) (D.gschreibt f) (QRequires P f) :=
  stabilKette_gilt Nb J _ _ _ (haengtAb_requires P f hT hG)

/-- The :220 site for `ensures`-shaped assertions. -/
theorem stabilKette_ensures_gilt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (P : Programm D) (f : D.Fn)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.ensures f).orte → D.schreibt f t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.ensures f).orte → D.gschreibt f g = true) :
    StabilKette Nb J (D.schreibt f) (D.gschreibt f) (QEnsures P f) :=
  stabilKette_gilt Nb J _ _ _ (haengtAb_ensures P f hT hG)

/-- The :220 site for invariant-shaped assertions, at any covering frame. -/
theorem stabilKette_invariante_gilt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (P : Programm D) (i : D.Inv)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hT : ∀ t : D.Tab, .inl t ∈ (P.invariante i).orte → W t = true)
    (hG : ∀ g : D.Glob, .inr g ∈ (P.invariante i).orte → G g = true) :
    StabilKette Nb J W G (QInvariante P i) :=
  stabilKette_gilt Nb J _ _ _ (haengtAb_invariante P i W G hT hG)

/-! ## 15. Vertraege in der §12-Rechnung: kein Vertragsfussabdruck faellt heraus

    `liestVertrag` fuehrt `requires`/`ensures` derselben Rechnung zu wie den
    Rumpf (`liestDirekt`), `liestVertragMitInv` nimmt die geschuldeten
    Invarianten dazu; `liesAusMitVertrag`/`liesAusMitInv` rechnen die Codes
    ueber der Domaene (`liesAus` in §12), und `liesTreueMitVertrag`/
    `liesTreueMitInv` beweisen die Deckung: keine Lesung -- Rumpf wie Vertrag
    -- faellt aus der Rechnung. `rahmenDecktLiesMitVertrag`/
    `rahmenDecktLiesMitInv` knuepfen die erweiterte Huelle an die Rahmen von
    `Interferenz.lean`; `liesVollMitVertrag` nennt die Pflicht des Pruefers
    auch fuer die Vertraege (unbewiesen als Form, wie `liesVoll`). -/

/-- The body PLUS its contracts: `requires` and `ensures` join the hull (S6). -/
def liestVertrag (P : Programm D) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte

/-- The table half of the contract hull. -/
def liestVertragTab (P : Programm D) (f : D.Fn) : List D.Tab :=
  (liestVertrag P f).filterMap fun o => match o with
    | .inl t => some t
    | .inr _ => none

/-- The global half of the contract hull. -/
def liestVertragGlob (P : Programm D) (f : D.Fn) : List D.Glob :=
  (liestVertrag P f).filterMap fun o => match o with
    | .inl _ => none
    | .inr g => some g

/-- Owed invariants join the hull: what `f` owes at `return`, it also reads. -/
def liestVertragMitInv (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) : List (D.Tab ⊕ D.Glob) :=
  liestVertrag P f ++
    (invs.filter (schuldet f)).flatMap (fun i => (P.invariante i).orte)

/-- The table half with owed invariants. -/
def liestVertragMitInvTab (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) : List D.Tab :=
  (liestVertragMitInv P f invs).filterMap fun o => match o with
    | .inl t => some t
    | .inr _ => none

/-- The global half with owed invariants. -/
def liestVertragMitInvGlob (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) : List D.Glob :=
  (liestVertragMitInv P f invs).filterMap fun o => match o with
    | .inl _ => none
    | .inr g => some g

/-- `requires` reads land in the contract hull. -/
theorem liestVertragTab_deckt_requires (P : Programm D) (f : D.Fn) (t : D.Tab)
    (h : (.inl t : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte) :
    t ∈ liestVertragTab P f := by
  unfold liestVertragTab
  exact List.mem_filterMap.mpr
    ⟨.inl t,
      by show (.inl t : D.Tab ⊕ D.Glob) ∈
             liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte
         exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))),
      rfl⟩

/-- `ensures` reads land in the contract hull. -/
theorem liestVertragTab_deckt_ensures (P : Programm D) (f : D.Fn) (t : D.Tab)
    (h : (.inl t : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte) :
    t ∈ liestVertragTab P f := by
  unfold liestVertragTab
  exact List.mem_filterMap.mpr
    ⟨.inl t,
      by show (.inl t : D.Tab ⊕ D.Glob) ∈
             liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte
         exact List.mem_append.mpr (Or.inr h),
      rfl⟩

/-- `requires` global reads land in the contract hull. -/
theorem liestVertragGlob_deckt_requires (P : Programm D) (f : D.Fn) (g : D.Glob)
    (h : (.inr g : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte) :
    g ∈ liestVertragGlob P f := by
  unfold liestVertragGlob
  exact List.mem_filterMap.mpr
    ⟨.inr g,
      by show (.inr g : D.Tab ⊕ D.Glob) ∈
             liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte
         exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))),
      rfl⟩

/-- `ensures` global reads land in the contract hull. -/
theorem liestVertragGlob_deckt_ensures (P : Programm D) (f : D.Fn) (g : D.Glob)
    (h : (.inr g : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte) :
    g ∈ liestVertragGlob P f := by
  unfold liestVertragGlob
  exact List.mem_filterMap.mpr
    ⟨.inr g,
      by show (.inr g : D.Tab ⊕ D.Glob) ∈
             liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte
         exact List.mem_append.mpr (Or.inr h),
      rfl⟩

/-- Owed invariant reads land in the hull with invariants. -/
theorem liestVertragMitInvTab_deckt_invariante (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (i : D.Inv) (hi : i ∈ invs)
    (hs : schuldet f i = true) (t : D.Tab)
    (h : (.inl t : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte) :
    t ∈ liestVertragMitInvTab P f invs := by
  unfold liestVertragMitInvTab
  exact List.mem_filterMap.mpr
    ⟨.inl t,
      by show (.inl t : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs
         exact List.mem_append.mpr (Or.inr
           (List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, hs⟩, h⟩)),
      rfl⟩

/-- Owed invariant global reads land in the hull with invariants. -/
theorem liestVertragMitInvGlob_deckt_invariante (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (i : D.Inv) (hi : i ∈ invs)
    (hs : schuldet f i = true) (g : D.Glob)
    (h : (.inr g : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte) :
    g ∈ liestVertragMitInvGlob P f invs := by
  unfold liestVertragMitInvGlob
  exact List.mem_filterMap.mpr
    ⟨.inr g,
      by show (.inr g : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs
         exact List.mem_append.mpr (Or.inr
           (List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, hs⟩, h⟩)),
      rfl⟩

/-- Case split on the contract hull: body, `requires`, or `ensures`. -/
theorem liestVertragTab_fall (P : Programm D) (f : D.Fn) (t : D.Tab)
    (h : t ∈ liestVertragTab P f) :
    t ∈ liestTab P f ∨ (.inl t : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte ∨
      (.inl t : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte := by
  have hmem : (.inl t : D.Tab ⊕ D.Glob) ∈ liestVertrag P f := by
    unfold liestVertragTab at h
    obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
    cases o with
    | inl t' =>
        have heq : t' = t := by simpa using hfo
        subst heq
        exact ho
    | inr _ =>
        simp at hfo
  have h2 : (.inl t : D.Tab ⊕ D.Glob) ∈
      liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte := hmem
  rcases List.mem_append.mp h2 with hV | hens
  · rcases List.mem_append.mp hV with hbody | hreq
    · left
      unfold liestTab
      exact List.mem_filterMap.mpr ⟨.inl t, hbody, rfl⟩
    · exact Or.inr (Or.inl hreq)
  · exact Or.inr (Or.inr hens)

/-- Case split on the global contract hull. -/
theorem liestVertragGlob_fall (P : Programm D) (f : D.Fn) (g : D.Glob)
    (h : g ∈ liestVertragGlob P f) :
    g ∈ liestGlob P f ∨ (.inr g : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte ∨
      (.inr g : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte := by
  have hmem : (.inr g : D.Tab ⊕ D.Glob) ∈ liestVertrag P f := by
    unfold liestVertragGlob at h
    obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
    cases o with
    | inl _ =>
        simp at hfo
    | inr g' =>
        have heq : g' = g := by simpa using hfo
        subst heq
        exact ho
  have h2 : (.inr g : D.Tab ⊕ D.Glob) ∈
      liestDirekt P f ++ (P.requires f).orte ++ (P.ensures f).orte := hmem
  rcases List.mem_append.mp h2 with hV | hens
  · rcases List.mem_append.mp hV with hbody | hreq
    · left
      unfold liestGlob
      exact List.mem_filterMap.mpr ⟨.inr g, hbody, rfl⟩
    · exact Or.inr (Or.inl hreq)
  · exact Or.inr (Or.inr hens)

/-- Case split with owed invariants: contract hull or an owed invariant. -/
theorem liestVertragMitInvTab_fall (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (t : D.Tab)
    (h : t ∈ liestVertragMitInvTab P f invs) :
    t ∈ liestVertragTab P f ∨
      ∃ i ∈ invs, schuldet f i = true ∧
        (.inl t : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte := by
  have hmem : (.inl t : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs := by
    unfold liestVertragMitInvTab at h
    obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
    cases o with
    | inl t' =>
        have heq : t' = t := by simpa using hfo
        subst heq
        exact ho
    | inr _ =>
        simp at hfo
  have h2 : (.inl t : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs := hmem
  rcases List.mem_append.mp h2 with hV | hI
  · left
    unfold liestVertragTab
    show t ∈ (liestVertrag P f).filterMap _
    exact List.mem_filterMap.mpr ⟨.inl t, hV, rfl⟩
  · right
    obtain ⟨i, hi, hmem_i⟩ := List.mem_flatMap.mp hI
    obtain ⟨hi_in, hi_sch⟩ := List.mem_filter.mp hi
    exact ⟨i, hi_in, hi_sch, hmem_i⟩

/-- Case split with owed invariants, global half. -/
theorem liestVertragMitInvGlob_fall (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (g : D.Glob)
    (h : g ∈ liestVertragMitInvGlob P f invs) :
    g ∈ liestVertragGlob P f ∨
      ∃ i ∈ invs, schuldet f i = true ∧
        (.inr g : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte := by
  have hmem : (.inr g : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs := by
    unfold liestVertragMitInvGlob at h
    obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
    cases o with
    | inl _ =>
        simp at hfo
    | inr g' =>
        have heq : g' = g := by simpa using hfo
        subst heq
        exact ho
  have h2 : (.inr g : D.Tab ⊕ D.Glob) ∈ liestVertragMitInv P f invs := hmem
  rcases List.mem_append.mp h2 with hV | hI
  · left
    unfold liestVertragGlob
    show g ∈ (liestVertrag P f).filterMap _
    exact List.mem_filterMap.mpr ⟨.inr g, hV, rfl⟩
  · right
    obtain ⟨i, hi, hmem_i⟩ := List.mem_flatMap.mp hI
    obtain ⟨hi_in, hi_sch⟩ := List.mem_filter.mp hi
    exact ⟨i, hi_in, hi_sch, hmem_i⟩

/-- The read hull per code: body AND contracts, filtered to the domain
    (`liesAus` in §12, contracts included). -/
def liesAusMitVertrag (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D) :
    Nat → List Nat :=
  fun n =>
    ((fns.filter fun f => decide (fnCode f = n)).flatMap fun f =>
      (((liestVertragTab P f).map tabCode).filter fun c => decide (c ∈ tabs.map tabCode)) ++
      (((liestVertragGlob P f).map globCode).filter fun c => decide (c ∈ globs.map globCode)))

/-- The read hull per code, owed invariants included. -/
def liesAusMitInv (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (invs : List D.Inv) : Nat → List Nat :=
  fun n =>
    ((fns.filter fun f => decide (fnCode f = n)).flatMap fun f =>
      (((liestVertragMitInvTab P f invs).map tabCode).filter fun c => decide (c ∈ tabs.map tabCode)) ++
      (((liestVertragMitInvGlob P f invs).map globCode).filter fun c => decide (c ∈ globs.map globCode)))

/-- **No contract footprint falls out:** every read in the contract hull --
    body, `requires`, `ensures` -- lands in the code footprint. -/
theorem liesTreueMitVertrag (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D) :
    (∀ f ∈ fns, ∀ t ∈ liestVertragTab P f,
      tabCode t ∈ tabs.map tabCode →
        tabCode t ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P (fnCode f)) ∧
    (∀ f ∈ fns, ∀ g ∈ liestVertragGlob P f,
      globCode g ∈ globs.map globCode →
        globCode g ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P (fnCode f)) := by
  constructor
  · intro f hf t ht hdom
    show tabCode t ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P (fnCode f)
    unfold liesAusMitVertrag
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inl (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨t, ht, rfl⟩, decide_eq_true hdom⟩))⟩
  · intro f hf g hg hdom
    show globCode g ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P (fnCode f)
    unfold liesAusMitVertrag
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inr (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨g, hg, rfl⟩, decide_eq_true hdom⟩))⟩

/-- **No owed invariant footprint falls out.** -/
theorem liesTreueMitInv (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (invs : List D.Inv) :
    (∀ f ∈ fns, ∀ t ∈ liestVertragMitInvTab P f invs,
      tabCode t ∈ tabs.map tabCode →
        tabCode t ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs (fnCode f)) ∧
    (∀ f ∈ fns, ∀ g ∈ liestVertragMitInvGlob P f invs,
      globCode g ∈ globs.map globCode →
        globCode g ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs (fnCode f)) := by
  constructor
  · intro f hf t ht hdom
    show tabCode t ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs (fnCode f)
    unfold liesAusMitInv
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inl (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨t, ht, rfl⟩, decide_eq_true hdom⟩))⟩
  · intro f hf g hg hdom
    show globCode g ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs (fnCode f)
    unfold liesAusMitInv
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inr (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨g, hg, rfl⟩, decide_eq_true hdom⟩))⟩

/-- **Read-completeness with contracts (the checker's duty).** No read hangs
    outside the domain -- body (§12 `liesVoll`) or contracts: what falls, the
    checker refuses (unproved as a shape, like `liesVoll`). -/
def liesVollMitVertrag (P : Programm D) (fns : List D.Fn) (invs : List D.Inv)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat) : Prop :=
  liesVoll P fns tabs tabCode globs globCode ∧
  (∀ f ∈ fns, ∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte →
    tabCode t ∈ tabs.map tabCode) ∧
  (∀ f ∈ fns, ∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte →
    globCode g ∈ globs.map globCode) ∧
  (∀ f ∈ fns, ∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte →
    tabCode t ∈ tabs.map tabCode) ∧
  (∀ f ∈ fns, ∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte →
    globCode g ∈ globs.map globCode) ∧
  (∀ f ∈ fns, ∀ i ∈ invs, schuldet f i = true →
    (∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte →
      tabCode t ∈ tabs.map tabCode) ∧
    (∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte →
      globCode g ∈ globs.map globCode))

/-- **The hull in the frame, contracts included.** What bodies, `requires`,
    and `ensures` read lies in the named frame -- the shape the two-thread
    model consumes (`rahmenDecktLies` in §12, contracts included). -/
def rahmenDecktLiesMitVertrag (P : Programm D) (fns : List D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool) : Prop :=
  (∀ f ∈ fns, ∀ t ∈ liestVertragTab P f, W t = true) ∧
  (∀ f ∈ fns, ∀ g ∈ liestVertragGlob P f, G g = true)

/-- **The hull in the frame, owed invariants included.** -/
def rahmenDecktLiesMitInv (P : Programm D) (fns : List D.Fn)
    (invs : List D.Inv) (W : D.Tab → Bool) (G : D.Glob → Bool) : Prop :=
  (∀ f ∈ fns, ∀ t ∈ liestVertragMitInvTab P f invs, W t = true) ∧
  (∀ f ∈ fns, ∀ g ∈ liestVertragMitInvGlob P f invs, G g = true)

/-- The frame covers the contract hull once it covers the body and every
    contract footprint. -/
theorem rahmenDecktLiesMitVertrag_aus_rahmen (P : Programm D)
    (fns : List D.Fn) (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hR : rahmenDecktLies P fns W G)
    (hReqT : ∀ f ∈ fns, ∀ t : D.Tab,
      (.inl t : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte → W t = true)
    (hReqG : ∀ f ∈ fns, ∀ g : D.Glob,
      (.inr g : D.Tab ⊕ D.Glob) ∈ (P.requires f).orte → G g = true)
    (hEnsT : ∀ f ∈ fns, ∀ t : D.Tab,
      (.inl t : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte → W t = true)
    (hEnsG : ∀ f ∈ fns, ∀ g : D.Glob,
      (.inr g : D.Tab ⊕ D.Glob) ∈ (P.ensures f).orte → G g = true) :
    rahmenDecktLiesMitVertrag P fns W G := by
  constructor
  · intro f hf t ht
    rcases liestVertragTab_fall P f t ht with hbody | hreq | hens
    · exact hR.1 f hf t hbody
    · exact hReqT f hf t hreq
    · exact hEnsT f hf t hens
  · intro f hf g hg
    rcases liestVertragGlob_fall P f g hg with hbody | hreq | hens
    · exact hR.2 f hf g hbody
    · exact hReqG f hf g hreq
    · exact hEnsG f hf g hens

/-- The frame covers the hull with owed invariants once it covers the
    contract hull and every owed invariant footprint. -/
theorem rahmenDecktLiesMitInv_aus_rahmen (P : Programm D)
    (fns : List D.Fn) (invs : List D.Inv)
    (W : D.Tab → Bool) (G : D.Glob → Bool)
    (hV : rahmenDecktLiesMitVertrag P fns W G)
    (hInvT : ∀ f ∈ fns, ∀ i ∈ invs, schuldet f i = true →
      ∀ t : D.Tab, (.inl t : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte → W t = true)
    (hInvG : ∀ f ∈ fns, ∀ i ∈ invs, schuldet f i = true →
      ∀ g : D.Glob, (.inr g : D.Tab ⊕ D.Glob) ∈ (P.invariante i).orte → G g = true) :
    rahmenDecktLiesMitInv P fns invs W G := by
  constructor
  · intro f hf t ht
    rcases liestVertragMitInvTab_fall P f invs t ht with hVtab | ⟨i, hi, hs, hmem⟩
    · exact hV.1 f hf t hVtab
    · exact hInvT f hf i hi hs t hmem
  · intro f hf g hg
    rcases liestVertragMitInvGlob_fall P f invs g hg with hVglob | ⟨i, hi, hs, hmem⟩
    · exact hV.2 f hf g hVglob
    · exact hInvG f hf i hi hs g hmem

#print axioms Gabbro.Grammatik.Extraktion.eval_liest_orte
#print axioms Gabbro.Grammatik.Extraktion.eval_aus_rahmen
#print axioms Gabbro.Grammatik.Extraktion.vertragW_mem
#print axioms Gabbro.Grammatik.Extraktion.vertragG_mem
#print axioms Gabbro.Grammatik.Extraktion.haengtAb_requires
#print axioms Gabbro.Grammatik.Extraktion.haengtAb_ensures
#print axioms Gabbro.Grammatik.Extraktion.haengtAb_invariante
#print axioms Gabbro.Grammatik.Extraktion.haengtAb_vertrag_gesamt
#print axioms Gabbro.Grammatik.Extraktion.stabilKette_requires_gilt
#print axioms Gabbro.Grammatik.Extraktion.stabilKette_ensures_gilt
#print axioms Gabbro.Grammatik.Extraktion.stabilKette_invariante_gilt
#print axioms Gabbro.Grammatik.Extraktion.liesTreueMitVertrag
#print axioms Gabbro.Grammatik.Extraktion.liesTreueMitInv
#print axioms Gabbro.Grammatik.Extraktion.rahmenDecktLiesMitVertrag_aus_rahmen
#print axioms Gabbro.Grammatik.Extraktion.rahmenDecktLiesMitInv_aus_rahmen

/-! ## 16. Die Treue der gerechneten Huellen: Rumpf, Vertrag, Traeger, Lauf

    (Bahn 123, Saetze -- Anhang: nichts Bestehendes ist geaendert, kein
    Schnitt geoeffnet.)

    Was §8 fuer Kanten/Fuesse/Paare ueber der W-EXT-Traversierung und §15
    fuer die Vertrags-Huellen bewies, steht hier geschlossen nebeneinander --
    ueber denselben Rechnungen, nicht ueber Nacherzaehlungen:

    * `liesTreue_aus_liesAus` ist die fehlende Schwester von
      `liesTreueMitVertrag`/`liesTreueMitInv`: die Rumpf-Huelle `liesAus`
      (§12) hatte bisher KEINEN Treue-Satz -- jede Lesung in der Domaene
      landet in der gerechneten Code-Liste. Damit traegt jede der drei
      Huellschichten (Rumpf, Vertrag, Vertrag-mit-Invarianten) ihren Satz.
    * `liestTab_in_liestVertragTab`/`liestGlob_in_liestVertragGlob` und
      `liestVertragTab_in_MitInvTab`/`liestVertragGlob_in_MitInvGlob`
      schichten die Huellen (Rumpf IN Vertrag IN Invarianten), und
      `liesAus_in_MitVertrag`/`liesAusMitVertrag_in_MitInv` heben die
      Schichtung auf die Code-Listen: keine Lesung geht beim Erweitern
      verloren.
    * `fussAus_in_traegerAus`/`liesAus_in_traegerAus`/
      `liesAusMitVertrag_in_traegerAus`/`liesAusMitInv_in_traegerAus` legen
      jeden gerechneten Fussabdruck in die Traegerdomaene (`traegerAus`), und
      `bauAus_schreibtFn_in_traeger` hebt das auf den `Geteilt.Bau`: was der
      errechnete Bau als beruehrt meldet, liegt in seinem `traeger` -- die
      `hmem`-Seite der `geteilt_treu`-Praemissen, eingeloeost statt getragen.
      Die `hu`-Seite (`geteilt`-Marke) loesen `geteiltAus_tab`/
      `geteiltAus_glob`/`geteiltAus_fremd` (§4) ein.
    * `eintritt_aus_baulaufSpiegel_aus_bau` und
      `nur_deklariert_aus_baulaufSpiegel_aus_bau` tragen zwei weitere
      `Geteilt`-Saetze auf die Spiegel-Form: jeder Schritt hat einen Eintritt
      (`lauf_hat_eintritt`), zwei Faeden nennen ein deklariertes Paar
      (`nur_deklariert_teilt_lauf`) -- dieselbe Verdrahtung wie
      `ungeteilt_aus_baulauf_aus_bau` (§9).

    Gebucht, nicht versteckt (die Verweigerungspflichten des Pruefers, mit
    der jeweils fehlenden Regel beim Namen -- `offeneVerweigerungspflichten`
    fuehrt sie als ein Register):
    B1. `kantenVoll`: Zeigerziele (`callInd`, `bindCallInd`) und fremde
        Ruempfe (`axiomCall`, `bindAxiom`) liefern keine Kante (S2), Codes
        ausserhalb der Domaene wirft `ruftNorm` (fehlende Regel: keine
        statische Aufloesung indirekter/fremder Ziele -- verweigern,
        fail-closed wie `W003`).
    B2. `liesVollMitVertrag` (darin `liesVoll`): Lesungen ausserhalb der
        Domaene -- Rumpf, `requires`/`ensures`, geschuldete Invarianten --
        wirft `liesAus`/`liesAusMitVertrag`/`liesAusMitInv` (fehlende Regel:
        keine Domaene fuer fremde Orte -- verweigern, S3/S6/S7).
    B3. `paarVoll`: haengende (`hbound`) und unerklaerte (`hvoll`) Paare wirft
        `nebenAus` (fehlende Regel: kein Lauf ausserhalb der Eintritte und
        kein Paar ausserhalb der Fassung -- verweigern, S4).
    B4. `liesTreue` IN den Bau: unbeweisbar fuer `bauAus` -- der Bau traegt
        nur Schreib-Effekte (`fussAus`), die Lesehuelle lebt in `liesAus*`,
        in keinem `Bau`-Feld (fehlende Regel: kein `Bau`-Feld traegt die
        Lesehuelle -- ein Pruefer, der Lesungen im Bau braucht, verweigert;
        ein `lesesFn`-Feld aenderte `Geteilt.Bau` und `bauAus` und liegt
        ausserhalb dieses Anhangs).
    B5. R1a/R1b/R1c wie im §12-Nachtrag gebucht: `old(…)` als Zwei-Welt-Lesung,
        nur-Welt-Praedikate ueber geteilter Umgebung, fremde Rufziele.
 -/

/-- **Lesetreue der Rumpf-Huelle:** jede Lesung in der Domaene landet in der
    gerechneten Code-Liste -- die fehlende Schwester von
    `liesTreueMitVertrag`/`liesTreueMitInv` (§15) fuer `liesAus` (§12). -/
theorem liesTreue_aus_liesAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D) :
    (∀ f ∈ fns, ∀ t ∈ liestTab P f,
      tabCode t ∈ tabs.map tabCode →
        tabCode t ∈ liesAus tabs tabCode globs globCode fns fnCode P (fnCode f)) ∧
    (∀ f ∈ fns, ∀ g ∈ liestGlob P f,
      globCode g ∈ globs.map globCode →
        globCode g ∈ liesAus tabs tabCode globs globCode fns fnCode P (fnCode f)) := by
  constructor
  · intro f hf t ht hdom
    show tabCode t ∈ liesAus tabs tabCode globs globCode fns fnCode P (fnCode f)
    unfold liesAus
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inl (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨t, ht, rfl⟩, decide_eq_true hdom⟩))⟩
  · intro f hf g hg hdom
    show globCode g ∈ liesAus tabs tabCode globs globCode fns fnCode P (fnCode f)
    unfold liesAus
    exact List.mem_flatMap.mpr
      ⟨f, List.mem_filter.mpr ⟨hf, decide_eq_true rfl⟩,
        List.mem_append.mpr (Or.inr (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨g, hg, rfl⟩, decide_eq_true hdom⟩))⟩

/-- Die Rumpf-Huelle liegt in der Vertrags-Huelle (Traegerhaelfte). -/
theorem liestTab_in_liestVertragTab (P : Programm D) (f : D.Fn) (t : D.Tab)
    (h : t ∈ liestTab P f) : t ∈ liestVertragTab P f := by
  unfold liestTab at h
  obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
  cases o with
  | inl t' =>
      have heq : t' = t := by simpa using hfo
      rw [heq] at ho
      unfold liestVertragTab
      exact List.mem_filterMap.mpr
        ⟨.inl t, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ho))), rfl⟩
  | inr _ =>
      simp at hfo

/-- Die Rumpf-Huelle liegt in der Vertrags-Huelle (Globalhaelfte). -/
theorem liestGlob_in_liestVertragGlob (P : Programm D) (f : D.Fn) (g : D.Glob)
    (h : g ∈ liestGlob P f) : g ∈ liestVertragGlob P f := by
  unfold liestGlob at h
  obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
  cases o with
  | inl _ =>
      simp at hfo
  | inr g' =>
      have heq : g' = g := by simpa using hfo
      rw [heq] at ho
      unfold liestVertragGlob
      exact List.mem_filterMap.mpr
        ⟨.inr g, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ho))), rfl⟩

/-- Die Vertrags-Huelle liegt in der Invarianten-Huelle (Traegerhaelfte). -/
theorem liestVertragTab_in_MitInvTab (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (t : D.Tab)
    (h : t ∈ liestVertragTab P f) : t ∈ liestVertragMitInvTab P f invs := by
  unfold liestVertragTab at h
  obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
  cases o with
  | inl t' =>
      have heq : t' = t := by simpa using hfo
      rw [heq] at ho
      unfold liestVertragMitInvTab liestVertragMitInv
      exact List.mem_filterMap.mpr
        ⟨.inl t, List.mem_append.mpr (Or.inl ho), rfl⟩
  | inr _ =>
      simp at hfo

/-- Die Vertrags-Huelle liegt in der Invarianten-Huelle (Globalhaelfte). -/
theorem liestVertragGlob_in_MitInvGlob (P : Programm D) (f : D.Fn)
    (invs : List D.Inv) (g : D.Glob)
    (h : g ∈ liestVertragGlob P f) : g ∈ liestVertragMitInvGlob P f invs := by
  unfold liestVertragGlob at h
  obtain ⟨o, ho, hfo⟩ := List.mem_filterMap.mp h
  cases o with
  | inl _ =>
      simp at hfo
  | inr g' =>
      have heq : g' = g := by simpa using hfo
      rw [heq] at ho
      unfold liestVertragMitInvGlob liestVertragMitInv
      exact List.mem_filterMap.mpr
        ⟨.inr g, List.mem_append.mpr (Or.inl ho), rfl⟩

/-- Die Rumpf-Codes ueberleben die Vertrags-Erweiterung: keine Lesung geht
    beim Erweitern verloren. -/
theorem liesAus_in_MitVertrag (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (n : Nat) (c : Nat)
    (h : c ∈ liesAus tabs tabCode globs globCode fns fnCode P n) :
    c ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P n := by
  unfold liesAus at h
  obtain ⟨f, hf, hmem⟩ := List.mem_flatMap.mp h
  unfold liesAusMitVertrag
  have hgoal : c ∈ ((((liestVertragTab P f).map tabCode).filter
        fun c => decide (c ∈ tabs.map tabCode)) ++
      (((liestVertragGlob P f).map globCode).filter
        fun c => decide (c ∈ globs.map globCode))) := by
    rcases List.mem_append.mp hmem with hT | hG
    · obtain ⟨hm, hd⟩ := List.mem_filter.mp hT
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
      exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨t, liestTab_in_liestVertragTab P f t ht, rfl⟩, hd⟩))
    · obtain ⟨hm, hd⟩ := List.mem_filter.mp hG
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
      exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨g, liestGlob_in_liestVertragGlob P f g hg, rfl⟩, hd⟩))
  exact List.mem_flatMap.mpr ⟨f, hf, hgoal⟩

/-- Die Vertrags-Codes ueberleben die Invarianten-Erweiterung. -/
theorem liesAusMitVertrag_in_MitInv (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (invs : List D.Inv) (n : Nat) (c : Nat)
    (h : c ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P n) :
    c ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs n := by
  unfold liesAusMitVertrag at h
  obtain ⟨f, hf, hmem⟩ := List.mem_flatMap.mp h
  unfold liesAusMitInv
  have hgoal : c ∈ ((((liestVertragMitInvTab P f invs).map tabCode).filter
        fun c => decide (c ∈ tabs.map tabCode)) ++
      (((liestVertragMitInvGlob P f invs).map globCode).filter
        fun c => decide (c ∈ globs.map globCode))) := by
    rcases List.mem_append.mp hmem with hT | hG
    · obtain ⟨hm, hd⟩ := List.mem_filter.mp hT
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
      exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨t, liestVertragTab_in_MitInvTab P f invs t ht, rfl⟩, hd⟩))
    · obtain ⟨hm, hd⟩ := List.mem_filter.mp hG
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
      exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨g, liestVertragGlob_in_MitInvGlob P f invs g hg, rfl⟩, hd⟩))
  exact List.mem_flatMap.mpr ⟨f, hf, hgoal⟩

/-- Der gerechnete Schreib-Fussabdruck liegt in der Traegerdomaene. -/
theorem fussAus_in_traegerAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat)
    (n : Nat) (c : Nat)
    (h : c ∈ fussAus tabs tabCode globs globCode fns fnCode n) :
    c ∈ traegerAus tabs tabCode globs globCode := by
  unfold fussAus at h
  obtain ⟨f, _, hmem⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hmem with hT | hG
  · obtain ⟨t, htmem, rfl⟩ := List.mem_map.mp hT
    unfold traegerAus
    exact List.mem_append.mpr
      (Or.inl (List.mem_map.mpr ⟨t, (List.mem_filter.mp htmem).1, rfl⟩))
  · obtain ⟨g, hgmem, rfl⟩ := List.mem_map.mp hG
    unfold traegerAus
    exact List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨g, (List.mem_filter.mp hgmem).1, rfl⟩))

/-- Die Rumpf-Lesehuelle liegt in der Traegerdomaene. -/
theorem liesAus_in_traegerAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (n : Nat) (c : Nat)
    (h : c ∈ liesAus tabs tabCode globs globCode fns fnCode P n) :
    c ∈ traegerAus tabs tabCode globs globCode := by
  unfold liesAus at h
  obtain ⟨f, _, hmem⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hmem with hT | hG
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hT
    have hd' : decide (c ∈ tabs.map tabCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inl (of_decide_eq_true hd'))
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hG
    have hd' : decide (c ∈ globs.map globCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inr (of_decide_eq_true hd'))

/-- Die Vertrags-Lesehuelle liegt in der Traegerdomaene. -/
theorem liesAusMitVertrag_in_traegerAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (n : Nat) (c : Nat)
    (h : c ∈ liesAusMitVertrag tabs tabCode globs globCode fns fnCode P n) :
    c ∈ traegerAus tabs tabCode globs globCode := by
  unfold liesAusMitVertrag at h
  obtain ⟨f, _, hmem⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hmem with hT | hG
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hT
    have hd' : decide (c ∈ tabs.map tabCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inl (of_decide_eq_true hd'))
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hG
    have hd' : decide (c ∈ globs.map globCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inr (of_decide_eq_true hd'))

/-- Die Invarianten-Lesehuelle liegt in der Traegerdomaene. -/
theorem liesAusMitInv_in_traegerAus (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (fns : List D.Fn) (fnCode : D.Fn → Nat) (P : Programm D)
    (invs : List D.Inv) (n : Nat) (c : Nat)
    (h : c ∈ liesAusMitInv tabs tabCode globs globCode fns fnCode P invs n) :
    c ∈ traegerAus tabs tabCode globs globCode := by
  unfold liesAusMitInv at h
  obtain ⟨f, _, hmem⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hmem with hT | hG
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hT
    have hd' : decide (c ∈ tabs.map tabCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inl (of_decide_eq_true hd'))
  · obtain ⟨_, hd⟩ := List.mem_filter.mp hG
    have hd' : decide (c ∈ globs.map globCode) = true := hd
    unfold traegerAus
    exact List.mem_append.mpr (Or.inr (of_decide_eq_true hd'))

/-- **Beruehrt heisst getragen:** was der errechnete Bau als Fussabdruck
    meldet, liegt in seinem `traeger` -- die `hmem`-Seite der
    `geteilt_treu`-Praemissen, eingeloeost statt getragen. -/
theorem bauAus_schreibtFn_in_traeger (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (g : Nat) (c : Nat)
    (h : c ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).schreibtFn g) :
    c ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).traeger := by
  have h' : c ∈ fussAus tabs tabCode globs globCode fns fnCode g := h
  show c ∈ traegerAus tabs tabCode globs globCode
  exact fussAus_in_traegerAus tabs tabCode globs globCode fns fnCode g c h'

/-- **Jeder Schritt hat einen Eintritt**, ueber dem errechneten Bau in
    Spiegel-Form (`Geteilt.lauf_hat_eintritt` durch `bauLaufSpiegel_genau`). -/
theorem eintritt_aus_baulaufSpiegel_aus_bau (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (fuel : Nat) (l : List (Nat × Nat))
    (hl : bauLaufSpiegel
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare) fuel l)
    (s : Nat × Nat) (hs : s ∈ l) :
    ∃ e, (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).eintritt[s.1]? = some e :=
  Geteilt.lauf_hat_eintritt _ fuel l
    ((bauLaufSpiegel_genau _ fuel l).mp hl) s hs

/-- **Nur deklarierte Paare teilen den Lauf**, ueber dem errechneten Bau in
    Spiegel-Form (`Geteilt.nur_deklariert_teilt_lauf` durch
    `bauLaufSpiegel_genau`). -/
theorem nur_deklariert_aus_baulaufSpiegel_aus_bau (P : Programm D)
    (fns : List D.Fn) (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (eintritt : List D.Fn) (paare : List (Nat × Nat))
    (fuel : Nat) (l : List (Nat × Nat))
    (hl : bauLaufSpiegel
      (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare) fuel l)
    (s₁ s₂ : Nat × Nat) (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l) (hfg : s₁.1 ≠ s₂.1) :
    (s₁.1, s₂.1) ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).neben ∨
    (s₂.1, s₁.1) ∈ (bauAus P fns fnCode tabs tabCode globs globCode eintritt paare).neben :=
  Geteilt.nur_deklariert_teilt_lauf _ fuel l
    ((bauLaufSpiegel_genau _ fuel l).mp hl) s₁ s₂ h₁ h₂ hfg

/-- **Die Verweigerungspflichten des Pruefers, ein Register (gebucht, nicht
    bewiesen).** Jede Konjunktion nennt die fehlende Regel beim Namen (B1-B3
    im Kopf dieses Abschnitts): was die Rechnung wirft (`ruftNorm`,
    `liesAus*`, `nebenAus`), verweigert der Pruefer -- fail-closed, nicht
    geraten. -/
def offeneVerweigerungspflichten (P : Programm D) (fns : List D.Fn)
    (fnCode : D.Fn → Nat)
    (tabs : List D.Tab) (tabCode : D.Tab → Nat)
    (globs : List D.Glob) (globCode : D.Glob → Nat)
    (invs : List D.Inv)
    (B : Geteilt.Bau) (Nb : Nebeneinander) : Prop :=
  kantenVoll P fns fnCode ∧
  liesVollMitVertrag P fns invs tabs tabCode globs globCode ∧
  paarVoll B Nb

#print axioms Gabbro.Grammatik.Extraktion.liesTreue_aus_liesAus
#print axioms Gabbro.Grammatik.Extraktion.liestTab_in_liestVertragTab
#print axioms Gabbro.Grammatik.Extraktion.liestGlob_in_liestVertragGlob
#print axioms Gabbro.Grammatik.Extraktion.liestVertragTab_in_MitInvTab
#print axioms Gabbro.Grammatik.Extraktion.liestVertragGlob_in_MitInvGlob
#print axioms Gabbro.Grammatik.Extraktion.liesAus_in_MitVertrag
#print axioms Gabbro.Grammatik.Extraktion.liesAusMitVertrag_in_MitInv
#print axioms Gabbro.Grammatik.Extraktion.fussAus_in_traegerAus
#print axioms Gabbro.Grammatik.Extraktion.liesAus_in_traegerAus
#print axioms Gabbro.Grammatik.Extraktion.liesAusMitVertrag_in_traegerAus
#print axioms Gabbro.Grammatik.Extraktion.liesAusMitInv_in_traegerAus
#print axioms Gabbro.Grammatik.Extraktion.bauAus_schreibtFn_in_traeger
#print axioms Gabbro.Grammatik.Extraktion.eintritt_aus_baulaufSpiegel_aus_bau
#print axioms Gabbro.Grammatik.Extraktion.nur_deklariert_aus_baulaufSpiegel_aus_bau

end Gabbro.Grammatik.Extraktion