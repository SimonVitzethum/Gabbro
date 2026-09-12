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
import Grammatik.Maschine
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
  | .axiomCall _ _ _ _ _ _ _ => []
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
  | .axiomCall _ args _ _ _ _ _ => args.orte
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
  | .shl _ _ _ _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .shr _ _ _ _ _ a b =>
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

/-! ## 14. The `prog` extraction: per-thread atoms from bodies

    What `Ziel.lean` §9b books as its single residual footprint premise: the
    goal consumes `prog : PCProg D` (one atom per thread and step) as
    own-logic -- the per-thread atom sequences are handed in by hand, and
    each `PCSchritt` rule verifies the pointed-to atom (`hpc` positions it,
    `hΛa` ties it to the fired statement, `hmark`/`hcar` check it against
    the step's events). This section computes that annotation from bodies,
    in the `fussAus`/`stmtOrte` style: a traversal over `Stmt`/`Block`/
    `Endblock`/`Arms`/`GrundArms` flattens each body into its atom sequence
    (`stmtAtome` and friends), and `progAus` runs that flattening per
    thread through a thread-to-function map (`code`).

    Every constructor stands explicitly -- including the ones that emit NO
    atom -- for the same reason as in §1: a silent drop must read as a
    decision, not as an oversight.

    What emits an atom: exactly the constructs a `GenSchritt`/`PCSchritt`
    can fire. A leaf `Stmt` (`istBlatt = true`) fires as `blatt`, so it
    emits one atom: `leaf` carrying the statement's own `Λ` as `Λa` (hence
    `hΛa` closes by `rfl` -- `stmtAtome_blatt_eq`) and, as `cs`, the written
    carrier plus the `stmtOrte` read hull (`stmtTraeger`,
    `stmtAtome_traeger_deckt`). A `locks L` side fires as `take`/`rel`, so
    it emits the bracket around its body (`stmtAtome_locks`). Compound
    statements (`ite`, calls, loops, ...) never fire as steps -- they open
    into further steps -- so they emit only their sub-bodies' atoms (both
    arms of a branch: over-approximation, never less, as in §8).

    What emits NO atom, and why (booked, not hidden):
    S8. Block-level reads (`bind`, `awaits`, `exchange`, the `regLiesElse`
        promise, `narrow`/`pruefung`/`gleit` conditions): no `GenSchritt`
        case fires a `Block` form, so these reads produce no PC-step event.
        They stay covered by the `stmtOrte` hull (§12); threading them as
        steps is `Maschine.lean` §12's booked Block-continuation work.
    S9. Call arguments and branch conditions: calls and compounds never
        fire, so their argument/condition reads produce no PC-step event.
        Callee bodies reach threads through the thread map (`code`); the
        foreign-body duty stays with S7.
    S10. Terminal `Endblock` forms (`ret`, `leave`, `next`):
        `GenSchritt.blatt` fires `Stmt` only, so a terminal never fires.
        Its expression reads are booked with S8.
    S11. `axiomCall` writes come from the axiom declaration, not the body:
        `stmtTraeger` filters the declared domains (`tabs`/`globs`) by
        `D.aschreibt`/`D.agschreibt`, exactly as `fussAus` filters by
        `D.schreibt`/`D.gschreibt` (§3).

    Remainder (booked, not hidden): the execution link. What closes here is
    the program-text match -- extracted atoms carry the fired statement's
    `Λ` definitionally and cover its static footprint. Discharging `hmark`/
    `hcar` of a fired step against the extracted atom needs, per leaf, the
    `execStmt` event characterization (every event's `lambda` is the
    statement's `Λ`; every event's `traeger` is the written carrier or a
    `stmtOrte` carrier) -- unwritten, the same grain as the §13 keystone
    but one level up (steps instead of expressions).
-/

/-- The written carrier of one statement: the touch no read hull covers.
    Compounds carry none (they never fire); `axiomCall` carries its declared
    writes over the given domains (`fussAus` in §3). -/
def stmtTraeger (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (D.Tab ⊕ D.Glob)
  | .assignSlot t _ _ _ _ _ => [.inl t]
  | .assignDurch _ t _ _ _ _ _ _ => [.inl t]
  | .assignGlob g _ _ _ => [.inr g]
  | .schreibBytes t _ _ _ _ _ _ _ _ _ => [.inl t]
  | .assignVar _ _ => []
  | .uebergang t _ _ _ _ _ _ _ _ _ => [.inl t]
  | .ite _ _ _ => []
  | .onOption _ _ _ => []
  | .onTag _ _ => []
  | .onGrund _ _ => []
  | .call _ _ _ _ => []
  | .callInd _ _ _ _ => []
  | .locks _ _ _ => []
  | .breaking _ _ => []
  | .traverse _ _ _ => []
  | .retry _ _ _ _ => []
  | .forever _ _ _ => []
  | .axiomCall a _ _ _ _ _ _ =>
      (tabs.filter (D.aschreibt a)).map .inl ++
        (globs.filter (D.agschreibt a)).map .inr
  | .regSchreib _ _ _ => []
  | .transition _ _ _ _ _ _ _ => []
  | .publish g _ _ _ _ _ => [.inr g]
  | .advances _ _ _ _ => []
  | .retires _ _ _ _ => []
  | .ret _ _ => []
  | .retGrund _ _ => []
  | .leave _ => []
  | .next _ => []

mutual

/-- The atoms of one statement: a leaf emits its singleton (`Λa` IS the
    statement's `Λ`, `cs` the written carrier plus the read hull);
    compounds emit their sub-bodies' atoms (`locks` bracketed by its sides);
    calls emit none (they open into further steps, S9). -/
def stmtAtome (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List (PCAtom D)
  | .ite _ t e => blockAtome tabs globs t ++ blockAtome tabs globs e
  | .onOption _ p a => blockAtome tabs globs p ++ blockAtome tabs globs a
  | .onTag _ arms => armsAtome tabs globs arms
  | .onGrund _ arms => grundArmsAtome tabs globs arms
  | .call _ _ _ _ => []
  | .callInd _ _ _ _ => []
  | .locks L _ body =>
      [PCAtom.take L] ++ blockAtome tabs globs body ++ [PCAtom.rel L]
  | .breaking _ body => blockAtome tabs globs body
  | .traverse _ _ body => blockAtome tabs globs body
  | .retry _ _ body ueber =>
      blockAtome tabs globs body ++ blockAtome tabs globs ueber
  | .forever _ _ body => blockAtome tabs globs body
  | s@(.assignSlot _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.assignDurch _ _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.assignGlob _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.schreibBytes _ _ _ _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.assignVar _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.uebergang _ _ _ _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.axiomCall _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.regSchreib _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.transition _ _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.publish _ _ _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.advances _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.retires _ _ _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.ret _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.retGrund _ _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.leave _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]
  | s@(.next _) =>
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)]

/-- The atoms of one block: the statement atoms in order; pure reads
    (`bind`, `awaits`, `exchange`, conditions) emit none (S8); else-branches
    emit theirs (either side may run). -/
def blockAtome (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List (PCAtom D)
  | .nil => []
  | .cons s rest => stmtAtome tabs globs s ++ blockAtome tabs globs rest
  | .bind _ rest => blockAtome tabs globs rest
  | .bindCall _ _ _ _ _ rest => blockAtome tabs globs rest
  | .bindCallInd _ _ _ _ _ rest => blockAtome tabs globs rest
  | .bindCallElse _ _ _ _ _ err rest =>
      endblockAtome tabs globs err ++ blockAtome tabs globs rest
  | .bindAxiom _ _ _ _ _ rest => blockAtome tabs globs rest
  | .regLies _ _ rest => blockAtome tabs globs rest
  | .regLiesElse _ _ _ sonst rest =>
      endblockAtome tabs globs sonst ++ blockAtome tabs globs rest
  | .awaits _ _ _ _ rest => blockAtome tabs globs rest
  | .exchange _ _ _ _ rest => blockAtome tabs globs rest
  | .narrow _ _ _ sonst rest =>
      endblockAtome tabs globs sonst ++ blockAtome tabs globs rest
  | .pruefung _ sonst rest =>
      endblockAtome tabs globs sonst ++ blockAtome tabs globs rest
  | .gleit _ _ _ _ _ rest => blockAtome tabs globs rest
  | .gleitLit _ _ _ rest => blockAtome tabs globs rest
  | .gleitVon _ _ _ rest => blockAtome tabs globs rest
  | .gleitNarrow _ _ _ sonst rest =>
      endblockAtome tabs globs sonst ++ blockAtome tabs globs rest

/-- The atoms of a non-falling block: terminals emit none (they never fire,
    S10); the chain emits its statements' atoms. -/
def endblockAtome (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (PCAtom D)
  | .ret _ _ => []
  | .retGrund _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => stmtAtome tabs globs s ++ endblockAtome tabs globs rest
  | .bind _ rest => endblockAtome tabs globs rest

/-- The atoms of a case split: every arm may run. -/
def armsAtome (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → List (PCAtom D)
  | .nil => []
  | .cons b rest => blockAtome tabs globs b ++ armsAtome tabs globs rest

/-- The atoms of a ground case split: every arm may run. -/
def grundArmsAtome (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → List (PCAtom D)
  | .nil => []
  | .cons b rest => blockAtome tabs globs b ++ grundArmsAtome tabs globs rest

end

/-- **The thread program from bodies.** Thread `f` runs `code f`: its
    program text is that body's flattened atoms. This is the annotation the
    goal's build-time premise consumes (`Ziel.lean` §9b) -- computed here
    instead of handed in by hand. -/
def progAus (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) : PCProg D :=
  fun f => endblockAtome tabs globs (P.rumpf (code f))

/-- `progAus` unfolds to the body's atoms. -/
theorem progAus_aus_rumpf (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) (f : Faden) :
    progAus P code tabs globs f = endblockAtome tabs globs (P.rumpf (code f)) :=
  rfl

/-- A `locks` body extracts to its bracketed atoms: the sides a
    `PCSchritt.take`/`rel` step points at. -/
theorem stmtAtome_locks (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ)) :
    stmtAtome tabs globs (Stmt.locks L hr body) =
      [PCAtom.take L] ++ blockAtome tabs globs body ++ [PCAtom.rel L] :=
  rfl

/-- **The leaf match.** A leaf statement extracts to exactly one atom, and
    its `Λa` IS the statement's `Λ`: a witness firing this statement takes
    the pointed-to atom to be this one, and `hΛa` closes by `rfl`. -/
theorem stmtAtome_blatt_eq {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (tabs : List D.Tab) (globs : List D.Glob) (h : s.istBlatt = true) :
    stmtAtome tabs globs s =
      [PCAtom.leaf Λ (stmtTraeger tabs globs s ++ stmtOrte s)] := by
  cases s <;> first | exact rfl | (simp [Stmt.istBlatt] at h)

/-- **Mark cover.** Every held mark of a leaf statement is named in its
    atom's mark text: what `hmark` must find is there. -/
theorem stmtAtome_marken_deckt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (tabs : List D.Tab) (globs : List D.Glob) (h : s.istBlatt = true)
    (m : D.Marke) (st : Nat) (hm : Res.marke m st ∈ Λ) :
    m ∈ (stmtAtome tabs globs s).flatMap PCAtom.marks := by
  rw [stmtAtome_blatt_eq s tabs globs h]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    PCAtom.marks]
  exact List.mem_filterMap.mpr ⟨Res.marke m st, hm, rfl⟩

/-- **Carrier cover.** The written carrier and every read-hull carrier of a
    leaf statement sit in its atom's carrier text: what `hcar` must find is
    there. -/
theorem stmtAtome_traeger_deckt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (tabs : List D.Tab) (globs : List D.Glob) (h : s.istBlatt = true)
    (o : D.Tab ⊕ D.Glob)
    (ho : o ∈ stmtTraeger tabs globs s ++ stmtOrte s) :
    o ∈ (stmtAtome tabs globs s).flatMap PCAtom.carriers := by
  rw [stmtAtome_blatt_eq s tabs globs h]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    PCAtom.carriers]
  exact ho

/-- **Program fidelity.** Every atom the body traversal yields is program
    text: the computed `prog` covers the flattened bodies, never less (the
    `kantenTreue` shape of §8, one level down: atoms, not edges). -/
def progTreue (prog : PCProg D) (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) : Prop :=
  ∀ f, ∀ a ∈ endblockAtome tabs globs (P.rumpf (code f)), a ∈ prog f

/-- The computed program is faithful: what the bodies flatten to is text. -/
theorem progTreue_aus_progAus (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob) :
    progTreue (progAus P code tabs globs) P code tabs globs := by
  intro f a ha
  exact ha

/-- Sprechprobe: the probe bodies are bare terminals (S10: never fired), so
    the extracted thread program is empty -- the computation runs to the
    end, loudly (`rfl` fails at elaboration on a wrong atom). -/
example : progAus miniP (fun _ => true) miniTabs miniGlobs 0 = [] := rfl

#print axioms Gabbro.Grammatik.Extraktion.progAus_aus_rumpf
#print axioms Gabbro.Grammatik.Extraktion.stmtAtome_locks
#print axioms Gabbro.Grammatik.Extraktion.stmtAtome_blatt_eq
#print axioms Gabbro.Grammatik.Extraktion.stmtAtome_marken_deckt
#print axioms Gabbro.Grammatik.Extraktion.stmtAtome_traeger_deckt
#print axioms Gabbro.Grammatik.Extraktion.progTreue_aus_progAus

/-! ## 17. The execution link: fired leaf events against extracted atoms

    (Tasked as §15; §§15-16 are already taken and the file ends with a second
    §14 -- the `prog` extraction -- so this section is §17: numbers stay
    unique, content stays appended, nothing existing moves.)

    What the English §14 (`prog` extraction) books as its remainder: discharging
    a fired step's `hmark`/`hcar` against the extracted atom needs the per-leaf
    `execStmt` event characterization. This section proves it and discharges
    the checks.

    * `mem_leseEr` is the read-event shape (one `World.lese`): statement `Λ`
      exactly, carriers inside the read list.
    * `rep_append_single`/`schreibBytes_spur_eq` are the byte-write shape:
      `World.schreibBytes` emits one `zugriff` per byte; lock state is untouched
      by `zugriff`, so every event shares the entry `haelt`.
    * `uebergang_ereignis_aus_blatt` is the `uebergang` branch case, split off:
      `split` with bullets inside `cases ... with` breaks the outer
      alternatives (measured: every later alternative reports "not provided"),
      so it lives here as its own lemma.
    * `execEreignis_aus_blatt_ohne_axiomCall` is the characterization per leaf:
      a fired non-oracle leaf step's every new event carries exactly the
      statement's `Λ`, and every carrier it touches sits in the written
      carrier plus the `stmtOrte` read hull.
    * `hmark_hcar_aus_progAus_ohne_axiomCall` discharges the `PCSchritt`
      footprint checks (`hmark`/`hcar`) against `progAus` atoms: a fired
      non-oracle leaf whose counter points at its extracted atom names only
      that atom's marks and touches only its carriers -- hence the thread's
      program text (`pcAtom_mem_marks`/`pcAtom_mem_carriers`).

    Remainder (booked, not hidden; continuing the S-series of §14):
    S12. Atom identity (`hcs`): the counter must point at the atom
         `stmtAtome_blatt_eq` yields for the fired statement. Positing the
         pointed-to atom is the scheduler/witness duty (as `hpc` is); proving
         the counter always does so is the scheduling argument, not this
         section.
    S13. `axiomCall`: the oracle (`O.wirkt`) answers with an arbitrary world,
         so its events carry arbitrary `Λ`/carriers. Closing it needs an
         oracle-event contract (every oracle event names the statement `Λ`
         within the declared writes plus `args.orte`) -- carried as a
         hypothesis by `GenSchritt`/`PCSchritt`, never derived here.
-/

/-- Read events of one `World.lese`: they carry the statement `Λ` exactly,
    and every carrier they name sits in the read list. -/
theorem mem_leseEr {Λ : List (Res D)} {h : List D.Lock}
    {os : List (D.Tab ⊕ D.Glob)} {e : Ereignis D}
    (hm : e ∈ os.map fun o => match o with
      | .inl t => Ereignis.zugriff t false Λ h
      | .inr g => Ereignis.gzugriff g false Λ h) :
    e.lambda = Λ ∧ ∀ o, e.traeger = some o → o ∈ os := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
  cases o with
  | inl t =>
      refine ⟨rfl, fun o' h' => ?_⟩
      have h2 : o' = .inl t := by simpa [Ereignis.traeger] using h'.symm
      rw [h2]; exact ho
  | inr g =>
      refine ⟨rfl, fun o' h' => ?_⟩
      have h2 : o' = .inr g := by simpa [Ereignis.traeger] using h'.symm
      rw [h2]; exact ho

/-- Appending one more copy on the right is consing on the left, for
    `replicate`. -/
theorem rep_append_single {α : Type} (n : Nat) (a : α) :
    List.replicate n a ++ [a] = a :: List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- `schreibBytes` emits exactly one `zugriff` event per byte, all with the
    statement `Λ` on the written carrier (lock state is untouched by
    `zugriff`, so every event shares the entry `haelt`). -/
theorem schreibBytes_spur_eq (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (k : Int) (bs : List Byte) :
    (σ.schreibBytes t f hf Λ k bs).spur =
      List.replicate bs.length (Ereignis.zugriff t true Λ σ.haelt) ++ σ.spur := by
  induction bs generalizing σ k with
  | nil => rfl
  | cons b bs ih =>
      simp only [World.schreibBytes]
      rw [ih]
      have hhaelt : (σ.schreibSlot t Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).haelt =
          σ.haelt := rfl
      have hspur1 : (σ.schreibSlot t Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).spur =
          [Ereignis.zugriff t true Λ σ.haelt] ++ σ.spur := rfl
      rw [hhaelt, hspur1, List.length_cons, ← List.append_assoc,
        rep_append_single, List.replicate_succ]

/-- `uebergang` through the taken branch: one write plus the
    `.inl t :: i.orte` reads. Split off from `execEreignis_aus_blatt_ohne_axiomCall`:
    `split` with bullets inside `cases ... with` breaks the outer alternatives,
    so this branch case lives here as its own lemma. -/
theorem uebergang_ereignis_aus_blatt (O : Orakel D) (passes : Nat)
    {V : Vertrag D} (l : Bool) {Γ : Ctx} {Λ : List (Res D)}
    (tabs : List D.Tab) (globs : List D.Glob)
    (t : D.Tab) (f : D.Feld t) {lo hi : Int} (hτ : D.typ t f = .int lo hi)
    (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int)
    (hn : lo ≤ nach ∧ nach ≤ hi)
    (he : D.erlaubt t f von nach = true) (hw : V.schreibt t = true)
    (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      ((Stmt.uebergang t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ Λ)) σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    (∀ e ∈ neu, e.lambda = Λ) ∧
      (∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ stmtTraeger tabs globs
          ((Stmt.uebergang t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ Λ)) ++
          stmtOrte ((Stmt.uebergang t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ Λ))) := by
  simp only [execStmt] at hstep
  split at hstep
  · simp only [Ausgang.welt, Option.some.injEq] at hstep
    have hspur : σ'.spur =
        [Ereignis.zugriff t true Λ (σ.lese Λ (.inl t :: i.orte)).haelt] ++
        (.inl t :: i.orte).map (fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
          | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
      rw [← hstep]; rfl
    rw [hspur] at hneu
    have hneueq := List.append_cancel_right hneu
    subst hneueq
    constructor
    · intro e' he'
      rcases List.mem_append.mp he' with h1 | h1
      · obtain rfl := List.mem_singleton.mp h1
        rfl
      · exact (mem_leseEr h1).1
    · intro e' he' o ho
      rcases List.mem_append.mp he' with h1 | h1
      · obtain rfl := List.mem_singleton.mp h1
        have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
        subst ho'
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
      · have hmem : o ∈ .inl t :: i.orte := (mem_leseEr h1).2 o ho
        simp only [stmtTraeger, stmtOrte]
        rcases List.mem_cons.mp hmem with rfl | hm
        · exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · exact List.mem_append.mpr (Or.inr hm)
  · simp only [Ausgang.welt] at hstep
    simp at hstep

/-- A fired non-oracle leaf step carries exactly its statement footprint:
    every new event names the statement `Λ`, and every carrier it touches
    sits in the written carrier plus the `stmtOrte` read hull. `axiomCall`
    is excluded: the oracle (`O.wirkt`) answers with an arbitrary world, so
    its events carry arbitrary `Λ`/carriers (remainder S13 below). -/
theorem execEreignis_aus_blatt_ohne_axiomCall
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (tabs : List D.Tab) (globs : List D.Glob)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    (∀ e ∈ neu, e.lambda = Λ) ∧
      (∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ stmtTraeger tabs globs s ++ stmtOrte s) := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
          (i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ i.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignDurch p t ht f i e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).haelt] ++
          (p.orte ++ i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ p.orte ++ i.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.gzugriff g true Λ (σ.lese Λ e.orte).haelt] ++
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inr g := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | schreibBytes t f hf n i hlo hhi e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          List.replicate (zahlZuBytes n
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n).length
            (Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt) ++
          ((i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur) := by
        rw [← hstep, schreibBytes_spur_eq]; rfl
      rw [hspur, ← List.append_assoc] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · have heq : e' =
              Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt :=
            (List.mem_replicate.mp h1).2
          rw [heq]
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · have heq : e' =
              Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt :=
            (List.mem_replicate.mp h1).2
          rw [heq] at ho
          have ho' : o = .inl t := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ i.orte ++ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | assignVar x e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        exact (mem_leseEr he').1
      · intro e' he' o ho
        have hmem : o ∈ e.orte := (mem_leseEr he').2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  | uebergang t f hτ i von nach hn he hw hL =>
      exact uebergang_ereignis_aus_blatt O passes l tabs globs t f hτ i von nach
        hn he hw hL σ ρ σ' neu hstep hneu
  | ite c t e => simp [Stmt.istBlatt] at hleaf
  | onOption o p a => simp [Stmt.istBlatt] at hleaf
  | onTag v arms => simp [Stmt.istBlatt] at hleaf
  | onGrund r arms => simp [Stmt.istBlatt] at hleaf
  | call f args hp hr => simp [Stmt.istBlatt] at hleaf
  | callInd p args hp hr => simp [Stmt.istBlatt] at hleaf
  | locks L hr body => simp [Stmt.istBlatt] at hleaf
  | breaking i body => simp [Stmt.istBlatt] at hleaf
  | traverse t inv body => simp [Stmt.istBlatt] at hleaf
  | retry n bis body ueberlauf => simp [Stmt.istBlatt] at hleaf
  | forever a inv body => simp [Stmt.istBlatt] at hleaf
  | axiomCall a args h hw hg hd hgd => exact False.elim hax
  | regSchreib r hk e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        exact (mem_leseEr he').1
      · intro e' he' o ho
        have hmem : o ∈ e.orte := (mem_leseEr he').2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'
  | publish g e payload hp hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.gzugriff g true Λ (σ.lese Λ e.orte).haelt] ++
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          rfl
        · exact (mem_leseEr h1).1
      · intro e' he' o ho
        rcases List.mem_append.mp he' with h1 | h1
        · obtain rfl := List.mem_singleton.mp h1
          have ho' : o = .inr g := by simpa [Ereignis.traeger] using ho.symm
          subst ho'
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
        · have hmem : o ∈ e.orte := (mem_leseEr h1).2 o ho
          simp only [stmtTraeger, stmtOrte]
          exact List.mem_append.mpr (Or.inr hmem)
  | advances m a h hs =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'
  | retires m s h a =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'
  | ret e hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          (e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        exact (mem_leseEr he').1
      · intro e' he' o ho
        have hmem : o ∈ e.orte := (mem_leseEr he').2 o ho
        simp only [stmtTraeger, stmtOrte]
        exact List.mem_append.mpr (Or.inr hmem)
  | retGrund r hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'
  | leave h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'
  | next h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur = ([] : List (Ereignis D)) ++ σ.spur := by rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      constructor
      · intro e' he'
        simp at he'
      · intro e' he' o ho
        simp at he'

/-- The `PCSchritt` footprint checks discharged against `progAus` atoms: a
    fired non-oracle leaf step whose counter points at its extracted atom
    names only that atom's marks and touches only its carriers -- hence the
    thread's program text (`pcAtom_mem_marks`/`pcAtom_mem_carriers`). The
    atom-identity premise (`hcs`) is the scheduler/witness duty: the counter
    must point at the atom `stmtAtome_blatt_eq` yields for `s` (remainder S12 below). -/
theorem hmark_hcar_aus_progAus_ohne_axiomCall
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob)
    (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (M : GenMaschine D) (f : Faden) (ρ : Env D Γ)
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ (M.weltVon f).spur)
    (pc : PCStand) (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (progAus P code tabs globs f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ)
    (hcs : cs = stmtTraeger tabs globs s ++ stmtOrte s) :
    (∀ e ∈ neu, ∀ (m : D.Marke) (st : Nat), Res.marke m st ∈ e.lambda →
      m ∈ (progAus P code tabs globs).marks f) ∧
    (∀ e ∈ neu, ∀ o, e.traeger = some o →
      o ∈ (progAus P code tabs globs).carriers f) := by
  obtain ⟨hlam, hcar⟩ :=
    execEreignis_aus_blatt_ohne_axiomCall O passes s hleaf hax tabs globs
      _ ρ σ' neu hstep hneu
  have ha : PCAtom.leaf Λa cs ∈ progAus P code tabs globs f :=
    List.mem_of_getElem? hpc
  constructor
  · intro e he m st hm
    rw [hlam e he] at hm
    rw [← hΛa] at hm
    exact pcAtom_mem_marks _ _ _ ha m
      (by simp only [PCAtom.marks]
          exact List.mem_filterMap.mpr ⟨Res.marke m st, hm, rfl⟩)
  · intro e he o ho
    have hmem : o ∈ stmtTraeger tabs globs s ++ stmtOrte s := hcar e he o ho
    apply pcAtom_mem_carriers _ _ _ ha o
    simp only [PCAtom.carriers]
    rw [hcs]
    exact hmem

#print axioms Gabbro.Grammatik.Extraktion.mem_leseEr
#print axioms Gabbro.Grammatik.Extraktion.rep_append_single
#print axioms Gabbro.Grammatik.Extraktion.schreibBytes_spur_eq
#print axioms Gabbro.Grammatik.Extraktion.uebergang_ereignis_aus_blatt
#print axioms Gabbro.Grammatik.Extraktion.execEreignis_aus_blatt_ohne_axiomCall
#print axioms Gabbro.Grammatik.Extraktion.hmark_hcar_aus_progAus_ohne_axiomCall

/-! ## 18. The oracle bound: event characterization for `axiomCall` leaves

    (Closes the S13 remainder of §17 for the bounded-oracle fragment.)

    The contract is the tree's own named oracle bound, `GutO` (`Satz.lean`):
    for every axiom, entry world, and environment, the oracle answer respects
    the declared footprint (`Rahmen (D.aschreibt a) (D.agschreibt a)`), keeps
    the held locks, and emits no events of its own (`spur` preserved). It
    travels as a hypothesis -- the `dma_inhalt` class (`Geraet.lean`): a NAMED
    assumption, never derived here, never an axiom.

    Under that bound a fired `axiomCall` leaf emits exactly its argument
    reads: the oracle adds nothing, so `neu` is the `args.orte` read prefix
    (`mem_leseEr`); every new event names the statement `Λ`, and every
    carrier it touches sits in the declared writes plus the read hull
    (`stmtTraeger ++ stmtOrte`).

    * `execEreignis_aus_axiomCall` is the characterization per oracle leaf.
    * `hmark_hcar_aus_progAus_axiomCall` discharges the `PCSchritt`
      footprint checks (`hmark`/`hcar`) against `progAus` atoms for oracle
      leaves -- the `hmark_hcar_aus_progAus_ohne_axiomCall` shape with the
      contract premise (`hO`) in place of the exclusion premise (`hax`).
      The proof consumes the `spur` conjunct of `GutO`; `Rahmen` and `haelt`
      ride along as the value-side bound (used by `stmt_gut`, harmless here).

    Remainder (booked, not hidden): oracles that emit their own events stay
    open. Closing them needs a per-event contract (every oracle-added event
    names the statement `Λ` within the declared writes plus `args.orte`) --
    same class, stronger duty, unwritten.
-/

/-- A fired oracle leaf step carries exactly its statement footprint, under
    the oracle bound: the oracle (`O.wirkt`) answers without emitting events
    of its own (`GutO`), so every new event is an argument read -- it names
    the statement `Λ`, and every carrier it touches sits in the declared
    writes plus the `args.orte` read hull. -/
theorem execEreignis_aus_axiomCall
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hO : GutO O)
    (tabs : List D.Tab) (globs : List D.Glob)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    (∀ e ∈ neu, e.lambda = Λ) ∧
      (∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ stmtTraeger tabs globs
          (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
          stmtOrte
            (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ)) := by
  have hspurO : ((O.wirkt a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1).spur =
      (σ.lese Λ args.orte).spur :=
    (hO a _ _).2.2
  simp only [execStmt] at hstep
  split at hstep
  · rename_i σ1 v ha
    simp only [Ausgang.welt, Option.some.injEq] at hstep
    subst hstep
    have hσ1 : σ1 = (O.wirkt a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1 := by
      have hfst := congrArg Prod.fst ha
      simp only [axiomAntwort] at hfst
      exact hfst.symm
    rw [hσ1, hspurO] at hneu
    have hneu2 : (args.orte.map fun o => match o with
        | .inl t => Ereignis.zugriff t false Λ σ.haelt
        | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur =
        neu ++ σ.spur := hneu
    have hneueq := List.append_cancel_right hneu2
    subst hneueq
    constructor
    · intro e' he'
      exact (mem_leseEr he').1
    · intro e' he' o ho
      have hmem : o ∈ args.orte := (mem_leseEr he').2 o ho
      simp only [stmtTraeger, stmtOrte]
      exact List.mem_append.mpr (Or.inr hmem)
  · simp [Ausgang.welt] at hstep

/-- The `PCSchritt` footprint checks discharged against `progAus` atoms for
    oracle leaves: a fired `axiomCall` leaf whose counter points at its
    extracted atom, under the oracle bound (`hO`), names only that atom's
    marks and touches only its carriers -- hence the thread's program text
    (`pcAtom_mem_marks`/`pcAtom_mem_carriers`). The atom-identity premise
    (`hcs`) stays the scheduler/witness duty (remainder S12 of §17). -/
theorem hmark_hcar_aus_progAus_axiomCall
    (O : Orakel D) (passes : Nat)
    (P : Programm D) (code : Faden → D.Fn)
    (tabs : List D.Tab) (globs : List D.Glob)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hO : GutO O)
    (M : GenMaschine D) (f : Faden) (ρ : Env D Γ)
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ (M.weltVon f).spur)
    (pc : PCStand) (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (progAus P code tabs globs f)[pc f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ)
    (hcs : cs = stmtTraeger tabs globs
      (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
      stmtOrte (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ)) :
    (∀ e ∈ neu, ∀ (m : D.Marke) (st : Nat), Res.marke m st ∈ e.lambda →
      m ∈ (progAus P code tabs globs).marks f) ∧
    (∀ e ∈ neu, ∀ o, e.traeger = some o →
      o ∈ (progAus P code tabs globs).carriers f) := by
  obtain ⟨hlam, hcar⟩ :=
    execEreignis_aus_axiomCall O passes a args h hw hg hd hgd hO tabs globs
      _ ρ σ' neu hstep hneu
  have ha : PCAtom.leaf Λa cs ∈ progAus P code tabs globs f :=
    List.mem_of_getElem? hpc
  constructor
  · intro e he m st hm
    rw [hlam e he] at hm
    rw [← hΛa] at hm
    exact pcAtom_mem_marks _ _ _ ha m
      (by simp only [PCAtom.marks]
          exact List.mem_filterMap.mpr ⟨Res.marke m st, hm, rfl⟩)
  · intro e he o ho
    have hmem : o ∈ stmtTraeger tabs globs
        (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) ++
        stmtOrte (Stmt.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ Λ) :=
      hcar e he o ho
    apply pcAtom_mem_carriers _ _ _ ha o
    simp only [PCAtom.carriers]
    rw [hcs]
    exact hmem

#print axioms Gabbro.Grammatik.Extraktion.execEreignis_aus_axiomCall
#print axioms Gabbro.Grammatik.Extraktion.hmark_hcar_aus_progAus_axiomCall

/-! ## 19. The hwit discharger: fired steps produce their zugriff events

    What `Ziel.lean` §10 books as its two remaining witness duties: the step
    witness (`hneu_wit`: the fired leaf's `neu` carries the `zugriff` event
    when the code writes the carrier) and the prefix witness (`hwit_old`:
    the old run's accesses are still posited, as scheduler duty). This
    section discharges the step duty at its source -- production by
    construction -- and names the induction base for the prefix duty.
    Read-only use of the §17 event shapes and the `execStmt` neu-event
    constructions (`schreibSlot`, `schreibBytes`, the taken `uebergang`
    branch); nothing existing moves.

    * `hwit_aus_feuerung_ohne_axiomCall` is the producer: a fired non-oracle
      leaf whose written carrier is the tracked table `t₀` (read as
      `.inl t₀ ∈ stmtTraeger tabs globs s`, §14) leaves a `zugriff` event
      for `t₀` in `neu` -- the write the `execStmt` shape puts there by
      construction. The `hneu_wit` duty of `kette_mit_zeugen[_orakel]` is
      then `fun _ => hwit_aus_feuerung_ohne_axiomCall ...`: the code
      predicate is vacuous once the leaf produces -- the event exists
      whenever the writing leaf fires, with `w = true` and the statement
      `Λ`.
    * `hwit_leer` is the prefix base: with no thread steps owed, no witness
      is owed -- the duty holds vacuously over any run. The induction step
      is the read-only `kette_mit_zeugen_schritt` link construction
      (`Ziel.lean` §10): old steps inherit from the package, the new
      writing step rides `genEigen_wit_index` on exactly the event produced
      here.

    Coverage (exactly): non-oracle leaves writing the tracked TABLE carrier
    (`assignSlot`, `assignDurch`, `uebergang`, `schreibBytes` with `0 < n`
    via `hbytes`); every premise is load-bearing (`hbytes` feeds the byte
    case, `hax` kills the oracle case, `hleaf` kills the compounds, `hmem`
    names the carrier in every other case).

    Remainder (booked, not hidden): `axiomCall` leaves (the oracle adds no
    events under `GutO`, §18 -- closing them needs the per-event oracle
    contract, same class as the S13 remainder); empty `schreibBytes`
    (`n = 0` writes nothing though the carrier is declared); leaves that
    write no table (`assignGlob`, `publish`, reads, terminals -- no table
    event exists to produce); globals (`gzugriff`, as `Ziel.lean` §10
    books); the full-run fold of the prefix duty over `PCReach`
    derivations (base here, step read-only, induction unwritten).
-/

/-- A fired non-oracle leaf that writes the tracked table produces its
    witness: `neu` carries a `zugriff` event for `t₀` (with `w = true` and
    the statement `Λ`). The byte writer needs `0 < n` (`hbytes`); `hstep`
    forces the taken `uebergang` branch, as in §17. -/
theorem hwit_aus_feuerung_ohne_axiomCall
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (tabs : List D.Tab) (globs : List D.Glob)
    (t₀ : D.Tab) (hmem : .inl t₀ ∈ stmtTraeger tabs globs s)
    (hbytes : match s with | .schreibBytes _ _ _ n _ _ _ _ _ _ => 0 < n | _ => True)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
      Ereignis.zugriff t₀ w Λw hwL ∈ neu := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [stmtTraeger] at hmem
      have hteq : t₀ = t := by simpa using List.mem_singleton.mp hmem
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
          (i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      refine ⟨true, Λ, (σ.lese Λ (i.orte ++ e.orte)).haelt, ?_⟩
      rw [hteq]
      exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
  | assignDurch p t ht f i e hw hL =>
      simp only [stmtTraeger] at hmem
      have hteq : t₀ = t := by simpa using List.mem_singleton.mp hmem
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          [Ereignis.zugriff t true Λ
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).haelt] ++
          (p.orte ++ i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
        rw [← hstep]; rfl
      rw [hspur] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      refine ⟨true, Λ, (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).haelt, ?_⟩
      rw [hteq]
      exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
  | assignGlob g e hw hL =>
      simp [stmtTraeger] at hmem
  | schreibBytes t f hf n i hlo hhi e hw hL =>
      simp only [stmtTraeger] at hmem
      have hteq : t₀ = t := by simpa using List.mem_singleton.mp hmem
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      have hspur : σ'.spur =
          List.replicate (zahlZuBytes n
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n).length
            (Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt) ++
          ((i.orte ++ e.orte).map (fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur) := by
        rw [← hstep, schreibBytes_spur_eq]; rfl
      rw [hspur, ← List.append_assoc] at hneu
      have hneueq := List.append_cancel_right hneu
      subst hneueq
      have hlen : (zahlZuBytes n
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n).length = n :=
        zahlZuBytes_length n _
      refine ⟨true, Λ, (σ.lese Λ (i.orte ++ e.orte)).haelt, ?_⟩
      rw [hteq]
      exact List.mem_append.mpr
        (Or.inl (List.mem_replicate.mpr ⟨by rw [hlen]; omega, rfl⟩))
  | assignVar x e =>
      simp [stmtTraeger] at hmem
  | uebergang t f hτ i von nach hn he hw hL =>
      simp only [stmtTraeger] at hmem
      have hteq : t₀ = t := by simpa using List.mem_singleton.mp hmem
      simp only [execStmt] at hstep
      split at hstep
      · simp only [Ausgang.welt, Option.some.injEq] at hstep
        have hspur : σ'.spur =
            [Ereignis.zugriff t true Λ (σ.lese Λ (.inl t :: i.orte)).haelt] ++
            (.inl t :: i.orte).map (fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := by
          rw [← hstep]; rfl
        rw [hspur] at hneu
        have hneueq := List.append_cancel_right hneu
        subst hneueq
        refine ⟨true, Λ, (σ.lese Λ (.inl t :: i.orte)).haelt, ?_⟩
        rw [hteq]
        exact List.mem_append.mpr (Or.inl (List.mem_singleton.mpr rfl))
      · simp only [Ausgang.welt] at hstep
        simp at hstep
  | ite c t e => simp [Stmt.istBlatt] at hleaf
  | onOption o p a => simp [Stmt.istBlatt] at hleaf
  | onTag v arms => simp [Stmt.istBlatt] at hleaf
  | onGrund r arms => simp [Stmt.istBlatt] at hleaf
  | call f args hp hr => simp [Stmt.istBlatt] at hleaf
  | callInd p args hp hr => simp [Stmt.istBlatt] at hleaf
  | locks L hr body => simp [Stmt.istBlatt] at hleaf
  | breaking i body => simp [Stmt.istBlatt] at hleaf
  | traverse t inv body => simp [Stmt.istBlatt] at hleaf
  | retry n bis body ueberlauf => simp [Stmt.istBlatt] at hleaf
  | forever a inv body => simp [Stmt.istBlatt] at hleaf
  | axiomCall a args h hw hg hd hgd => exact False.elim hax
  | regSchreib r hk e =>
      simp [stmtTraeger] at hmem
  | transition r hk m hm hl maske bits =>
      simp [stmtTraeger] at hmem
  | publish g e payload hp hw hL =>
      simp [stmtTraeger] at hmem
  | advances m a h hs =>
      simp [stmtTraeger] at hmem
  | retires m s h a =>
      simp [stmtTraeger] at hmem
  | ret e hΛ =>
      simp [stmtTraeger] at hmem
  | retGrund r hΛ =>
      simp [stmtTraeger] at hmem
  | leave h =>
      simp [stmtTraeger] at hmem
  | next h =>
      simp [stmtTraeger] at hmem

/-- The prefix base: with no thread steps owed, no witness is owed -- the
    witness duty holds vacuously over any run. `hempty` types the
    contradiction; `run`/`t₀` type the conclusion. -/
theorem hwit_leer (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (run : Lauf D) (t₀ : D.Tab) (hempty : J.schrittFaden = []) :
    ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        run[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)) := by
  intro k g hk _
  rw [hempty] at hk
  simp at hk

#print axioms Gabbro.Grammatik.Extraktion.hwit_aus_feuerung_ohne_axiomCall
#print axioms Gabbro.Grammatik.Extraktion.hwit_leer

/-! ## 20. The hwit prefix fold over whole `PCReach` runs

    What `Ziel.lean` section 10 books as the prefix witness duty (`hwit_old`:
    the old run's accesses are still posited, as scheduler duty) is folded here
    over whole `PCReach` derivations: the empty prefix holds vacuously
    (read-only `hwit_leer`, section 19), each non-oracle leaf step produces its
    witness by construction (read-only `hwit_aus_feuerung_ohne_axiomCall`,
    section 19, transported into the extended run), and each lock step inherits
    the posited prefix witness (`hwit_lock`, the same shape
    `MaschinenKette.kette_aus_lauf_bezeugt` posits). Nothing existing moves.

    What is proved (no `sorry`, no `admit`, no `axiom`):

    - `hwit_alt_transport` (list only): an event of `neu` sits in the extended
      run `lauf ++ genEigen f neu` at a computed index. It is proved locally:
      the same transport lives in `Ziel.lean` (`genEigen_wit_index`), which
      imports this file and hence cannot be reused here. Every premise is
      load-bearing: `he` yields the index, `lauf`/`f`/`neu` type the
      conclusion.
    - `hwit_alt_schritt`: one-step prefix extension. A duty over
      (`schrittFaden`, `lauf`) plus a witness for the acting thread inside
      the extended run yields the duty over (`schrittFaden ++ [f]`,
      `lauf ++ genEigen f neu`): old entries inherit through the left append
      leg, the new entry is exactly the supplied witness, past-the-end indices
      are impossible. Every premise is load-bearing.
    - `hwit_alt_faltung`: the fold over whole `PCReach` derivations. The
      scheduler steps accumulate as a bare list (`[]` at `start`, discharged
      by `hwit_leer` over a posited empty joint run, `++ [f]` per step);
      counter routing (`hsingle_prog`) rules out foreign steps; every fired
      leaf meets the producer premises (`hax_all`/`hmem_all`/`hbytes_all`
      feed exactly `hwit_aus_feuerung_ohne_axiomCall`, nothing else);
      lock steps inherit the posited prefix witness (`hwit_lock`).
      Every premise is load-bearing, and there is no `have _ :=` discard.

    Coverage (exactly): single-thread `PCReach` runs whose every fired leaf
    is a non-oracle leaf writing the tracked TABLE carrier `t₀` (with `0 < n`
    for `schreibBytes`), plus lock steps whose witness the prefix already
    records.

    Remainder (booked, not hidden): `axiomCall` leaves (the oracle adds no
    events under `GutO`, same class as the section-19 remainder -- `hax_all`
    marks exactly this fragment); leaves that write no table and empty
    `schreibBytes` (no event exists to produce, so `hmem_all`/`hbytes_all`
    cannot hold for them); globals (`gzugriff`); the seed joint run `J₀`
    (the glue that instantiates the fold supplies it); multi-thread runs.
-/

/-- List-level witness transport: an event of `neu` sits in the extended run
    `lauf ++ genEigen f neu` at index `lauf.length + i`, where `i` is its
    index in `neu.reverse` (the order `genEigen` maps over). Every premise is
    load-bearing: `he` yields the index, `lauf`/`f`/`neu` type the
    conclusion. -/
theorem hwit_alt_transport (lauf : Lauf D) (f : Faden) (neu : List (Ereignis D))
    (e : Ereignis D) (he : e ∈ neu) :
    ∃ (j : Nat), (lauf ++ genEigen f neu)[j]? = some (Schritt.mk f e) := by
  have hmem : e ∈ neu.reverse := List.mem_reverse.mpr he
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨lauf.length + i, ?_⟩
  have hmap : (genEigen f neu)[i]? = some (Schritt.mk f e) := by
    simp only [genEigen, List.getElem?_map, List.getElem?_eq_getElem hi, hget,
      Option.map_some]
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  have hsub : lauf.length + i - lauf.length = i := by omega
  rw [hsub]
  exact hmap

#print axioms Gabbro.Grammatik.Extraktion.hwit_alt_transport

/-- One-step prefix extension: a witness duty over (`schrittFaden`, `lauf`)
    plus a witness for the acting thread `f` inside the extended run yields
    the duty over (`schrittFaden ++ [f]`, `lauf ++ genEigen f neu`). Old
    entries inherit from the prefix duty through the left append leg, the new
    entry is the supplied witness, past-the-end indices are impossible. Every
    premise is load-bearing: `hold` closes the old entries, `hnew` closes the
    new one, the rest type the conclusion. -/
theorem hwit_alt_schritt
    (code : Faden → D.Fn)
    (schrittFaden : List Faden) (lauf : Lauf D)
    (f : Faden) (neu : List (Ereignis D)) (t₀ : D.Tab)
    (hold : ∀ (k : Nat) (g : Faden), schrittFaden[k]? = some g →
      TraegerSchreibt (code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)))
    (hnew : TraegerSchreibt (code f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        (lauf ++ genEigen f neu)[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he))) :
    ∀ (k : Nat) (g : Faden), (schrittFaden ++ [f])[k]? = some g →
      TraegerSchreibt (code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        (lauf ++ genEigen f neu)[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)) := by
  intro k g hk hwr
  by_cases hlt : k < schrittFaden.length
  · have eOld : (schrittFaden ++ [f])[k]? = schrittFaden[k]? :=
      List.getElem?_append_left hlt
    rw [eOld] at hk
    obtain ⟨j, w, Λe, he, hw⟩ := hold k g hk hwr
    have hjlt : j < lauf.length := by
      by_cases h : j < lauf.length
      · exact h
      · have hle : lauf.length ≤ j := by omega
        rw [List.getElem?_eq_none hle] at hw
        simp at hw
    refine ⟨j, w, Λe, he, ?_⟩
    rw [List.getElem?_append_left hjlt]
    exact hw
  · by_cases heq : k = schrittFaden.length
    · subst heq
      have eNew : (schrittFaden ++ [f])[schrittFaden.length]? = some f := by
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [eNew] at hk
      have hg : g = f := (Option.some_inj.mp hk).symm
      subst hg
      exact hnew hwr
    · have hle : schrittFaden.length ≤ k := by omega
      have eNone : (schrittFaden ++ [f])[k]? = none := by
        rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
          List.length_singleton]
        omega
      rw [eNone] at hk
      simp at hk

#print axioms Gabbro.Grammatik.Extraktion.hwit_alt_schritt

/-- The hwit prefix fold over whole `PCReach` runs, non-oracle leaves: the
    prefix witness duty (`hwit_old` shape) holds at the end of a single-thread
    run whose every fired leaf meets the producer premises. The scheduler
    steps accumulate as a bare list (`[]` at `start` via `hwit_leer` over the
    posited empty joint run `J₀`, `++ [f]` per step via `hwit_alt_schritt`);
    foreign steps are ruled out by counter routing (`hsingle_prog`); each
    fired leaf discharges through `hwit_aus_feuerung_ohne_axiomCall`
    (`hax_all` kills the oracle case, `hmem_all` names the carrier,
    `hbytes_all` feeds the byte case); lock steps inherit the posited prefix
    witness (`hwit_lock`). Every premise is load-bearing. -/
theorem hwit_alt_faltung
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (Nb : Nebeneinander) (J₀ : GemeinsamerLauf (D := D) Nb)
    (hempty : J₀.schrittFaden = [])
    (code : Faden → D.Fn) (hcode : J₀.code = code)
    (t₀ : D.Tab) (f : Faden)
    (tabs : List D.Tab) (globs : List D.Glob)
    (hsingle_prog : ∀ g, g ≠ f → prog g = [])
    (hax_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (_hleaf : s.istBlatt = true),
      (match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True))
    (hmem_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (_hleaf : s.istBlatt = true),
      .inl t₀ ∈ stmtTraeger tabs globs s)
    (hbytes_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ'),
      (match s with | .schreibBytes _ _ _ n _ _ _ _ _ _ => 0 < n | _ => True))
    (hwit_lock : ∀ (Mx : GenMaschine D) (pcx : PCStand),
      PCReach P O passes prog (GenStart sp) Mx pcx →
      TraegerSchreibt (code f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        Mx.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he)))
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    ∃ (sched : List Faden),
      ∀ (k : Nat) (g : Faden), sched[k]? = some g →
        TraegerSchreibt (code g) (.inl t₀) = true →
        ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
          M.lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)) := by
  induction h with
  | start =>
    have hbase := hwit_leer Nb J₀ (GenStart sp).lauf t₀ hempty
    rw [hempty, hcode] at hbase
    exact ⟨[], hbase⟩
  | step Mmid Mend pcmid pcend g hmid hs ih =>
    obtain ⟨sched, hduty⟩ := ih
    rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
      ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      refine ⟨sched ++ [f], ?_⟩
      show ∀ (k : Nat) (g : Faden), (sched ++ [f])[k]? = some g →
        TraegerSchreibt (code g) (.inl t₀) = true →
        ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
          (Mmid.lauf ++ genEigen f neu)[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he))
      have hnew : TraegerSchreibt (code f) (.inl t₀) = true →
          ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
            (Mmid.lauf ++ genEigen f neu)[j]? =
              some (Schritt.mk f (.zugriff t₀ w Λe he)) := by
        intro _
        obtain ⟨w, Λw, hwL, hmem_neu⟩ :=
          hwit_aus_feuerung_ohne_axiomCall O passes s hleaf
            (hax_all V l Γ Λ Λ' s hleaf) tabs globs t₀
            (hmem_all V l Γ Λ Λ' s hleaf) (hbytes_all V l Γ Λ Λ' s)
            (Mmid.weltVon f) ρ σ' neu hstep hneu
        obtain ⟨j, hj⟩ := hwit_alt_transport Mmid.lauf f neu _ hmem_neu
        exact ⟨j, w, Λw, hwL, hj⟩
      exact hwit_alt_schritt code sched Mmid.lauf f neu t₀ hduty hnew
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      refine ⟨sched ++ [f], ?_⟩
      show ∀ (k : Nat) (g : Faden), (sched ++ [f])[k]? = some g →
        TraegerSchreibt (code g) (.inl t₀) = true →
        ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
          (Mmid.lauf ++ genEigen f [Ereignis.nimmt L (offen (Mmid.spuren f))])[j]? =
            some (Schritt.mk g (.zugriff t₀ w Λe he))
      have hnew : TraegerSchreibt (code f) (.inl t₀) = true →
          ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
            (Mmid.lauf ++ genEigen f [Ereignis.nimmt L (offen (Mmid.spuren f))])[j]? =
              some (Schritt.mk f (.zugriff t₀ w Λe he)) := by
        intro hwr
        obtain ⟨j, w, Λe, he, hw⟩ := hwit_lock Mmid pcmid hmid hwr
        have hjlt : j < Mmid.lauf.length := by
          by_cases h : j < Mmid.lauf.length
          · exact h
          · have hle : Mmid.lauf.length ≤ j := by omega
            rw [List.getElem?_eq_none hle] at hw
            simp at hw
        refine ⟨j, w, Λe, he, ?_⟩
        rw [List.getElem?_append_left hjlt]
        exact hw
      exact hwit_alt_schritt code sched Mmid.lauf f
        [Ereignis.nimmt L (offen (Mmid.spuren f))] t₀ hduty hnew
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      refine ⟨sched ++ [f], ?_⟩
      show ∀ (k : Nat) (g : Faden), (sched ++ [f])[k]? = some g →
        TraegerSchreibt (code g) (.inl t₀) = true →
        ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
          (Mmid.lauf ++ genEigen f [Ereignis.gibt L])[j]? =
            some (Schritt.mk g (.zugriff t₀ w Λe he))
      have hnew : TraegerSchreibt (code f) (.inl t₀) = true →
          ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
            (Mmid.lauf ++ genEigen f [Ereignis.gibt L])[j]? =
              some (Schritt.mk f (.zugriff t₀ w Λe he)) := by
        intro hwr
        obtain ⟨j, w, Λe, he, hw⟩ := hwit_lock Mmid pcmid hmid hwr
        have hjlt : j < Mmid.lauf.length := by
          by_cases h : j < Mmid.lauf.length
          · exact h
          · have hle : Mmid.lauf.length ≤ j := by omega
            rw [List.getElem?_eq_none hle] at hw
            simp at hw
        refine ⟨j, w, Λe, he, ?_⟩
        rw [List.getElem?_append_left hjlt]
        exact hw
      exact hwit_alt_schritt code sched Mmid.lauf f
        [Ereignis.gibt L] t₀ hduty hnew

#print axioms Gabbro.Grammatik.Extraktion.hwit_alt_transport
#print axioms Gabbro.Grammatik.Extraktion.hwit_alt_schritt
#print axioms Gabbro.Grammatik.Extraktion.hwit_alt_faltung

/-! ## 21. Witness duties from firing: `hwit_aus_lauf`

    The fold `kette_aus_lauf_bezeugt` (`MaschinenKette.lean`, read-only here)
    takes two witness duties as hypotheses at every step: per firing
    (`hwit_leaf`: the fired leaf records its access) and per prefix
    (`hwit_lock`: the prefix already records one). As STATED they are not
    theorems but scheduler/witness duties, and they cannot be -- the
    `hwit_leaf` quantifier leaves `neu` free (`hstep` does not mention it,
    so `neu = []` refutes the instance), and the `hwit_lock` quantifier
    ranges over the start machine (whose run is empty, so no `zugriff`
    step exists to exhibit). This section discharges both duties over the
    fragment where firing produces: non-oracle single-thread table runs
    over lock-free programs. Nothing existing moves; read-only reuse of
    `hwit_aus_feuerung_ohne_axiomCall` (§19), `hwit_alt_transport` (§20),
    and the `PCSchritt` fired-step shapes (`Maschine.lean`).

    What is proved (no `sorry`, no `admit`, no `axiom`):

    - `hwit_aus_lauf_blatt` (leaf leg): every fired producing leaf
      satisfies the `hwit_leaf` CONCLUSION -- `neu` carries a `zugriff`
      event for `t₀`. One positional application of the §19 producer with
      the pre-world fixed to the acting thread's machine world
      (`M.weltVon f`); the `hneu` spur equation rides the fired step, as
      in §20. The `hwit_leaf` code predicate (`TraegerSchreibt`) is
      VACUOUS here and hence dropped, not carried: the event exists
      whenever the writing leaf fires, as §19 already books. The
      held-footprint premise (`HeldGenau`) is not needed either --
      production is by `execStmt` construction alone -- so the leg is
      strictly stronger than the duty instance. Every premise is
      load-bearing.
    - `hwit_aus_lauf` (prefix leg): every prefix of a single-thread run
      over a lock-free program whose every fired leaf meets the producer
      premises EITHER is empty OR satisfies the `hwit_lock` conclusion
      (a `zugriff` step for `t₀` sits in its run). Induction over
      `PCReach`: the base holds by `rfl` (the start run is empty);
      foreign steps die by counter routing (`hsingle_prog`); leaf steps
      establish the right leg through the blatt leg plus transport; lock
      steps are impossible (`hlockfree` contradicts the pointed-to
      `take`/`rel` atom). Every premise is load-bearing, and there is no
      `have _ :=` discard.

    Coverage (exactly): single-thread `PCReach` runs over programs with
    no `take`/`rel` atom on the acting thread, whose every fired leaf is
    a non-oracle leaf writing the tracked TABLE carrier `t₀` (with
    `0 < n` for `schreibBytes`).

    Remainder (booked, not hidden): `axiomCall` leaves (killed by
    `hax_all`, same class as the §19 remainder); leaves that write no
    table and empty `schreibBytes` (no event exists to produce);
    globals (`gzugriff`); programs WITH lock atoms (the lock step from
    an empty prefix genuinely records no `zugriff`, so the unconditional
    prefix duty is false there -- the disjunction marks exactly this);
    the empty prefix itself (left leg of the disjunction); multi-thread
    runs.
-/

/-- Every fired producing leaf satisfies the `hwit_leaf` conclusion:
    `neu` carries a `zugriff` event for `t₀`. The §19 producer applied
    positionally with the pre-world fixed to the acting thread's machine
    world; the duty's code predicate is vacuous once the leaf produces
    and is hence dropped. Every premise is load-bearing: `hleaf` kills
    the compounds, `hax` the oracle case, `hmem` names the carrier,
    `hbytes` feeds the byte case, `hstep`/`hneu` give the spur equation
    of the fired step. -/
theorem hwit_aus_lauf_blatt
    (O : Orakel D) (passes : Nat)
    (M : GenMaschine D) (f : Faden)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (tabs : List D.Tab) (globs : List D.Glob)
    (t₀ : D.Tab) (hmem : .inl t₀ ∈ stmtTraeger tabs globs s)
    (hbytes : match s with | .schreibBytes _ _ _ n _ _ _ _ _ _ => 0 < n | _ => True)
    (ρ : Env D Γ)
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ M.spuren f) :
    ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
      Ereignis.zugriff t₀ w Λw hwL ∈ neu :=
  hwit_aus_feuerung_ohne_axiomCall O passes s hleaf hax tabs globs t₀ hmem hbytes
    (M.weltVon f) ρ σ' neu hstep hneu

#print axioms Gabbro.Grammatik.Extraktion.hwit_aus_lauf_blatt

/-- Every prefix of a single-thread lock-free run with producing leaves
    either is empty or satisfies the `hwit_lock` conclusion: a `zugriff`
    step for `t₀` sits in its run. The base is the empty start run
    (`Or.inl rfl`); each leaf step establishes the right leg through
    `hwit_aus_lauf_blatt` plus `hwit_alt_transport`; lock steps die at
    `hlockfree`, foreign steps at `hsingle_prog`. Every premise is
    load-bearing. -/
theorem hwit_aus_lauf
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (code : Faden → D.Fn) (t₀ : D.Tab) (f : Faden)
    (tabs : List D.Tab) (globs : List D.Glob)
    (hsingle_prog : ∀ g, g ≠ f → prog g = [])
    (hlockfree : ∀ (n : Nat) (L : D.Lock),
      (prog f)[n]? ≠ some (PCAtom.take L) ∧ (prog f)[n]? ≠ some (PCAtom.rel L))
    (hax_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (_hleaf : s.istBlatt = true),
      (match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True))
    (hmem_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (_hleaf : s.istBlatt = true),
      .inl t₀ ∈ stmtTraeger tabs globs s)
    (hbytes_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ'),
      (match s with | .schreibBytes _ _ _ n _ _ _ _ _ _ => 0 < n | _ => True))
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    M.lauf = [] ∨ (TraegerSchreibt (code f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        M.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he))) := by
  induction h with
  | start =>
    exact Or.inl rfl
  | step Mmid Mend pcmid pcend g _hmid hs _ih =>
    rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
      ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      refine Or.inr ?_
      intro _
      obtain ⟨w, Λw, hwL, hmem_neu⟩ :=
        hwit_aus_lauf_blatt O passes Mmid f s hleaf
          (hax_all V l Γ Λ Λ' s hleaf) tabs globs t₀
          (hmem_all V l Γ Λ Λ' s hleaf) (hbytes_all V l Γ Λ Λ' s)
          ρ σ' neu hstep hneu
      obtain ⟨j, hj⟩ := hwit_alt_transport Mmid.lauf f neu _ hmem_neu
      show ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        (Mmid.lauf ++ genEigen f neu)[j]? =
          some (Schritt.mk f (.zugriff t₀ w Λe he))
      exact ⟨j, w, Λw, hwL, hj⟩
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      exact absurd hpc (hlockfree (pcmid f) L).1
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      exact absurd hpc (hlockfree (pcmid f) L).2

#print axioms Gabbro.Grammatik.Extraktion.hwit_aus_lauf

/-! ## 22. The memory-contract instance: `SpeicherVertrag` over `QRequires` / `QEnsures`

    The downstream fold of the §23 engine (`InterferenzAllgemein.lean`,
    read-only here): a `World.speicher` equality unfolds into slot and global
    agreements, and the contract predicates fold over the diagonal
    (`eval_liest_nur_speicher_diag`).

    What is proved (no `sorry`, no `admit`, no `axiom`):

    - `speicherVertrag_aus_Q`: the contracts of `P` at `f` -- `QRequires P`
      as `Pre`, `QEnsures P` as `Post` -- read only live memory. Both legs
      unfold the memory equality into pointwise slot/global agreement
      (`congrArg` on the `Speicher` projections) and fold the contract
      predicate over the diagonal: `requires` quantifies over parameter
      environments, `ensures` over return values and parameter environments,
      and each instance meets the diagonal at exactly its environment.
      Every premise is load-bearing: `hmem` feeds both `hS` and `hG`,
      and both fire in every diagonal call.

    Coverage (exactly): both `SpeicherVertrag` legs (`memPre`, `memPost`)
    for every program `P` and every function `f`, with no footprint premise.

    Remainder (booked, not hidden): none -- the fold closes fully.
-/

/-- The contracts of `P` at `f` read only live memory: worlds over the same
    memory agree on `requires` and on `ensures`. The memory equality unfolds
    into pointwise slot/global agreement; each contract predicate then folds
    over the `eval` diagonal at its own environment. -/
theorem speicherVertrag_aus_Q (P : Programm D) (f : D.Fn) :
    SpeicherVertrag (QRequires P) (QEnsures P) f :=
  { memPre := by
      intro σ σ' hmem
      have hS : ∀ t : D.Tab, ∀ (k : Int) (f' : D.Feld t),
          σ.slots t k f' = σ'.slots t k f' :=
        fun t k f' => congrArg (fun s : Speicher D => s.slots t k f') hmem
      have hG : ∀ g : D.Glob, σ.globs g = σ'.globs g :=
        fun g => congrArg (fun s : Speicher D => s.globs g) hmem
      simp only [QRequires, QExpr]
      constructor
      · intro h ρ
        have he := eval_liest_nur_speicher_diag (P.requires f) σ σ' ρ hS hG
        rw [← he]
        exact h ρ
      · intro h ρ
        have he := eval_liest_nur_speicher_diag (P.requires f) σ σ' ρ hS hG
        rw [he]
        exact h ρ
    , memPost := by
      intro σ σ' hmem
      have hS : ∀ t : D.Tab, ∀ (k : Int) (f' : D.Feld t),
          σ.slots t k f' = σ'.slots t k f' :=
        fun t k f' => congrArg (fun s : Speicher D => s.slots t k f') hmem
      have hG : ∀ g : D.Glob, σ.globs g = σ'.globs g :=
        fun g => congrArg (fun s : Speicher D => s.globs g) hmem
      simp only [QEnsures]
      constructor
      · intro h v ρ
        have he := eval_liest_nur_speicher_diag (P.ensures f) σ σ'
          (ergEnv (D.erg f) v ρ) hS hG
        rw [← he]
        exact h v ρ
      · intro h v ρ
        have he := eval_liest_nur_speicher_diag (P.ensures f) σ σ'
          (ergEnv (D.erg f) v ρ) hS hG
        rw [he]
        exact h v ρ }

#print axioms Gabbro.Grammatik.Extraktion.speicherVertrag_aus_Q


end Gabbro.Grammatik.Extraktion