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
-/

import Grammatik.Geteilt
import Grammatik.Syntax
import Grammatik.Wettlauf

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

end Gabbro.Grammatik.Extraktion