/- Part 2 of 9 of `Extraktion` (split by instrumente/teile/lean-teilen.py; the umbrella `Extraktion.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Extraktion.T1

namespace Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

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
  | true => .ret .empty (List.Perm.refl [])
  | false => .ret .empty (List.Perm.refl [])

/-- Das Probe-Programm ueber `miniD`. -/
def miniP : Programm miniD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
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
  | .assignThru p _ _ _ i e _ _ => p.orte ++ i.orte ++ e.orte
  | .assignGlob _ e _ _ => e.orte
  | .putBytes _ _ _ _ i _ _ e _ _ => i.orte ++ e.orte
  | .assignVar _ e => e.orte
  | .shift _ _ _ i _ _ _ _ _ _ => i.orte
  | .ite c t e => c.orte ++ blockOrte t ++ blockOrte e
  | .onOption o p a => o.orte ++ blockOrte p ++ blockOrte a
  | .onTag v arms => v.orte ++ armsOrte arms
  | .onWhy r arms => r.orte ++ grundArmsOrte arms
  | .call _ args _ _ => args.orte
  | .callInd p args _ _ => p.orte ++ args.orte
  | .locks _ _ body => blockOrte body
  | .breaking _ body => blockOrte body
  | .traverse _ inv body => inv.orte ++ blockOrte body
  | .retry _ bis body ueber => bis.orte ++ blockOrte body ++ blockOrte ueber
  | .forever _ inv body => inv.orte ++ blockOrte body
  | .axiomCall _ args _ _ _ _ _ => args.orte
  | .regWrite _ _ e => e.orte
  | .transition _ _ _ _ _ _ _ => []
  | .publish _ e _ _ _ _ => e.orte
  | .advances _ _ _ _ => []
  | .retires _ _ _ _ => []
  | .ret e _ => e.orte
  | .retWhy _ _ => []
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
  | .bindAxiom _ args _ _ _ _ _ rest => args.orte ++ blockOrte rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest => args.orte ++ endblockOrte err ++ blockOrte rest
  | .regRead _ _ rest => blockOrte rest
  | .regReadElse _ _ zusage sonst rest =>
      zusage.orte ++ endblockOrte sonst ++ blockOrte rest
  | .awaits g _ _ _ rest => .inr g :: blockOrte rest
  | .exchange g neu _ _ rest => .inr g :: neu.orte ++ blockOrte rest
  | .narrow e _ _ sonst rest =>
      e.orte ++ endblockOrte sonst ++ blockOrte rest
  | .check c sonst rest =>
      c.orte ++ endblockOrte sonst ++ blockOrte rest
  | .float _ a b _ _ rest => a.orte ++ b.orte ++ blockOrte rest
  | .floatLit _ _ _ rest => blockOrte rest
  | .floatOf e _ _ rest => e.orte ++ blockOrte rest
  | .floatNarrow e _ _ sonst rest =>
      e.orte ++ endblockOrte sonst ++ blockOrte rest

/-- Die gelesenen Orte eines nicht abfallenden Blocks. -/
def endblockOrte {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List (D.Tab ⊕ D.Glob)
  | .ret e _ => e.orte
  | .retWhy _ _ => []
  | .leave _ => []
  | .next _ => []
  | .cons s rest => stmtOrte s ++ endblockOrte rest
  | .bind e rest => e.orte ++ endblockOrte rest
  | .bindCall _ args _ _ _ rest => args.orte ++ endblockOrte rest
  | .bindCallElse _ args _ _ _ err rest =>
      args.orte ++ endblockOrte err ++ endblockOrte rest
  | .bindAxiom _ args _ _ _ _ _ rest => args.orte ++ endblockOrte rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest => args.orte ++ endblockOrte err ++ endblockOrte rest

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


end Gabbro.Grammatik.Extraktion
