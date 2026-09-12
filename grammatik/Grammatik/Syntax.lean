/-
  Datei:      Grammatik/Syntax.lean
  Gegenstand: **DIE GRAMMATIK VON GABBRO** -- als getypte Familie, ueber die GANZE Sprache.

              Ein Satz der Grammatik ist ein Term dieser Typen, und jedes Attribut, das
              `SYNTAX.md` neben eine Produktion schreibt, ist hier ein Argument des
              Konstruktors: die Schranke am Index, der Bereich am Ergebnis, das gehaltene
              Sperrzeugnis am geschuetzten Ort, das Schreibrecht an der Zuweisung, die
              verbrauchte Marke am Ruf, die Stufe an der Phasenmarke, die Registerklasse am
              Geraetezugriff, die Paarung an der Veroeffentlichung.

              **Was die Grammatik nicht ableitet, ist nicht schreibbar** -- und was sie
              ableitet, hat in `Semantik.lean` eine totale Bedeutung.

  DIE ABDECKUNG -- jede Produktion von `SYNTAX.md` und wo sie hier steht
    §1  program/module/use/const/static/when  -> `Deklaration` (Namen sind statisch; ein
                                               `const` ist ein Literal, ein `static` ein `Glob`)
    §2  typedecl/intty/floatty/tagged/linear  -> `Ty` (`int`, `fl`, `sum`, `never`, …), `Marke`
    §3  ptrty/space/rights                    -> `Ty.ptr t rw`; ein Zugriff hindurch ist ein
                                               Zugriff auf `t` mit dessen Waechtern («SG-8»)
    §4  expr/primary/place/call/fnvalue/old   -> `Expr` (alle Operatoren), `Expr.fnref`,
                                               `Expr.altGlob`/`altSlot`, `Expr.ptrOf`
    §5  pred/quant/domain/reach/Held          -> `forallSlots`, `existsSlots`, `reaches`;
                                               `Held(L)` ist `Res.held L ∈ Λ`
    §6  fndecl mit allen Klauseln             -> `Signatur`, `Programm.requires/ensures/rumpf`,
                                               `decreases` = Rekursionstiefe, `refines` =
                                               `ensures` der Spezifikation (Logik), `by
                                               induction` = kein Term, `spec fn` = eingesetzt
    §7  stmt/letstmt/assign/if/match/narrow   -> `Stmt`, `Block`, `Endblock`, `Arms`, `GrundArms`
    §8  traverse/retry/forever                -> `Stmt.traverse/retry/forever`
    §9  table/ops/tree/occupied/format/walk   -> `Tab` mit `count`; `ops` = erzeugte `Fn` mit
                                               `requires`; `format` = `Tab` mit `count 1` und
                                               `where` als `Block.pruefung`; `walk` = ein
                                               `traverse` je Stufe (`levels` konstant)
    §10 device/reg/bank/transition/mirrors    -> `Reg` mit Klasse; `Block.regLies`,
                                               `Stmt.regSchreib` (die Klasse ist ableitbar
                                               oder nicht); `transition` = `regSchreib`
    §11 atomic/publishes/awaits/exchange/lock/rcu/group/accumulates
                                              -> `Stmt.publish`, `Block.awaits` mit der
                                               Paarung als Attribut; `Stmt.locks` mit Rang;
                                               `observes` = `locks` einer RCU-Sperre; `group` =
                                               `Inv` ueber mehrere Traeger; `accumulates` =
                                               `Glob` + erzeugte Zuweisung
    §12 assume/axiom                           -> `Annahme`, `Ax`
    §13 check                                  -> eine Marke (`Duty`): erzeugt vom `check`,
                                               verbraucht von `gates` (`konsumiert`)
    §14 boot/entry/entrust/asm/prim/divergent  -> fremde Ruempfe sind `Ax`; `-> never` ist
                                               `Ty.never` (kein `return` ableitbar); `retires`
                                               ist `Stmt.retires` (Marke weg, Annahme genannt)
    «F» f32/f64/rounded/finite                -> `Ty.fl`, `Block.gleit*` -- jede Rechnung
                                               gegen ihren Bereich, von der MASCHINE (IEEE ist
                                               Annahme: `Hardware.ieee`)
    «B37» order/advances                       -> `Res.marke m stufe`, `Stmt.advances`
    state/transition ueber Felder              -> `Stmt.uebergang` (die Vorstufe ist Logik)
    seit dem Abend des 2026-09-09 («SG-3»², «SG-16»², «SG-15»², «SG-13»², «SG-20», «SG-21»):
    vorzeichenbehaftete Division              -> `Expr.sdiv/srem`
    Bytes und `format` als Sicht               -> `Expr.leseBytes`, `Stmt.schreibBytes`
    `transition` mit Spiegel, Registerzusage   -> `Stmt.transition`, `D.spiegel`, `D.rzusage`
    `awaits` und das Speichermodell            -> `Orakel.sichtbar`, `Hardware.sichtbarkeit`
    `requires Held(L)` GENAU                   -> `RufPasst.hh` (↔), `Signatur.haelt`
    `shared`, U003 als Erklaerung              -> `D.geteilt`, `D.invarianten_gehalten`
    Faeden                                     -> `Wettlauf.lean` (Lauf, Gesittet, HB)

  QUELLSAETZE
    dokumente/SYNTAX.md (die neue Fassung, 2026-09-09) -- jede Produktion nennt ihren
    Konstruktor hier; SPRACHE.md:788 "Linear means linear, not affine".
-/
import Grammatik.Typen

namespace Gabbro.Grammatik

/-! ## 1. Die Deklarationen -- was `program = { item }` vor dem ersten Rumpf festlegt -/

/-- Eine Funktionssignatur (`fndecl` ohne Rumpf, `fnptr`). -/
structure Signatur (Tab Glob Lock Marke : Type) where
  params : List Ty
  erg : Option Ty
  /-- `or R` mit `n` Gruenden; `0` heisst: kein Fehlerkanal. -/
  gruende : Nat
  /-- `requires Held(L)` -- die Sperrzeugnisse, die der Rufer in der Hand haben muss und der
      Rumpf von Anfang an haelt. -/
  haelt : List Lock
  /-- `effects { writes T }` -/
  schreibt : Tab → Bool
  gschreibt : Glob → Bool
  /-- `effects { consumes m }` / `allocs m` -- die Marken mit ihrer STUFE (`order`). -/
  konsumiert : List (Marke × Nat)
  produziert : List (Marke × Nat)

/-- Die Klasse eines Geraeteregisters (`class r | w | rw | w1c | rc`). -/
inductive Regklasse where
  | r | w | rw | w1c | rc
  deriving DecidableEq, Repr

def Regklasse.lesbar : Regklasse → Bool
  | .r | .rw | .w1c | .rc => true
  | .w => false

def Regklasse.schreibbar : Regklasse → Bool
  | .w | .rw | .w1c => true
  | .r | .rc => false

/-- Die deklarierte Welt einer Uebersetzungseinheit. -/
structure Deklaration where
  Tab : Type
  [decTab : DecidableEq Tab]
  /-- `table T count N`; ein `format` und ein Verbund sind Tabellen mit `count 1`. -/
  count : Tab → Int
  Feld : Tab → Type
  [decFeld : ∀ t, DecidableEq (Feld t)]
  typ : ∀ t, Feld t → Ty
  /-- `state S { … }` -- welche Uebergaenge ein Feld zulaesst (ueber der Zahl). -/
  erlaubt : ∀ t, Feld t → Int → Int → Bool
  /-- Die Tabelle Nummer `n` -- fuer `ptr` und `fnptr`, deren Typ eine NUMMER nennt. -/
  tabNr : Nat → Option Tab
  Glob : Type
  [decGlob : DecidableEq Glob]
  gtyp : Glob → Ty
  /-- `atomic A : T publishes { … }` -- die Nutzlast, die eine Veroeffentlichung von `A`
      mitnimmt (`V001`-`V004`: dieselbe Menge an `awaits`). -/
  nutzlast : Glob → List Glob
  /-- `atomic A` -- ein Global, dessen Zugriffe die Maschine ORDNET (A10); jedes Global ohne
      Waechter ist ein `atomic`, sonst waere sein Zugriff ein Wettlauf ohne Namen. -/
  atomar : Glob → Bool
  /-- `shared` -- der Traeger ist von mehr als einem Faden erreichbar (`H013` als Erklaerung).
      Ein geteilter Traeger hat einen Waechter; ein geteiltes Global einen Waechter oder ist
      `atomic`. Ein ungeteilter Traeger gehoert EINEM Faden (`per cpu`, Stapel, Boot). -/
  geteilt : Tab → Bool
  ggeteilt : Glob → Bool
  Lock : Type
  [decLock : DecidableEq Lock]
  /-- `lock L … rank N` -/
  rang : Lock → Int
  /-- `lock L … masks irqs` -- das Nehmen der Sperre maskiert Unterbrechungen. -/
  maskiert : Lock → Bool
  /-- `linear type M;` -- die Marken, mit Stufen (`order { a, b, c }`: Stufe `0, 1, 2`). -/
  Marke : Type
  [decMarke : DecidableEq Marke]
  stufen : Marke → Nat
  /-- Was ein Zugriff auf den Traeger in der Hand haben muss: `Held(L)` aus `protects`, die
      Eigentumsmarke aus `owner`. -/
  braucht : Tab → List (Lock ⊕ (Marke × Nat))
  gbraucht : Glob → List (Lock ⊕ (Marke × Nat))
  eigner : Tab → List Marke
  Fn : Type
  /-- Die Signaturnummer -- `fnptr n` ist ein Zeiger auf eine Funktion mit Signatur `n`. -/
  sig : Fn → Nat
  sigNr : Nat → Signatur Tab Glob Lock Marke
  eigner_nie_erzeugt : ∀ n t m s, m ∈ eigner t → (m, s) ∉ (sigNr n).produziert
  /-- `table … { invariant I }` / `group … { invariant I }`. -/
  Inv : Type
  traeger : Inv → List Tab
  invs : List Inv
  /-- `axiom`, und jeder FREMDE Rumpf: `extern fn`, `prim fn`, `asm`, `entry`, `entrust`. -/
  Ax : Type
  aparams : Ax → List Ty
  aerg : Ax → Option Ty
  aschreibt : Ax → Tab → Bool
  agschreibt : Ax → Glob → Bool
  /-- `device … { reg R : T @off class K }` -/
  Reg : Type
  rtyp : Reg → Ty
  rklasse : Reg → Regklasse
  /-- `mirrors W from R` -- das Register, aus dem ein Schreiben auf `W` die uebrigen Bits
      mitnimmt (Falle 4). -/
  spiegel : Reg → Option Reg
  /-- `reg R … requires p` OHNE `else`: die Zusage des Geraets ueber den gelesenen Wert. Sie
      wird an jeder Lesung gehalten, und ihr Bruch ist `Hardware.geraet r` -- die Annahme
      ueber das Geraet, benannt am Register. -/
  rzusage : ∀ r : Reg, Val Fn sig (rtyp r) → Bool
  /-- `assume a "…" falsifier …` -- die benannten Annahmen, an `progress` und `retires`. -/
  Annahme : Type
  /-- A10: das Speichermodell -- `publishes`/`awaits` ordnen, wie die Maschine es zusagt. -/
  a10 : Annahme
  /-- Ein Traeger ohne Waechter ist nicht geteilt; ein Global ohne Waechter ist `atomic`
      oder nicht geteilt. Das ist die Erklaerung, aus der `kein_wettlauf` (Wettlauf.lean)
      seine Voraussetzung nimmt. -/
  geteilt_bewacht : ∀ t, geteilt t = true → braucht t ≠ []
  /-- `U003` als Erklaerung: wer einen Traeger einer Invariante schreibt, haelt die Sperren
      ALLER ihrer Traeger -- denn er schuldet sie am `return`, und sie liest sie alle. -/
  invarianten_gehalten : ∀ n i, (traeger i).any (sigNr n).schreibt = true →
      ∀ t ∈ traeger i, ∀ L, Sum.inl L ∈ braucht t → L ∈ (sigNr n).haelt
  ggeteilt_bewacht : ∀ g, ggeteilt g = true → gbraucht g ≠ [] ∨ atomar g = true
  /-- `ghost table T` / `ghost static G` -- spec-only carriers: the semantics treats
      them like any carrier (so every theorem stays valid) and the emitter omits
      them. That the emitter may do so is rule `G001`: executable code reads no
      ghost -- `Geist.lean` says what that means. Default: none is ghost. -/
  geist : Tab → Bool := fun _ => false
  ggeist : Glob → Bool := fun _ => false

attribute [instance] Deklaration.decTab Deklaration.decFeld Deklaration.decGlob
  Deklaration.decLock Deklaration.decMarke

namespace Deklaration
variable (D : Deklaration)
def signatur (f : D.Fn) := D.sigNr (D.sig f)
def params (f : D.Fn) : List Ty := (D.signatur f).params
def erg (f : D.Fn) : Option Ty := (D.signatur f).erg
def gruende (f : D.Fn) : Nat := (D.signatur f).gruende
def haelt (f : D.Fn) : List D.Lock := (D.signatur f).haelt
def schreibt (f : D.Fn) : D.Tab → Bool := (D.signatur f).schreibt
def gschreibt (f : D.Fn) : D.Glob → Bool := (D.signatur f).gschreibt
def konsumiert (f : D.Fn) : List (D.Marke × Nat) := (D.signatur f).konsumiert
def produziert (f : D.Fn) : List (D.Marke × Nat) := (D.signatur f).produziert
end Deklaration

variable (D : Deklaration)

/-- Der Wert eines Typs in dieser Deklaration. -/
abbrev Wert : Ty → Type := Val D.Fn D.sig

/-- Was ein Rumpf HAELT: Sperrzeugnisse (`Held(L)`) und lineare Marken auf ihrer Stufe. -/
inductive Res where
  | held (L : D.Lock)
  | marke (m : D.Marke) (stufe : Nat)
  deriving DecidableEq

def Untermulti {α : Type} (k Λ : List α) : Prop := ∃ l, List.Perm k l ∧ List.Sublist l Λ

def Res.von : D.Lock ⊕ (D.Marke × Nat) → Res D
  | .inl L => .held L
  | .inr (m, s) => .marke m s

def Res.vonMarke : D.Marke × Nat → Res D
  | (m, s) => .marke m s

/-- Der Zugriff auf `t` hat alles in der Hand, was `t` verlangt (`H007`, `owner`). -/
def darf (t : D.Tab) (Λ : List (Res D)) : Prop := ∀ w ∈ D.braucht t, Res.von D w ∈ Λ
def gdarf (g : D.Glob) (Λ : List (Res D)) : Prop := ∀ w ∈ D.gbraucht g, Res.von D w ∈ Λ

/-- Nach einem Ruf mit Signatur `S`: die verbrauchten Marken sind weg, die erzeugten da. -/
def nachSig (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) : List (Res D) :=
  (S.konsumiert.foldl (fun acc m => acc.erase (Res.vonMarke D m)) Λ)
    ++ S.produziert.map (Res.vonMarke D)

def nach (f : D.Fn) (Λ : List (Res D)) : List (Res D) := nachSig D (D.signatur f) Λ

/-- Der Vertrag der Funktion, in der eine Anweisung steht. -/
structure Vertrag where
  schreibt : D.Tab → Bool
  gschreibt : D.Glob → Bool
  erg : Option Ty
  gruende : Nat
  haelt : List D.Lock
  produziert : List (D.Marke × Nat)

def Vertrag.vonSig (S : Signatur D.Tab D.Glob D.Lock D.Marke) : Vertrag D :=
  ⟨S.schreibt, S.gschreibt, S.erg, S.gruende, S.haelt, S.produziert⟩

/-- Was ein Rumpf am Ende in der Hand haben muss: seine Zeugnisse und die erzeugten Marken. -/
def Vertrag.ende (V : Vertrag D) : List (Res D) :=
  V.haelt.map Res.held ++ V.produziert.map (Res.vonMarke D)

/-- Womit ein Rumpf anfaengt: die Zeugnisse der Signatur und die verbrauchten Marken. -/
def Signatur.anfang (S : Signatur D.Tab D.Glob D.Lock D.Marke) : List (Res D) :=
  S.haelt.map Res.held ++ S.konsumiert.map (Res.vonMarke D)

/-- Die Signatur eines Rufs passt in den Vertrag des Rufers: Schreibrechte enthalten,
    verbrauchte Marken in der Hand. -/
structure RufPasst (V : Vertrag D) (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) : Prop where
  hw : ∀ t, S.schreibt t = true → V.schreibt t = true
  hg : ∀ g, S.gschreibt g = true → V.gschreibt g = true
  hk : Untermulti (S.konsumiert.map (Res.vonMarke D)) Λ
  /-- `requires Held(L)` des Gerufenen nennt GENAU die Zeugnisse, die der Rufer haelt: die
      Sperrmenge ist Teil des Vertrags. Nur so kann der Rang eines `locks` im Gerufenen gegen
      ALLES Gehaltene stehen (`H006` ueber Rufgrenzen hinweg). -/
  hh : ∀ L, Res.held L ∈ Λ ↔ L ∈ S.haelt

/-! ## 2. Sichtbereich und Variablen -/

abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type where
  | hier : Var (τ :: Γ) τ
  | dort : Var Γ τ → Var (σ :: Γ) τ

def ArmCtx (Γ : Ctx) : Option (Int × Int) → Ctx
  | none => Γ
  | some (lo, hi) => .int lo hi :: Γ

/-! ## 3. Ausdruecke -- `expr`, `pred`

    Jeder Konstruktor traegt den Bereich seines Ergebnisses im Typ. Was `M104` rechnet,
    steht hier als Index; was `M102`/`M103`/`M137` verlangen, steht als Argument. -/

mutual

inductive Expr : Ctx → List (Res D) → Ty → Type where
  | lit (n : Int) : Expr Γ Λ (.int n n)
  | wahr : Expr Γ Λ .bool
  | falsch : Expr Γ Λ .bool
  | var (x : Var Γ τ) : Expr Γ Λ τ
  /-- Ein `static`/`atomic`: unter seinen Waechtern (`H007`). -/
  | glob (g : D.Glob) (hL : gdarf D g Λ) : Expr Γ Λ (D.gtyp g)
  /-- `T.slots[i].f` -- Index vom ERZEUGTEN Indextyp (`M103`), Traeger unter Waechtern. -/
  | slot (t : D.Tab) (f : D.Feld t) (i : Expr Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
      Expr Γ Λ (D.typ t f)
  /-- `p->f`, `p[i].f` -- ein Zugriff DURCH einen Zeiger auf Traeger `n`: derselbe Zugriff wie
      `slot`, mit denselben Waechtern; der Zeiger ist die Faehigkeit, `t` zu nennen (M3). -/
  | durch (p : Expr Γ Λ (.ptr n rw)) (t : D.Tab) (ht : D.tabNr n = some t) (f : D.Feld t)
      (i : Expr Γ Λ (.index (D.count t))) (hL : darf D t Λ) : Expr Γ Λ (D.typ t f)
  /-- Der Zeiger auf einen Traeger -- die einzige Adresse, die es gibt: die eines DEKLARIERTEN
      Dings. Es gibt keine Adresse eines Ausdrucks (`SYNTAX.md` §4, `fnvalue`). -/
  | ptrOf (t : D.Tab) (n : Nat) (ht : D.tabNr n = some t) (rw : Bool) : Expr Γ Λ (.ptr n rw)
  /-- `&f` -- der Funktionszeiger: eine Funktion GENAU dieser Signatur («B8»). -/
  | fnref (f : D.Fn) (n : Nat) (h : D.sig f = n) : Expr Γ Λ (.fnptr n)
  /-- `old(g)`, `old(T.slots[i].f)` -- nur in `ensures`: der Wert beim Eintritt. -/
  | altGlob (g : D.Glob) (hL : gdarf D g Λ) : Expr Γ Λ (D.gtyp g)
  | altSlot (t : D.Tab) (f : D.Feld t) (i : Expr Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
      Expr Γ Λ (D.typ t f)
  | weiter (h1 : lo' ≤ lo) (h2 : hi ≤ hi') (e : Expr Γ Λ (.int lo hi)) : Expr Γ Λ (.int lo' hi')
  | add (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ (.int (l1 + l2) (h1 + h2))
  | sub (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ (.int (l1 - h2) (h1 - l2))
  | neg (a : Expr Γ Λ (.int lo hi)) : Expr Γ Λ (.int (-hi) (-lo))
  | mul (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
                     (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2))))
  /-- `/` `%` -- `M102`: Nenner in `1 ..`, Zaehler in `0 ..` («SG-3»). -/
  | div (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int 0 h1)
  | rem (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int 0 (h2 - 1))
  /-- Vorzeichenbehaftete Division und Rest («SG-3», zweiter Satz): der Nenner schliesst
      die Null aus (`1 ≤ lo₂` oder `hi₂ ≤ −1`); Ergebnis in `−M .. M`. -/
  | sdiv (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int (-(betragMax l1 h1)) (betragMax l1 h1))
  | srem (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1))
  /-- `n` Bytes ab Index `i` eines Bytetraegers, als EINE Zahl («SG-16»): `offset_into`,
      `@bitpos`, `embeds` und die zweite Sicht auf dieselben Bytes sind Lesungen dieser
      Form. Der Bereich des Index plus `n` liegt in der Tabelle -- das ist die Schranke am
      Versatz, als Attribut. -/
  | leseBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t) (hL : darf D t Λ) :
      Expr Γ Λ (.int 0 (256 ^ n - 1))
  /-- `&` `|` `^` `<<` `>>` `~` -- `M137`: nur ueber nichtnegativen Bereichen; `|`, `^`, `~`
      nennen die Breite. `~a` ist `a ^ (2^w − 1)`. -/
  | band (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int 0 h1)
  | bor (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
      (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ (.int 0 (2 ^ w - 1))
  | bxor (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
      (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ (.int 0 (2 ^ w - 1))
  | shl (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int 0 (h1 * 2 ^ h2.toNat))
  | shr (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int 0 h1)
  | lt (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ .bool
  | le (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ .bool
  | eq (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ .bool
  /-- Gleitkommavergleiche -- total, weil ein `Val (.fl …)` ENDLICH ist (`finite`): die
      Trichotomie gilt, die NaN-Vierteilung («F») gibt es nicht. -/
  | fllt (a : Expr Γ Λ (.fl l1 h1)) (b : Expr Γ Λ (.fl l2 h2)) : Expr Γ Λ .bool
  | flle (a : Expr Γ Λ (.fl l1 h1)) (b : Expr Γ Λ (.fl l2 h2)) : Expr Γ Λ .bool
  | und (a b : Expr Γ Λ .bool) : Expr Γ Λ .bool
  | oder (a b : Expr Γ Λ .bool) : Expr Γ Λ .bool
  | nicht (a : Expr Γ Λ .bool) : Expr Γ Λ .bool
  | none (n : Int) : Expr Γ Λ (.opt n)
  | some (e : Expr Γ Λ (.index n)) : Expr Γ Λ (.opt n)
  | istSome (e : Expr Γ Λ (.opt n)) : Expr Γ Λ .bool
  | fall (cs : List (Option (Int × Int))) (i : Fin cs.length)
      (nutz : NutzlastExpr Γ Λ (cs.get i)) : Expr Γ Λ (.sum cs)
  | grund (n : Nat) (r : Fin n) : Expr Γ Λ (.grund n)
  /-- `forall k in slots of T : pred` / `elems of` / `queue` -- der Binder traegt den Index. -/
  | forallSlots (t : D.Tab) (body : Expr (.index (D.count t) :: Γ) Λ .bool) (hL : darf D t Λ) :
      Expr Γ Λ .bool
  | existsSlots (t : D.Tab) (body : Expr (.index (D.count t) :: Γ) Λ .bool) (hL : darf D t Λ) :
      Expr Γ Λ .bool
  /-- `a reaches b via f` -- die Kette ueber ein `option index into Self`-Feld, mit `count`
      Schritten Treibstoff (mehr Schritte als Slots wiederholen einen). `descendants of`,
      `ancestors of` und `chain(…) in` sind `forallSlots` mit `reaches` als Filter. -/
  | reaches (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .opt (D.count t))
      (a b : Expr Γ Λ (.index (D.count t))) (hL : darf D t Λ) : Expr Γ Λ .bool

inductive NutzlastExpr : Ctx → List (Res D) → Option (Int × Int) → Type where
  | keine : NutzlastExpr Γ Λ none
  | zahl (e : Expr Γ Λ (.int lo hi)) : NutzlastExpr Γ Λ (some (lo, hi))

end

inductive Args : Ctx → List (Res D) → List Ty → Type where
  | nil : Args Γ Λ []
  | cons (e : Expr D Γ Λ τ) (rest : Args Γ Λ τs) : Args Γ Λ (τ :: τs)

/-! ## 4. Anweisungen -- `stmt`, `block`, und der Block, der nicht abfaellt -/

inductive ErgExpr (Γ : Ctx) (Λ : List (Res D)) : Option Ty → Type where
  | keine : ErgExpr Γ Λ none
  | wert (e : Expr D Γ Λ τ) : ErgExpr Γ Λ (some τ)

/-- Die Gleitkommarechnung («F»): jede Operation nennt den Bereich ihres Ergebnisses; die
    Maschine rechnet, und das Ergebnis wird gegen den Bereich gehalten (`rounded`). -/
inductive GleitOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr

variable (V : Vertrag D)

mutual

inductive Stmt : Bool → Ctx → List (Res D) → List (Res D) → Type where
  | assignSlot (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) : Stmt l Γ Λ Λ
  /-- `p->f = e;` -- Schreiben DURCH einen `rw`-Zeiger (`R002`/`R003`: kein `w` ohne Recht). -/
  | assignDurch (p : Expr D Γ Λ (.ptr n true)) (t : D.Tab) (ht : D.tabNr n = some t)
      (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
      (hw : V.schreibt t = true) (hL : darf D t Λ) : Stmt l Γ Λ Λ
  | assignGlob (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) : Stmt l Γ Λ Λ
  /-- `n` Bytes ab Index `i` schreiben («SG-16») -- ein Feld eines `format` ueber einem
      Bytetraeger setzen. -/
  | schreibBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t)
      (e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      Stmt l Γ Λ Λ
  | assignVar (x : Var Γ τ) (e : Expr D Γ Λ τ) : Stmt l Γ Λ Λ
  /-- `T.slots[i].s = B;` an einem `state`-Feld: der Uebergang `von -> nach` ist ERKLAERT
      (`state S { … }`), und dass das Feld gerade auf `von` steht, ist die Logik des
      Schreibers (`Logik.uebergang`). -/
  | uebergang (t : D.Tab) (f : D.Feld t) (hτ : D.typ t f = .int lo hi)
      (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
      (he : D.erlaubt t f von nach = true) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      Stmt l Γ Λ Λ
  | ite (c : Expr D Γ Λ .bool) (t e : Block l Γ Λ Λ') : Stmt l Γ Λ Λ'
  | onOption (o : Expr D Γ Λ (.opt n)) (p : Block l (.index n :: Γ) Λ Λ') (a : Block l Γ Λ Λ') :
      Stmt l Γ Λ Λ'
  | onTag (v : Expr D Γ Λ (.sum cs)) (arms : Arms l Γ Λ Λ' cs) : Stmt l Γ Λ Λ'
  | onGrund (r : Expr D Γ Λ (.grund n)) (arms : GrundArms l Γ Λ Λ' n) : Stmt l Γ Λ Λ'
  /-- `f(a, b);` -/
  | call (f : D.Fn) (args : Args D Γ Λ (D.params f)) (hp : RufPasst D V (D.signatur f) Λ)
      (hr : D.gruende f = 0) : Stmt l Γ Λ (nach D f Λ)
  /-- `p(a, b);` durch einen Funktionszeiger («B8»): der Vertrag steht am TYP. -/
  | callInd (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0) :
      Stmt l Γ Λ (nachSig D (D.sigNr n) Λ)
  /-- `locks L { … }` / `observes R { … }` -- Rang groesser als alles Gehaltene (`H006`). -/
  | locks (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block l Γ (.held L :: Λ) (.held L :: Λ)) : Stmt l Γ Λ Λ
  /-- `breaking I { … }` -- die Invariante ruht; ihre Wiederherstellung wird am `return`
      verlangt wie ohne `breaking` (`schuldet`). Der Name steht im Term, damit er
      nachgelesen werden kann (`D013`). -/
  | breaking (i : D.Inv) (body : Block l Γ Λ Λ') : Stmt l Γ Λ Λ'
  | traverse (t : D.Tab) (inv : Expr D Γ Λ .bool) (body : Block true (.index (D.count t) :: Γ) Λ Λ) :
      Stmt l Γ Λ Λ
  | retry (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block true Γ Λ Λ) (ueberlauf : Block l Γ Λ Λ) :
      Stmt l Γ Λ Λ
  | forever (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block true Γ Λ Λ) : Stmt l Γ Λ Λ
  | axiomCall (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true) : Stmt l Γ Λ Λ
  /-- `R = e;` an einem Register (`transition` ist dieselbe Anweisung mit dem Spiegel): die
      Klasse erlaubt das Schreiben, oder die Anweisung ist nicht ableitbar (`R005`/`R006`). -/
  | regSchreib (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (e : Expr D Γ Λ (D.rtyp r)) :
      Stmt l Γ Λ Λ
  /-- `transition t { R.b : 0 -> 1 }` (Falle 4): EIN Lesen des Spiegels `m`, EIN Schreiben
      auf `R` -- die Bits `bits` unter der Maske `maske` ersetzt, alle anderen aus dem
      Spiegel. Dass `m` der Spiegel von `R` ist, steht in der Deklaration (`mirrors`); dass
      das Geraet die zwei Zugriffe in dieser Reihenfolge sieht, ist die Annahme am Geraet. -/
  | transition (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (m : D.Reg)
      (hm : D.spiegel r = some m) (hl : (D.rklasse m).lesbar = true) (maske bits : Int) :
      Stmt l Γ Λ Λ
  /-- `A = e publishes { p, q };` -- die Nutzlast ist die erklaerte (`V001`-`V004` als Form);
      die Sichtbarkeit ist das Speichermodell, Annahme A10. -/
  | publish (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (payload : List D.Glob)
      (hp : payload = D.nutzlast g) (hw : V.gschreibt g = true) (hL : gdarf D g Λ) : Stmt l Γ Λ Λ
  /-- `advances a -> b` («B37»): die Marke steht auf Stufe `a`, und `b` ist die naechste. -/
  | advances (m : D.Marke) (a : Nat) (h : Res.marke m a ∈ Λ) (hs : a + 1 < D.stufen m) :
      Stmt l Γ Λ ((Λ.erase (.marke m a)) ++ [.marke m (a + 1)])
  /-- `retires t from space falsifier s` (S3): die Marke wird verbraucht, die Annahme genannt. -/
  | retires (m : D.Marke) (s : Nat) (h : Res.marke m s ∈ Λ) (a : D.Annahme) :
      Stmt l Γ Λ (Λ.erase (.marke m s))
  | ret (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) : Stmt l Γ Λ Λ
  | retGrund (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) : Stmt l Γ Λ Λ
  | leave (h : l = true) : Stmt l Γ Λ Λ
  | next (h : l = true) : Stmt l Γ Λ Λ

inductive Block : Bool → Ctx → List (Res D) → List (Res D) → Type where
  | nil : Block l Γ Λ Λ
  | cons (s : Stmt l Γ Λ Λ') (rest : Block l Γ Λ' Λ'') : Block l Γ Λ Λ''
  | bind (e : Expr D Γ Λ τ) (rest : Block l (τ :: Γ) Λ Λ') : Block l Γ Λ Λ'
  | bindCall (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
      (rest : Block l (τ :: Γ) (nach D f Λ) Λ') : Block l Γ Λ Λ'
  | bindCallInd (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
      (rest : Block l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ') : Block l Γ Λ Λ'
  | bindCallElse (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
      (err : Endblock l (.grund (D.gruende f) :: Γ) (nach D f Λ))
      (rest : Block l (τ :: Γ) (nach D f Λ) Λ') : Block l Γ Λ Λ'
  | bindAxiom (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (rest : Block l (τ :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = R;` -- eine Registerlesung, lesbar nach Klasse; `requires … else` (B26) ist die
      Form `regLiesElse`. -/
  | regLies (r : D.Reg) (hk : (D.rklasse r).lesbar = true) (rest : Block l (D.rtyp r :: Γ) Λ Λ') :
      Block l Γ Λ Λ'
  /-- `let x = R else (e) { … }` -- die Lesung ist fehlbar; die Geraetezusage (`requires`) ist
      die Bedingung, der `else`-Zweig faellt nicht ab. -/
  | regLiesElse (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock l Γ Λ)
      (rest : Block l (D.rtyp r :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = A awaits { p, q };` -- dieselbe Nutzlast wie am `publishes`. -/
  | awaits (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g) (hL : gdarf D g Λ)
      (rest : Block l (D.gtyp g :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = A exchange update(v) { … } …` -- Lesen, Rechnen, Schreiben: als EINE Anweisung
      (die Atomizitaet ist A10); `bounded`/`on_exceeded` sind die von `retry`. -/
  | exchange (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) (rest : Block l (D.gtyp g :: Γ) Λ Λ') : Block l Γ Λ Λ'
  | narrow (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock l Γ Λ)
      (rest : Block l (.int lo' hi' :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `where`-Bedingung eines `format`-Felds, `requires` einer Lesung, jede benannte Absage
      (Regel 3): die Bedingung gilt, oder der `else`-Zweig -- der nicht abfaellt. -/
  | pruefung (c : Expr D Γ Λ .bool) (sonst : Endblock l Γ Λ) (rest : Block l Γ Λ Λ') :
      Block l Γ Λ Λ'
  /-- Gleitkomma («F»): `let y = a op b;` mit erklaertem Bereich `lo .. hi` -- die Maschine
      rechnet (IEEE), das Ergebnis wird gegen den Bereich gehalten, und ein Ergebnis
      ausserhalb (oder NaN, Unendlich) ist `Hardware.ieee`. -/
  | gleit (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) (lo hi : Int × Int)
      (rest : Block l (.fl lo hi :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- Ein Gleitkommaliteral `1.5 rounded` in seinem Bereich. -/
  | gleitLit (q : Int × Int) (lo hi : Int × Int) (rest : Block l (.fl lo hi :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- Eine Zahl als Gleitkommazahl, in ihrem Bereich. -/
  | gleitVon (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int) (rest : Block l (.fl lo hi :: Γ) Λ Λ') :
      Block l Γ Λ Λ'
  /-- `narrow x to finite` -- eine Gleitkommazahl in einen engeren Bereich, sonst der
      `else`-Zweig. -/
  | gleitNarrow (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int) (sonst : Endblock l Γ Λ)
      (rest : Block l (.fl lo hi :: Γ) Λ Λ') : Block l Γ Λ Λ'

inductive Endblock : Bool → Ctx → List (Res D) → Type where
  | ret (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) : Endblock l Γ Λ
  | retGrund (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) : Endblock l Γ Λ
  | leave (h : l = true) : Endblock l Γ Λ
  | next (h : l = true) : Endblock l Γ Λ
  | cons (s : Stmt l Γ Λ Λ') (rest : Endblock l Γ Λ') : Endblock l Γ Λ
  | bind (e : Expr D Γ Λ τ) (rest : Endblock l (τ :: Γ) Λ) : Endblock l Γ Λ

inductive Arms : Bool → Ctx → List (Res D) → List (Res D) → List (Option (Int × Int)) → Type where
  | nil : Arms l Γ Λ Λ []
  | cons (b : Block l (ArmCtx Γ c) Λ Λ') (rest : Arms l Γ Λ Λ' cs) : Arms l Γ Λ Λ' (c :: cs)

inductive GrundArms : Bool → Ctx → List (Res D) → List (Res D) → Nat → Type where
  | nil : GrundArms l Γ Λ Λ 0
  | cons (b : Block l Γ Λ Λ') (rest : GrundArms l Γ Λ Λ' n) : GrundArms l Γ Λ Λ' (n + 1)

end

/-! ## 5. Das Programm -- Ruempfe und Vertraege zu den Signaturen -/

def vertragVon (f : D.Fn) : Vertrag D := Vertrag.vonSig D (D.signatur f)

def ErgCtx (Γ : Ctx) : Option Ty → Ctx
  | none => Γ
  | some τ => τ :: Γ

def invSicht (i : D.Inv) : List (Res D) :=
  (D.traeger i).foldr (fun t acc => (D.braucht t).map (Res.von D) ++ acc) []

/-- Ein Programm: je Funktion `requires`, `ensures` (mit `refines`: die `ensures` der
    Spezifikation sind darin enthalten -- eine Konjunktion, kein zweiter Kanal) und ein
    Rumpf, der nicht abfaellt; je Invariante ihr Praedikat. -/
structure Programm where
  invariante : ∀ i : D.Inv, Expr D [] (invSicht D i) .bool
  requires : ∀ f : D.Fn, Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool
  ensures : ∀ f : D.Fn, Expr D (ErgCtx (D.params f) (D.erg f)) (vertragVon D f).ende .bool
  rumpf : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f))

end Gabbro.Grammatik
