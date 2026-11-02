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
                                               Annahme `gleitkomma_ieee`, C-Seite; ein
                                               Ergebnis ausserhalb ist `Logik.bereich`)
    «B37» order/advances                       -> `Res.marke m stufe`, `Stmt.advances`
    state/transition ueber Felder              -> `Stmt.uebergang` (die Vorstufe ist Logik)
    seit dem Abend des 2026-09-09 («SG-3»², «SG-16»², «SG-15»², «SG-13»², «SG-20», «SG-21»):
    vorzeichenbehaftete Division              -> `Expr.sdiv/srem`
    Bytes und `format` als Sicht               -> `Expr.leseBytes`, `Stmt.schreibBytes`
    `transition` mit Spiegel, Registerzusage   -> `Stmt.transition`, `D.spiegel`, `D.rzusage`
    `awaits` und das Speichermodell            -> `Orakel.sichtbar`, `Hardware.sichtbarkeit`
    `requires Held(L)`                         -> `RufPasst.hh` (⊆ since 2026-09-13; `hx`/`hb`
                                               with the lock floor `Signatur.boden`), `Signatur.haelt`
    `shared`, U003 als Erklaerung              -> `D.geteilt`, `D.invarianten_gehalten`
    Faeden                                     -> `Wettlauf.lean` (Lauf, Gesittet, HB)

  QUELLSAETZE
    dokumente/SYNTAX.md (die neue Fassung, 2026-09-09) -- jede Produktion nennt ihren
    Konstruktor hier; LANGUAGE.md:788 "Linear means linear, not affine".
-/
module

public import Grammatik.Kern.Syntax.Typen.Teil2

@[expose] public section



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
  /-- The lock FLOOR (2026-09-13, held-set relaxation): `some c` -- the body
      takes only locks of rank at least `c` (`Stmt.ueberBoden`, a program
      fact, `StufenOk`), so a caller may hold, beyond `haelt`, any lock of
      rank below `c` while this function runs (`RufPasst.hx`); `none` -- no
      lock beyond `haelt` may be held at entry (the old exact held set). The
      checker's counterpart is its interprocedural `H006`/`H003` walk; the
      value is computed from the call graph, not written by the user. -/
  boden : Option Int := none

/-- **A function conforms to a pointer type** (Simon, 2026-10-21: pointer types are STRUCTURAL):
    the function's own signature `S` fits the signature `T` its pointer type names. Equal
    parameters, result, reasons and marks (consumed and produced: the caller's held set after
    the call is `nachSig T`, which must be the one the callee leaves); its writes are among
    `T`'s; it requires only locks `T` requires; a lock `T` requires and `S` does not stays held
    by the caller through the call and ranks below `S`'s floor; `T`'s floor is at most `S`'s.
    So everything a call through the pointer establishes for `T` (`RufPasst`) holds for `S`
    (`RufPasst.vonPasst`). The model has no contract on a signature: `requires`/`ensures` are
    the program's, per function, and stay with the function actually called. -/
structure SigPasst {Tab Glob Lock Marke : Type} (rang : Lock → Int)
    (S T : Signatur Tab Glob Lock Marke) : Prop where
  params : S.params = T.params
  erg : S.erg = T.erg
  gruende : S.gruende = T.gruende
  schreibt : ∀ t, S.schreibt t = true → T.schreibt t = true
  gschreibt : ∀ g, S.gschreibt g = true → T.gschreibt g = true
  konsumiert : S.konsumiert = T.konsumiert
  produziert : S.produziert = T.produziert
  haelt : ∀ L, L ∈ S.haelt → L ∈ T.haelt
  extra : ∀ L, L ∈ T.haelt → L ∉ S.haelt → ∃ c, S.boden = some c ∧ rang L < c
  boden : ∀ c, T.boden = some c → ∃ c', S.boden = some c' ∧ c ≤ c'

/-- A signature conforms to itself. -/
theorem SigPasst.refl {Tab Glob Lock Marke : Type} (rang : Lock → Int) (S : Signatur Tab Glob Lock Marke) :
    SigPasst rang S S :=
  ⟨rfl, rfl, rfl, fun _ h => h, fun _ h => h, rfl, rfl, fun _ h => h, fun _ h hn => absurd h hn,
    fun c h => ⟨c, h, Int.le_refl c⟩⟩

/-- Exactly the signature number: the pointer types before 2026-10-21. -/
theorem SigPasst.von_eq {Tab Glob Lock Marke F : Type} (rang : Lock → Int) (sig : F → Nat)
    (sigNr : Nat → Signatur Tab Glob Lock Marke) {f : F} {n : Nat} (h : sig f = n) :
    SigPasst rang (sigNr (sig f)) (sigNr n) := h ▸ SigPasst.refl rang _

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
  /-- `table T from p` -- an OPEN table: a region without a declared element ceiling. Its cells are addressed by
      `ref` values (`Expr.slotRef`), not by the bounded index type; `count` does not bound them. Every cell of
      such a region comes from the program's own provider (an answer of type `ref`); that it has memory to give is
      user logic. Default: no table is open. -/
  offen : Tab → Bool := fun _ => false
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
  /-- **Conformance of a function to a pointer type** (2026-10-21): `passt f n` -- `f` may be
      the value of a `fnptr n`. Default: exactly the signature number (`sig f = n`). -/
  passt : Fn → Nat → Bool := fun f n => decide (sig f = n)
  /-- What conformance means: the function's own signature fits the pointer's (`SigPasst`). -/
  passt_ok : ∀ f n, passt f n = true → SigPasst rang (sigNr (sig f)) (sigNr n) := by
    intro f n h; have e := of_decide_eq_true h; subst e; exact SigPasst.refl _ _
  eigner_nie_erzeugt : ∀ n t m s, m ∈ eigner t → (m, s) ∉ (sigNr n).produziert
  /-- `table … { invariant I }` / `group … { invariant I }`. The carriers of an invariant are tables AND
      globals (C05): one list over the sum of both kinds, like `rtraeger`. -/
  Inv : Type
  traeger : Inv → List (Tab ⊕ Glob)
  invs : List Inv
  /-- `axiom`, und jeder FREMDE Rumpf: `extern fn`, `prim fn`, `asm`, `entry`, `entrust`. -/
  Ax : Type
  aparams : Ax → List Ty
  aerg : Ax → Option Ty
  aschreibt : Ax → Tab → Bool
  agschreibt : Ax → Glob → Bool
  /-- `-> T or R` at a foreign body (a fallible `syscall` gate): the number of reasons of its
      channel (C-free lane, 2026-09-30). The machine's raw answer then carries the channel
      PACKED like a `tagged` value (`summePasst`): case `0` is the value, case `i + 1` the
      reason `i` (`axiomAntwortSonst`, Semantik.lean). Default: no channel -- every
      declaration written before this field is the declaration of before. -/
  agruende : Ax → Nat := fun _ => 0
  /-- `table T from p` -- the provider of an open table: the foreign item whose answer is a fresh cell of
      `T`, and the item `alloc T` calls (`Block.alloc`, Zucker.lean). Default: no table has a provider. -/
  anbieter : Tab → Option Ax := fun _ => none
  /-- A provider fits its table: the table is open, the provider takes no arguments and answers `ref T`. A
      declaration whose provider answers anything else cannot be built. -/
  anbieter_passt : ∀ t a, anbieter t = some a →
      offen t = true ∧ aparams a = [] ∧ ∃ n, aerg a = some (.ref n) ∧ tabNr n = some t := by
    intro _ _ h; exact nomatch h
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
  rzusage : ∀ r : Reg, Val Fn passt (rtyp r) → Bool
  /-- The carriers that hold the state of `r`'s device: the tables and
      globals a read of `r` may depend on (`RegLokal`, `ZielOrtGeraet.lean`).
      A device whose state changes by itself changes these carriers, through
      a declared write (an axiom whose frame names them). Default: none --
      the answer depends on no memory at all. -/
  rtraeger : Reg → List (Tab ⊕ Glob) := fun _ => []
  /-- `assume a "…" falsifier …` -- die benannten Annahmen, an `progress` und `retires`. -/
  Annahme : Type
  /-- A10: das Speichermodell -- `publishes`/`awaits` ordnen, wie die Maschine es zusagt. -/
  a10 : Annahme
  /-- Ein Traeger ohne Waechter ist nicht geteilt; ein Global ohne Waechter ist `atomic`
      oder nicht geteilt. Das ist die Erklaerung, aus der `kein_wettlauf` (Wettlauf.lean)
      seine Voraussetzung nimmt. -/
  geteilt_bewacht : ∀ t, geteilt t = true → braucht t ≠ []
  /-- `U003` als Erklaerung: wer einen Traeger einer Invariante schreibt (eine Tabelle ueber `schreibt`,
      ein Global ueber `gschreibt`), haelt die Sperren ALLER ihrer Traeger (`braucht` bzw. `gbraucht`) --
      denn er schuldet sie am `return`, und sie liest sie alle. -/
  invarianten_gehalten : ∀ n i,
      (traeger i).any (Sum.elim (sigNr n).schreibt (sigNr n).gschreibt) = true →
      ∀ c ∈ traeger i, ∀ L, Sum.inl L ∈ Sum.elim braucht gbraucht c → L ∈ (sigNr n).haelt
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
abbrev Wert : Ty → Type := Val D.Fn D.passt

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

/-- A conforming callee leaves the caller the held set the pointer type promises. -/
theorem nachSig_passt {S T : Signatur D.Tab D.Glob D.Lock D.Marke} (h : SigPasst D.rang S T)
    (Λ : List (Res D)) : nachSig D S Λ = nachSig D T Λ := by
  unfold nachSig; rw [h.konsumiert, h.produziert]

/-- The signature of a function that conforms to `fnptr n` fits `n`. -/
theorem Deklaration.passt_sig {f : D.Fn} {n : Nat} (h : D.passt f n = true) :
    SigPasst D.rang (D.signatur f) (D.sigNr n) := D.passt_ok f n h

/-- Der Vertrag der Funktion, in der eine Anweisung steht. -/
structure Vertrag where
  schreibt : D.Tab → Bool
  gschreibt : D.Glob → Bool
  erg : Option Ty
  gruende : Nat
  haelt : List D.Lock
  produziert : List (D.Marke × Nat)
  /-- The lock floor of the function (`Signatur.boden`). -/
  boden : Option Int := none

def Vertrag.vonSig (S : Signatur D.Tab D.Glob D.Lock D.Marke) : Vertrag D :=
  ⟨S.schreibt, S.gschreibt, S.erg, S.gruende, S.haelt, S.produziert, S.boden⟩

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
  /-- Every lock the callee requires (`requires Held(L)`) is held by the caller:
      the callee's held set is a SUBSET of the caller's (relaxed 2026-09-13 from
      the exact held set, verdict note T -- what the checker accepts). The
      caller's extra locks stay held for the whole callee frame; the callee
      neither names, releases nor re-takes them. -/
  hh : ∀ L, L ∈ S.haelt → Res.held L ∈ Λ
  /-- An extra lock (held by the caller, not required by the callee) ranks
      below the callee's floor: so every `locks M` of the callee (rank at least
      the floor, `StufenOk`) still ranks above EVERYTHING held (`H006` across
      the call boundary) and never re-takes a held lock (`H003`). Vacuous
      for an exact held set. -/
  hx : ∀ L, Res.held L ∈ Λ → L ∉ S.haelt → ∃ c, S.boden = some c ∧ D.rang L < c := by
    intro L hL; first
      | exact absurd hL (by simp)
      | exact nomatch L
      | (intro hn; exact absurd hL (by simp_all))
  /-- The caller's own floor is at most the callee's: locks the caller runs
      under without naming them (its own extras) stay below the callee's floor. -/
  hb : ∀ c, V.boden = some c → ∃ c', S.boden = some c' ∧ c ≤ c' := by
    intro c hc; first
      | cases hc
      | (simp at hc)
      | exact ⟨c, hc, Int.le_refl c⟩

/-- The exact held set (the form before 2026-09-13) gives the relaxed `hh`. -/
theorem RufPasst.hh_von {D : Deklaration} {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)}
    (h : ∀ L, Res.held L ∈ Λ ↔ L ∈ S.haelt) : ∀ L, L ∈ S.haelt → Res.held L ∈ Λ :=
  fun L hL => (h L).mpr hL

/-- ... and makes `hx` vacuous: there is no extra lock. -/
theorem RufPasst.hx_von {D : Deklaration} {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)}
    (h : ∀ L, Res.held L ∈ Λ ↔ L ∈ S.haelt) :
    ∀ L, Res.held L ∈ Λ → L ∉ S.haelt → ∃ c, S.boden = some c ∧ D.rang L < c :=
  fun L hL hn => absurd ((h L).mp hL) hn

/-- **A call through a pointer fits the callee** (2026-10-21): what the caller establishes for the
    pointer's signature `T` holds for the signature `S` of every function that conforms to it. -/
theorem RufPasst.vonPasst {D : Deklaration} {V : Vertrag D} {S T : Signatur D.Tab D.Glob D.Lock D.Marke}
    {Λ : List (Res D)} (hs : SigPasst D.rang S T) (hp : RufPasst D V T Λ) : RufPasst D V S Λ where
  hw t h := hp.hw t (hs.schreibt t h)
  hg g h := hp.hg g (hs.gschreibt g h)
  hk := by rw [hs.konsumiert]; exact hp.hk
  hh L h := hp.hh L (hs.haelt L h)
  hx L hL hn := by
    by_cases hT : L ∈ T.haelt
    · exact hs.extra L hT hn
    · obtain ⟨c, hc, hr⟩ := hp.hx L hL hT
      obtain ⟨c', hc', hle⟩ := hs.boden c hc
      exact ⟨c', hc', Int.lt_of_lt_of_le hr hle⟩
  hb c hc := by
    obtain ⟨c', hc', hle⟩ := hp.hb c hc
    obtain ⟨c'', hc'', hle'⟩ := hs.boden c' hc'
    exact ⟨c'', hc'', Int.le_trans hle hle'⟩

/-! ## 2. Sichtbereich und Variablen -/

abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type where
  | here : Var (τ :: Γ) τ
  | there : Var Γ τ → Var (σ :: Γ) τ

def ArmCtx (Γ : Ctx) : Option (Int × Int) → Ctx
  | none => Γ
  | some (lo, hi) => .int lo hi :: Γ

/-! ## 3. Ausdruecke -- `expr`, `pred`

    Jeder Konstruktor traegt den Bereich seines Ergebnisses im Typ. Was `M104` rechnet,
    steht hier als Index; was `M102`/`M103`/`M137` verlangen, steht als Argument. -/

end Gabbro.Grammatik
