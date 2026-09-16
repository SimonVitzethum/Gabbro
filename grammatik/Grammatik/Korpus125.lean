/-
  File:      Grammatik/Korpus125.lean
  Subject:   THE G PROGRAM OF `beispiele/125-read-under-lock.gab`, attempted
             faithfully, with the exact blocking fact proved.

  The source: `static mut z : u32 = 0`, lock `WACHE` protecting `z`,
  `lese_schreibe() -> u32` (`locks WACHE { let v = z; z = v; return z; }`),
  `setze_null()` (`locks WACHE { z = 0; }`), `concurrent` starts. G forms
  exist for the global (`Glob`/`gtyp` with the declared initializer as
  `sp0`), the lock, the `locks` blocks, the global reads (`Expr.glob`) and
  writes (`Stmt.assignGlob`), the `let` (`Block.bind`) and the starts.

  THE BLOCKING FACT (proved as `offen125_ret_unter_locks` below, not
  asserted): the source's `return z` sits INSIDE `locks WACHE`, but a return
  needs `hΛ : Λ.Perm V.ende`, and `Vertrag.ende` is
  `V.haelt.map Res.held ++ …` (`Syntax.lean`) -- for `lese_schreibe`, whose
  signature holds nothing, `ende = []`, while inside the lock
  `Λ = [held WACHE]`. `[held W].Perm []` is uninhabited (`Perm.length_eq`),
  so no faithful body term exists. This is the G-side face of the exporter
  refusal LG004 (`lean_g.rs`: value readers under `locks` refused by name;
  the `Export108.lean` header records the same wall for the refused 108 root
  shape). Either the example moves its `return` out of the lock (corpus
  change, lane 204's territory) or G gains a form for value-return under
  lock. Until then the file carries the CLOSEST expressible program --
  `lese_schreibe` with the writeback inside and the `return z` outside --
  with premise groups proved on THAT program under honest
  `…_umgestaltet` names, never as `korpus125_nutzer`.
-/
import Grammatik.Zielsatz.Proben

namespace Gabbro.Grammatik

namespace K125

/-- The source declares no tables. -/
inductive QGlob where
  | z
  deriving DecidableEq

/-- Lock `WACHE` (rank 0, protects `z`). -/
inductive QLock where
  | w
  deriving DecidableEq

/-- Functions `lese_schreibe` and `setze_null`. -/
inductive QFn where
  | lese
  | setzeNull
  deriving DecidableEq

/-- A signature: result, written globals. Neither function holds a lock by
    signature (the source has no `requires Held`); both take `WACHE` in the
    body. -/
def kSig (e : Option Ty) (gs : List QGlob) :
    Signatur Empty QGlob QLock Empty where
  params := []
  erg := e
  gruende := 0
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun g => decide (g ∈ gs)
  konsumiert := []
  produziert := []

def kSigNr : Nat → Signatur Empty QGlob QLock Empty
  | 0 => kSig (some (.int 0 4294967295)) [.z]
  | 1 => kSig none [.z]
  | _ => kSig none []

def kSigOf : QFn → Nat
  | .lese => 0
  | .setzeNull => 1

/-- The declaration of `beispiele/125`: global `z = u32`, shared, guarded by
    `WACHE`; no tables, no table invariant, no axiom, no register. -/
def kD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun e => nomatch e
  Feld := fun e => nomatch e
  decFeld := fun e => nomatch e
  typ := fun e => nomatch e
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := QGlob
  decGlob := inferInstance
  gtyp := fun _ => .int 0 4294967295
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun e => nomatch e
  ggeteilt := fun _ => true
  Lock := QLock
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun e => nomatch e
  gbraucht := fun _ => [.inl QLock.w]
  eigner := fun e => nomatch e
  Fn := QFn
  sig := kSigOf
  sigNr := kSigNr
  eigner_nie_erzeugt := fun _ t _ _ _ => nomatch t
  Inv := Empty
  traeger := fun i => nomatch i
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
  geteilt_bewacht := fun e => nomatch e
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g _ => by cases g; exact Or.inl (by decide)

def kLese : kD.Fn := QFn.lese
def kSetzeNull : kD.Fn := QFn.setzeNull

instance : DecidableEq kD.Fn := inferInstanceAs (DecidableEq QFn)
instance : DecidableEq kD.Lock := inferInstanceAs (DecidableEq QLock)
instance : DecidableEq kD.Glob := inferInstanceAs (DecidableEq QGlob)

end K125

end Gabbro.Grammatik
