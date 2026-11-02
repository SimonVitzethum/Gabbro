/-
  File:      Grammatik/Korpus125.lean
  Subject:   THE G PROGRAM OF `beispiele/0125-read-under-lock.gab`, value-
             faithful: `lese_schreibe` returns the `z` it read under the lock.

  The source: `static mut z : u32 = 0`, lock `WACHE` protecting `z`,
  `lese_schreibe() -> u32` (`locks WACHE { let v = z; z = v; return z; }`),
  `setze_null()` (`locks WACHE { z = 0; }`), `concurrent` starts. G forms
  exist for the global (`Glob`/`gtyp` with the declared initializer as
  `sp0`), the lock, the `locks` blocks, the global reads (`Expr.glob`) and
  writes (`Stmt.assignGlob`), the `let` (`Block.bind`), a write to an outer
  local (`Stmt.assignVar`) and the starts.

  THE ONE DIVERGENCE OF FORM: a `return` INSIDE `locks WACHE` has no G term
  (`offen125_ret_unter_locks`: a return needs `Λ.Perm V.ende`, and inside
  the lock `Λ = [held WACHE]` while `ende = []`). The body below is
  `let r = 0; locks WACHE { let v = z; z = v; r = z; } return r;` -- the
  value `z` is read under the lock into an outer local and returned right
  after the release, which is what the source's `return z` inside the lock
  returns (the release is the only thing between the read and the return,
  and a release writes no carrier). This is the term review G02 (2026-09-21)
  found; fix lane F8 built it and re-proved every premise group on it, so
  the earlier reshaped body (constant `return 0`) and its `…_umgestaltet`
  names are gone. The Rust exporter still refuses the source shape (LG004,
  `tests/lean_g.rs::return_under_locks_stays_refused`): it has no rule that
  rewrites a return under a lock into this outer-local form -- a gap of the
  exporter, not of G.
-/
module
public import Grammatik.Zielsatz.Kern.Proben
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


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
  schreibt := fun t => (nomatch t)
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
  count := fun e => (nomatch e)
  Feld := fun e => (nomatch e)
  decFeld := fun e => (nomatch e)
  typ := fun e => (nomatch e)
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := QGlob
  decGlob := inferInstance
  gtyp := fun _ => .int 0 4294967295
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun e => (nomatch e)
  ggeteilt := fun _ => true
  Lock := QLock
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => (nomatch e)
  braucht := fun e => (nomatch e)
  gbraucht := fun _ => [.inl QLock.w]
  eigner := fun e => (nomatch e)
  Fn := QFn
  sig := kSigOf
  sigNr := kSigNr
  eigner_nie_erzeugt := fun _ t _ _ _ => (nomatch t)
  Inv := Empty
  traeger := fun i => (nomatch i)
  invs := []
  Ax := Empty
  aparams := fun e => (nomatch e)
  aerg := fun e => (nomatch e)
  aschreibt := fun e => (nomatch e)
  agschreibt := fun e => (nomatch e)
  Reg := Empty
  rtyp := fun e => (nomatch e)
  rklasse := fun e => (nomatch e)
  spiegel := fun e => (nomatch e)
  rzusage := fun e => (nomatch e)
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun e => (nomatch e)
  invarianten_gehalten := fun _ i => (nomatch i)
  ggeteilt_bewacht := fun g _ => by cases g; exact Or.inl (by decide)

def kLese : kD.Fn := QFn.lese
def kSetzeNull : kD.Fn := QFn.setzeNull

instance : DecidableEq kD.Fn := inferInstanceAs (DecidableEq QFn)
instance : DecidableEq kD.Lock := inferInstanceAs (DecidableEq QLock)
instance : DecidableEq kD.Glob := inferInstanceAs (DecidableEq QGlob)

abbrev kLW : List (Res kD) := [Res.held (D := kD) QLock.w]

theorem kGdarfW : gdarf kD QGlob.z kLW := by
  intro w h
  change w ∈ ([Sum.inl QLock.w] : List (QLock ⊕ (Empty × Nat))) at h
  have e : w = Sum.inl QLock.w := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-- `0 : u32`, the constant `setze_null` writes. -/
def kNull {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 4294967295) :=
  .widen (by decide) (by decide) (.lit 0)

/-- `setze_null()`: `locks WACHE { z = 0; }` -- exactly the source body. -/
def kRumpfSetzeNull : Endblock kD (vertragVon kD kSetzeNull) false [] [] :=
  .cons (.locks QLock.w (fun _ h => nomatch h)
    (.cons (.assignGlob QGlob.z kNull rfl kGdarfW) .nil))
    (.ret .empty List.Perm.nil)

/-- `lese_schreibe`, value-faithful: `let r = 0; locks WACHE { let v = z;
    z = v; r = z; } return r;` -- the source's `return z` inside the lock
    becomes a write of `z` to the outer local `r` inside the lock and the
    return of `r` right after the release (see the header). -/
def kRumpfLese : Endblock kD (vertragVon kD kLese) false [] [] :=
  .bind kNull
    (.cons (.locks QLock.w (fun _ h => nomatch h)
      (.bind (.glob QGlob.z kGdarfW)
        (.cons (.assignGlob QGlob.z (.var .here) rfl kGdarfW)
          (.cons (.assignVar (.there .here) (.glob QGlob.z kGdarfW)) .nil))))
      (.ret (.val (.var .here)) List.Perm.nil))

/-- **The program of `beispiele/125`** (value-faithful `lese_schreibe`);
    trivial contracts (the source declares no `requires`/`ensures`). -/
def kP : Programm kD where
  invariante := fun i => (nomatch i)
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .lese => kRumpfLese
    | .setzeNull => kRumpfSetzeNull

def kFs : List kD.Fn := [kLese, kSetzeNull]

theorem kFs_voll : ∀ g : kD.Fn, g ∈ kFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self


end K125

end Gabbro.Grammatik
