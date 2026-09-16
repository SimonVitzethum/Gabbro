/-
  File:      Grammatik/Korpus109.lean
  Subject:   THE G PROGRAM OF `beispiele/109-lockfree-entry-roots.gab`, with the
             bodies of the source, and every premise group of the goal theorem on it.

  The source: tables `T`, `U` (count 4, `u32` field `v`), locks `L`, `M`
  (ranks 0/1, disjoint carriers), leaves `write_a`/`write_b` (`requires Held`,
  one slot write of a constant), distributors `distribute_a`/`distribute_b`
  (`locks` around one call), two `entry` items dispatching to the
  distributors. Every form has a G counterpart: index params are
  `Ty.index (count)`, `requires Held` is the signature-held set, `locks`
  blocks and direct calls are `Stmt`, the entry dispatch roots are the
  declared starts, `costs` is ignored form (like `reads`). No annotation is
  dropped: 109 carries no `deadline`/`falsifier`. No lock invariant is
  declared in the source, so the family is trivially true (owed nowhere).
-/
import Grammatik.Zielsatz.Proben

namespace Gabbro.Grammatik

namespace K109

/-- Tables `T` and `U` of the source. -/
inductive KTab where
  | t
  | u
  deriving DecidableEq

/-- Locks `L` (rank 0, protects `T`) and `M` (rank 1, protects `U`). -/
inductive KLock where
  | l
  | m
  deriving DecidableEq

/-- Functions `write_a`, `distribute_a`, `write_b`, `distribute_b`. -/
inductive KFn where
  | writeA
  | distA
  | writeB
  | distB
  deriving DecidableEq

/-- A signature: parameters, result, signature locks, written tables. -/
def kSig (ps : List Ty) (e : Option Ty) (h : List KLock) (ts : List KTab) :
    Signatur KTab Empty KLock Empty where
  params := ps
  erg := e
  gruende := 0
  haelt := h
  schreibt := fun t => decide (t ∈ ts)
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def kBraucht : KTab → List (KLock ⊕ (Empty × Nat))
  | .t => [.inl .l]
  | .u => [.inl .m]

/-- Both tables are shared, each guarded by its lock. -/
def kGeteilt : KTab → Bool
  | _ => true

def kRang : KLock → Int
  | .l => 0
  | .m => 1

def kSigNr : Nat → Signatur KTab Empty KLock Empty
  | 0 => kSig [Ty.index 4] none [.l] [.t]
  | 1 => kSig [] none [] [.t]
  | 2 => kSig [Ty.index 4] none [.m] [.u]
  | 3 => kSig [] none [] [.u]
  | _ => kSig [] none [] []

def kSigOf : KFn → Nat
  | .writeA => 0
  | .distA => 1
  | .writeB => 2
  | .distB => 3

/-- The declaration of `beispiele/109`: tables `T`, `U` (shared, guarded by
    `L`/`M`), two slots... four slots each, `v = u32`; no global, no table
    invariant, no axiom, no register. -/
def kD : Deklaration where
  Tab := KTab
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 4294967295
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := kGeteilt
  ggeteilt := fun e => nomatch e
  Lock := KLock
  decLock := inferInstance
  rang := kRang
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := kBraucht
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := KFn
  sig := kSigOf
  sigNr := kSigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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
  geteilt_bewacht := fun t h => by cases t <;> simp_all [kGeteilt, kBraucht]
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def kWriteA : kD.Fn := KFn.writeA
def kDistA : kD.Fn := KFn.distA
def kWriteB : kD.Fn := KFn.writeB
def kDistB : kD.Fn := KFn.distB

instance : DecidableEq kD.Fn := inferInstanceAs (DecidableEq KFn)
instance : DecidableEq kD.Lock := inferInstanceAs (DecidableEq KLock)

end K109

end Gabbro.Grammatik
