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

abbrev kLW : List (Res kD) := [Res.held (D := kD) QLock.w]

theorem kGdarfW : gdarf kD QGlob.z kLW := by
  intro w h
  change w ∈ ([Sum.inl QLock.w] : List (QLock ⊕ (Empty × Nat))) at h
  have e : w = Sum.inl QLock.w := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-- `0 : u32`, the constant `setze_null` writes. -/
def kNull {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 4294967295) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- `setze_null()`: `locks WACHE { z = 0; }` -- exactly the source body. -/
def kRumpfSetzeNull : Endblock kD (vertragVon kD kSetzeNull) false [] [] :=
  .cons (.locks QLock.w (fun _ h => nomatch h)
    (.cons (.assignGlob QGlob.z kNull rfl kGdarfW) .nil))
    (.ret .keine List.Perm.nil)

/-- `lese_schreibe` RESHAPED: the writeback `z = z` inside `locks WACHE`,
    `return 0` outside. The source returns `z` inside; that term does not
    exist (`offen125_ret_unter_locks` below), and a guarded read outside the
    lock is untypeable too (`offen125_lese_aussen`), so the reshaped return
    is a constant. Both divergences are findings, not silent changes. -/
def kRumpfLese : Endblock kD (vertragVon kD kLese) false [] [] :=
  .cons (.locks QLock.w (fun _ h => nomatch h)
    (.cons (.assignGlob QGlob.z (.glob QGlob.z kGdarfW) rfl kGdarfW) .nil))
    (.ret (.wert kNull) List.Perm.nil)

/-- **The program of `beispiele/125`** with the reshaped `lese_schreibe`;
    trivial contracts (the source declares no `requires`/`ensures`). -/
def kP : Programm kD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .lese => kRumpfLese
    | .setzeNull => kRumpfSetzeNull

def kFs : List kD.Fn := [kLese, kSetzeNull]

theorem kFs_voll : ∀ g : kD.Fn, g ∈ kFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **The lock family**: `WACHE` protects `z`; the source declares no
    invariant, so it is trivially true. -/
def kSI : SperrInv kD :=
  ⟨fun _ => [.inr QGlob.z], fun _ _ => true⟩

theorem kSI_ok : SperrInvOk kSI := by
  refine ⟨fun L c hc => ?_, fun L s s' h => rfl⟩
  · cases L
    have e : c = .inr QGlob.z := List.mem_singleton.mp hc
    subst e
    change Sum.inl QLock.w ∈ ([Sum.inl QLock.w] : List (QLock ⊕ (Empty × Nat)))
    exact List.mem_singleton.mpr rfl

theorem kLocks_voll : ∀ L : kD.Lock, L ∈ ([QLock.w] : List kD.Lock) := fun L => by
  cases L
  exact List.mem_singleton_self _

def kCs : List (kD.Tab ⊕ kD.Glob) := [.inr QGlob.z]

theorem kCs_voll : ∀ c : kD.Tab ⊕ kD.Glob, c ∈ kCs := fun c => by
  rcases c with t | g
  · exact nomatch t
  · cases g; simp [kCs]

/-- **The checker accepts the reshaped program** with its declared starts
    `lese_schreibe`, `setze_null` (the `concurrent` members). -/
theorem kP_akzeptiert : Akzeptiert kP kSI kFs [QLock.w] kCs [kLese, kSetzeNull] = true := by decide

/-! ## 3. The blocking facts, proved -/

/-- `lese_schreibe` holds nothing by signature, so its end holdings are `[]`. -/
theorem kEndeLese : (vertragVon kD kLese).ende = [] := rfl

/-- **No faithful `lese_schreibe` body exists**: a return inside
    `locks WACHE` would need `[held WACHE].Perm []` (the `hΛ` of `Stmt.ret`
    at `Λ = [held WACHE]` against `ende = []`), which is uninhabited. -/
theorem offen125_ret_unter_locks :
    ¬ (([Res.held (D := kD) QLock.w] : List (Res kD)).Perm (vertragVon kD kLese).ende) := by
  rw [kEndeLese]
  intro h
  have := List.Perm.length_eq h
  simp at this

/-- **No guarded read outside the lock**: `z` is shared and guarded, so
    `gdarf z []` is uninhabited -- the reshaped `return 0` cannot read `z`. -/
theorem offen125_lese_aussen : ¬ gdarf kD QGlob.z [] := by
  intro h
  have h2 : Res.held (D := kD) QLock.w ∈ ([] : List (Res kD)) :=
    h _ (List.mem_singleton.mpr rfl)
  simp at h2

/-- Named open premise for the corpus decision (lane 204's territory): the
    source-shape `return z` inside `locks WACHE` has no G term until the
    example moves it out or G gains value-return under lock. -/
def offen125 : String :=
  "lese_schreibe returns z inside locks WACHE: no G term (offen125_ret_unter_locks); move the return out or add the form"

end K125

end Gabbro.Grammatik
