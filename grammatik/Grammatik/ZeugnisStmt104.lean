/-
  File:     Grammatik/ZeugnisStmt104.lean
  Subject:  GENERATED statement certificates (lane 153, T1 transfer).

  The `CertEnd2` terms below are verbatim output of
  `gabbro certificate` (module `certstmt.rs`, one term per function body;
  see `crates/gabbro-check/tests/certstmt.rs` for the pinned probes).
  Each `example` runs the Lean checker (`certEnd2Ok ... = true` by
  `decide`); each soundness corollary applies `zeugnisStmt2_sound`.
  The `beispiele/104-referenz.gab` bodies themselves are REFUSED by the
  printer (pointer write, call with arguments, pointer read -- see CUTS);
  the checked terms below come from the fitting probe bodies.
-/
import Grammatik.ZeugnisStmt2

namespace Gabbro.Grammatik

/-! ## 1. The demo declaration: the probe names as Lean types

    The printer prints surface names verbatim (`T`, `x`, `f`), so the demo
    declaration carries them as constructors. Resources erase to `[]` (the
    printer convention), hence no locks: `braucht` is empty and every
    `haelt` is empty, so `darf` holds vacuously and `Vertrag.ende` is `[]`.
    `count` is the literal `2` the probes declare. -/

/-- The probe table. -/
inductive CSTab where
  | T
  deriving DecidableEq

/-- The probe field. -/
inductive CSFeld where
  | x
  deriving DecidableEq

/-- The probe functions: one per pinned probe body. -/
inductive CSFn where
  | fRet
  | fBind
  | fVar
  | fWenn
  | fSlot
  deriving DecidableEq

/-- Elimination out of `Empty` for the unused carrier maps: a plain
    constant, so no tuple ever holds an inline `nomatch`. -/
def csElimBool : Empty → Bool := fun e => nomatch e

/-- Signatures: the parameter and result ranges the probes claim. -/
def csSig : CSFn → Signatur CSTab Empty Empty Empty
  | .fRet => ⟨[.int 0 10], some (.int 0 10), 0, [], fun _ => false,
    csElimBool, [], []⟩
  | .fBind => ⟨[], some (.int 3 3), 0, [], fun _ => false,
    csElimBool, [], []⟩
  | .fVar => ⟨[.int 0 10], some (.int 0 10), 0, [], fun _ => false,
    csElimBool, [], []⟩
  | .fWenn => ⟨[.int 0 10], some (.int 0 10), 0, [], fun _ => false,
    csElimBool, [], []⟩
  | .fSlot => ⟨[], none, 0, [], fun _ => true,
    csElimBool, [], []⟩

/-- The demo declaration. -/
def csD : Deklaration where
  Tab := CSTab
  count := fun _ => 2
  Feld := fun _ => CSFeld
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some .T | _ => none
  Glob := Empty
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := CSFn
  sig := fun | .fRet => 0 | .fBind => 1 | .fVar => 2 | .fWenn => 3 | .fSlot => 4
  sigNr := fun
    | 0 => csSig .fRet
    | 1 => csSig .fBind
    | 2 => csSig .fVar
    | 3 => csSig .fWenn
    | _ => csSig .fSlot
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
  ggeteilt_bewacht := fun e => nomatch e

/-- Contracts at the demo: writes only for the slot body, ends empty. -/
def csV : CSFn → Vertrag csD
  | .fRet => ⟨fun _ => false, csElimBool, some (.int 0 10), 0, [], []⟩
  | .fBind => ⟨fun _ => false, csElimBool, some (.int 3 3), 0, [], []⟩
  | .fVar => ⟨fun _ => false, csElimBool, some (.int 0 10), 0, [], []⟩
  | .fWenn => ⟨fun _ => false, csElimBool, some (.int 0 10), 0, [], []⟩
  | .fSlot => ⟨fun _ => true, csElimBool, none, 0, [], []⟩

/-! ## 2. Generated certificates: the fitting probe bodies

    Each `csCert*` is verbatim printer output for the probe body named in
    its docstring (pinned in `crates/gabbro-check/tests/certstmt.rs`); each
    `example` runs the Lean checker; each soundness corollary applies
    `zeugnisStmt2_sound`. Contexts list the head first: `Γ = [.int 0 10]`
    means the parameter `x`, `Γ = [.int 0 10, .int 0 10]` the local `y`
    over the parameter `x`. -/

/-- Printer output for `return x;` with `x : K`, `K = u32 in 0 .. 10`. -/
def csCertRet : CertEnd2 csD (csV .fRet) :=
  (.liftE (.retWert (.var 0) 0 10))

/-- The print is valid, by `decide`. -/
example : certEnd2Ok csD (csV .fRet) false [.int 0 10] [] csCertRet = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock csD (csV .fRet) false [.int 0 10] [], True :=
  zeugnisStmt2_sound csD _ false _ _ csCertRet (by decide)

/-- Printer output for `let y : D3 = 1 + 2; return y;`, `D3 = 0 .. 3`. -/
def csCertBind : CertEnd2 csD (csV .fBind) :=
  (.liftE (.bind (.add (.lit 1) (.lit 2)) 3 3 (.retWert (.var 0) 3 3)))

/-- The print is valid, by `decide`. -/
example : certEnd2Ok csD (csV .fBind) false [.int 3 3] [] csCertBind = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock csD (csV .fBind) false [.int 3 3] [], True :=
  zeugnisStmt2_sound csD _ false _ _ csCertBind (by decide)

/-- Printer output for `let y : K = x; y = y + 0; return y;`, `K = 0 .. 10`. -/
def csCertVar : CertEnd2 csD (csV .fVar) :=
  (.liftE (.bind (.var 0) 0 10
    (.cons (.assignVar 0 0 10 (.add (.var 0) (.lit 0))) []
      (.retWert (.var 0) 0 10))))

/-- The print is valid, by `decide`. -/
example : certEnd2Ok csD (csV .fVar) false [.int 0 10, .int 0 10] []
    csCertVar = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock csD (csV .fVar) false [.int 0 10, .int 0 10] [],
    True :=
  zeugnisStmt2_sound csD _ false _ _ csCertVar (by decide)

/-- Printer output for `let y : K = x; if y < 3 { y = y + 0; } return y;`. -/
def csCertWenn : CertEnd2 csD (csV .fWenn) :=
  (.liftE (.bind (.var 0) 0 10
    (.cons (.ite (.lt (.var 0) (.lit 3))
      (.cons (.assignVar 0 0 10 (.add (.var 0) (.lit 0))) [] .nil) .nil) []
      (.retWert (.var 0) 0 10))))

/-- The print is valid, by `decide`. -/
example : certEnd2Ok csD (csV .fWenn) false [.int 0 10, .int 0 10] []
    csCertWenn = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock csD (csV .fWenn) false [.int 0 10, .int 0 10] [],
    True :=
  zeugnisStmt2_sound csD _ false _ _ csCertWenn (by decide)

end Gabbro.Grammatik

/-! ## CUTS: what is not proved (skeleton; filled with the transfer) -/

-- #print axioms Gabbro.Grammatik.csMarker
