/-
  File:     Grammatik/ZeugnisStmt104.lean
  Subject:  GENERATED statement certificates (lane 153, T1 transfer).

  The `CertEnd2` terms below are verbatim output of
  `gabbro certificate` (module `certstmt.rs`, one term per function body;
  see `crates/gabbro-check/tests/certstmt.rs` for the pinned probes).
  Each `example` runs the Lean checker (`certEnd2Ok ... = true` by
  `decide`); each soundness corollary applies `zeugnisStmt2_sound`.
  `csCertDoppelt` is verbatim output for a real corpus body
  (`beispiele/93-const-scalars.gab`, `doppelt`); the rest are the pinned
  probe bodies. The `beispiele/104-referenz.gab` bodies themselves are
  REFUSED by the printer -- section 3 records the exact output.
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

/-- The probe functions: one per pinned probe body, plus `doppelt`
    (`beispiele/93-const-scalars.gab`, a real corpus body). -/
inductive CSFn where
  | fRet
  | fBind
  | fVar
  | fWenn
  | fSlot
  | fDoppelt
  deriving DecidableEq

/-- Elimination out of `Empty` for the unused carrier maps: a plain
    constant, so no tuple ever holds an inline `nomatch`. -/
def csElimBool : Empty → Bool := fun e => nomatch e

/-- Signatures: the parameter and result ranges the probes claim. -/
def csSig : CSFn → Signatur CSTab Empty Empty Empty
  | .fRet => ⟨[.int 0 10], some (.int 0 10), 0, [], fun _ => false,
    csElimBool, [], [], none⟩
  | .fBind => ⟨[], some (.int 3 3), 0, [], fun _ => false,
    csElimBool, [], [], none⟩
  | .fVar => ⟨[.int 0 10], some (.int 0 10), 0, [], fun _ => false,
    csElimBool, [], [], none⟩
  | .fWenn => ⟨[.int 0 10], some (.int 0 10), 0, [], fun _ => false,
    csElimBool, [], [], none⟩
  | .fSlot => ⟨[], none, 0, [], fun _ => true,
    csElimBool, [], [], none⟩
  | .fDoppelt => ⟨[.int 0 1000], some (.int 0 2000), 0, [], fun _ => false,
    csElimBool, [], [], none⟩

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
  sig := fun
    | .fRet => 0
    | .fBind => 1
    | .fVar => 2
    | .fWenn => 3
    | .fSlot => 4
    | .fDoppelt => 5
  sigNr := fun
    | 0 => csSig .fRet
    | 1 => csSig .fBind
    | 2 => csSig .fVar
    | 3 => csSig .fWenn
    | 4 => csSig .fSlot
    | _ => csSig .fDoppelt
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
  | .fRet => ⟨fun _ => false, csElimBool, some (.int 0 10), 0, [], [], none⟩
  | .fBind => ⟨fun _ => false, csElimBool, some (.int 3 3), 0, [], [], none⟩
  | .fVar => ⟨fun _ => false, csElimBool, some (.int 0 10), 0, [], [], none⟩
  | .fWenn => ⟨fun _ => false, csElimBool, some (.int 0 10), 0, [], [], none⟩
  | .fSlot => ⟨fun _ => true, csElimBool, none, 0, [], [], none⟩
  | .fDoppelt => ⟨fun _ => false, csElimBool, some (.int 0 2000), 0, [], [], none⟩

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

/-- Printer output for `T.slots[0].x = 42; return;` (`count 2`, `0 .. 100`). -/
def csCertSlot : CertEnd2 csD (csV .fSlot) :=
  (.liftE (.cons (.assignSlot .T .x (.wide 0 1 (.lit 0))
    (.wide 0 100 (.lit 42))) [] .ret))

/-- The print is valid, by `decide`. -/
example : certEnd2Ok csD (csV .fSlot) false [] [] csCertSlot = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock csD (csV .fSlot) false [] [], True :=
  zeugnisStmt2_sound csD _ false _ _ csCertSlot (by decide)

/-- Printer output for `return 5;` at result `0 .. 10`: the literal
    narrows under `wide`, exactly where the checker elaborates `weiter`. -/
def csCertWide5 : CertEnd2 csD (csV .fRet) :=
  (.liftE (.retWert (.wide 0 10 (.lit 5)) 0 10))

/-- The print is valid, by `decide`. -/
example : certEnd2Ok csD (csV .fRet) false [] [] csCertWide5 = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock csD (csV .fRet) false [] [], True :=
  zeugnisStmt2_sound csD _ false _ _ csCertWide5 (by decide)

/-- VERBATIM printer output for `doppelt` (`beispiele/93-const-scalars.gab`):
    `const fn doppelt(n : u32 in 0 .. 1000) -> u32 in 0 .. 2000`
    with body `return n + n;`. A real corpus body, checked by `decide`. -/
def csCertDoppelt : CertEnd2 csD (csV .fDoppelt) :=
  (.liftE (.retWert (.add (.var 0) (.var 0)) 0 2000))

/-- The print is valid, by `decide`. -/
example : certEnd2Ok csD (csV .fDoppelt) false [.int 0 1000] []
    csCertDoppelt = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock csD (csV .fDoppelt) false [.int 0 1000] [], True :=
  zeugnisStmt2_sound csD _ false _ _ csCertDoppelt (by decide)

/-! ## 3. The 104 record: what the printer says about the reference program

    Verbatim output of `gabbro certificate beispiele/104-referenz.gab`
    (section S). Both bodies are refused, each at its first outside form:
    `einzahlen` writes through the pointer `k` with the index variable `i`
    (`CertStmt2.assignDurch` needs a recomputable index range; an
    index-typed variable has none) and then calls `lies(k, i)` with
    arguments (calls with arguments have no `CertStmt` shape -- the R-2
    fragment is nullary only); `lies` returns `k.slots[i].stand`, a
    pointer read (`durch` has no `CertExpr` shape). No truncation: every
    refusal names the function and the form.

    ```text
    S  STATEMENT CERTIFICATES (transfer printer)
       function einzahlen: REFUSED CS002: pointer write k.slots[…].stand
         has no CertStmt shape
       function lies: REFUSED CS002: pointer access k.slots[…].stand
         has no CertExpr shape
    ```

    No corpus body with a loop or a match prints either: the survey over
    `beispiele/*.gab` (lane report) finds `CertEnd2` terms only for
    straight-line integer bodies (`doppelt` above; `(.liftE .ret)` for the
    `abnahme`/`freigabe` acceptance bodies of `06`, `43`, `52`; the
    eight-variable sum of `70-kernel-namen.gab`). Every loop (`traverse`,
    `retry`, `forever`) and every `match` is refused by name -- the
    fragment boundary is measured, not hoped. -/

end Gabbro.Grammatik

/-! ## CUTS: what is not proved

    - The file holds NO theorems, only generated data (`csCert*`) plus
      `decide` examples and soundness corollaries. Rule-13 witnesses are
      owed by none of them; the joint witnesses of `zeugnisStmt_sound`
      and `zeugnisStmt2_sound` (`ZeugnisStmt.lean`, `ZeugnisStmt2.lean`)
      already instantiate the soundness conclusions on the reference
      fixture with its non-degenerate run.
    - 104 does not check: its bodies fall outside `CertEnd`/`CertEnd2`
      (pointer write/read, call with arguments, index variable), so there
      is no `certEnd2Ok ... = true` for them -- the refusal above is the
      honest artifact. A lane that wires index-typed variables or
      with-arguments calls into new certificate rows extends this file.
    - Resource flow erases to `[]`: the demo declaration is lock-free by
      construction (`braucht` empty, `haelt` empty), so `darf` holds
      vacuously. Guarded tables fail `decide` loudly; they are not
      silently certified.
    - `RufPasst` travels as proof (R-3): bodies with calls print nothing
      (`CS004`), so no pasted term owes a proof hole.
    - Term identity (`print (elab x) = x`) is proved NOWHERE -- the
      `ZeugnisStmt2.lean` CUTS booking. The terms below are linked to
      their bodies by construction of the printer, pinned in
      `crates/gabbro-check/tests/certstmt.rs`.
-/

#print axioms Gabbro.Grammatik.csCertRet
#print axioms Gabbro.Grammatik.csCertBind
#print axioms Gabbro.Grammatik.csCertVar
#print axioms Gabbro.Grammatik.csCertWenn
#print axioms Gabbro.Grammatik.csCertSlot
#print axioms Gabbro.Grammatik.csCertWide5
#print axioms Gabbro.Grammatik.csCertDoppelt

/-! ## CUTS: what is not proved (skeleton; filled with the transfer) -/

-- #print axioms Gabbro.Grammatik.csMarker
