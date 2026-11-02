module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineD
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF

@[expose] public section



namespace Gabbro.Grammatik

/-- Signature of `einzahlen`: one `.int 0 10` parameter, no result, holds
    the lock, may write the table. -/
def refSigEin : Signatur Unit Empty Unit Empty where
  params := [.int 0 10]
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Signature of `lies`: no parameters, one `.int 0 100` result, holds the
    lock, writes nothing. -/
def refSigLies : Signatur Unit Empty Unit Empty where
  params := []
  erg := some (.int 0 100)
  gruende := 0
  haelt := [()]
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The reference declaration: one table `konto` of 2 slots with one
    `.int 0 100` field, guarded by the single lock `m` (`braucht`);
    `einzahlen` is `true`, `lies` is `false`; both signatures line up by id.
    `geteilit` is true so the shared table is guarded, not orphaned. -/
def refD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun | 0 => refSigEin | _ => refSigLies
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The two function ids: `einzahlen` (`true`) and `lies` (`false`). -/
def refEin : refD.Fn := show refD.Fn from true

def refLies : refD.Fn := show refD.Fn from false

/-- Parameters of `einzahlen`, by computation. -/
theorem refEin_params : refD.params refEin = [.int 0 10] := by rfl

/-- `einzahlen` returns nothing. -/
theorem refEin_erg : refD.erg refEin = none := by rfl

/-- Parameters of `lies`, by computation. -/
theorem refLies_params : refD.params refLies = [] := by rfl

/-- `lies` returns `.int 0 100`. -/
theorem refLies_erg : refD.erg refLies = some (.int 0 100) := by rfl

/-- The argument of the witness call: 7 in `.int 0 10`. -/
def refRho7 : Env refD (refD.params refEin) :=
  refEin_params.symm ▸ (.cons ⟨7, by decide, by decide⟩ .nil :
    Env refD [.int 0 10])

/-- `einzahlen` writes the table. -/
theorem refEin_schreibt (t : refD.Tab) :
    (vertragVon refD refEin).schreibt t = true := by
  cases t <;> rfl

/-- `lies` writes nothing. -/
theorem refLies_schreibt (t : refD.Tab) :
    (refD.signatur refLies).schreibt t = false := by
  cases t <;> rfl

/-- `lies` holds the lock. -/
theorem refLies_haelt : (refD.signatur refLies).haelt = [()] := by rfl

/-- `lies` has no error channel. -/
theorem refLies_gruende : refD.gruende refLies = 0 := by rfl

/-- End holdings of `einzahlen`: the lock. -/
theorem refEin_ende :
    (vertragVon refD refEin).ende = [Res.held (D := refD) ()] := by rfl

/-- End holdings of `lies`: the lock. -/
theorem refLies_ende :
    (vertragVon refD refLies).ende = [Res.held (D := refD) ()] := by rfl

/-- The table access is allowed holding the lock. -/
theorem refDarf : darf refD () [Res.held (D := refD) ()] := by
  intro w h
  simp only [refD] at h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  have hh : w ∈ refD.braucht () := h
  rw [e] at hh ⊢
  exact List.mem_singleton.mpr rfl

/-- Same access right at the `einzahlen` end holdings. -/
theorem refDarfEin : darf refD () (vertragVon refD refEin).ende := by
  rw [refEin_ende]
  exact refDarf

/-- Same access right at the `lies` end holdings. -/
theorem refDarfLies : darf refD () (vertragVon refD refLies).ende := by
  rw [refLies_ende]
  exact refDarf

/-! ## 2. Expressions and contracts -/

/-- Index `0` into the two-slot table, in the `einzahlen` context. -/
def refIdxEin : Expr refD [.int 0 10] [Res.held (D := refD) ()]
    (.index (refD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

/-- Index `0` in the `lies` body context. -/
def refIdxLies : Expr refD [] [Res.held (D := refD) ()]
    (.index (refD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

/-- The cap value `100` in range. -/
def refHundert : Expr refD [.int 0 10] [Res.held (D := refD) ()] (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 100)

/-- `einzahlen` requires `true`. -/
def refReqEin : Expr refD (refD.params refEin)
    (Signatur.anfang refD (refD.signatur refEin)) .bool :=
  .tru

/-- `einzahlen` ensures the slot did not decrease (`old ≤ new`). -/
def refEnsEin : Expr refD (ErgCtx (refD.params refEin) (refD.erg refEin))
    (vertragVon refD refEin).ende .bool :=
  .le (.oldS () () refIdxEin refDarfEin)
    (.slot () () refIdxEin refDarfEin)

/-- Index `0` in the `lies` ensures context (result before params). -/
def refIdxEnsLies :
    Expr refD (ErgCtx (refD.params refLies) (refD.erg refLies))
      (vertragVon refD refLies).ende (.index (refD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

/-- `lies` requires `true`. -/
def refReqLies : Expr refD (refD.params refLies)
    (Signatur.anfang refD (refD.signatur refLies)) .bool :=
  .tru

/-- `lies` ensures `result = konto[0]`. -/
def refEnsLies : Expr refD (ErgCtx (refD.params refLies) (refD.erg refLies))
    (vertragVon refD refLies).ende .bool :=
  .eq (.var .here)
    (.slot () () refIdxEnsLies refDarfLies)

/-! ## 3. Bodies and the program -/

end Gabbro.Grammatik
