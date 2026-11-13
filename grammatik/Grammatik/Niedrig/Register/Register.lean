/-
  File:      Grammatik/Niedrig/Register/Register.lean
  Subject:   DEVICE REGISTERS AS AN ABSTRACT CONTRACT LAYER (L2c),
    DEFINITIONS: `RegClass`, `RegDecl`, `Device`, the total operations
    `regRead` / `regReadElse` / `regWrite` / `regTransition` with named
    refusals, and the independence hypothesis `Unabhaengig`. Theorems are in
    `RegisterSaetze.lean`, the witness in `RegisterZeuge.lean`.

  THE LAYER (outside the statement: `Spec.lean`, machine G and `Akzeptiert`
  are not touched; nothing imports these modules except the witness and the
  later L2 packages; no `unsafe`, no assembly text).
  * `Device` holds no device behaviour: `lies` and `schreib` are parameters.
    Read side effects of real hardware are OUTSIDE this layer; a later
    package names them as its hardware assumption. Saying what a device
    does is NOT CLAIMED here.
  * Reading is a query: `regRead` returns the stored state unchanged.
    A read whose value breaks the promise takes the ELSE branch, never an
    error and never a default.
  * `transition` performs exactly one read and one write: it reads the
    mirror (or the register itself when it has no mirror and is readable),
    clears `maske`, sets `bits`, and writes back.

  G VOCABULARY (read, never imported; this package adds a layer beside G):
  * `Orakel.regLies : D.Reg -> World D -> Int`
    (grammatik/Grammatik/Kern/Semantik/Semantik/T1/Teil2.lean:29) and
    `Orakel.regSchreib : D.Reg -> Int -> Unit` (:31). A later lemma
    `orakelAntwortGleich` would state that `Device.lies` answers what
    `Orakel.regLies` answers on the device carriers, and that a successful
    `regWrite` calls `Orakel.regSchreib` with the truncated value while the
    world stays put (as `execStmt` for `Stmt.regWrite` shows the world
    unchanged).
  * `Regklasse` (`r | w | rw | w1c | rc`)
    (grammatik/Grammatik/Kern/Syntax/Syntax/Teil1.lean:152-154) with
    `Regklasse.lesbar` (:156-158) and `Regklasse.schreibbar` (:160-162).
    A later lemma `klasseGleich` would state that `darfLesen` /
    `darfSchreiben` agree with `Regklasse.lesbar` / `Regklasse.schreibbar`
    under the canonical class mapping.
  * `Deklaration.rklasse` (:258), `Deklaration.spiegel` (:261),
    `Deklaration.rzusage` (:265), `Deklaration.rtraeger` (:271). Later
    lemmas `declEntspricht` (this `RegDecl` mirrors `rklasse`, `spiegel`
    and `rzusage` on the mapped registers) and `traegerBleibt` (register
    answers depend only on `rtraeger`, hence `Unabhaengig` implies the
    `RegLokal` shape below).
  * `Stmt.regWrite` (grammatik/Grammatik/Kern/Syntax/Syntax/Teil2.lean:67-68),
    `Stmt.transition` (:73-75), `Block.regRead` (:187-188),
    `Block.regReadElse` (:191-193), `Endblock.regRead` (:298-299) and
    `Endblock.regReadElse` (:302-304). Later lemmas `liesSchritt`,
    `schreibSchritt`, `sonstSchritt` and `wechselSchritt` would state that
    each operation here simulates its G counterpart in `execStmt` /
    `execBlock` (for `transition`, the G shape at
    `grammatik/Grammatik/Kern/Semantik/Semantik/T2/Teil2.lean:131-135`:
    one `regLies` of the mirror, one `regSchreib` of the masked value).
  * `RegLokal` (grammatik/Grammatik/Zielsatz/ZielOrt/Geraet/ZielOrtGeraetSem/Teil1.lean:22-26):
    a register answers from its device carriers. A later lemma
    `unabhaengigRegLokal` would derive the `RegLokal` shape from
    `Unabhaengig` once the device carriers are mapped to `rtraeger`.
-/
module

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Register

/-- A register index. Registers are named numbers; the declaration table
    says which ones exist. -/
abbrev Reg := Nat

/-- The register classes, exactly the five classes G names (`r | w | rw |
    w1c | rc`). -/
inductive RegClass
  | r : RegClass
  | w : RegClass
  | rw : RegClass
  | w1c : RegClass
  | rc : RegClass
  deriving DecidableEq

/-- Read is allowed under `r`, `rw`, `w1c` and `rc`, as in G. -/
def darfLesen : RegClass → Bool
  | RegClass.r => true
  | RegClass.w => false
  | RegClass.rw => true
  | RegClass.w1c => true
  | RegClass.rc => true

/-- Write is allowed under `w`, `rw` and `w1c`, as in G. -/
def darfSchreiben : RegClass → Bool
  | RegClass.r => false
  | RegClass.w => true
  | RegClass.rw => true
  | RegClass.w1c => true
  | RegClass.rc => false

/-- A register declaration: its class, its width in bits, the fallible-read
    promise on the truncated value, and the optional mirror register. -/
structure RegDecl where
  klasse : RegClass
  breite : Nat
  zusage : Nat → Bool
  spiegel : Option Reg

/-- An abstract device. `lies` and `schreib` are parameters: the device's
    own behaviour is NOT modelled here (a later package names it as its
    hardware assumption). -/
structure Device (S : Type) where
  decl : Reg → Option RegDecl
  lies : S → Reg → Nat
  schreib : S → Reg → Nat → S

/-- The observable events of one operation: a read, or a write with value. -/
inductive Event
  | lese : Reg → Event
  | schreibe : Reg → Nat → Event
  deriving DecidableEq

/-- The outcome of a fallible read: the value held (`ok`), or the value
    with the promise broken (`sonst`). The ELSE branch is never an error
    and never a default. -/
inductive FallErgebnis
  | ok : Nat → FallErgebnis
  | sonst : Nat → FallErgebnis
  deriving DecidableEq

/-- Refusal: the register is not declared. -/
def unbekannt : String :=
  "register-unbekannt"

/-- Refusal: the class has no read right. -/
def ohneLeserecht : String :=
  "register-ohne-leserecht"

/-- Refusal: the class has no write right. -/
def ohneSchreibrecht : String :=
  "register-ohne-schreibrecht"

/-- Refusal: the value does not fit the width. -/
def wertZuGross : String :=
  "register-wert-zu-gross"

/-- Refusal: the transition has no mirror and the register itself is not
    readable. -/
def ohneSpiegel : String :=
  "register-ohne-spiegel"

/-- Refusal: the declared mirror is not declared. -/
def spiegelUnbekannt : String :=
  "register-spiegel-unbekannt"

/-- Refusal: the declared mirror is not readable. -/
def spiegelNichtLesbar : String :=
  "register-spiegel-nicht-lesbar"

/-- The modulus of a width: values live below `2 ^ breite`. -/
def maxWert (breite : Nat) : Nat :=
  2 ^ breite

/-- Truncation to a width. -/
def kuerze (breite v : Nat) : Nat :=
  v % (2 ^ breite)

/-- The cleared bits of a width: the complement of the truncated mask
    inside `2 ^ breite - 1`. -/
def maskeKompl (breite maske : Nat) : Nat :=
  Nat.xor (kuerze breite maske) ((2 ^ breite) - 1)

/-- The transition value: the old value with `maske` cleared, `bits` set,
    truncated to the width. -/
def neuerWert (breite alt maske bits : Nat) : Nat :=
  (Nat.lor (Nat.land alt (maskeKompl breite maske)) (kuerze breite bits)) % (2 ^ breite)

/-- The independence hypothesis: writes to one register do not disturb
    reads of another, a write installs its value, and two writes commute
    pointwise. This is taken as an explicit hypothesis wherever commutation
    is claimed, never assumed silently. -/
def Unabhaengig {S : Type} (d : Device S) : Prop :=
  (∀ s r1 r2 v, r1 ≠ r2 → d.lies (d.schreib s r1 v) r2 = d.lies s r2) ∧
  (∀ s r v, d.lies (d.schreib s r v) r = v) ∧
  (∀ s r1 r2 v1 v2 r,
    d.lies (d.schreib (d.schreib s r1 v1) r2 v2) r =
    d.lies (d.schreib (d.schreib s r2 v2) r1 v1) r)

/-- Total read with named refusals: the register must be declared and its
    class must allow reading; the answer is the device answer truncated to
    the width. The state is unchanged. -/
def regRead {S : Type} (d : Device S) (s : S) (r : Reg) :
    S × Except String Nat × List Event :=
  match d.decl r with
  | none => (s, Except.error unbekannt, [])
  | some decl =>
    if darfLesen decl.klasse = true then
      (s, Except.ok (kuerze decl.breite (d.lies s r)), [Event.lese r])
    else
      (s, Except.error ohneLeserecht, [])

/-- Total fallible read: as `regRead`, then the promise. A value whose
    promise fails takes the ELSE branch (`FallErgebnis.sonst`); that is
    success, never an error and never a default. -/
def regReadElse {S : Type} (d : Device S) (s : S) (r : Reg) :
    S × Except String FallErgebnis × List Event :=
  match d.decl r with
  | none => (s, Except.error unbekannt, [])
  | some decl =>
    if darfLesen decl.klasse = true then
      let v := kuerze decl.breite (d.lies s r)
      if decl.zusage v = true then
        (s, Except.ok (FallErgebnis.ok v), [Event.lese r])
      else
        (s, Except.ok (FallErgebnis.sonst v), [Event.lese r])
    else
      (s, Except.error ohneLeserecht, [])

/-- Total write with named refusals: the register must be declared, its
    class must allow writing, and the value must fit the width. -/
def regWrite {S : Type} (d : Device S) (s : S) (r v : Nat) :
    S × Except String Unit × List Event :=
  match d.decl r with
  | none => (s, Except.error unbekannt, [])
  | some decl =>
    if darfSchreiben decl.klasse = true then
      if v < 2 ^ decl.breite then
        (d.schreib s r v, Except.ok (), [Event.schreibe r v])
      else
        (s, Except.error wertZuGross, [])
    else
      (s, Except.error ohneSchreibrecht, [])

/-- Total transition: read the mirror (or the register itself when it has
    no mirror and is readable), clear `maske`, set `bits`, write back.
    Exactly one read and one write. -/
def regTransition {S : Type} (d : Device S) (s : S) (r maske bits : Nat) :
    S × Except String Unit × List Event :=
  match d.decl r with
  | none => (s, Except.error unbekannt, [])
  | some decl =>
    if darfSchreiben decl.klasse = true then
      match decl.spiegel with
      | some m =>
        match d.decl m with
        | none => (s, Except.error spiegelUnbekannt, [])
        | some mdecl =>
          if darfLesen mdecl.klasse = true then
            let alt := kuerze decl.breite (d.lies s m)
            let neu := neuerWert decl.breite alt maske bits
            (d.schreib s r neu, Except.ok (), [Event.lese m, Event.schreibe r neu])
          else
            (s, Except.error spiegelNichtLesbar, [])
      | none =>
        if darfLesen decl.klasse = true then
          let alt := kuerze decl.breite (d.lies s r)
          let neu := neuerWert decl.breite alt maske bits
          (d.schreib s r neu, Except.ok (), [Event.lese r, Event.schreibe r neu])
        else
          (s, Except.error ohneSpiegel, [])
    else
      (s, Except.error ohneSchreibrecht, [])

end Gabbro.Grammatik.Niedrig.Register
