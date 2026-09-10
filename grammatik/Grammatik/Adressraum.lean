/-
  File:     Grammatik/Adressraum.lean
  Subject:  **The user/kernel boundary as a shape** -- the design piece that
             `messung/TOCTOU-ADRESSRAUM.md` finds missing (verdict GAP).

             SYNTAX §3 has six spaces and no user one; `Ty.ptr` drops the space;
             `Expr.durch` is one read with one guard set; `World` (both the
             grammar's and `Body.lean`'s) is a single flat mapping; M3 holds
             rights and placement and never check-then-copy. So a `copy_from_user`
             shape -- validate a user range, then copy from it, while the user
             side may rewrite the bytes between the two reads -- is neither
             writable, statable, nor refused anywhere.

              This file draws the shape and proves what the shape carries:
              a checked copy run as ONE copy through the checked handle shows
              no check-then-copy TOCTOU -- under the single-copy-atomicity
              premise `EinSnapshot`, named explicitly (the Koernung shape:
              `Koernung.lean` runs one event indivisibly; here check and copy
              are one indivisible copy). An unvalidated crossing runs in the
              same sequence shape with the premise dropped -- the named gap.
              What it gives:

               `Seite`         -- the two sides of one boundary.
               `UserRegion`    -- a user-memory region: base plus length.
               `Richtung`      -- which way the bytes move (`vonUser` is the
                                  `copy_from_user` shape).
               `Kopie`         -- the copy primitive: user address, kernel
                                  address, byte count, direction, in ONE datum.
               `innerhalb`     -- the check, as a Prop: the accessed range lies
                                  inside the region.
               `GepruefteKopie`-- validation-then-copy, inseparable: the check
                                  and the copy name the SAME region, address,
                                  and length. A check over one triple paired
                                  with a copy over another is not of this shape.
               `Lesung` / `PruefDannKopie` -- the TOCTOU sequence: the checked
                                  reading and the copied reading, as two data.
               `ohneToctou`    -- the soundness shape, as a Prop: the checked
                                  value IS the copied value -- one snapshot,
                                  read once. A sequence whose two readings can
                                  differ has this property nowhere.
                `KernAnweisung` / `kreuzt` -- boundary-crossing statement shapes:
                                   a kernel step is pure or carries exactly one
                                   copy; crossing is an existential over the term.
                `UserMem` / `laufSequenz` -- the run: check-time and copy-time
                                   snapshots feeding the checked handle.
                `EinSnapshot`   -- the premise, named explicitly: both
                                   snapshots agree at the checked address
                                   (single-copy atomicity, Koernung shape).
               safety / gap    -- `gepruefteKopie_ohneToctou` under the
                                    premise; `toctouZeuge_toctou` and
                                    `laufSequenz_toctou_ohneSnapshot` name
                                    the gap without it.
               wiring (§7)     -- `weltByte`/`weltBytes` read the checked
                                    address out of `World` (the same
                                    `World.bytesAb` the `leseBytes` read
                                    path binds); `schreibSlot_liestSelbe`
                                    lands the write where the read looks;
                                    `modellSequenz_ohneToctou` proves the
                                    safety INSIDE the model, and
                                    `modellSequenz_toctou_ohneSnapshotWelt`
                   names the gap there. The region check
                   itself (`validiert`) still has no `exec`
                   counterpart -- that is cut C6, not §7.
                partition (§8, design only, no discharge) -- `KernRegion` /
                    `SeitenRegion` name both sides of `Seite`; `execFordertBereich`
                    is the range-check-inside-`exec` shape (out-of-region refuses
                    as `ausserhalbVerweigert`); `adresseInRegion` /
                    `schluesselInRegion` / `benutzerTeil` hang the user side of
                    the world mapping on `UserRegion`, `bereicheGetrennt` names
                    the split. No transition discharges any of it -- cut C7.

              Mirror (this file takes one same-project import,
              `Grammatik.Semantik`; the `Grammatik.lean` index is untouched,
              so the file wires itself -- names were chosen for this):

             | here                | there                                        |
             |---------------------|----------------------------------------------|
             | `UserRegion`        | the missing seventh `space` (SYNTAX §3)      |
             | `Kopie`             | the missing copy primitive (no `Expr` ctor)  |
             | `GepruefteKopie`    | the missing rule (no M3 rule fires on it)    |
              | `ohneToctou`        | the missing statement (one flat `World`)     |
               | `Nat` addresses     | wiring: byte offsets into a byte carrier     |
               |                     | (§7: `weltByte` over `World.bytesAb`)        |
               | `EinSnapshot`       | the atomic event (`Koernung.lean`: `EreignisAtomar`)|

              CUTS (booked, not hidden):
              C1. Addresses and values are `Nat`: placeholders for byte offsets
                  and byte strings. §7 wires ONE byte carrier: a `Nat` address
                  is the `Int` index into a table field typed `.int 0 255`
                  (`Typen.lean`: `Byte`), read through `World.bytesAb` --
                  the same function the `leseBytes` read path binds. Every
                  other carrier (all remaining `Tab` slots / `Glob`s) is
                  still unwired.
              C2. No clock: `PruefDannKopie` orders the two readings by position
                  (check first, copy second), not by time. A writer between them
                  is the environment, named as an assumption like `Hardware.*`.
                  §7 keeps this: the two model reads take two worlds, and
                  nothing in `exec` orders them.
              C3. One copy per statement: a loop copying a range chunk by chunk
                  is `n` terms of this shape, each checked -- that per-chunk
                  check is exactly what the shape demands.
               C4. `vonUser` only is the hazard direction. `nachUser` shares the
                   datatype so the check is not skipped on the way out; the
                   TOCTOU reading hazard runs check-then-copy from user.
                   Wiring (§7): `vonUser` is the read path (`bytesAb`, as in
                   `eval`'s `leseBytes` branch); `nachUser` is the write path
                   (`schreibSlot`/`schreibBytes`, as in `execStmt`).
               C5. No writer modelled: `m₁`/`m₂` are check-time/copy-time
                   snapshots; `EinSnapshot` says they agree at the checked
                   address. A writer between them is environment (like
                   `Hardware.*`), never a transition here. One `Nat` per
                   address again (cut C1, at the run): no byte-list wiring.
                   §7 carries this over: `σ₁`/`σ₂` are two worlds, and
                   `EinSnapshotWelt` says they agree at the checked byte.
               C6. The region check is still beside `exec`: `World` is one
                   flat mapping with no `Seite`, and no `Stmt`/`Block`
                   transition discharges `validiert` -- an out-of-region
                   `Kopie` still reads and writes in the model, because the
                   model memory is total. The exact missing link: a range
                   check inside `exec` (a statement shape whose transition
                   requires `validiert`), and a user partition in `World`
                   it could check against.
               C7. The discharge inside `exec` stays future work (§8 books the
                   shape, not the transition): no `Stmt`/`Block` transition
                   requires `execFordertBereich`, and no `World` carries a
                   `Seite` partition yet -- `benutzerTeil`/`bereicheGetrennt`
                   name the user side it could check against.

               Core only: no `mathlib`; one same-project import
               (`Grammatik.Semantik`), no new dependency. Zero `sorry`,
               no `admit`, no new `axiom`. `#print axioms` below shows §§1-6
               rest on nothing; §7 rests on Lean core only (`propext`,
               `Classical.choice`, `Quot.sound`) -- the same baseline every
               `Semantik`-based file of the project shows, carried by the
               `World` types, not by any proof step here.
-/

import Grammatik.Semantik

namespace Gabbro.Grammatik.Adressraum

/-! ## 1. The two sides, and the region the far side lives in -/

/-- The two sides of one boundary: kernel memory and user memory. -/
inductive Seite where
  | kern
  | user
  deriving DecidableEq, Repr

/-- A region of user memory: base plus length, both in bytes (cut C1). -/
structure UserRegion where
  basis : Nat
  laenge : Nat
  deriving DecidableEq, Repr

/-- Which way the bytes move across the boundary. -/
inductive Richtung where
  /-- `copy_from_user` shape: kernel reads user bytes. -/
  | vonUser
  /-- `copy_to_user` shape: kernel writes user bytes. -/
  | nachUser
  deriving DecidableEq, Repr

/-! ## 2. The copy primitive: validation-then-copy, inseparable -/

/-- One boundary-crossing copy: the user address, the kernel address, the byte
    count, and the direction -- in ONE datum, so no half of it can travel
    without the rest. -/
structure Kopie where
  userAddr : Nat
  kernAddr : Nat
  laenge : Nat
  richtung : Richtung
  deriving DecidableEq, Repr

/-- The check: the whole `[addr, addr + laenge)` lies inside the region. -/
def innerhalb (r : UserRegion) (addr laenge : Nat) : Prop :=
  r.basis ≤ addr ∧ addr + laenge ≤ r.basis + r.laenge

/-- The validation: the copy's user range lies inside the region. -/
def validiert (r : UserRegion) (k : Kopie) : Prop :=
  innerhalb r k.userAddr k.laenge

/-- Validation-then-copy: the check and the copy name the SAME region,
    address, and length. A check over one triple paired with a copy over
    another is not of this shape -- that pairing is the TOCTOU below. -/
structure GepruefteKopie where
  region : UserRegion
  kopie : Kopie
  gecheckt : validiert region kopie

/-- The checked triple, read back off the shape: what was validated is what
    is copied, by construction. -/
def GepruefteKopie.bereich (g : GepruefteKopie) : Nat × Nat :=
  (g.kopie.userAddr, g.kopie.laenge)

/-! ## 3. The TOCTOU sequence: two readings, one check between them -/

/-- One reading of user memory: the address and the value seen (cut C1: the
    value is one `Nat` standing for the byte string). -/
structure Lesung where
  addr : Nat
  wert : Nat
  deriving DecidableEq, Repr

/-- The check-then-copy sequence: the checked reading first, the copied
    reading second (cut C2: order by position, not by time). -/
structure PruefDannKopie where
  pruefung : Lesung
  kopie : Lesung
  deriving DecidableEq, Repr

/-- No TOCTOU: the checked value IS the copied value -- one snapshot, read
    once. A sequence whose two readings can differ has this property nowhere;
    holding it means the copy did not re-read mutable bytes. -/
def ohneToctou (s : PruefDannKopie) : Prop :=
  s.pruefung = s.kopie

/-- The snapshot reading: the single address both readings agree on. Only
    meaningful where `ohneToctou` holds; stated separately so the shape, not
    a proof, carries the address. -/
def snapshotAddr (s : PruefDannKopie) : Nat :=
  s.pruefung.addr

/-! ## 4. Boundary-crossing statement shapes -/

/-- A kernel statement: either pure (no crossing) or exactly one copy
    (cut C3: a chunked loop is `n` terms of this shape). -/
inductive KernAnweisung where
  | rein : KernAnweisung
  | kopie : Kopie → KernAnweisung
  deriving DecidableEq, Repr

/-- A statement crosses the boundary exactly when it carries a copy. -/
def kreuzt : KernAnweisung → Prop
  | .rein => False
  | .kopie _ => True

/-- The carried copy, where there is one: which bytes cross, and which way. -/
def getrageneKopie : KernAnweisung → Option Kopie
  | .rein => none
  | .kopie k => some k

/-- A crossing statement with its validation: the statement, the region it
    was checked against, and the check -- the three travel together, as in
    `GepruefteKopie` above. -/
structure GepruefterUebergang where
  anweisung : KernAnweisung
  region : UserRegion
  kopie : Kopie
  traegt : getrageneKopie anweisung = some kopie
  gecheckt : validiert region kopie

/-! ## 5. Validated-copy safety: one snapshot, read once -/

/-- User memory: address to value. One `Nat` per address stands for the
    byte string there (cut C1 again, at the run); a memory is total, so
    the hazard modelled here is staleness, never absence. -/
abbrev UserMem := Nat → Nat

/-- The checked reading: the copy's user address, seen at check time. -/
def checkLesung (g : GepruefteKopie) (m₁ : UserMem) : Lesung :=
  { addr := g.kopie.userAddr, wert := m₁ g.kopie.userAddr }

/-- The copied reading: the SAME address, seen at copy time -- the checked
    handle. A copy from another address is not of this shape; that pairing
    is the gap in §6. -/
def kopieLesung (g : GepruefteKopie) (m₂ : UserMem) : Lesung :=
  { addr := g.kopie.userAddr, wert := m₂ g.kopie.userAddr }

/-- Running a validated copy: check first, copy second (cut C2: order by
    position, `m₁` then `m₂`, never by time). -/
def laufSequenz (g : GepruefteKopie) (m₁ m₂ : UserMem) : PruefDannKopie :=
  { pruefung := checkLesung g m₁, kopie := kopieLesung g m₂ }

/-- **Single-copy atomicity** -- the explicitly named Koernung-shape
    premise (cf. `Koernung.lean`: `EreignisAtomar`, one event covers at
    most one cell and runs indivisibly): check and copy are ONE indivisible
    copy, so no writer runs between the two positions -- both snapshots
    agree at the checked address. The writer itself stays environment,
    named here and modelled nowhere (cut C5). -/
def EinSnapshot (g : GepruefteKopie) (m₁ m₂ : UserMem) : Prop :=
  m₁ g.kopie.userAddr = m₂ g.kopie.userAddr

/-- The premise is satisfiable, never vacuous: one snapshot agrees with
    itself (cf. `Koernung.lean`: `ereignisAtomar_gilt`). -/
theorem einSnapshot_refl (g : GepruefteKopie) (m : UserMem) :
    EinSnapshot g m m := rfl

/-- The run reads the validated address on both positions: what is checked
    is what is copied -- the handle, before any atomicity. -/
theorem laufSequenz_liestGeprueft (g : GepruefteKopie) (m₁ m₂ : UserMem) :
    (laufSequenz g m₁ m₂).pruefung.addr = g.kopie.userAddr ∧
    (laufSequenz g m₁ m₂).kopie.addr = g.kopie.userAddr :=
  ⟨rfl, rfl⟩

/-- **Validated-copy safety.** A checked copy run as a single copy through
    the checked handle shows no check-then-copy TOCTOU -- UNDER
    `EinSnapshot`. The handle fixes the address (both readings name the
    checked one); the premise fixes the value (no writer between). Drop
    the premise and the goal is unwritable -- that is §6, not this. -/
theorem gepruefteKopie_ohneToctou (g : GepruefteKopie) (m₁ m₂ : UserMem)
    (h : EinSnapshot g m₁ m₂) : ohneToctou (laufSequenz g m₁ m₂) := by
  have e : checkLesung g m₁ = kopieLesung g m₂ := by
    unfold EinSnapshot at h
    unfold checkLesung kopieLesung
    rw [h]
  exact e

/-! ## 6. The named gap: unvalidated crossing can re-read -/

/-- The witness: checked zero, copied one -- at the SAME address, so the
    handle alone (one address twice) does NOT exclude TOCTOU. Only the
    snapshot premise does. -/
def toctouZeuge : PruefDannKopie :=
  { pruefung := { addr := 0, wert := 0 }, kopie := { addr := 0, wert := 1 } }

/-- The witness exhibits TOCTOU. -/
theorem toctouZeuge_toctou : ¬ ohneToctou toctouZeuge := by
  unfold ohneToctou toctouZeuge at ⊢
  decide

/-- **The gap, named in `ohneToctou` shape.** A run whose snapshots differ
    at the copied address -- the writer between check and copy, i.e. the
    crossing WITHOUT the single-copy premise -- shows TOCTOU. An
    unvalidated crossing (`kreuzt` with no `GepruefteKopie` behind it) runs
    in this shape, so nothing here excludes its TOCTOU. -/
theorem laufSequenz_toctou_ohneSnapshot (g : GepruefteKopie) (m₁ m₂ : UserMem)
    (h : m₁ g.kopie.userAddr ≠ m₂ g.kopie.userAddr) :
    ¬ ohneToctou (laufSequenz g m₁ m₂) := by
  intro hc
  unfold ohneToctou laufSequenz checkLesung kopieLesung at hc
  exact h (congrArg Lesung.wert hc)

/-! ## 7. Wiring into the world: the checked handle reads the model -/

/- A user address is a byte offset into ONE byte carrier: table `t`, field
   `f` typed `.int 0 255`. The read below is `World.bytesAb` -- the same
   function `eval`'s `leseBytes` branch binds as `bs` and `World.schreibBytes`
   walks. All other carriers stay unwired (cut C1); the region check stays
   beside `exec` (cut C6). -/

/-- One user-address byte out of the world: the checked address, read from
    the carrier. `Wert D (.int 0 255)` IS `Byte` (`Typen.lean`: `Byte` is
    `Zahl 0 255`), so no conversion happens -- the cast only moves the
    field's type proof, exactly as `World.bytesAb` does. -/
def weltByte (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (σ : World D) (addr : Nat) : Byte :=
  cast (congrArg (Wert D) hf) (σ.slots t (addr : Int) f)

/-- `len` user bytes from `addr`: the model read behind the checked handle. -/
def weltBytes (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (σ : World D) (addr len : Nat) : List Byte :=
  σ.bytesAb t f hf len (addr : Int)

/-- The model read IS the read path: `weltBytes` is `World.bytesAb` applied
    to the checked address -- the function the `leseBytes` read path binds
    (`eval`: `let bs := σ.bytesAb …`) and the `schreibBytes` write path walks
    (`execStmt`: `σ.schreibBytes …`). Stated as `rfl` because the wiring is
    by identity, not by correspondence. -/
theorem weltBytes_istBytesAb (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (σ : World D) (addr len : Nat) :
    weltBytes D t f hf σ addr len = σ.bytesAb t f hf len (addr : Int) :=
  rfl

/-- The write lands where the read looks: a slot written through the write
    path (`World.schreibSlot`, as `execStmt` calls it) reads back the written
    value. The `nachUser` direction of the shape, at the model. -/
theorem schreibSlot_liestSelbe (D : Deklaration) (σ : World D) (t : D.Tab)
    (Λ : List (Res D)) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    (σ.schreibSlot t Λ k f v).slots t k f = v := by
  have e : (σ.schreibSlot t Λ k f v).slots t k f
      = (σ.storeSlot t k f v).slots t k f := rfl
  rw [e]
  simp [World.storeSlot]

/-- The checked reading, from the world at check time: the copy's user
    address, seen in `σ₁` -- the checked handle, at the model. -/
def modellPruefung (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (g : GepruefteKopie) (σ₁ : World D) : Lesung :=
  { addr := g.kopie.userAddr, wert := (weltByte D t f hf σ₁ g.kopie.userAddr).n.toNat }

/-- The copied reading, from the world at copy time: the SAME address, seen
    in `σ₂`. A copy from another address is not of this shape. -/
def modellKopie (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (g : GepruefteKopie) (σ₂ : World D) : Lesung :=
  { addr := g.kopie.userAddr, wert := (weltByte D t f hf σ₂ g.kopie.userAddr).n.toNat }

/-- Running a validated copy against the world: check first, copy second --
    two worlds, one handle. -/
def modellSequenz (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (g : GepruefteKopie) (σ₁ σ₂ : World D) :
    PruefDannKopie :=
  { pruefung := modellPruefung D t f hf g σ₁, kopie := modellKopie D t f hf g σ₂ }

/-- **Single-copy atomicity, at the model** -- the `EinSnapshot` premise over
    worlds: both snapshots agree at the checked byte (Koernung shape, one
    indivisible copy; the writer between them stays environment, cut C5). -/
def EinSnapshotWelt (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (g : GepruefteKopie) (σ₁ σ₂ : World D) : Prop :=
  weltByte D t f hf σ₁ g.kopie.userAddr = weltByte D t f hf σ₂ g.kopie.userAddr

/-- The run reads the validated address on both positions: what is checked
    is what is copied -- the handle, at the model, before any atomicity. -/
theorem modellSequenz_liestGeprueft (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (g : GepruefteKopie) (σ₁ σ₂ : World D) :
    (modellSequenz D t f hf g σ₁ σ₂).pruefung.addr = g.kopie.userAddr ∧
    (modellSequenz D t f hf g σ₁ σ₂).kopie.addr = g.kopie.userAddr :=
  ⟨rfl, rfl⟩

/-- Under the premise, the two model reads agree: the checked byte IS the
    copied byte. -/
theorem einSnapshotWelt_gibtWertGleich (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (g : GepruefteKopie) (σ₁ σ₂ : World D)
    (h : EinSnapshotWelt D t f hf g σ₁ σ₂) :
    (modellPruefung D t f hf g σ₁).wert = (modellKopie D t f hf g σ₂).wert := by
  unfold EinSnapshotWelt at h
  unfold modellPruefung modellKopie
  rw [h]

/-- **Validated-copy safety, INSIDE the model.** A checked copy run as a
    single copy through the checked handle shows no check-then-copy TOCTOU
    at the model read -- UNDER `EinSnapshotWelt`. The handle fixes the
    address (both readings name the checked one, out of `World.slots`); the
    premise fixes the value (no writer between). Drop the premise and the
    goal is unwritable -- that is the next theorem, not this. -/
theorem modellSequenz_ohneToctou (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (g : GepruefteKopie) (σ₁ σ₂ : World D)
    (h : EinSnapshotWelt D t f hf g σ₁ σ₂) :
    ohneToctou (modellSequenz D t f hf g σ₁ σ₂) := by
  have e : modellPruefung D t f hf g σ₁ = modellKopie D t f hf g σ₂ := by
    unfold EinSnapshotWelt at h
    unfold modellPruefung modellKopie
    rw [h]
  unfold ohneToctou modellSequenz
  exact e

/-- **The gap, at the model.** A run whose model reads differ -- the writer
    between check and copy, i.e. the crossing WITHOUT the single-copy
    premise -- shows TOCTOU. An unvalidated crossing runs in this shape, so
    nothing here excludes its TOCTOU; and the region check that would refuse
    it is still beside `exec` (cut C6). -/
theorem modellSequenz_toctou_ohneSnapshotWelt (D : Deklaration) (t : D.Tab)
    (f : D.Feld t) (hf : D.typ t f = .int 0 255) (g : GepruefteKopie)
    (σ₁ σ₂ : World D)
    (h : (modellPruefung D t f hf g σ₁).wert ≠ (modellKopie D t f hf g σ₂).wert) :
    ¬ ohneToctou (modellSequenz D t f hf g σ₁ σ₂) := by
  intro hc
  unfold ohneToctou modellSequenz at hc
  exact h (congrArg Lesung.wert hc)

#print axioms EinSnapshot
#print axioms einSnapshot_refl
#print axioms laufSequenz_liestGeprueft
#print axioms gepruefteKopie_ohneToctou
#print axioms toctouZeuge
#print axioms toctouZeuge_toctou
#print axioms laufSequenz_toctou_ohneSnapshot
#print axioms weltBytes_istBytesAb
#print axioms schreibSlot_liestSelbe
#print axioms modellSequenz_liestGeprueft
#print axioms einSnapshotWelt_gibtWertGleich
#print axioms modellSequenz_ohneToctou
#print axioms modellSequenz_toctou_ohneSnapshotWelt

/-! ## 8. Die Seitentrennung: Benutzer- gegen Kernbereich (Entwurf, ohne Entladung) -/

/- Beide Seiten teilen die Form von `UserRegion` (Basis plus Laenge, Schnitt C1),
   stehen aber als benannte Typen nebeneinander, damit eine kuenftige Pruefung in
   `exec` gegen genau eine Seite laufen kann. Die Entladung selbst bleibt
   kuenftige Arbeit (Schnitt C7 im Kopf): kein Uebergang hier stellt eine
   Forderung an `exec`. -/

/-- Der Kernbereich: dieselbe Form wie `UserRegion` (Basis plus Laenge), als
    eigener Name, damit die Trennung benennbar bleibt. -/
def KernRegion := UserRegion

/-- Die seitenabhaengige Bereichsform: je Seite der zugehoerige Bereichstyp. -/
def SeitenRegion (s : Seite) : Type :=
  match s with
  | .kern => KernRegion
  | .user => UserRegion

/-! ### Die Bereichspruefung in `exec`: Gestalt ohne Entladung -/

/- Die Gestalt, die ein kuenftiger `exec`-Uebergang einloesen muesste: Wer die
   Kopie `k` traegt, laeuft gegen den Bereich `r` nur bei `validiert r k`.
   Hier steht die Forderung als Form; der Uebergang, der sie stellt, fehlt
   noch (Schnitt C7). -/

/-- Die Gestalt der Bereichspruefung in `exec`: ein Uebergang, der die Kopie `k`
    traegt, darf gegen den Bereich `r` nur bei `validiert r k` laufen. Eine Kopie
    ausserhalb des Bereichs wird verweigert. -/
def execFordertBereich (a : KernAnweisung) (r : UserRegion) (k : Kopie) : Prop :=
  getrageneKopie a = some k → validiert r k

/-- Die Verweigerungsgestalt: eine Kopie ausserhalb des Bereichs wird abgewiesen;
    erst mit der Entladung in `exec` (Schnitt C7) wird daraus ein Uebergang. -/
def ausserhalbVerweigert (r : UserRegion) (k : Kopie) : Prop :=
  ¬ validiert r k

/-! ### Der Benutzerteil der Weltabbildung -/

/- Der Benutzerteil als Adressmenge: `adresseInRegion` nennt die Zugehoerigkeit
   auf `Nat`-Adressen (die Bereichsform von `innerhalb`, einfacher gelesen),
   `schluesselInRegion` dieselbe auf den `Int`-Schluesseln von `World.slots` --
   `weltByte` liest `(addr : Int)`, also haengt hierueber der Benutzerteil der
   Weltabbildung am Bereich. `bereicheGetrennt` nennt die Trennung selbst. -/

/-- Eine Adresse im Bereich: `[basis, basis + laenge)` -- die Bereichsform von
    `innerhalb`, als einstellige Zugehoerigkeit. -/
def adresseInRegion (r : UserRegion) (addr : Nat) : Prop :=
  r.basis ≤ addr ∧ addr < r.basis + r.laenge

/-- Ein Weltenschluessel im Bereich: dieselbe Zugehoerigkeit auf den
    `Int`-Schluesseln von `World.slots` -- hierueber haengt der Benutzerteil der
    Weltabbildung am Bereich. -/
def schluesselInRegion (r : UserRegion) (k : Int) : Prop :=
  (r.basis : Int) ≤ k ∧ k < (r.basis : Int) + (r.laenge : Int)

/-- Der Benutzerteil der Weltabbildung: genau die Schluessel des
    Benutzerbereichs. -/
def benutzerTeil (u : UserRegion) (k : Int) : Prop :=
  schluesselInRegion u k

/-- Die Trennung: Benutzer- und Kernbereich teilen keine Adresse -- die
    Seitentrennung als Gestalt, noch ohne Traeger in `World`. -/
def bereicheGetrennt (u k : UserRegion) : Prop :=
  ∀ addr : Nat, adresseInRegion u addr → adresseInRegion k addr → False

end Gabbro.Grammatik.Adressraum
