/-
  File:    gabbrov/V1.lean
  Subject: **V1 of `dokumente/GABBROV.md` -- are the 66 logic obligations SAYABLE in the
           Lean fragment of §7?**

  This file is the measurement, not a report about one. Every one of the 66 `L` rows of
  `dokumente/PFLICHTEN.md` stands below as a Lean `Prop` over `Gabbro.Body.State`, or it
  stands below with the reason it cannot -- and `lean` type-checks the file either way.
  *A count of what is expressible, produced by a tool that refuses what is not, is worth
  more than the same count produced by a reader.*

  WHY IT IMPORTS `Gabbro.Body` AND DEFINES NO SECOND SEMANTICS
    §8: GabbroV checks obligations against a meaning of Gabbro, and GabbroC's correctness
    proof uses one -- **it must be the same one.** So this file adds no `Value`, no `Place`
    and no `World`. Where the existing four-form `Value` cannot carry an obligation, that is
    a FINDING and it is written down as one, not repaired by a local definition that would
    make the two semantics differ in exactly the place the section warns about.

  THE FRAGMENT, as §7 outlines it
    "Lean terms of a certain type, with outlined means: predicates over values, integer and
     bitvector arithmetic with overflow behaviour, aggregation over table domains, pure
     helper functions in the translatable part."

    Taken literally, and every means is built below from Lean core -- `programmlogik` has NO
    mathlib, and its lakefile says why. So no `Finset`, no `Relation.ReflTransGen`: a table
    domain is a `List Int` and the aggregation is `List.filter`.

  THE FOUR VERDICTS, and the count in §8 is read off the file rather than written beside it
    SAYABLE    -- a `Prop` stands there and `lean` accepted it.
    DEMAND     -- sayable, but through a means §7 must carry. The means is a pure helper over
                  the UNCHANGED `Gabbro.Body`, so it costs the shared semantics nothing --
                  which is exactly what separates it from the next line.
    EXTENSION  -- sayable only if the SHARED `Value` grows a form. §8 forbids growing it
                  here, so the row carries `notSayable` and the price is named.
    NOT        -- no `Prop` over one or two states expresses it, and no extension of `Value`
                  would change that. The reason stands at the row.
-/
import Gabbro.Body

set_option autoImplicit false

open Gabbro.Body

namespace GabbroV.V1

/-! ## 0. The fragment's means, §7, out of Lean core

    Three helpers, and **each is a DEMAND on §7 -- of which §7 records one.** Each says at its
    head which it is and what hangs on it. All three are pure functions over the unchanged
    `Gabbro.Body`: that they type-check here IS the proof that they cost the shared semantics
    nothing.
-/

/-- A table domain -- the finite list of slot indices a `table … count N` declares.
    `forall s in slots of T` is bounded quantification over exactly this, and that is the
    single commonest shape among the 66. -/
abbrev Domain := List Int

/-- `forall s in slots of T : P s`. -/
def allD (d : Domain) (p : Int → Prop) : Prop := ∀ s, s ∈ d → p s

/-- **DEMAND 1 -- aggregation, and §7 RECORDS this one.**

    `refcount == count(s in slots : s.object == o)`. `pred` has no production for `count`
    (reserved word, no rule -- `messung/AGGREGATION.md` measures the refusal); Lean has one
    as soon as the domain is a list. Rows that hang on it: **L03.** -/
def countD (d : Domain) (p : Int → Bool) : Nat := (d.filter p).length

/-- **DEMAND 2 -- a fold that is NOT `count`, and §7 does not record it.**

    «B10» and F6:1094 both need *the FIRST element of an ordered domain satisfying P*, not how
    many there are, and no amount of `count` builds a minimality statement. *§7's word for the
    means is "aggregation"; what the corpus asks for is FOLDS, of which `count` is one.*
    Rows: **L29, L54.** -/
def firstD (d : Domain) (p : Int → Bool) : Option Int := d.find? p

/-- **DEMAND 3 -- bounded reachability, and §7 does not record it although the LANGUAGE
    already has it.**

    `SYNTAX.md`:717 carries `reach = place "reaches" place "via" ident`, `parse.rs`:2117
    parses it into `PredArt::Erreicht`, and a probe through the unchanged checker passes with
    **0 errors**. So this is not a wish. The Lean channel refuses it by name --
    `LeanReason::Quantified`, *"a QUANTIFIER, `reaches`, or a set membership"* -- and the same
    obligation, exported with `gabbro pflichten --lean`, comes back as
    `table-invariant (1)` with no goal.

    **§7's own argument about aggregation applies here word for word:** if the fragment does
    not carry it, the same gap moves one level up. Rows: **L04, L05, L09, L15, L16** -- five,
    which is more than the demand §7 does record.

    The bound is the table's own `count`, so the helper is total and the unrolling finite.
    That is what makes it translatable at all, and it is the whole reason the row reads
    DEMAND and not NOT. -/
def reachesIn (w : World) (c : String) (f : String) : Nat → Int → Int → Bool
  | 0,     s, t => decide (s = t)
  | n + 1, s, t =>
      if s = t then true
      else match w (.slot c s f) with
           | .present k => reachesIn w c f n k t
           | _          => false

/-- The slot of `c` at `s`, field `f` -- written once so the rows below read like the
    fragment they come from. -/
abbrev sl (w : World) (c : String) (s : Int) (f : String) : Value := w (.slot c s f)

/-- A named field of a named register: `GSTS.TES`, `GCMD.SRTP`. -/
abbrev reg (w : World) (r f : String) : Value := w (.field r f)

/-- The marker for a row the fragment cannot state. **It is `False` on purpose**: whoever
    later believes one of these is expressible has to delete the marker, and then this file
    and `messung/GABBROV-V1.md` disagree loudly instead of quietly. -/
def notSayable : Prop := False

/-! ## 1. F1 -- Cap space, 17 obligations

    Carriers: `"c"` the `CapSpace`, `"o"` the `CapObjects`. Two carrier names are two objects
    -- the alias statement, assumed here as everywhere (`Body.lean` U3).
-/

/-- **L01 -- SAYABLE.** A root has no predecessor. -/
def L01 (w : World) (d : Domain) : Prop :=
  allD d fun s => sl w "c" s "parent" = .absent → sl w "c" s "prev_sibling" = .absent

/-- **L02 -- SAYABLE, and «B14» is a `pred` gap and not a Lean one.**

    `slots[s.next].prev == s`. What `pred` cannot do is RESOLVE an `option index into`; the
    model's `Value.present` carries the index in the open, so the resolution is a pattern
    match and costs nothing. -/
def L02 (w : World) (d : Domain) : Prop :=
  allD d fun s => ∀ n, sl w "c" s "next_sibling" = .present n →
                       sl w "c" n "prev_sibling" = .present s

/-- **L03 -- DEMAND 1.** `refcount == count(s in slots : s.object == o)` -- the core of the
    capability system's bookkeeping. -/
def L03 (w : World) (dSlots dObj : Domain) : Prop :=
  allD dObj fun o =>
    sl w "o" o "refcount"
      = .int (countD dSlots (fun s => decide (sl w "c" s "object" = .present o)))

/-- **L04 -- DEMAND 3.** `cdt_wohlgeformt` -- every slot reaches the root via `parent`.
    `bound` is the table's own `count`. -/
def cdtWf (w : World) (d : Domain) (bound : Nat) (root : Int) : Prop :=
  allD d fun s => reachesIn w "c" "parent" bound s root = true

/-- **L05 -- DEMAND 3.** `unlink` maintains it. -/
def L05 (s s' : State) (d : Domain) (b : Nat) (root : Int) : Prop :=
  cdtWf s.world d b root → cdtWf s'.world d b root

/-- **L06 -- SAYABLE.** The four relink cases are exhaustive and each is correct. The
    exhaustiveness is the `match`'s and therefore plumbing; what stands here is the
    correctness -- the removed slot is out of both chains and the neighbours are joined. -/
def L06 (s s' : State) (x : Int) : Prop :=
  (∀ p, sl s.world "c" x "prev_sibling" = .present p →
        sl s'.world "c" p "next_sibling" = sl s.world "c" x "next_sibling")
  ∧ (∀ n, sl s.world "c" x "next_sibling" = .present n →
          sl s'.world "c" n "prev_sibling" = sl s.world "c" x "prev_sibling")
  ∧ (sl s.world "c" x "prev_sibling" = .absent →
     ∀ par, sl s.world "c" x "parent" = .present par →
            sl s'.world "c" par "first_child" = sl s.world "c" x "next_sibling")

/-- **L07 -- SAYABLE.** `ist_blatt` -- the cap has no children. -/
def istBlatt (w : World) (d : Domain) (x : Int) : Prop :=
  allD d fun k => sl w "c" k "parent" ≠ .present x

/-- **L08 -- SAYABLE.** The refcount fell by exactly one. Two states and integer arithmetic;
    `old(…)` is the pre-state, and a hand-written spec has both. *`OldState` is a refusal of
    the AUTOMATIC channel, not a limit of the fragment.* -/
def L08 (s s' : State) (obj : Int) : Prop :=
  ∀ n, sl s.world "o" obj "refcount" = .int n →
       sl s'.world "o" obj "refcount" = .int (n - 1)

/-- **L09 -- DEMAND 3.** `delete_leaf` maintains `cdt_wohlgeformt`. -/
def L09 (s s' : State) (d : Domain) (b : Nat) (root : Int) : Prop :=
  cdtWf s.world d b root → cdtWf s'.world d b root

/-- **L10 -- SAYABLE.** Released exactly at zero, and in both directions. -/
def L10 (s s' : State) (obj : Int) : Prop :=
  (sl s.world "o" obj "refcount" = .int 0 → sl s'.world "o" obj "used" = .bool false)
  ∧ (sl s.world "o" obj "refcount" ≠ .int 0 →
     sl s'.world "o" obj "used" = sl s.world "o" obj "used")

/-  **L11, L12, L13 -- EXTENSION. One finding, one price, three rows.**

    `tagged type ObjectKind = { Memory(Region), … Reply(ReplyRef), … Dma(DmaRef), … }`
    (`FRAGMENTE.md`@708beed:128). All three obligations speak about the PAYLOAD:

      L11  `Memory` -- **the region** goes back to the RAM allocator
      L12  `Dma`    -- released only after proof
      L13  `Reply`  -- **the caller** is unblocked

    `Region`, `DmaRef` and `ReplyRef` are RECORDS. `Value` is four forms and the list is
    closed -- `int`, `bool`, `absent`, `present n` -- and `present` carries ONE `Int`, an
    index and not a record. The emitter books exactly this by name:
    `LeanReason::ConstructedValue`, *"a constructor whose VALUE this model has no form for --
    a record, a `tagged`, or a device handle … the price is a MODEL EXTENSION, and it is a
    different price from a missing gate."*

    **Why they are not repaired here.** A `Value` grown in `gabbrov/` and not in
    `Gabbro.Body` is §8's two-formalisations hazard in miniature: the obligation would be
    provable in GabbroV's model and mean nothing in GabbroC's. *The price is real and it is
    payable -- but it is payable in one place only, and this is not that place.*

    Contrast L41: `tagged type BufPhase = { Driver, Device }` carries NO payload, so it is a
    tag, a tag is an `Int`, and that row costs nothing.
-/
def L11 : Prop := notSayable
def L12 : Prop := notSayable
def L13 : Prop := notSayable

/-- **L14 -- SAYABLE.** No reference survives: after the deed no live slot points at the
    object. -/
def L14 (w : World) (d : Domain) (obj : Int) : Prop :=
  allD d fun s => sl w "c" s "used" = .bool true → sl w "c" s "object" ≠ .present obj

/-- **L15 -- DEMAND 3.** The CDT is well-formed on entry -- a `requires`. -/
def L15 (s : State) (d : Domain) (b : Nat) (root : Int) : Prop := cdtWf s.world d b root

/-- **L16 -- DEMAND 3.** `revoke` maintains it. -/
def L16 (s s' : State) (d : Domain) (b : Nat) (root : Int) : Prop :=
  cdtWf s.world d b root → cdtWf s'.world d b root

/-- **L17 -- SAYABLE.** Every `victim` is a leaf when `delete_leaf` sees it -- *the
    load-bearing statement of `revoke`*. -/
def L17 (w : World) (d victims : Domain) : Prop :=
  allD victims fun v => istBlatt w d v

/-! ## 2. F2 -- VT-d, 5 obligations

    All five are one shape: a `transition`'s `requires` over REGISTER FIELDS. They are the
    cheapest of the 66 -- propositional statements over extracted bits -- and none of them
    needs a domain at all.
-/

/-- **L18 -- SAYABLE.** `setze_rtp` -- TE off or RTPS already set. -/
def L18 (w : World) : Prop := reg w "GSTS" "TES" = .int 0 ∨ reg w "GSTS" "RTPS" = .int 1

/-- **L19 -- SAYABLE.** `scharf_te` -- RTPS is set. -/
def L19 (w : World) : Prop := reg w "GSTS" "RTPS" = .int 1

/-- **L20 -- SAYABLE.** `setze_irtp` -- QIES is set. -/
def L20 (w : World) : Prop := reg w "GSTS" "QIES" = .int 1

/-- **L21 -- SAYABLE.** `scharf_ire` -- IRTPS set and CFIS clear. -/
def L21 (w : World) : Prop := reg w "GSTS" "IRTPS" = .int 1 ∧ reg w "GSTS" "CFIS" = .int 0

/-- **L22 -- SAYABLE.** `scharf_qie` -- QIES is clear. -/
def L22 (w : World) : Prop := reg w "GSTS" "QIES" = .int 0

/-! ## 3. F3 -- IPC fastpath, 13 obligations

    F3 carries the densest logic of the ten fragments, and **two of the four rows of the
    ordering class**. That is not a coincidence: an IPC fastpath IS a sequence of writes whose
    order is the specification.
-/

/-- **L23 -- SAYABLE.** `caller` and `reply_owner` are set together or not at all. -/
def antwortpflichtPaarig (w : World) (d : Domain) : Prop :=
  allD d fun e => (sl w "e" e "caller" = .absent) ↔ (sl w "e" e "reply_owner" = .absent)

/-  **L24 -- NOT. The first of the ordering class, and the sharpest of the four.**

    *"The two places are written in ONE step."* `FRAGMENTE.md`@708beed:594 says what the
    fragment means: **`caller` and `reply_owner` are NEVER HALF SET.**

    Every means of §7 is a predicate over A STATE or over a pre/post PAIR. "In one step" is a
    statement about the EXECUTION between them -- that no third state exists in which one
    place is written and the other is not. `Body.lean`'s `exec` is big-step: it maps a state
    and a list of statements to an `Outcome`, and **there is no intermediate state to name,
    let alone to quantify over.**

    The two ways out, and why neither is one:

      * *Take it as vacuous.* Under a big-step semantics the pair IS written atomically by
        construction, so the obligation is trivially true -- which is precisely §5's vacuity
        hazard, and §5 says what it looks like: it would read as proved and say nothing.
      * *Add a ghost sequence number.* Then the `Prop` speaks about state the program does not
        have, and a specification over invented state specifies a different program.

    **What IS sayable is the pre/post half**, and that half is already its own row (L23, L27).
    *The residue of L24 once L23 is subtracted is exactly the part the fragment cannot hold* --
    which is why subtracting it would not shrink the finding, only hide it.
-/
def L24 : Prop := notSayable

/-- **L25 -- SAYABLE.** `msg_kopiert` -- the message arrived. Bounded quantification over an
    array domain plus a pre-state; «B12» (*no numeric-range domain*) is a gap in Gabbro's
    grammar, and a Lean domain is a list. -/
def L25 (s s' : State) (idx : Domain) : Prop :=
  allD idx fun i => s'.world (.slot "dst" i "msg") = s.world (.slot "src" i "msg")

/-- **L26 -- SAYABLE.** Postconditions may speak about the return value. «B6» is closed in the
    language; in the fragment the returned value is simply a parameter of the `Prop`, which is
    what `Outcome.returned` already carries. -/
def L26 (s' : State) (result picked : Int) : Prop :=
  sl s'.world "t" picked "frame" = .present result

/-- **L27 -- SAYABLE.** `antwortpflicht_paarig` is maintained. -/
def L27 (s s' : State) (d : Domain) : Prop :=
  antwortpflichtPaarig s.world d → antwortpflichtPaarig s'.world d

/-- **L28 -- SAYABLE.** A quiescing endpoint starts no new transaction. -/
def L28 (s s' : State) (core : Int) : Prop :=
  sl s.world "e" core "quiescing" = .bool true →
    sl s'.world "e" core "caller" = sl s.world "e" core "caller"
    ∧ sl s'.world "e" core "reply_owner" = sl s.world "e" core "reply_owner"

/-- **L29 -- DEMAND 2.** The fastpath takes the FIRST live receiver and stops. «B10» in the
    language; in the fragment it is a minimality statement, and `count` cannot make one. -/
def L29 (w : World) (queue : Domain) (picked : Int) : Prop :=
  firstD queue (fun t => decide (sl w "t" t "frame" ≠ .absent)) = some picked

/-- **L30 -- SAYABLE.** The chosen receiver is alive. -/
def L30 (w : World) (picked : Int) : Prop := sl w "t" picked "frame" ≠ .absent

/-- **L31 -- SAYABLE.** A full queue is REFUSED by name, not blocked -- *D11 literally, and
    the best move in F3*. A `reason` value is a small integer, hence a `Value`. -/
def L31 (s s' : State) (core errEpFull : Int) : Prop :=
  sl s.world "e" core "senders_count" = .int 32 →
    s'.world (.field "f" "result") = .int errEpFull
    ∧ sl s'.world "e" core "senders_count" = sl s.world "e" core "senders_count"

/-- **L32 -- SAYABLE.** The caller is blocked. -/
def L32 (s' : State) (caller : Int) : Prop := sl s'.world "t" caller "blocked" = .bool true

/-- **L33 -- SAYABLE.** The message arrives at the right thread. -/
def L33 (s s' : State) (picked : Int) (idx : Domain) : Prop :=
  ∀ fr, sl s.world "t" picked "frame" = .present fr →
        allD idx fun i => s'.world (.slot "frames" (fr + i) "word")
                          = s.world (.slot "f" i "word")

/-  **L34 -- NOT. The ordering class, and this row states the intermediate state OUTRIGHT.**

    *"The invariant does not hold BETWEEN the two assignments."* `FRAGMENTE.md`@708beed:675 in
    the fragment's own words: *"Ohne ihn zwei Zuweisungen, und die Invariante gilt dazwischen
    nicht."*

    L24 needs to say that no intermediate state exists. **L34 needs to say that one does, and
    what fails in it.** The same missing means, used in opposite directions -- which is why
    the two belong together and why repairing one would repair both.

    The language has since NAMED the region -- `breaking antwortpflicht_paarig { … }`
    (`SYNTAX.md`:882) -- and `Body.lean` carries the constructor `breaking (invariants) (body)`.
    But read what the model does with it: *"A suspension changes no state."* The names travel
    as DATA; no line of the semantics says the invariant is suspended, and `SPRACHE.md` §8.3.1
    records that `D013` does not check it either. *The construct exists at both ends and the
    statement exists at neither* -- and `GABBROV.md` §3 picks exactly this out as the place
    where GabbroV would create value beyond convenience. **The measurement says it cannot, not
    at V1's fragment.**
-/
def L34 : Prop := notSayable

/-- **L35 -- SAYABLE.** A same-core rendezvous switches directly. -/
def L35 (s s' : State) (picked core : Int) : Prop :=
  sl s.world "t" picked "core" = .int core →
    s'.world (.global "current") = .int picked

/-! ## 4. F4 -- virtio driver, 7 obligations

    The status bits, as the fragment declares them: `ACK @0, DRIVER @1, DRIVER_OK @2,
    FEATURES_OK @3`. They are disjoint, so the OR of a subset is its sum -- written out rather
    than hidden behind a notation, because the reader has to be able to check it.
-/

def ACK : Int := 1
def DRIVER : Int := 2
def DRIVER_OK : Int := 4
def FEATURES_OK : Int := 8

/-- **L36 -- SAYABLE.** `ack` -- from 0 to ACK. -/
def L36 (s s' : State) : Prop :=
  s.world (.global "DEVICE_STATUS") = .int 0 →
  s'.world (.global "DEVICE_STATUS") = .int ACK

/-- **L37 -- SAYABLE.** `drv` -- ACK to ACK|DRIVER. -/
def L37 (s s' : State) : Prop :=
  s.world (.global "DEVICE_STATUS") = .int ACK →
  s'.world (.global "DEVICE_STATUS") = .int (ACK + DRIVER)

/-- **L38 -- SAYABLE.** `featok`. -/
def L38 (s s' : State) : Prop :=
  s.world (.global "DEVICE_STATUS") = .int (ACK + DRIVER) →
  s'.world (.global "DEVICE_STATUS") = .int (ACK + DRIVER + FEATURES_OK)

/-- **L39 -- SAYABLE.** `drvok`. -/
def L39 (s s' : State) : Prop :=
  s.world (.global "DEVICE_STATUS") = .int (ACK + DRIVER + FEATURES_OK) →
  s'.world (.global "DEVICE_STATUS") = .int (ACK + DRIVER + FEATURES_OK + DRIVER_OK)

/-- **L40 -- SAYABLE, and «B26» is a grammar gap and not a fragment one.** A reset applies
    from EVERY state -- the quantified pre-state Gabbro has no placeholder for, and which a
    Lean `Prop` gives away for free. *A construct missing at one end is not a statement
    missing at both.* -/
def L40 (s s' : State) : Prop :=
  ∀ v : Int, s.world (.global "DEVICE_STATUS") = .int v →
             s'.world (.global "DEVICE_STATUS") = .int 0

/-- **L41 -- SAYABLE.** A buffer belongs to exactly one side. `tagged type BufPhase =
    { Driver, Device }` carries NO payload, so it is a tag and a tag is an `Int` -- which is
    the whole difference between this row and L11-L13. -/
def L41 (w : World) (d : Domain) : Prop :=
  allD d fun b => (sl w "q" b "phase" = .int 0 ∨ sl w "q" b "phase" = .int 1)
                  ∧ ¬(sl w "q" b "phase" = .int 0 ∧ sl w "q" b "phase" = .int 1)

/-  **L42 -- NOT, and the reason is a MISFILING rather than a shortfall.**

    *"It ends because **the device** completes or faults."* `retry warten until
    q.USED_IDX != von bounded MAX_POLL ops progress device_completes_or_faults`.

    `PFLICHTEN.md` names the borderline in the row itself: *"not 'over a finite set' but
    'because the device makes progress'"*. **The measure is not in the program's state.** No
    predicate over one state or over a pre/post pair says "this loop ends", and the reason it
    ends lies with an agent the program does not contain.

    **In GabbroV's own vocabulary this row is an `assumption`** -- §5's second class, the one
    that already has a falsification discipline against real hardware
    (`falsifiziert(probe_…)`). It is booked in the manifest as `obligation`, and the fragment
    is the wrong instrument for it. *That is a finding about the manifest's classification,
    not about the cut* -- and it is the cheapest of the seven to act on: it moves a row, it
    does not build anything.
-/
def L42 : Prop := notSayable

/-! ## 5. F5 -- Userspace service loop, 10 obligations -/

/-- **L43 -- SAYABLE.** Every startup failure is named and leaves the program -- six
    `let … else` with six distinct signal codes. -/
def L43 (s' : State) (codes : List Int) : Prop :=
  ∀ c, c ∈ codes → s'.world (.global "notification") = .int c →
       s'.world (.global "terminated") = .bool true

/-- **L44 -- SAYABLE, and this is the row the model was BUILT for.** *"Never read yet" is
    distinguishable from zero.* `Value.absent` against `Value.int 0` -- two different values
    under `DecidableEq`, no encoding, no convention. «B14» is the gap in Gabbro (`option` only
    in `slottype`); the fragment has had the distinction since its first line. -/
def L44 (w : World) : Prop :=
  w (.global "capacity") = .absent → w (.global "capacity") ≠ .int 0

/-- **L45 -- SAYABLE.** The service loop has a NAMED exit. `reason ServiceExit
    { EndpointGone = 1, Stopped = 2 }` -- the codes stand in the source, so the exit reason is
    an `Int` and the statement is a membership.

    **What is not sayable is a different thing, and it is not this row:** `Body.lean`'s
    `Outcome` has `running`/`returned`/`stuck` and no arm for a `leave`
    (`LeanReason::NonLocalExit`). That is a gap in the BODY model and it bites when the
    obligation is to be PROVED. *V1 asks whether it can be SAID, and it can.* -/
def L45 (s' : State) : Prop :=
  s'.world (.global "exit_reason") = .int 1 ∨ s'.world (.global "exit_reason") = .int 2

/-  **L46 -- NOT, same class and same misfiling as L42.**

    *"It makes progress because a client calls or the endpoint is revoked."*
    `progress client_calls_or_endpoint_revoked`. The reason the service loop advances is an
    event outside the program: a client, or a revocation. **An `assumption`, not an
    `obligation`** -- and unlike L42 its falsifier is not hardware but the rest of the system,
    so §5's probe discipline does not reach it as written either. *Two rows, one class, two
    different falsifiers -- and §5 has an instrument for one of them.*
-/
def L46 : Prop := notSayable

/-- **L47 -- SAYABLE.** A revoked endpoint ends the service. -/
def L47 (s s' : State) : Prop :=
  s.world (.global "EP_revoked") = .bool true →
  s'.world (.global "terminated") = .bool true

/-- **L48 -- SAYABLE.** `Info` -- capacity is reported and cached. -/
def L48 (s' : State) (r : Int) : Prop :=
  s'.world (.global "capacity") = .int r ∧ s'.world (.field "reply" "sectors") = .int r

/-- **L49 -- SAYABLE.** `Read`/`Write` -- the request lies inside the client's range. Integer
    arithmetic, and the addition is the one §7's overflow behaviour is about. -/
def L49 (w : World) (lo hi : Int) : Prop :=
  ∀ start len, w (.field "m" "start") = .int start → w (.field "m" "len") = .int len →
               lo ≤ start ∧ start + len ≤ hi

/-  **L50 -- NOT. The ordering class, third of four.**

    *"`Flush` -- the flush completed BEFORE the reply."* The body is
    `let r2 = request_flush(transport, pool); reply4(EP, …);` -- two effects, and the
    obligation is about their ORDER.

    A pre/post pair sees the state before the arm and the state after it. Both effects have
    happened in the post state and neither has in the pre state; **the order between them is
    in neither.** The two ways out fail exactly as at L24.

    *This is the cheapest of the four to get wrong:* `flush ∧ reply` type-checks, reads right,
    and is a strictly weaker statement wearing the obligation's name. **A fragment that
    silently accepts it is the "translation that does not understand something and leaves it
    out" §7 names as the commonest way such tools go unsound** -- which is why the row reads
    NOT rather than a weakened SAYABLE.
-/
def L50 : Prop := notSayable

/-- **L51 -- SAYABLE.** `Scan` -- the partition table is read or refused. -/
def L51 (s' : State) : Prop :=
  s'.world (.field "reply" "status") = .int 0 ∨ s'.world (.field "reply" "status") = .int 1

/-  **L52 -- NOT. The ordering class, fourth and last.**

    *"`Stop` -- the reply still goes out BEFORE the service ends."* The same shape as L50, and
    the fragment's own note says what hangs on it: without a named exit only `exit()` remains,
    *"and the cleanup promise moves to two places. Literally the class C8 paid for."*

    **A cleanup promise IS a statement of this class** -- that one effect precedes another on
    every path -- and it is the one shape a state-pair fragment cannot hold. *The four rows of
    this class are not four accidents; they are one missing means, and it is the same means at
    all four.*
-/
def L52 : Prop := notSayable

/-! ## 6. F6 -- Test scaffold, 5 obligations -/

/-- **L53 -- SAYABLE.** "Never measured" is distinguishable from zero -- L44's statement at a
    second site, and the same `absent`/`int 0` pair answers it. -/
def L53 (w : World) : Prop :=
  w (.global "frei_min") = .absent → w (.global "frei_min") ≠ .int 0

/-- **L54 -- DEMAND 2.** The first untouched word marks the depth: `if w != MUSTER
    { return i * 8; }`. A minimality statement over an ordered domain -- the means L29 needs,
    asked for by an unrelated fragment. *Two independent demands for one construct is what
    Rule A calls measured demand.* -/
def L54 (w : World) (words : Domain) (muster depth : Int) : Prop :=
  firstD words (fun i => decide (w (.slot "f" i "wort") ≠ .int muster)) = some depth

/-- **L55 -- SAYABLE.** The measuring instrument reports the known depth. Three concrete
    equalities, and the `check`'s `claim` names all three. -/
def L55 (w : World) (len tiefe : Int) : Prop :=
  w (.global "unberuehrt_leer") = .int 0
  ∧ w (.global "unberuehrt_voll") = .int len
  ∧ w (.global "unberuehrt_tief") = .int ((len - tiefe) * 8)

/-- **L56 -- SAYABLE.** At the foot of every EL0 kernel stack an eighth stays untouched, and
    the three parts fit in the size. Bounded quantification plus integer arithmetic. -/
def L56 (w : World) (stacks : Domain) (nenner : Int) : Prop :=
  allD stacks fun k =>
    ∀ g f irq, sl w "st" k "groesse" = .int g → sl w "st" k "frei_min" = .int f →
               sl w "st" k "irq_tiefe_max" = .int irq →
               f ≥ g / nenner ∧ (g - f) + irq + g / nenner ≤ g

/-  **L57 -- NOT, and it is alone in its class.**

    *"The check can go RED."* `counterprobe "Fuellung ausgehaengt" expects erschoepft_waechst`
    -- *the speech test as a language construct*.

    Every other of the 66 is a statement about ONE program's states. This one is a statement
    about **a second, deliberately broken program**: that under a named mutation the check
    fails. To say it, the fragment would have to quantify over PROGRAMS, and §7's terms range
    over values.

    **It is also the row whose absence would be least visible**, which is the whole reason the
    construct exists (`R11`: *a guardian nobody has ever seen say no is an ornament*). *A
    fragment that cannot state the speech test can still be given one from outside -- but it
    cannot be given one by GabbroV, and the manifest hands this row to GabbroV.*
-/
def L57 : Prop := notSayable

/-! ## 7. F7-F10 -- Loader, Scheduler, MMU, Parser, 9 obligations -/

/-- **L58 -- SAYABLE.** Before the MMU the console is lock-free -- *a property of the PHASE*.
    The phase is a place and the lock is a place; the obligation relates the two. -/
def L58 (w : World) : Prop :=
  w (.global "phase") = .int 0 → w (.global "CONSOLE_LOCK_held") = .bool false

/-- **L59 -- SAYABLE.** The revalidation -- the thread may have vanished between selection and
    deed, so the resolved index really carries the thread asked for. -/
def L59 (w : World) (t : Int) : Prop :=
  ∀ i, w (.global "aufgeloest") = .present i →
       sl w "l" i "tid" = .int t ∧ sl w "l" i "belegt" = .bool true

/-- **L60 -- SAYABLE.** Both exits are forced, and each is right. -/
def L60 (s s' : State) (result : Value) : Prop :=
  (∀ i, s.world (.global "aufgeloest") = .present i →
        sl s'.world "l" i "belegt" = .bool false ∧ result = .bool true)
  ∧ (s.world (.global "aufgeloest") = .absent → result = .bool false)

/-- **L61 -- SAYABLE.** A non-leaf entry points at a next level. -/
def L61 (w : World) (d : Domain) : Prop :=
  allD d fun e => sl w "pt" e "PS" = .int 0 → sl w "pt" e "down" ≠ .absent

/-- **L62 -- SAYABLE.** `PS == 1` marks a leaf. -/
def L62 (w : World) (d : Domain) : Prop :=
  allD d fun e => sl w "pt" e "PS" = .int 1 → sl w "pt" e "down" = .absent

/-- **L63 -- SAYABLE.** The leaf level is reached. -/
def L63 (w : World) : Prop :=
  w (.field "abbildung" "level") = .int 3 → w (.global "walk_done") = .bool true

/-- **L64 -- SAYABLE, and its gap is at the OTHER end.** W^X over the page table.

    `PFLICHTEN.md` carries this row with `gap: not in the fragment at all` and the 2026-08-14
    sentence *"a real property falls out of all seven domains"*. **That is a gap in the GABBRO
    fragment -- the property was never written there.** V1 asks whether the fragment of §7 can
    SAY it, and it is the most ordinary statement in this file: a bounded quantification over
    the page table with a negated conjunction.

    *The two gaps must not be added together.* One says the corpus never stated a property;
    the other would say the specification language cannot state it. **Only the second
    falsifies the cut, and this row is the first.** -/
def L64 (w : World) (d : Domain) : Prop :=
  allD d fun p => ¬(sl w "pt" p "W" = .int 1 ∧ sl w "pt" p "X" = .int 1)

/-- **L65 -- SAYABLE.** The buffer is a device tree -- `magie == MAGIE`. -/
def L65 (w : World) (magie : Int) : Prop := w (.field "kopf" "magie") = .int magie

/-- **L66 -- SAYABLE, and it is the CONTRAST that makes L42 and L46 a class rather than a
    complaint.** *"It ends because **a token is consumed**"* -- `progress token_verbraucht`.

    `PFLICHTEN.md` names the difference in the row itself: *"the ALGORITHM's progress measure,
    not the machine's finiteness"*. The measure is a place in the program's own state, so it
    is a decreasing integer and the fragment holds it. **L42 and L46 differ from this row in
    exactly one respect, and it is the respect that decides: their measure is outside.** -/
def L66 (s s' : State) : Prop :=
  ∀ n m : Int, s.world (.global "tokens_left") = .int n →
               s'.world (.global "tokens_left") = .int m → m < n

/-! ## 8. The count, read off THIS file

    A number in a comment drifts away from the file beneath it. These are the file's own
    definitions, so a row that changes its verdict without changing this block makes the two
    disagree -- and `#eval` prints them at build time.
-/

/-- The rows that carry `notSayable`, by the reason they carry it. -/
def nichtSagbar : List (String × List String) :=
  [("EXTENSION -- record payload of a `tagged` variant; the SHARED `Value` must grow a form",
      ["L11", "L12", "L13"]),
   ("NOT -- ordering and atomicity; needs a state BETWEEN the pre and the post",
      ["L24", "L34", "L50", "L52"]),
   ("NOT -- environment liveness; an `assumption` (§5), not an `obligation`",
      ["L42", "L46"]),
   ("NOT -- a statement about a SECOND, mutated program",
      ["L57"])]

/-- The demands on §7's fragment, with the rows that hang on each. **All three are pure
    helpers over the unchanged `Gabbro.Body`** -- that they type-check above is the proof. -/
def bedarf : List (String × List String) :=
  [("aggregation -- `count` over a table domain  (§7 RECORDS this one)", ["L03"]),
   ("folds that are not `count` -- `the FIRST x with P`",                ["L29", "L54"]),
   ("bounded reachability -- `place reaches place via field`",
      ["L04", "L05", "L09", "L15", "L16"])]

def summe (l : List (String × List String)) : Nat := (l.map (·.2.length)).foldl (· + ·) 0

/-! ## 9. The speech test -- R11, and it found something

    *A guardian nobody has ever seen say no is an ornament.* Three of the means above are
    helpers I wrote, and **a helper that always answers `true` passes every row that uses it
    without a word** -- `W16` exactly, one level down from where this folder usually books it.
    So each is driven in BOTH directions, and `reachesIn` -- which five rows hang on -- gets
    the poison case as well as the clean one.
-/

/-- A four-slot chain: `2 -> 1 -> 0`, and `0` is the root. -/
def wKette : World := fun p =>
  if p = Place.slot "c" 2 "parent" then .present 1
  else if p = Place.slot "c" 1 "parent" then .present 0
  else .absent

/-- The same world with the chain BROKEN: `2` points at itself, so it never reaches `0`. -/
def wSchleife : World := fun p =>
  if p = Place.slot "c" 2 "parent" then .present 2
  else if p = Place.slot "c" 1 "parent" then .present 0
  else .absent

/-- **`reachesIn` says yes when it should.** -/
example : reachesIn wKette "c" "parent" 4 2 0 = true := by decide

/-- **And no when it should -- the half that makes the other half mean anything.** A cycle is
    the shape a broken CDT actually takes, and it is the shape a helper that always answers
    `true` would swallow. -/
example : reachesIn wSchleife "c" "parent" 4 2 0 = false := by decide

/-- **The bound is a real bound, not decoration.** With three steps of budget the chain is
    reached; the cycle is not reached at any budget. *A helper whose bound did nothing would
    pass this line and the one above alike.* -/
example : reachesIn wKette "c" "parent" 1 2 0 = false := by decide

/-- **`countD` counts, and it counts the right ones.** -/
example : countD [0, 1, 2, 3] (fun i => decide (i = 1 ∨ i = 3)) = 2 := by decide
example : countD [0, 1, 2, 3] (fun _ => false) = 0 := by decide

/-- **`firstD` takes the FIRST and not merely SOME** -- the whole content of DEMAND 2. If it
    returned any satisfying element, L29 would be a different obligation: *"the fastpath takes
    A live receiver"*, and the fragment's own note calls that a different program. -/
example : firstD [3, 4, 5, 6] (fun i => decide (i > 3)) = some 4 := by decide
example : firstD [3, 4, 5, 6] (fun i => decide (i > 9)) = none := by decide

/-- **The distinction L44 and L53 rest on, proved rather than asserted:** "never read yet" is
    not zero. It is one `decide` because `Value` derives `DecidableEq`, and that is the point
    -- the model did not have to be talked into it. -/
example : (Value.absent) ≠ Value.int 0 := by decide

/-- **And `notSayable` is empty**, so no row below it can be discharged by accident. -/
theorem notSayable_leer : ¬ notSayable := id

#eval s!"L total                    66"
#eval s!"  not written as a Prop    {summe nichtSagbar}"
#eval s!"  written as a Prop        {66 - summe nichtSagbar}"
#eval s!"demands on the fragment    {bedarf.length}, over {summe bedarf} rows \
(and §7 records ONE of the three)"

end GabbroV.V1
