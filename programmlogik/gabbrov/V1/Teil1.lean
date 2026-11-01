module

public import Gabbro.Body
meta import Gabbro.Body

@[expose] public section



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
    (`FRAGMENTS.md`@708beed:128). All three obligations speak about the PAYLOAD:

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

    *"The two places are written in ONE step."* `FRAGMENTS.md`@708beed:594 says what the
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

    *"The invariant does not hold BETWEEN the two assignments."* `FRAGMENTS.md`@708beed:675 in
    the fragment's own words: *"Ohne ihn zwei Zuweisungen, und die Invariante gilt dazwischen
    nicht."*

    L24 needs to say that no intermediate state exists. **L34 needs to say that one does, and
    what fails in it.** The same missing means, used in opposite directions -- which is why
    the two belong together and why repairing one would repair both.

    The language has since NAMED the region -- `breaking antwortpflicht_paarig { … }`
    (`SYNTAX.md`:882) -- and `Body.lean` carries the constructor `breaking (invariants) (body)`.
    But read what the model does with it: *"A suspension changes no state."* The names travel
    as DATA; no line of the semantics says the invariant is suspended, and `LANGUAGE.md` §8.3.1
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
    not about the cut* -- and it is the cheapest of the ten to act on: it moves a row, it does
    not build anything.

    **And that is not my classification -- it is the grammar's.** `SYNTAX.md`:1074, at the
    `forever` form: ***"`progress` names WHO ends it -- an assumption about the environment,
    with a falsifier. The watchdog IS the falsifier."***

    The ten fragments carry **exactly three** `progress` clauses -- `FRAGMENTS.md`@708beed:887
    (this row), :981 (L46) and :1656 (L66) -- and `PFLICHTEN.md` books **all three as logic
    obligations `L`.** So the misfiling is wider than the two rows that fail to be sayable:
    *the construct that produces all three is documented as an assumption, and the manifest
    books all three as obligations.*

    What separates L66 from these two is not the construct but **the referent of the named
    predicate**: `token_verbraucht` is about the program's own state, `device_completes_or_faults`
    and `client_calls_or_endpoint_revoked` are about the world. `PFLICHTEN.md` draws exactly
    that line in L66's own row -- *"the ALGORITHM's progress measure, not the machine's
    finiteness"* -- and it is the line that decides sayability. **The classification question
    and the sayability question have different answers, and three rows sit where they differ.**
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
end GabbroV.V1
