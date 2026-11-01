module

public import Gabbro.Body
meta import Gabbro.Body
public import gabbrov.V1.Teil1

@[expose] public section

set_option autoImplicit false
open Gabbro.Body
namespace GabbroV.V1

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
    exactly one respect, and it is the respect that decides: their measure is outside.**

    **But the CONSTRUCT is the same one at all three sites**, and `SYNTAX.md`:1074 calls that
    construct an assumption about the environment. *So this row is sayable AND arguably
    misfiled, which is why the two questions are kept apart at L42.* -/
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
