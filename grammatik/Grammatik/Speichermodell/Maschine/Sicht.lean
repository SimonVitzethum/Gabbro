/-
  File:      Grammatik/Speichermodell/Sicht.lean
  Subject:   THE VIEW DISCIPLINE of the weak memory model (Opus agent B, 2026-09-26), and the
             classic litmus shapes as Lean facts about it.

  WHICH MODEL, AND WHY THIS ONE. The emitter lowers every access to an `atomic` through an
  explicit `atomic_*_explicit` call (`emit.rs`, lane 152; `C-SPEICHERMODELL.md` §1c) with
  exactly these orders:
  * a declaration `release` or `acquire`: stores `memory_order_release`, loads
    `memory_order_acquire`, a fetch RMW `memory_order_acq_rel` (`holordnung`), a CAS loop
    release on success and acquire on the load;
  * a declaration `seq`: `memory_order_seq_cst` on both sides;
  * a declaration `relaxed` or NO ordering word: `memory_order_relaxed` on both sides.
  No `atomic_thread_fence`, no `consume` (measured in `C-SPEICHERMODELL.md` §1c). Plain carriers
  are ordinary C objects; the lock primitive `L_nimm`/`L_gib` is a `pthread_mutex`
  (`treiber.rs`), i.e. an acquire at the lock and a release at the unlock.

  For that fragment the model is the TIMESTAMP (view) machine of RC11 WITHOUT promises, as in
  Kang et al., "A promising semantics for relaxed-memory concurrency" (POPL 2017) restricted to
  its promise-free part, and Lahav, Giannarakis, Vafeiadis, "Taming release-acquire
  consistency" (POPL 2016) for the release/acquire half:
  * every location has a HISTORY of messages `⟨ts, wert, sicht⟩`; the timestamps of one
    location are its modification order;
  * every thread has a VIEW (a timestamp per location); a read of `x` may return ANY message of
    `x` at or above the reader's view of `x` -- that is the weakness -- and raises the view;
  * a write picks a FRESH timestamp strictly above the writer's view of `x` (not necessarily
    the largest: two writers may be ordered either way), so a later write may even be placed
    below an earlier one in modification order;
  * an ACQUIRE read joins the message's view into the reader's view; a RELEASE write stores
    the writer's whole view in its message; a relaxed read/write carries only its own
    location;
  * a lock carries a view: taking it joins the lock's view, releasing it joins the thread's.
  `seq_cst` is modelled as release/acquire. That is an OVER-approximation (the model admits
  every RC11 behaviour of a `seq_cst` access and more, e.g. store buffering, `sb_sc_modell`);
  every claim proved over the model therefore holds for the C, and no claim here uses the
  total order of `seq_cst`. What the model does NOT contain: promises, hence no load
  buffering (RC11 forbids it too: `po ∪ rf` is acyclic there), and no out-of-thin-air.

  THE LITMUS FACTS (below, over a small instruction machine built from exactly these
  primitives; the machine of Gabbro, `RufSchrittW`, MaschineW.lean, uses the same ones):
  * `mp_ra_verboten`   -- message passing with a release store and an acquire load: the
                          outcome "flag seen, data not" is FORBIDDEN;
  * `mp_rlx_erlaubt`   -- the same shape all relaxed: that outcome is REACHABLE (non-SC);
  * `sb_erlaubt`       -- store buffering, all release/acquire: both reads 0 is REACHABLE
                          (non-SC; RC11 allows it for release/acquire);
  * `sb_sc_verboten`   -- the same outcome is NOT reachable on the SC machine
                          (`LSchrittSC`: reads take the newest, writes append) -- the weak
                          machine is strictly weaker than SC;
  * `corr_verboten`    -- coherence read-read: after reading the second of two writes to one
                          location, a thread never reads the first.
-/

namespace Gabbro.Grammatik.Speichermodell

/-! ## 1. The primitives -/

/-- **The memory orders of the fragment.** `entspannt` is `memory_order_relaxed` (and every
    plain access); `freigabe` is a release store, an acquire load, an `acq_rel` RMW -- and
    `seq_cst`, modelled as release/acquire (an over-approximation, see the header). -/
inductive Ordnung where
  | entspannt
  | freigabe
  deriving DecidableEq, Repr

/-- A view: one timestamp per location. -/
def Sicht (Ort : Type) := Ort → Nat

section Prim

variable {Ort Wert : Type}

/-- The empty view. -/
def Sicht.null : Sicht Ort := fun _ => 0

/-- The join of two views. -/
def Sicht.verein (a b : Sicht Ort) : Sicht Ort := fun x => max (a x) (b x)

/-- The view that knows one location at one timestamp. -/
def Sicht.eins [DecidableEq Ort] (x : Ort) (n : Nat) : Sicht Ort := fun y => if y = x then n else 0

/-- A view with one location set. -/
def Sicht.setze [DecidableEq Ort] (v : Sicht Ort) (x : Ort) (n : Nat) : Sicht Ort :=
  fun y => if y = x then n else v y

theorem Sicht.verein_links (a b : Sicht Ort) (x : Ort) : a x ≤ (a.verein b) x :=
  Nat.le_max_left _ _

theorem Sicht.verein_rechts (a b : Sicht Ort) (x : Ort) : b x ≤ (a.verein b) x :=
  Nat.le_max_right _ _

theorem Sicht.eins_selbst [DecidableEq Ort] (x : Ort) (n : Nat) : Sicht.eins x n x = n := by
  simp [Sicht.eins]

theorem Sicht.setze_selbst [DecidableEq Ort] (v : Sicht Ort) (x : Ort) (n : Nat) :
    v.setze x n x = n := by
  simp [Sicht.setze]

theorem Sicht.setze_anders [DecidableEq Ort] (v : Sicht Ort) {x y : Ort} (n : Nat) (h : y ≠ x) :
    v.setze x n y = v y := by
  simp [Sicht.setze, h]

/-- **A message** of one location: its timestamp (the position in modification order), the
    value, and the view it carries (the writer's view for a release write, only its own
    location for a relaxed one). -/
structure Nachricht (Ort Wert : Type) where
  ts : Nat
  wert : Wert
  sicht : Sicht Ort

/-- What a read of message `m` at `x` in order `o` adds to the reader's view: its own
    timestamp, and for an acquire read the message's whole view. -/
def beitrag [DecidableEq Ort] (o : Ordnung) (x : Ort) (m : Nachricht Ort Wert) : Sicht Ort :=
  match o with
  | .entspannt => Sicht.eins x m.ts
  | .freigabe => m.sicht.verein (Sicht.eins x m.ts)

theorem beitrag_selbst [DecidableEq Ort] (o : Ordnung) (x : Ort) (m : Nachricht Ort Wert) :
    m.ts ≤ beitrag o x m x := by
  cases o
  · simp [beitrag, Sicht.eins]
  · exact Nat.le_trans (by simp [Sicht.eins]) (Sicht.verein_rechts _ _ x)

/-- The message a write of `w` at `x` with timestamp `ts` in order `o` by a writer whose view
    is `v` creates. -/
def nachricht [DecidableEq Ort] (o : Ordnung) (v : Sicht Ort) (x : Ort) (ts : Nat) (w : Wert) :
    Nachricht Ort Wert :=
  ⟨ts, w, match o with
    | .entspannt => Sicht.eins x ts
    | .freigabe => v.setze x ts⟩

/-- A read by a thread with view `v` may return message `m` of `x`: it is in the history, at
    or above the view (THE weakness: not necessarily the newest). -/
def Lesbar (hist : Ort → List (Nachricht Ort Wert)) (v : Sicht Ort) (x : Ort)
    (m : Nachricht Ort Wert) : Prop :=
  m ∈ hist x ∧ v x ≤ m.ts

/-- A write by a thread with view `v` may take timestamp `ts` at `x`: strictly above the view,
    and not in use. -/
def Frisch (hist : Ort → List (Nachricht Ort Wert)) (v : Sicht Ort) (x : Ort) (ts : Nat) :
    Prop :=
  v x < ts ∧ ∀ m ∈ hist x, m.ts ≠ ts

end Prim

/-! ## 2. A small instruction machine over the primitives (for the litmus shapes) -/

/-- One instruction: a write of a constant, or a read into a register. -/
inductive Befehl (Ort : Type) where
  | schreib (x : Ort) (w : Int) (o : Ordnung)
  | lies (x : Ort) (r : Nat) (o : Ordnung)

/-- The state: per thread a program counter, registers and a view; per location a history. -/
structure LZustand (Ort : Type) where
  pc : Nat → Nat
  reg : Nat → Nat → Int
  hist : Ort → List (Nachricht Ort Int)
  sicht : Nat → Sicht Ort

/-- The start: every location holds its initial message `⟨0, 0, ∅⟩`, every view is empty. -/
def LZustand.start (Ort : Type) : LZustand Ort :=
  ⟨fun _ => 0, fun _ _ => 0, fun _ => [⟨0, 0, Sicht.null⟩], fun _ => Sicht.null⟩

section Maschine

variable {Ort : Type} [DecidableEq Ort]

/-- Point update of a function on `Nat`. -/
def aufN {α : Type} (f : Nat → α) (t : Nat) (a : α) : Nat → α := fun u => if u = t then a else f u

/-- Point update of a function on locations. -/
def aufO {α : Type} (f : Ort → α) (x : Ort) (a : α) : Ort → α := fun y => if y = x then a else f y

/-- The state after thread `t` wrote `w` at `x` with timestamp `ts` in order `o`. -/
def LZustand.nachSchreib (Z : LZustand Ort) (t : Nat) (x : Ort) (w : Int) (o : Ordnung)
    (ts : Nat) : LZustand Ort :=
  { Z with pc := aufN Z.pc t (Z.pc t + 1)
           hist := aufO Z.hist x (nachricht o (Z.sicht t) x ts w :: Z.hist x)
           sicht := aufN Z.sicht t ((Z.sicht t).setze x ts) }

/-- The state after thread `t` read message `m` of `x` into register `r` in order `o`. -/
def LZustand.nachLies (Z : LZustand Ort) (t : Nat) (x : Ort) (r : Nat) (o : Ordnung)
    (m : Nachricht Ort Int) : LZustand Ort :=
  { Z with pc := aufN Z.pc t (Z.pc t + 1)
           reg := aufN Z.reg t (aufN (Z.reg t) r m.wert)
           sicht := aufN Z.sicht t ((Z.sicht t).verein (beitrag o x m)) }

/-- **The weak step**: a write at a fresh timestamp above the writer's view, or a read of any
    message at or above the reader's view. -/
inductive LSchritt (prog : Nat → List (Befehl Ort)) : LZustand Ort → LZustand Ort → Prop
  | schreib (Z : LZustand Ort) (t : Nat) (x : Ort) (w : Int) (o : Ordnung) (ts : Nat)
      (hb : (prog t)[Z.pc t]? = some (.schreib x w o)) (hf : Frisch Z.hist (Z.sicht t) x ts) :
      LSchritt prog Z (Z.nachSchreib t x w o ts)
  | lies (Z : LZustand Ort) (t : Nat) (x : Ort) (r : Nat) (o : Ordnung) (m : Nachricht Ort Int)
      (hb : (prog t)[Z.pc t]? = some (.lies x r o)) (hl : Lesbar Z.hist (Z.sicht t) x m) :
      LSchritt prog Z (Z.nachLies t x r o m)

/-- **The SC step** (for comparison): a write appends (its timestamp is above every message of
    `x`), a read takes the newest message. Every SC step is a weak step (`lSchrittSC_schwach`). -/
inductive LSchrittSC (prog : Nat → List (Befehl Ort)) : LZustand Ort → LZustand Ort → Prop
  | schreib (Z : LZustand Ort) (t : Nat) (x : Ort) (w : Int) (o : Ordnung) (ts : Nat)
      (hb : (prog t)[Z.pc t]? = some (.schreib x w o)) (hf : Frisch Z.hist (Z.sicht t) x ts)
      (hoben : ∀ m ∈ Z.hist x, m.ts < ts) :
      LSchrittSC prog Z (Z.nachSchreib t x w o ts)
  | lies (Z : LZustand Ort) (t : Nat) (x : Ort) (r : Nat) (o : Ordnung) (m : Nachricht Ort Int)
      (hb : (prog t)[Z.pc t]? = some (.lies x r o)) (hl : Lesbar Z.hist (Z.sicht t) x m)
      (hoben : ∀ m' ∈ Z.hist x, m'.ts ≤ m.ts) :
      LSchrittSC prog Z (Z.nachLies t x r o m)

theorem lSchrittSC_schwach {prog : Nat → List (Befehl Ort)} {Z Z' : LZustand Ort}
    (h : LSchrittSC prog Z Z') : LSchritt prog Z Z' := by
  cases h with
  | schreib t x w o ts hb hf _ => exact .schreib _ t x w o ts hb hf
  | lies t x r o m hb hl _ => exact .lies _ t x r o m hb hl

/-- Reachable states of a step relation. -/
inductive LErreichbar (S : LZustand Ort → LZustand Ort → Prop) : LZustand Ort → Prop
  | start : LErreichbar S (LZustand.start Ort)
  | schritt {Z Z' : LZustand Ort} : LErreichbar S Z → S Z Z' → LErreichbar S Z'

theorem aufN_gleich {α : Type} (f : Nat → α) (t : Nat) (a : α) : aufN f t a t = a := by
  simp [aufN]

theorem aufN_anders {α : Type} (f : Nat → α) {t u : Nat} (a : α) (h : u ≠ t) :
    aufN f t a u = f u := by
  simp [aufN, h]

theorem aufO_gleich {α : Type} (f : Ort → α) (x : Ort) (a : α) : aufO f x a x = a := by
  simp [aufO]

theorem aufO_anders {α : Type} (f : Ort → α) {x y : Ort} (a : α) (h : y ≠ x) :
    aufO f x a y = f y := by
  simp [aufO, h]

end Maschine

/-! ## 3. The two locations of the litmus shapes -/

inductive LOrt where
  | x
  | y
  deriving DecidableEq, Repr

open Befehl LOrt Ordnung

/-- A lookup in a two-thread program: thread 0 runs `p0`, thread 1 `p1`, every other thread
    nothing. -/
def zwei (p0 p1 : List (Befehl LOrt)) : Nat → List (Befehl LOrt)
  | 0 => p0
  | 1 => p1
  | _ => []

theorem zwei_fall {p0 p1 : List (Befehl LOrt)} {t n : Nat} {b : Befehl LOrt}
    (h : (zwei p0 p1 t)[n]? = some b) : (t = 0 ∧ p0[n]? = some b) ∨ (t = 1 ∧ p1[n]? = some b) := by
  match t, h with
  | 0, h => exact Or.inl ⟨rfl, h⟩
  | 1, h => exact Or.inr ⟨rfl, h⟩
  | _ + 2, h => simp [zwei] at h

/-- Lookup in a two-instruction list. -/
theorem zwei_befehle {a b c : Befehl LOrt} {n : Nat} (h : [a, b][n]? = some c) :
    (n = 0 ∧ c = a) ∨ (n = 1 ∧ c = b) := by
  match n, h with
  | 0, h => simp at h; exact Or.inl ⟨rfl, h.symm⟩
  | 1, h => simp at h; exact Or.inr ⟨rfl, h.symm⟩
  | _ + 2, h => simp at h

theorem befehl_schreib_inj {x x' : LOrt} {w w' : Int} {o o' : Ordnung}
    (h : Befehl.schreib x w o = Befehl.schreib x' w' o') : x = x' ∧ w = w' ∧ o = o' := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem befehl_lies_inj {x x' : LOrt} {r r' : Nat} {o o' : Ordnung}
    (h : Befehl.lies x r o = Befehl.lies x' r' o') : x = x' ∧ r = r' ∧ o = o' := by
  cases h; exact ⟨rfl, rfl, rfl⟩

/-! ## 4. Message passing with release/acquire: the stale outcome is FORBIDDEN -/

/-- `MP` with release/acquire. Thread 0: `x := 1` (relaxed); `y := 1` (release). Thread 1:
    `r0 := y` (acquire); `r1 := x` (relaxed). -/
def mpRA : Nat → List (Befehl LOrt) :=
  zwei [schreib .x 1 .entspannt, schreib .y 1 .freigabe] [lies .y 0 .freigabe, lies .x 1 .entspannt]

/-- The invariant of `mpRA`. -/
structure MPInv (Z : LZustand LOrt) : Prop where
  xEins : ∀ m ∈ Z.hist .x, 1 ≤ m.ts → m.wert = 1
  yEins : ∀ m ∈ Z.hist .y, m.wert = 1 → 1 ≤ m.sicht .x
  t0 : 1 ≤ Z.pc 0 → 1 ≤ Z.sicht 0 .x
  r0 : Z.pc 1 = 0 → Z.reg 1 0 = 0
  t1 : 1 ≤ Z.pc 1 → Z.reg 1 0 = 1 → 1 ≤ Z.sicht 1 .x
  r1 : 2 ≤ Z.pc 1 → Z.reg 1 0 = 1 → Z.reg 1 1 = 1

theorem mpInv_start : MPInv (LZustand.start LOrt) where
  xEins m hm h := by simp [LZustand.start] at hm; subst hm; simp at h
  yEins m hm h := by simp [LZustand.start] at hm; subst hm; simp at h
  t0 h := by simp [LZustand.start] at h
  r0 _ := rfl
  t1 h := by simp [LZustand.start] at h
  r1 h := by simp [LZustand.start] at h

theorem mpInv_schritt {Z Z' : LZustand LOrt} (hI : MPInv Z) (hs : LSchritt mpRA Z Z') :
    MPInv Z' := by
  cases hs with
  | schreib t xo w o ts hb hf =>
      rcases zwei_fall hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · rcases zwei_befehle hb with ⟨hpc, hc⟩ | ⟨hpc, hc⟩
        · -- thread 0 writes `x := 1`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
          have hts : 1 ≤ ts := Nat.lt_of_le_of_lt (Nat.zero_le _) hf.1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro m hm _
            simp only [LZustand.nachSchreib, aufO_gleich] at hm
            rcases List.mem_cons.mp hm with rfl | hm
            · rfl
            · exact hI.xEins m hm ‹_›
          · intro m hm h
            simp only [LZustand.nachSchreib, aufO_anders _ _ (show LOrt.y ≠ LOrt.x by decide)] at hm
            exact hI.yEins m hm h
          · intro _
            simp only [LZustand.nachSchreib, aufN_gleich]
            simpa [Sicht.setze] using hts
          · intro h
            simp only [LZustand.nachSchreib, aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)] at h ⊢
            exact hI.r0 h
          · intro h h'
            simp only [LZustand.nachSchreib, aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)] at h h' ⊢
            exact hI.t1 h h'
          · intro h h'
            simp only [LZustand.nachSchreib, aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)] at h h' ⊢
            exact hI.r1 h h'
        · -- thread 0 writes `y := 1` (release)
          obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
          have hx : 1 ≤ Z.sicht 0 .x := hI.t0 (by omega)
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro m hm h
            simp only [LZustand.nachSchreib, aufO_anders _ _ (show LOrt.x ≠ LOrt.y by decide)] at hm
            exact hI.xEins m hm h
          · intro m hm h
            simp only [LZustand.nachSchreib, aufO_gleich] at hm
            rcases List.mem_cons.mp hm with rfl | hm
            · simpa [nachricht, Sicht.setze] using hx
            · exact hI.yEins m hm h
          · intro _
            simpa [LZustand.nachSchreib, aufN, Sicht.setze] using hx
          · intro h
            simp only [LZustand.nachSchreib, aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)] at h ⊢
            exact hI.r0 h
          · intro h h'
            simp only [LZustand.nachSchreib, aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)] at h h' ⊢
            exact hI.t1 h h'
          · intro h h'
            simp only [LZustand.nachSchreib, aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)] at h h' ⊢
            exact hI.r1 h h'
      · rcases zwei_befehle hb with ⟨_, hc⟩ | ⟨_, hc⟩ <;> cases hc
  | lies t xo r o m hb hl =>
      rcases zwei_fall hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · rcases zwei_befehle hb with ⟨_, hc⟩ | ⟨_, hc⟩ <;> cases hc
      · rcases zwei_befehle hb with ⟨hpc, hc⟩ | ⟨hpc, hc⟩
        · -- thread 1 reads `y` (acquire) into r0
          obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
          refine ⟨hI.xEins, hI.yEins, ?_, ?_, ?_, ?_⟩
          · intro h
            simp only [LZustand.nachLies, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)] at h ⊢
            exact hI.t0 h
          · intro h
            simp [LZustand.nachLies, aufN] at h
          · intro _ h'
            simp only [LZustand.nachLies, aufN_gleich] at h' ⊢
            have hmy := hl.1
            have h1 : 1 ≤ m.sicht .x := hI.yEins m hmy h'
            exact Nat.le_trans h1 (Nat.le_trans (Sicht.verein_links _ _ LOrt.x)
              (Sicht.verein_rechts _ _ LOrt.x))
          · intro h
            simp [LZustand.nachLies, aufN, hpc] at h
        · -- thread 1 reads `x` (relaxed) into r1
          obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
          refine ⟨hI.xEins, hI.yEins, ?_, ?_, ?_, ?_⟩
          · intro h
            simp only [LZustand.nachLies, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)] at h ⊢
            exact hI.t0 h
          · intro h
            simp [LZustand.nachLies, aufN] at h
          · intro _ h'
            simp only [LZustand.nachLies, aufN_gleich, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)]
              at h' ⊢
            exact Nat.le_trans (hI.t1 (by omega) h') (Sicht.verein_links _ _ LOrt.x)
          · intro _ h'
            simp only [LZustand.nachLies, aufN_gleich, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)]
              at h' ⊢
            have hv := hI.t1 (by omega) h'
            exact hI.xEins m hl.1 (Nat.le_trans hv hl.2)

/-- **MP with release/acquire: FORBIDDEN.** On every reachable state where thread 1 has run
    both reads and saw the flag (`r0 = 1`), it saw the data (`r1 = 1`). -/
theorem mpInv_erreichbar {Z : LZustand LOrt} (h : LErreichbar (LSchritt mpRA) Z) : MPInv Z := by
  induction h with
  | start => exact mpInv_start
  | schritt _ hs ih => exact mpInv_schritt ih hs

theorem mp_ra_verboten {Z : LZustand LOrt} (h : LErreichbar (LSchritt mpRA) Z)
    (hpc : Z.pc 1 = 2) (h0 : Z.reg 1 0 = 1) : Z.reg 1 1 = 1 :=
  (mpInv_erreichbar h).r1 (by omega) h0

/-! ## 5. The same shape all relaxed: the stale outcome is REACHABLE -/

/-- `MP` all relaxed. -/
def mpRlx : Nat → List (Befehl LOrt) :=
  zwei [schreib .x 1 .entspannt, schreib .y 1 .entspannt] [lies .y 0 .entspannt, lies .x 1 .entspannt]

/-- **MP relaxed: the non-SC outcome is reachable.** Thread 1 sees the flag (`r0 = 1`) and
    then the OLD data (`r1 = 0`): the relaxed read of `x` returns the initial message, which
    lies at the reader's view. -/
theorem mp_rlx_erlaubt : ∃ Z : LZustand LOrt, LErreichbar (LSchritt mpRlx) Z ∧
    Z.pc 1 = 2 ∧ Z.reg 1 0 = 1 ∧ Z.reg 1 1 = 0 := by
  let Z0 := LZustand.start LOrt
  let Z1 := Z0.nachSchreib 0 .x 1 .entspannt 1
  let Z2 := Z1.nachSchreib 0 .y 1 .entspannt 1
  let my : Nachricht LOrt Int := nachricht .entspannt (Z1.sicht 0) .y 1 1
  let Z3 := Z2.nachLies 1 .y 0 .entspannt my
  let m0 : Nachricht LOrt Int := ⟨0, 0, Sicht.null⟩
  let Z4 := Z3.nachLies 1 .x 1 .entspannt m0
  have s1 : LSchritt mpRlx Z0 Z1 := LSchritt.schreib Z0 0 .x 1 .entspannt 1 (by rfl)
    ⟨by decide, by simp [Z0, LZustand.start]⟩
  have s2 : LSchritt mpRlx Z1 Z2 := LSchritt.schreib Z1 0 .y 1 .entspannt 1 (by rfl)
    ⟨by simp [Z1, Z0, LZustand.nachSchreib, LZustand.start, aufN, Sicht.setze, Sicht.null],
     by simp [Z1, Z0, LZustand.nachSchreib, LZustand.start, aufO]⟩
  have s3 : LSchritt mpRlx Z2 Z3 := LSchritt.lies Z2 1 .y 0 .entspannt my (by rfl)
    ⟨by simp [Z2, my, LZustand.nachSchreib, aufO],
     by simp [Z2, Z1, Z0, my, LZustand.nachSchreib, LZustand.start, aufN, Sicht.null, nachricht]⟩
  have s4 : LSchritt mpRlx Z3 Z4 := LSchritt.lies Z3 1 .x 1 .entspannt m0 (by rfl)
    ⟨by simp [Z3, Z2, Z1, Z0, m0, LZustand.nachLies, LZustand.nachSchreib, LZustand.start, aufO],
     by simp [Z3, Z2, Z1, Z0, m0, my, LZustand.nachLies, LZustand.nachSchreib, LZustand.start,
       aufN, Sicht.null, Sicht.verein, beitrag, Sicht.eins]⟩
  refine ⟨Z4, .schritt (.schritt (.schritt (.schritt .start s1) s2) s3) s4, ?_, ?_, ?_⟩ <;>
    simp [Z4, Z3, Z2, Z1, Z0, my, m0, LZustand.nachLies, LZustand.nachSchreib, LZustand.start,
      aufN, nachricht]

/-! ## 6. Store buffering: both reads 0 is REACHABLE, even with release/acquire, and NOT on SC -/

/-- `SB` with release stores and acquire loads. Thread 0: `x := 1`; `r0 := y`. Thread 1:
    `y := 1`; `r0 := x`. -/
def sbRA : Nat → List (Befehl LOrt) :=
  zwei [schreib .x 1 .freigabe, lies .y 0 .freigabe] [schreib .y 1 .freigabe, lies .x 0 .freigabe]

/-- **SB: both reads 0 is reachable on the weak machine** (RC11 allows it for release/acquire,
    and the model keeps it for `seq_cst`, where RC11 forbids it: the named over-approximation
    of the header). -/
theorem sb_erlaubt : ∃ Z : LZustand LOrt, LErreichbar (LSchritt sbRA) Z ∧
    Z.pc 0 = 2 ∧ Z.pc 1 = 2 ∧ Z.reg 0 0 = 0 ∧ Z.reg 1 0 = 0 := by
  let Z0 := LZustand.start LOrt
  let Z1 := Z0.nachSchreib 0 .x 1 .freigabe 1
  let Z2 := Z1.nachSchreib 1 .y 1 .freigabe 1
  let m0 : Nachricht LOrt Int := ⟨0, 0, Sicht.null⟩
  let Z3 := Z2.nachLies 0 .y 0 .freigabe m0
  let Z4 := Z3.nachLies 1 .x 0 .freigabe m0
  have s1 : LSchritt sbRA Z0 Z1 := LSchritt.schreib Z0 0 .x 1 .freigabe 1 (by rfl)
    ⟨by decide, by simp [Z0, LZustand.start]⟩
  have s2 : LSchritt sbRA Z1 Z2 := LSchritt.schreib Z1 1 .y 1 .freigabe 1 (by rfl)
    ⟨by simp [Z1, Z0, LZustand.nachSchreib, LZustand.start, aufN, Sicht.null],
     by simp [Z1, Z0, LZustand.nachSchreib, LZustand.start, aufO]⟩
  have s3 : LSchritt sbRA Z2 Z3 := LSchritt.lies Z2 0 .y 0 .freigabe m0 (by rfl)
    ⟨by simp [Z2, Z1, Z0, m0, LZustand.nachSchreib, LZustand.start, aufO],
     by simp [Z2, Z1, Z0, m0, LZustand.nachSchreib, LZustand.start, aufN, Sicht.null,
       Sicht.setze]⟩
  have s4 : LSchritt sbRA Z3 Z4 := LSchritt.lies Z3 1 .x 0 .freigabe m0 (by rfl)
    ⟨by simp [Z3, Z2, Z1, Z0, m0, LZustand.nachLies, LZustand.nachSchreib, LZustand.start, aufO],
     by simp [Z3, Z2, Z1, Z0, m0, LZustand.nachLies, LZustand.nachSchreib, LZustand.start,
       aufN, Sicht.null, Sicht.setze]⟩
  refine ⟨Z4, .schritt (.schritt (.schritt (.schritt .start s1) s2) s3) s4, ?_, ?_, ?_, ?_⟩ <;>
    simp [Z4, Z3, Z2, Z1, Z0, m0, LZustand.nachLies, LZustand.nachSchreib, LZustand.start, aufN]

/-- The invariant of `sbRA` on the SC machine. -/
structure SBInv (Z : LZustand LOrt) : Prop where
  xOben : ∀ m ∈ Z.hist .x, (∀ m' ∈ Z.hist .x, m'.ts ≤ m.ts) → 1 ≤ Z.pc 0 → m.wert = 1
  yOben : ∀ m ∈ Z.hist .y, (∀ m' ∈ Z.hist .y, m'.ts ≤ m.ts) → 1 ≤ Z.pc 1 → m.wert = 1
  r0 : 2 ≤ Z.pc 0 → Z.reg 0 0 = 0 → 2 ≤ Z.pc 1 → Z.reg 1 0 = 1

theorem sbInv_start : SBInv (LZustand.start LOrt) where
  xOben _ _ _ h := by simp [LZustand.start] at h
  yOben _ _ _ h := by simp [LZustand.start] at h
  r0 h := by simp [LZustand.start] at h

/-- The newest message after an appending write is the written one. -/
theorem oben_neu {hist : List (Nachricht LOrt Int)} {n m : Nachricht LOrt Int}
    (hoben : ∀ m' ∈ hist, m'.ts < n.ts) (hm : m ∈ n :: hist)
    (hmax : ∀ m' ∈ n :: hist, m'.ts ≤ m.ts) : m = n := by
  rcases List.mem_cons.mp hm with h | h
  · exact h
  · have h1 := hoben m h
    have h2 := hmax n List.mem_cons_self
    omega

theorem sbInv_schritt {Z Z' : LZustand LOrt} (hI : SBInv Z) (hs : LSchrittSC sbRA Z Z') :
    SBInv Z' := by
  cases hs with
  | schreib t xo w o ts hb hf hoben =>
      rcases zwei_fall hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · rcases zwei_befehle hb with ⟨hpc, hc⟩ | ⟨_, hc⟩
        · obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
          refine ⟨?_, ?_, ?_⟩
          · intro m hm hmax _
            simp only [LZustand.nachSchreib, aufO_gleich] at hm hmax
            rw [oben_neu (n := nachricht .freigabe (Z.sicht 0) .x ts 1) hoben hm hmax]
            rfl
          · intro m hm hmax h
            simp only [LZustand.nachSchreib, aufO_anders _ _ (show LOrt.y ≠ LOrt.x by decide),
              aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)] at hm hmax h
            exact hI.yOben m hm hmax h
          · intro h
            simp [LZustand.nachSchreib, aufN, hpc] at h
        · cases hc
      · rcases zwei_befehle hb with ⟨hpc, hc⟩ | ⟨_, hc⟩
        · obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
          refine ⟨?_, ?_, ?_⟩
          · intro m hm hmax h
            simp only [LZustand.nachSchreib, aufO_anders _ _ (show LOrt.x ≠ LOrt.y by decide),
              aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)] at hm hmax h
            exact hI.xOben m hm hmax h
          · intro m hm hmax _
            simp only [LZustand.nachSchreib, aufO_gleich] at hm hmax
            rw [oben_neu (n := nachricht .freigabe (Z.sicht 1) .y ts 1) hoben hm hmax]
            rfl
          · intro _ _ h
            simp [LZustand.nachSchreib, aufN, hpc] at h
        · cases hc
  | lies t xo r o m hb hl hoben =>
      rcases zwei_fall hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · rcases zwei_befehle hb with ⟨_, hc⟩ | ⟨hpc, hc⟩
        · cases hc
        · -- thread 0 reads the newest `y`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
          refine ⟨?_, ?_, ?_⟩
          · intro m' hm hmax h
            simp only [LZustand.nachLies] at hm hmax h
            exact hI.xOben m' hm hmax (by simp [aufN] at h; omega)
          · intro m' hm hmax h
            simp only [LZustand.nachLies, aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)] at hm hmax h
            exact hI.yOben m' hm hmax h
          · intro _ h0 h1
            simp only [LZustand.nachLies, aufN_gleich, aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)]
              at h0 h1
            have hy := hI.yOben m hl.1 hoben (by omega)
            rw [hy] at h0
            exact absurd h0 (by decide)
      · rcases zwei_befehle hb with ⟨_, hc⟩ | ⟨hpc, hc⟩
        · cases hc
        · -- thread 1 reads the newest `x`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
          refine ⟨?_, ?_, ?_⟩
          · intro m' hm hmax h
            simp only [LZustand.nachLies, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)] at hm hmax h
            exact hI.xOben m' hm hmax h
          · intro m' hm hmax h
            simp only [LZustand.nachLies] at hm hmax h
            exact hI.yOben m' hm hmax (by simp [aufN] at h; omega)
          · intro h2 _ _
            simp only [LZustand.nachLies, aufN_gleich, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)]
              at h2 ⊢
            exact hI.xOben m hl.1 hoben (by omega)

theorem sbInv_erreichbar {Z : LZustand LOrt} (h : LErreichbar (LSchrittSC sbRA) Z) : SBInv Z := by
  induction h with
  | start => exact sbInv_start
  | schritt _ hs ih => exact sbInv_schritt ih hs

/-- **SB on the SC machine: both reads 0 is NOT reachable.** Together with `sb_erlaubt` this
    shows that the weak machine has behaviours the SC machine does not. -/
theorem sb_sc_verboten {Z : LZustand LOrt} (h : LErreichbar (LSchrittSC sbRA) Z)
    (h0 : Z.pc 0 = 2) (h1 : Z.pc 1 = 2) : ¬ (Z.reg 0 0 = 0 ∧ Z.reg 1 0 = 0) := by
  rintro ⟨r0, r1⟩
  have := (sbInv_erreichbar h).r0 (by omega) r0 (by omega)
  rw [r1] at this
  exact absurd this (by decide)

/-- Every SC run is a weak run. -/
theorem lErreichbar_sc_schwach {prog : Nat → List (Befehl LOrt)} {Z : LZustand LOrt}
    (h : LErreichbar (LSchrittSC prog) Z) : LErreichbar (LSchritt prog) Z := by
  induction h with
  | start => exact .start
  | schritt _ hs ih => exact .schritt ih (lSchrittSC_schwach hs)

/-! ## 7. Coherence read-read: FORBIDDEN on the weak machine -/

/-- `CoRR`. Thread 0: `x := 1`; `x := 2` (relaxed). Thread 1: `r0 := x`; `r1 := x` (relaxed). -/
def coRR : Nat → List (Befehl LOrt) :=
  zwei [schreib .x 1 .entspannt, schreib .x 2 .entspannt] [lies .x 0 .entspannt, lies .x 1 .entspannt]

/-- The invariant of `coRR`. -/
structure CoInv (Z : LZustand LOrt) : Prop where
  ordnung : ∀ m ∈ Z.hist .x, m.wert = 1 → ∀ m' ∈ Z.hist .x, m'.wert = 2 → m.ts < m'.ts
  t0 : ∀ m ∈ Z.hist .x, m.wert = 1 → m.ts ≤ Z.sicht 0 .x
  zwei0 : ∀ m ∈ Z.hist .x, m.wert = 2 → 2 ≤ Z.pc 0
  eins0 : ∀ m ∈ Z.hist .x, m.wert = 1 → 1 ≤ Z.pc 0
  gesehen : 1 ≤ Z.pc 1 → Z.reg 1 0 = 2 → ∃ m ∈ Z.hist .x, m.wert = 2
  t1 : 1 ≤ Z.pc 1 → Z.reg 1 0 = 2 → ∀ m ∈ Z.hist .x, m.wert = 1 → m.ts < Z.sicht 1 .x
  r1 : 2 ≤ Z.pc 1 → Z.reg 1 0 = 2 → Z.reg 1 1 ≠ 1

theorem coInv_start : CoInv (LZustand.start LOrt) where
  ordnung m hm h := by simp [LZustand.start] at hm; subst hm; simp at h
  t0 m hm h := by simp [LZustand.start] at hm; subst hm; simp at h
  zwei0 m hm h := by simp [LZustand.start] at hm; subst hm; simp at h
  eins0 m hm h := by simp [LZustand.start] at hm; subst hm; simp at h
  gesehen h := by simp [LZustand.start] at h
  t1 h := by simp [LZustand.start] at h
  r1 h := by simp [LZustand.start] at h

theorem coInv_schritt {Z Z' : LZustand LOrt} (hI : CoInv Z) (hs : LSchritt coRR Z Z') :
    CoInv Z' := by
  cases hs with
  | schreib t xo w o ts hb hf =>
      rcases zwei_fall hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · rcases zwei_befehle hb with ⟨hpc, hc⟩ | ⟨hpc, hc⟩
        · -- `x := 1`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
          have kein2 : ∀ m ∈ Z.hist .x, m.wert ≠ 2 := fun m hm h => by
            have := hI.zwei0 m hm h; omega
          have kein1 : ∀ m ∈ Z.hist .x, m.wert ≠ 1 := fun m hm h => by
            have := hI.eins0 m hm h; omega
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [LZustand.nachSchreib, aufO_gleich, aufN_gleich,
              aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)]
          · intro m hm h1 m' hm' h2
            rcases List.mem_cons.mp hm' with rfl | hm'
            · simp [nachricht] at h2
            · exact absurd h2 (kein2 m' hm')
          · intro m hm h1
            rcases List.mem_cons.mp hm with rfl | hm
            · simp [nachricht, Sicht.setze_selbst]
            · exact absurd h1 (kein1 m hm)
          · intro m hm h2
            rcases List.mem_cons.mp hm with rfl | hm
            · simp [nachricht] at h2
            · exact absurd h2 (kein2 m hm)
          · intro _ _ _; simp [aufN]
          · intro h h'
            obtain ⟨m, hm, h2⟩ := hI.gesehen h h'
            exact absurd h2 (kein2 m hm)
          · intro h h'
            obtain ⟨m, hm, h2⟩ := hI.gesehen h h'
            exact absurd h2 (kein2 m hm)
          · exact hI.r1
        · -- `x := 2`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [LZustand.nachSchreib, aufO_gleich, aufN_gleich,
              aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)]
          · intro m hm h1 m' hm' h2
            rcases List.mem_cons.mp hm with rfl | hm
            · simp [nachricht] at h1
            · rcases List.mem_cons.mp hm' with rfl | hm'
              · have := hI.t0 m hm h1
                have := hf.1
                simp only [nachricht]
                omega
              · exact hI.ordnung m hm h1 m' hm' h2
          · intro m hm h1
            rcases List.mem_cons.mp hm with rfl | hm
            · simp [nachricht] at h1
            · have := hI.t0 m hm h1
              have := hf.1
              rw [Sicht.setze_selbst]
              omega
          · intro _ _ _; simp [aufN, hpc]
          · intro _ _ _; simp [aufN, hpc]
          · intro h h'
            obtain ⟨m, hm, h2⟩ := hI.gesehen h h'
            exact ⟨m, List.mem_cons_of_mem _ hm, h2⟩
          · intro h h' m hm h1
            rcases List.mem_cons.mp hm with rfl | hm
            · simp [nachricht] at h1
            · exact hI.t1 h h' m hm h1
          · exact hI.r1
      · rcases zwei_befehle hb with ⟨_, hc⟩ | ⟨_, hc⟩ <;> cases hc
  | lies t xo r o m hb hl =>
      rcases zwei_fall hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · rcases zwei_befehle hb with ⟨_, hc⟩ | ⟨_, hc⟩ <;> cases hc
      · rcases zwei_befehle hb with ⟨hpc, hc⟩ | ⟨hpc, hc⟩
        · -- `r0 := x`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
          refine ⟨hI.ordnung, hI.t0, hI.zwei0, hI.eins0, ?_, ?_, ?_⟩ <;>
            simp only [LZustand.nachLies, aufN_gleich, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)]
          · intro _ h'
            try simp [aufN] at h'
            exact ⟨m, hl.1, h'⟩
          · intro _ h' m1 hm1 h1
            try simp [aufN] at h'
            have h2 := hI.ordnung m1 hm1 h1 m hl.1 h'
            exact Nat.lt_of_lt_of_le h2 (Nat.le_trans (beitrag_selbst _ _ _)
              (Sicht.verein_rechts _ _ LOrt.x))
          · intro h; simp [aufN, hpc] at h
        · -- `r1 := x`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
          simp only [LZustand.nachLies, aufN_gleich, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)]
          have hpc1 : 1 ≤ Z.pc 1 := by omega
          refine ⟨hI.ordnung, hI.t0, hI.zwei0, hI.eins0, ?_, ?_, ?_⟩
          · intro _ h'
            simp [aufN] at h'
            exact hI.gesehen hpc1 h'
          · intro _ h' m1 hm1 h1
            simp [aufN] at h'
            exact Nat.lt_of_lt_of_le (hI.t1 hpc1 h' m1 hm1 h1) (Sicht.verein_links _ _ LOrt.x)
          · intro _ h' h1
            simp [aufN] at h' h1
            have := hI.t1 hpc1 h' m hl.1 h1
            have := hl.2
            omega

theorem coInv_erreichbar {Z : LZustand LOrt} (h : LErreichbar (LSchritt coRR) Z) : CoInv Z := by
  induction h with
  | start => exact coInv_start
  | schritt _ hs ih => exact coInv_schritt ih hs

/-- **CoRR: FORBIDDEN.** A thread that read the second write (`2`) never reads the first (`1`)
    afterwards -- per-location coherence, from the view alone. -/
theorem corr_verboten {Z : LZustand LOrt} (h : LErreichbar (LSchritt coRR) Z) (hpc : Z.pc 1 = 2)
    (h0 : Z.reg 1 0 = 2) : Z.reg 1 1 ≠ 1 :=
  (coInv_erreichbar h).r1 (by omega) h0

end Gabbro.Grammatik.Speichermodell
