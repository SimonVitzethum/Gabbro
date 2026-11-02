module


@[expose] public section


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
  simp only [eins, ↓reduceIte]

theorem Sicht.setze_selbst [DecidableEq Ort] (v : Sicht Ort) (x : Ort) (n : Nat) :
    v.setze x n x = n := by
  simp only [setze, ↓reduceIte]

theorem Sicht.setze_anders [DecidableEq Ort] (v : Sicht Ort) {x y : Ort} (n : Nat) (h : y ≠ x) :
    v.setze x n y = v y := by
  simp only [setze, h, ↓reduceIte]

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
  · simp only [beitrag, Sicht.eins, ↓reduceIte, Std.le_refl]
  · exact Nat.le_trans (by simp only [Sicht.eins, ↓reduceIte, Std.le_refl]) (Sicht.verein_rechts _ _ x)

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
  simp only [aufN, ↓reduceIte]

theorem aufN_anders {α : Type} (f : Nat → α) {t u : Nat} (a : α) (h : u ≠ t) :
    aufN f t a u = f u := by
  simp only [aufN, h, ↓reduceIte]

theorem aufO_gleich {α : Type} (f : Ort → α) (x : Ort) (a : α) : aufO f x a x = a := by
  simp only [aufO, ↓reduceIte]

theorem aufO_anders {α : Type} (f : Ort → α) {x y : Ort} (a : α) (h : y ≠ x) :
    aufO f x a y = f y := by
  simp only [aufO, h, ↓reduceIte]

end Maschine
end Gabbro.Grammatik.Speichermodell
