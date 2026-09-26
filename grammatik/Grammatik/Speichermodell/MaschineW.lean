/-
  File:      Grammatik/Speichermodell/MaschineW.lean
  Subject:   MACHINE W -- machine G over the WEAK memory of `Sicht.lean` (Opus agent B,
             2026-09-26). Definitions, and `w_aus_g`: every run of G is a run of W.

  WHAT W IS. A state of W is a state `g` of machine G plus the weak memory: a HISTORY of
  messages per carrier (tables and globals, plain and `atomic` alike), a VIEW per thread and a
  view per lock. One step of thread `u`:
  * the thread is PRESENTED a memory `σ`: at every carrier its step READS (a recorded read
    event, `LiestG`), `σ` holds the value of SOME message of that carrier at or above `u`'s
    view (`Lesbar` -- not necessarily the newest: that is the weakness); at every carrier it
    does not read, `σ` is G's memory;
  * machine G takes the step on the presented memory (`RufSchrittG` from `mitSpeicher W.g σ`);
  * every carrier the step WRITES (`SchreibG`: a write event or a changed value) gets a new
    message at a FRESH timestamp strictly above the thread's view (`Frisch`), carrying the new
    value and -- for a release write of a `release`/`acquire`/`seq` atomic -- the thread's view;
    G's memory takes the written carriers from the step and keeps every other one;
  * views: a read raises the view to the message (an acquire read joins the message's view,
    `beitrag`), a lock the step TAKES joins the lock's view (`locksicht`), a write sets the
    view to its timestamp, a lock the step RELEASES joins the thread's final view.
  Plain carriers are modelled like relaxed atomics. For a race-free program that is an
  over-approximation of C11 (a race-free plain read reads the happens-before-latest write,
  which the views keep readable); for a racy one C11 is undefined anyway. The order of an
  atomic is the argument `ord` (the source declaration's; the exporter does not carry it, so
  every theorem about W quantifies over all of them, `relaxed` everywhere included).

  WHY THE WEAK CHOICE SITS AT THE RECORDED READS. What a step of G reads is what it records
  (`OrteInvG`, `schritt_ev`: every read event is a footprint carrier of the acting function);
  race freedom (`RennfreiBis`) is stated over the same records. A step that depended on a
  carrier without recording it would already escape the race leg of G. So "the thread sees an
  old value exactly where it reads" is the reading G already makes, not a new assumption; the
  answers of foreign code (`Orakel.wirkt`, `regLies`, `sichtbar`) stay the oracle's, over the
  presented world, as in G.

  PROVED HERE: `w_aus_g` -- every machine G reaches is the G-part of a machine W reaches (W
  admits every SC behaviour: always write above everything and read the newest). The other
  direction for accepted programs is the DRF theorem, `Speichermodell/DRF.lean`.
-/
import Grammatik.RennfreiVoll
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik

open Speichermodell

variable {D : Deklaration}

/-! ## 1. The state -/

/-- A message of a carrier: timestamp, the memory after the write (only the carrier's own
    component is read), and the view it carries. -/
abbrev NachrichtW (D : Deklaration) := Nachricht (D.Tab ⊕ D.Glob) (Speicher D)

/-- A view over the carriers. -/
abbrev SichtW (D : Deklaration) := Sicht (D.Tab ⊕ D.Glob)

/-- **A state of machine W**: machine G's state and the weak memory. -/
structure RufMaschineW (D : Deklaration) where
  g : RufMaschineG D
  hist : D.Tab ⊕ D.Glob → List (NachrichtW D)
  sicht : Faden → SichtW D
  lsicht : D.Lock → SichtW D

/-- **The start of W** over a start of G: every carrier holds ONE message, the initial memory
    at timestamp 0; every view is empty. -/
def RufStartW (M0 : RufMaschineG D) : RufMaschineW D :=
  ⟨M0, fun _ => [⟨0, M0.speicher, Sicht.null⟩], fun _ => Sicht.null, fun _ => Sicht.null⟩

/-- The order of a carrier: a table and a plain global are relaxed; an `atomic` has the order
    of its declaration (`ord`). -/
def ordVon (ord : D.Glob → Ordnung) : D.Tab ⊕ D.Glob → Ordnung
  | .inl _ => .entspannt
  | .inr g => if D.atomar g then ord g else .entspannt

/-- A machine of G with its shared memory replaced. -/
def mitSpeicher (M : RufMaschineG D) (σ : Speicher D) : RufMaschineG D :=
  { M with speicher := σ }

/-- The carriers a step READS (its recorded read events). -/
def lesenVon (M M' : RufMaschineG D) (u : Faden) : List (D.Tab ⊕ D.Glob) :=
  (zugriffe M M' u).filterMap fun p => if p.2 then none else some p.1

/-- The locks a step TAKES (its `nimmt` events). -/
def genommenVon (M M' : RufMaschineG D) (u : Faden) : List D.Lock :=
  (ereignisse M M' u).filterMap fun e => match e with
    | .nimmt L _ => some L
    | _ => none

/-- The locks a step RELEASES (its `gibt` events). -/
def gegebenVon (M M' : RufMaschineG D) (u : Faden) : List D.Lock :=
  (ereignisse M M' u).filterMap fun e => match e with
    | .gibt L => some L
    | _ => none

/-- The view after the reads of `rs` (message `wahl c` at `c`). -/
def lesesicht (ord : D.Glob → Ordnung) (wahl : D.Tab ⊕ D.Glob → NachrichtW D)
    (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D) : SichtW D :=
  rs.foldr (fun c w => w.verein (beitrag (ordVon ord c) c (wahl c))) v

/-- The view after taking the locks `Ls`. -/
def locksicht (ls : D.Lock → SichtW D) (Ls : List D.Lock) (v : SichtW D) : SichtW D :=
  Ls.foldr (fun L w => w.verein (ls L)) v

/-- The view of thread `u` before its writes: after its reads and the locks it takes. -/
def vorSicht (ord : D.Glob → Ordnung) (W : RufMaschineW D) (u : Faden) (σ : Speicher D)
    (M'' : RufMaschineG D) (wahl : D.Tab ⊕ D.Glob → NachrichtW D) : SichtW D :=
  locksicht W.lsicht (genommenVon (mitSpeicher W.g σ) M'' u)
    (lesesicht ord wahl (lesenVon (mitSpeicher W.g σ) M'' u) (W.sicht u))

/-! ## 2. The step -/

/-- **One step of W, with its witnesses**: the presented memory `σ`, G's step to `M''` on it,
    the message read at every carrier (`wahl`), and the timestamp of every write (`neu`). -/
structure SchrittW (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (W : RufMaschineW D) (u : Faden) (W' : RufMaschineW D) (σ : Speicher D)
    (M'' : RufMaschineG D) (wahl : D.Tab ⊕ D.Glob → NachrichtW D)
    (neu : D.Tab ⊕ D.Glob → Nat) : Prop where
  /-- Machine G steps on the presented memory. -/
  schritt : RufSchrittG P O passes (mitSpeicher W.g σ) u M''
  /-- At a carrier the step reads: SOME message at or above the thread's view. -/
  lies : ∀ c, LiestG (mitSpeicher W.g σ) M'' u c →
    Lesbar W.hist (W.sicht u) c (wahl c) ∧ TraegerGleich σ (wahl c).wert c
  /-- At a carrier the step does not read: G's memory. -/
  ungelesen : ∀ c, ¬ LiestG (mitSpeicher W.g σ) M'' u c → TraegerGleich σ W.g.speicher c
  /-- A write takes a fresh timestamp above the view before the writes. -/
  frisch : ∀ c, SchreibG (mitSpeicher W.g σ) M'' u c →
    Frisch W.hist (vorSicht ord W u σ M'' wahl) c (neu c)
  /-- G's memory: written carriers from the step, the others unchanged. -/
  speicherS : ∀ c, SchreibG (mitSpeicher W.g σ) M'' u c →
    TraegerGleich W'.g.speicher M''.speicher c
  speicherU : ∀ c, ¬ SchreibG (mitSpeicher W.g σ) M'' u c →
    TraegerGleich W'.g.speicher W.g.speicher c
  faeden : W'.g.faeden = M''.faeden
  lauf : W'.g.lauf = M''.lauf
  start : W'.g.start = M''.start
  /-- A written carrier gets its message. -/
  histS : ∀ c, SchreibG (mitSpeicher W.g σ) M'' u c →
    W'.hist c = nachricht (ordVon ord c) (vorSicht ord W u σ M'' wahl) c (neu c) W'.g.speicher
      :: W.hist c
  histU : ∀ c, ¬ SchreibG (mitSpeicher W.g σ) M'' u c → W'.hist c = W.hist c
  /-- The acting thread's view: its write timestamps, else the view before the writes. -/
  sichtS : ∀ c, SchreibG (mitSpeicher W.g σ) M'' u c → W'.sicht u c = neu c
  sichtU : ∀ c, ¬ SchreibG (mitSpeicher W.g σ) M'' u c →
    W'.sicht u c = vorSicht ord W u σ M'' wahl c
  sichtF : ∀ t, t ≠ u → W'.sicht t = W.sicht t
  /-- A released lock joins the thread's final view. -/
  lsicht : ∀ L, W'.lsicht L =
    if L ∈ gegebenVon (mitSpeicher W.g σ) M'' u then (W.lsicht L).verein (W'.sicht u)
    else W.lsicht L

/-- **The step relation of W.** -/
def RufSchrittW (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (W : RufMaschineW D) (u : Faden) (W' : RufMaschineW D) : Prop :=
  ∃ σ M'' wahl neu, SchrittW P O passes ord W u W' σ M'' wahl neu

/-- **The machines W reaches** from `W0`. -/
inductive RufErreichbarW (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (W0 : RufMaschineW D) : RufMaschineW D → Prop where
  | start : RufErreichbarW P O passes ord W0 W0
  | schritt (W W' : RufMaschineW D) (u : Faden) :
      RufErreichbarW P O passes ord W0 W → RufSchrittW P O passes ord W u W' →
        RufErreichbarW P O passes ord W0 W'

/-! ## 3. Views grow -/

section Wachsen

variable {ord : D.Glob → Ordnung}

theorem lesesicht_ge (wahl : D.Tab ⊕ D.Glob → NachrichtW D) :
    ∀ (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D) (x : D.Tab ⊕ D.Glob),
      v x ≤ lesesicht ord wahl rs v x
  | [], _, _ => Nat.le_refl _
  | c :: rs, v, x => Nat.le_trans (lesesicht_ge wahl rs v x) (Sicht.verein_links _ _ x)

/-- A carrier read in the list: the view reaches the message read there. -/
theorem lesesicht_mem (wahl : D.Tab ⊕ D.Glob → NachrichtW D) :
    ∀ (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D) (c : D.Tab ⊕ D.Glob), c ∈ rs →
      ∀ x, beitrag (ordVon ord c) c (wahl c) x ≤ lesesicht ord wahl rs v x
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | c' :: rs, v, c, h, x => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Sicht.verein_rechts _ _ x
      · exact Nat.le_trans (lesesicht_mem wahl rs v c h x) (Sicht.verein_links _ _ x)

/-- The view after reads stays below a bound that bounds the view and every contribution. -/
theorem lesesicht_le (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (T : D.Tab ⊕ D.Glob → Nat) :
    ∀ (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D), (∀ x, v x ≤ T x) →
      (∀ c ∈ rs, ∀ x, beitrag (ordVon ord c) c (wahl c) x ≤ T x) →
      ∀ x, lesesicht ord wahl rs v x ≤ T x
  | [], _, hv, _, x => hv x
  | c :: rs, v, hv, hb, x => by
      show max (lesesicht ord wahl rs v x) (beitrag (ordVon ord c) c (wahl c) x) ≤ T x
      exact Nat.max_le.mpr ⟨lesesicht_le wahl T rs v hv (fun c' h => hb c' (List.mem_cons_of_mem _ h)) x,
        hb c List.mem_cons_self x⟩

theorem locksicht_ge (ls : D.Lock → SichtW D) :
    ∀ (Ls : List D.Lock) (v : SichtW D) (x : D.Tab ⊕ D.Glob), v x ≤ locksicht ls Ls v x
  | [], _, _ => Nat.le_refl _
  | _ :: Ls, v, x => Nat.le_trans (locksicht_ge ls Ls v x) (Sicht.verein_links _ _ x)

theorem locksicht_mem (ls : D.Lock → SichtW D) :
    ∀ (Ls : List D.Lock) (v : SichtW D) (L : D.Lock), L ∈ Ls →
      ∀ x, ls L x ≤ locksicht ls Ls v x
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | L' :: Ls, v, L, h, x => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Sicht.verein_rechts _ _ x
      · exact Nat.le_trans (locksicht_mem ls Ls v L h x) (Sicht.verein_links _ _ x)

theorem locksicht_le (ls : D.Lock → SichtW D) (T : D.Tab ⊕ D.Glob → Nat) :
    ∀ (Ls : List D.Lock) (v : SichtW D), (∀ x, v x ≤ T x) → (∀ L ∈ Ls, ∀ x, ls L x ≤ T x) →
      ∀ x, locksicht ls Ls v x ≤ T x
  | [], _, hv, _, x => hv x
  | L :: Ls, v, hv, hL, x => by
      show max (locksicht ls Ls v x) (ls L x) ≤ T x
      exact Nat.max_le.mpr ⟨locksicht_le ls T Ls v hv (fun L' h => hL L' (List.mem_cons_of_mem _ h)) x,
        hL L List.mem_cons_self x⟩

/-- The view before the writes is at least the old view. -/
theorem vorSicht_ge (W : RufMaschineW D) (u : Faden) (σ : Speicher D) (M'' : RufMaschineG D)
    (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (x : D.Tab ⊕ D.Glob) :
    W.sicht u x ≤ vorSicht ord W u σ M'' wahl x :=
  Nat.le_trans (lesesicht_ge wahl _ _ x) (locksicht_ge _ _ _ x)

/-- **Views only grow**: the acting thread's view after a step is at least the one before. -/
theorem sicht_waechst {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    (t : Faden) (x : D.Tab ⊕ D.Glob) : W.sicht t x ≤ W'.sicht t x := by
  by_cases ht : t = u
  · subst ht
    have hv := vorSicht_ge (ord := ord) W t σ M'' wahl x
    by_cases hw : SchreibG (mitSpeicher W.g σ) M'' t x
    · rw [h.sichtS x hw]
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt hv (h.frisch x hw).1)
    · rw [h.sichtU x hw]; exact hv
  · rw [h.sichtF t ht]; exact Nat.le_refl _

theorem lsicht_waechst {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    (L : D.Lock) (x : D.Tab ⊕ D.Glob) : W.lsicht L x ≤ W'.lsicht L x := by
  rw [h.lsicht L]
  split
  · exact Sicht.verein_links _ _ x
  · exact Nat.le_refl _

end Wachsen

/-! ## 4. Memories agreeing on every carrier are equal -/

theorem speicher_ext {s s' : Speicher D} (h : ∀ c, TraegerGleich s s' c) : s = s' := by
  cases s with
  | mk sl gl =>
    cases s' with
    | mk sl' gl' =>
      have e1 : sl = sl' := funext fun t => h (.inl t)
      have e2 : gl = gl' := funext fun g => h (.inr g)
      subst e1 e2
      rfl

theorem mitSpeicher_selbst (M : RufMaschineG D) : mitSpeicher M M.speicher = M := by
  cases M; rfl

/-- Not written: the step leaves the carrier as it was. -/
theorem traegerGleich_of_nicht_schreib {M M' : RufMaschineG D} {u : Faden} {c : D.Tab ⊕ D.Glob}
    (h : ¬ SchreibG M M' u c) : TraegerGleich M'.speicher M.speicher c :=
  Classical.byContradiction fun hn => h (Or.inr hn)

theorem traegerGleich_trans {s s' s'' : Speicher D} {c : D.Tab ⊕ D.Glob}
    (h1 : TraegerGleich s s' c) (h2 : TraegerGleich s' s'' c) : TraegerGleich s s'' c := by
  cases c
  · exact h1.trans h2
  · exact h1.trans h2

theorem traegerGleich_symm {s s' : Speicher D} {c : D.Tab ⊕ D.Glob}
    (h : TraegerGleich s s' c) : TraegerGleich s' s c := by
  cases c
  · exact h.symm
  · exact h.symm

/-- **A step of W whose presented memory is G's own is a step of G**, and its G-part is G's
    successor. -/
theorem schrittW_g {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
    {W W' : RufMaschineW D} {u : Faden} {M'' : RufMaschineG D}
    {wahl : D.Tab ⊕ D.Glob → NachrichtW D} {neu : D.Tab ⊕ D.Glob → Nat}
    (h : SchrittW P O passes ord W u W' W.g.speicher M'' wahl neu) :
    RufSchrittG P O passes W.g u M'' ∧ W'.g = M'' := by
  have hs := h.schritt
  rw [mitSpeicher_selbst] at hs
  refine ⟨hs, ?_⟩
  have esp : W'.g.speicher = M''.speicher := speicher_ext fun c => by
    by_cases hw : SchreibG (mitSpeicher W.g W.g.speicher) M'' u c
    · exact h.speicherS c hw
    · have h1 := h.speicherU c hw
      have h2 := traegerGleich_of_nicht_schreib hw
      rw [mitSpeicher_selbst] at h2
      exact traegerGleich_trans h1 (traegerGleich_symm h2)
  have e1 := h.faeden
  have e2 := h.lauf
  have e3 := h.start
  cases hW' : W'.g with
  | mk sp fa la st =>
    cases M'' with
    | mk sp'' fa'' la'' st'' =>
      rw [hW'] at esp e1 e2 e3
      simp only at esp e1 e2 e3
      subst esp e1 e2 e3
      rfl

/-! ## 5. Every run of G is a run of W (`w_aus_g`) -/

section Einbettung

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}

/-- **The SC shape of a W state**: a bound `T` per carrier that a message carrying G's value
    reaches, and that bounds every timestamp and every view. Always writing at `T + 1` and
    reading the message at `T` keeps it. -/
def SCForm (W : RufMaschineW D) : Prop :=
  ∃ T : D.Tab ⊕ D.Glob → Nat, ∀ c,
    (∃ m ∈ W.hist c, m.ts = T c ∧ TraegerGleich W.g.speicher m.wert c) ∧
    (∀ m ∈ W.hist c, m.ts ≤ T c) ∧ (∀ t, W.sicht t c ≤ T c) ∧ (∀ L, W.lsicht L c ≤ T c) ∧
    (∀ x, ∀ m ∈ W.hist x, m.sicht c ≤ T c)

theorem scForm_start (M0 : RufMaschineG D) : SCForm (RufStartW M0) :=
  ⟨fun _ => 0, fun c => ⟨⟨⟨0, M0.speicher, Sicht.null⟩, List.mem_singleton_self _, rfl,
    traegerGleich_refl _ c⟩, fun m hm => by rw [List.mem_singleton.mp hm]; exact Nat.le_refl 0,
    fun _ => Nat.le_refl _,
    fun _ => Nat.le_refl _, fun _ m hm => by rw [List.mem_singleton.mp hm]; exact Nat.le_refl _⟩⟩

theorem beitrag_le {T : D.Tab ⊕ D.Glob → Nat} {o : Ordnung} {c : D.Tab ⊕ D.Glob} {m : NachrichtW D}
    (hts : m.ts ≤ T c) (hs : ∀ x, m.sicht x ≤ T x) (x : D.Tab ⊕ D.Glob) : beitrag o c m x ≤ T x := by
  have heins : Sicht.eins c m.ts x ≤ T x := by
    unfold Sicht.eins
    split
    · rename_i h; subst h; exact hts
    · exact Nat.zero_le _
  cases o
  · exact heins
  · exact Nat.max_le.mpr ⟨hs x, heins⟩

open Classical in
/-- **One G step lifts to a W step** that keeps the SC shape. -/
theorem schrittW_aus_g {W : RufMaschineW D} (hF : SCForm W) {u : Faden} {M' : RufMaschineG D}
    (hs : RufSchrittG P O passes W.g u M') :
    ∃ W', RufSchrittW P O passes ord W u W' ∧ W'.g = M' ∧ SCForm W' := by
  obtain ⟨T, hT⟩ := hF
  let wahl : D.Tab ⊕ D.Glob → NachrichtW D := fun c => Classical.choose (hT c).1
  have hwahl : ∀ c, wahl c ∈ W.hist c ∧ (wahl c).ts = T c ∧
      TraegerGleich W.g.speicher (wahl c).wert c := fun c => by
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (hT c).1
    exact ⟨h1, h2, h3⟩
  let Mσ := mitSpeicher W.g W.g.speicher
  have eMσ : Mσ = W.g := mitSpeicher_selbst W.g
  let v := vorSicht ord W u W.g.speicher M' wahl
  have hvT : ∀ x, v x ≤ T x := by
    apply locksicht_le _ T _ _ _ (fun L _ x => (hT x).2.2.2.1 L)
    apply lesesicht_le wahl T _ _ (fun x => (hT x).2.2.1 u)
    intro c _ x
    exact beitrag_le (Nat.le_of_eq (hwahl c).2.1) (fun y => (hT y).2.2.2.2 c (wahl c) (hwahl c).1) x
  let neu : D.Tab ⊕ D.Glob → Nat := fun c => T c + 1
  let schreibt : D.Tab ⊕ D.Glob → Prop := fun c => SchreibG Mσ M' u c
  let T' : D.Tab ⊕ D.Glob → Nat := fun c => if schreibt c then T c + 1 else T c
  have hTT' : ∀ c, T c ≤ T' c := fun c => by
    show T c ≤ (if schreibt c then T c + 1 else T c)
    split <;> omega
  let s' : SichtW D := fun c => if schreibt c then neu c else v c
  let W' : RufMaschineW D :=
    ⟨M',
     fun c => if schreibt c then nachricht (ordVon ord c) v c (neu c) M'.speicher :: W.hist c
       else W.hist c,
     fun t => if t = u then s' else W.sicht t,
     fun L => if L ∈ gegebenVon Mσ M' u then (W.lsicht L).verein s' else W.lsicht L⟩
  have hs' : RufSchrittG P O passes Mσ u M' := by rw [eMσ]; exact hs
  have hs'T : ∀ x, s' x ≤ T' x := fun x => by
    show (if schreibt x then neu x else v x) ≤ (if schreibt x then T x + 1 else T x)
    split
    · exact Nat.le_refl _
    · exact hvT x
  refine ⟨W', ⟨W.g.speicher, M', wahl, neu, ?_⟩, rfl, ?_⟩
  · refine {
      schritt := hs'
      lies := fun c _ => ⟨⟨(hwahl c).1, by rw [(hwahl c).2.1]; exact (hT c).2.2.1 u⟩,
        (hwahl c).2.2⟩
      ungelesen := fun c _ => traegerGleich_refl _ c
      frisch := fun c _ => ⟨Nat.lt_succ_of_le (hvT c), fun m hm he => by
        have := (hT c).2.1 m hm
        show False
        simp only [neu] at he
        omega⟩
      speicherS := fun c _ => traegerGleich_refl _ c
      speicherU := fun c hw => by
        have h := traegerGleich_of_nicht_schreib hw
        exact h
      faeden := rfl
      lauf := rfl
      start := rfl
      histS := fun c hw => by
        show (if schreibt c then _ else _) = _
        rw [if_pos hw]
      histU := fun c hw => by
        show (if schreibt c then _ else _) = _
        rw [if_neg hw]
      sichtS := fun c hw => by
        show (if u = u then s' else W.sicht u) c = neu c
        rw [if_pos rfl]
        show (if schreibt c then neu c else v c) = neu c
        rw [if_pos hw]
      sichtU := fun c hw => by
        show (if u = u then s' else W.sicht u) c = v c
        rw [if_pos rfl]
        show (if schreibt c then neu c else v c) = v c
        rw [if_neg hw]
      sichtF := fun t ht => by
        show (if t = u then s' else W.sicht t) = W.sicht t
        rw [if_neg ht]
      lsicht := fun L => by
        show (if L ∈ gegebenVon Mσ M' u then (W.lsicht L).verein s' else W.lsicht L) =
          (if L ∈ gegebenVon Mσ M' u then
            (W.lsicht L).verein (if u = u then s' else W.sicht u) else W.lsicht L)
        rw [if_pos (rfl : u = u)] }
  · refine ⟨T', fun c => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · -- the message at the bound carries G's value
      by_cases hw : schreibt c
      · refine ⟨nachricht (ordVon ord c) v c (neu c) M'.speicher, ?_, ?_, traegerGleich_refl _ c⟩
        · show _ ∈ (if schreibt c then _ else _)
          rw [if_pos hw]; exact List.mem_cons_self
        · show neu c = (if schreibt c then T c + 1 else T c)
          rw [if_pos hw]
      · refine ⟨wahl c, ?_, ?_, ?_⟩
        · show _ ∈ (if schreibt c then _ else _)
          rw [if_neg hw]; exact (hwahl c).1
        · show (wahl c).ts = (if schreibt c then T c + 1 else T c)
          rw [if_neg hw]; exact (hwahl c).2.1
        · have h1 : TraegerGleich M'.speicher Mσ.speicher c := traegerGleich_of_nicht_schreib hw
          rw [eMσ] at h1
          exact traegerGleich_trans h1 (hwahl c).2.2
    · intro m hm
      change m ∈ (if schreibt c then _ else _) at hm
      by_cases hw : schreibt c
      · rw [if_pos hw] at hm
        rcases List.mem_cons.mp hm with rfl | hm
        · show neu c ≤ (if schreibt c then T c + 1 else T c)
          rw [if_pos hw]
          exact Nat.le_refl _
        · exact Nat.le_trans ((hT c).2.1 m hm) (hTT' c)
      · rw [if_neg hw] at hm
        exact Nat.le_trans ((hT c).2.1 m hm) (hTT' c)
    · intro t
      show (if t = u then s' else W.sicht t) c ≤ T' c
      split
      · exact hs'T c
      · exact Nat.le_trans ((hT c).2.2.1 t) (hTT' c)
    · intro L
      show (if L ∈ gegebenVon Mσ M' u then (W.lsicht L).verein s' else W.lsicht L) c ≤ T' c
      split
      · exact Nat.max_le.mpr ⟨Nat.le_trans ((hT c).2.2.2.1 L) (hTT' c), hs'T c⟩
      · exact Nat.le_trans ((hT c).2.2.2.1 L) (hTT' c)
    · intro x m hm
      change m ∈ (if schreibt x then _ else _) at hm
      by_cases hw : schreibt x
      · rw [if_pos hw] at hm
        rcases List.mem_cons.mp hm with rfl | hm
        · show (match ordVon ord x with
            | .entspannt => Sicht.eins x (neu x)
            | .freigabe => v.setze x (neu x)) c ≤ T' c
          have hx : neu x ≤ T' x := by
            show neu x ≤ (if schreibt x then T x + 1 else T x)
            rw [if_pos hw]
            exact Nat.le_refl _
          cases ordVon ord x
          · show (if c = x then neu x else 0) ≤ T' c
            split
            · rename_i h; subst h; exact hx
            · exact Nat.zero_le _
          · show (if c = x then neu x else v c) ≤ T' c
            split
            · rename_i h; subst h; exact hx
            · exact Nat.le_trans (hvT c) (hTT' c)
        · exact Nat.le_trans ((hT c).2.2.2.2 x m hm) (hTT' c)
      · rw [if_neg hw] at hm
        exact Nat.le_trans ((hT c).2.2.2.2 x m hm) (hTT' c)

/-- **Every run of G is a run of W** (for every choice of orders): W adds behaviour, it
    removes none. -/
theorem w_aus_g {M0 M : RufMaschineG D} (hr : RufErreichbarG P O passes M0 M) :
    ∃ W, RufErreichbarW P O passes ord (RufStartW M0) W ∧ W.g = M ∧ SCForm W := by
  induction hr with
  | start => exact ⟨RufStartW M0, .start, rfl, scForm_start M0⟩
  | schritt M M' u _ hs ih =>
      obtain ⟨W, hW, rfl, hF⟩ := ih
      obtain ⟨W', hstep, hg, hF'⟩ := schrittW_aus_g (ord := ord) hF hs
      exact ⟨W', .schritt W W' u hW hstep, hg, hF'⟩

/-- **Building a W step with ANY admissible reads** (for witnesses): given a G step on a
    presented memory that agrees with G's memory off the reads and with the chosen messages at
    the reads, and a bound `T` on every timestamp and view, W takes the step, writing at
    `T + 1`. -/
theorem schrittW_bau {W : RufMaschineW D} {σ : Speicher D} {u : Faden} {M'' : RufMaschineG D}
    (hs : RufSchrittG P O passes (mitSpeicher W.g σ) u M'')
    (wahl : D.Tab ⊕ D.Glob → NachrichtW D)
    (hl : ∀ c, LiestG (mitSpeicher W.g σ) M'' u c →
      Lesbar W.hist (W.sicht u) c (wahl c) ∧ TraegerGleich σ (wahl c).wert c)
    (hu : ∀ c, ¬ LiestG (mitSpeicher W.g σ) M'' u c → TraegerGleich σ W.g.speicher c)
    (T : D.Tab ⊕ D.Glob → Nat)
    (hT : ∀ c, (∀ m ∈ W.hist c, m.ts ≤ T c) ∧ (∀ t, W.sicht t c ≤ T c) ∧
      (∀ L, W.lsicht L c ≤ T c) ∧ (∀ x, ∀ m ∈ W.hist x, m.sicht c ≤ T c))
    (hwahl : ∀ c, wahl c ∈ W.hist c) :
    ∃ W', SchrittW P O passes ord W u W' σ M'' wahl (fun c => T c + 1) ∧
      (∀ c, SchreibG (mitSpeicher W.g σ) M'' u c → TraegerGleich W'.g.speicher M''.speicher c) ∧
      (∀ c, ¬ SchreibG (mitSpeicher W.g σ) M'' u c →
        TraegerGleich W'.g.speicher W.g.speicher c) := by
  classical
  let Mσ := mitSpeicher W.g σ
  let v := vorSicht ord W u σ M'' wahl
  have hvT : ∀ x, v x ≤ T x := by
    apply locksicht_le _ T _ _ _ (fun L _ x => (hT x).2.2.1 L)
    apply lesesicht_le wahl T _ _ (fun x => (hT x).2.1 u)
    intro c _ x
    exact beitrag_le ((hT c).1 _ (hwahl c)) (fun y => (hT y).2.2.2 c (wahl c) (hwahl c)) x
  let schreibt : D.Tab ⊕ D.Glob → Prop := fun c => SchreibG Mσ M'' u c
  let sp' : Speicher D :=
    ⟨fun t => if schreibt (.inl t) then M''.speicher.slots t else W.g.speicher.slots t,
     fun g => if schreibt (.inr g) then M''.speicher.globs g else W.g.speicher.globs g⟩
  have hsp1 : ∀ c, schreibt c → TraegerGleich sp' M''.speicher c := by
    intro c hc
    cases c with
    | inl t => show (if schreibt (.inl t) then _ else _) = _; rw [if_pos hc]
    | inr g => show (if schreibt (.inr g) then _ else _) = _; rw [if_pos hc]
  have hsp2 : ∀ c, ¬ schreibt c → TraegerGleich sp' W.g.speicher c := by
    intro c hc
    cases c with
    | inl t => show (if schreibt (.inl t) then _ else _) = _; rw [if_neg hc]
    | inr g => show (if schreibt (.inr g) then _ else _) = _; rw [if_neg hc]
  let s' : SichtW D := fun c => if schreibt c then T c + 1 else v c
  let W' : RufMaschineW D :=
    ⟨{ M'' with speicher := sp' },
     fun c => if schreibt c then nachricht (ordVon ord c) v c (T c + 1) sp' :: W.hist c
       else W.hist c,
     fun t => if t = u then s' else W.sicht t,
     fun L => if L ∈ gegebenVon Mσ M'' u then (W.lsicht L).verein s' else W.lsicht L⟩
  refine ⟨W', ?_, hsp1, hsp2⟩
  exact {
    schritt := hs
    lies := hl
    ungelesen := hu
    frisch := fun c _ => ⟨Nat.lt_succ_of_le (hvT c), fun m hm he => by
      have := (hT c).1 m hm
      omega⟩
    speicherS := hsp1
    speicherU := hsp2
    faeden := rfl
    lauf := rfl
    start := rfl
    histS := fun c hw => by
      show (if schreibt c then _ else _) = _
      rw [if_pos hw]
    histU := fun c hw => by
      show (if schreibt c then _ else _) = _
      rw [if_neg hw]
    sichtS := fun c hw => by
      show (if u = u then s' else W.sicht u) c = T c + 1
      rw [if_pos rfl]
      show (if schreibt c then T c + 1 else v c) = T c + 1
      rw [if_pos hw]
    sichtU := fun c hw => by
      show (if u = u then s' else W.sicht u) c = v c
      rw [if_pos rfl]
      show (if schreibt c then T c + 1 else v c) = v c
      rw [if_neg hw]
    sichtF := fun t ht => by
      show (if t = u then s' else W.sicht t) = W.sicht t
      rw [if_neg ht]
    lsicht := fun L => by
      show (if L ∈ gegebenVon Mσ M'' u then (W.lsicht L).verein s' else W.lsicht L) =
        (if L ∈ gegebenVon Mσ M'' u then
          (W.lsicht L).verein (if u = u then s' else W.sicht u) else W.lsicht L)
      rw [if_pos (rfl : u = u)] }

end Einbettung

#print axioms Gabbro.Grammatik.schrittW_bau
#print axioms Gabbro.Grammatik.schrittW_g
#print axioms Gabbro.Grammatik.w_aus_g

end Gabbro.Grammatik
