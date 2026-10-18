import Grammatik.Speichermodell.Atomar.Atomar

/-
  File:      Grammatik/Speichermodell/Payload/PayloadHb.lean
  Subject:   PHASE B, ITEM 1 (OFFEN O25, `N291`): HAPPENS-BEFORE OVER A PLAIN PAYLOAD and the
             MESSAGE-PASSING THEOREM on machine W (the memory machine under GA/GX).
             Model only: `Spec.lean`, the checker and the exporter are untouched by this file.

  THE PATTERN. Thread `t` writes a PLAIN carrier `c` (the payload: a table cell, a plain
  global), then WRITES a flag `f` with order `freigabe` (`publishes`). Thread `u` READS `f` with
  order `freigabe` (`awaits`) and sees the message `t` wrote, and only then reads `c`.

  WHAT IS DEFINED.
  * `HbSeen W u c m` -- the write message `m` of `c` HAPPENS BEFORE thread `u`'s next access to
    `c` in state `W`: `m` is in the history and `u`'s view of `c` has reached `m`'s timestamp.
    This is the view-based happens-before of RC11 (program order joined with release/acquire
    synchronisation), read off the machine instead of a second relation over events.
  * `HbRace W u c m` -- the complement: `m` is in the history and NOT below `u`'s view, so a
    read of `u` may legally return a message older than `m` (the weakness of W).

  WHAT IS PROVED, on EVERY program (generic over `P`, `O`, `ord`, no footprint premise):
  * `payload_mp` -- THE MESSAGE-PASSING THEOREM: along the pattern above, the payload write
    happens-before the reader's state after the await, and stays so on every later state
    (`HbSeen` is monotone along W runs, `hbSeen_laufW`).
  * `payload_mp_lesen` -- every read of `c` by `u` after the await returns a message at or
    above the written one: never anything older than what `t` wrote before the release.
  * `payload_mp_wert` -- with the two memory-level facts the footprint rule of the checker
    will supply (the publisher had seen the whole payload history before its write, and no
    step after it adds a message at `c` -- written once per epoch), the reader's presented
    memory at `c` IS the memory `t` wrote: it reads the payload, not a stale or a later value.
  * `payload_kein_rennen` -- no `HbRace`: after the await the payload write is ordered before
    the reader's access.
  * `gesehen_einzelschreiber`, `still_of_kein_schreiben` -- the two memory facts of
    `payload_mp_wert` from thread-level facts: only `t` writes `c`; no step after the write
    writes `c`.
  * `erwartet_bestaetigt` -- the BRANCH FACT (SPRACHE §11.5 rule 2): a reader that branched on
    a value no earlier message of the flag carries read the message the publish added.

  The release/acquire hand-off these build on is `hb_uebergabe` (Atomar.lean); this file adds
  the payload write on the writer's side (`payload_schreib`), the run segments between the
  events, the value, and the race reading. The counter-models (relaxed flag, payload read
  before the await, a rewritten payload) are in `PayloadLitmus.lean`.
-/

namespace Gabbro.Grammatik

open Speichermodell

variable {D : Deklaration}

section Payload

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}

/-! ## 1. Happens-before over a payload carrier -/

/-- **The write `m` of carrier `c` happens before thread `u`'s next access to `c`** in `W`. -/
def HbSeen (W : RufMaschineW D) (u : Faden) (c : D.Tab ⊕ D.Glob) (m : NachrichtW D) : Prop :=
  m ∈ W.hist c ∧ m.ts ≤ W.sicht u c

/-- **A race on `c`**: the message `m` is in the history and `u` has not seen it, so a read of
    `u` may return an older one (`Lesbar` only demands a message at or above the view). -/
def HbRace (W : RufMaschineW D) (u : Faden) (c : D.Tab ⊕ D.Glob) (m : NachrichtW D) : Prop :=
  m ∈ W.hist c ∧ ¬ m.ts ≤ W.sicht u c

theorem hbSeen_not_race {W : RufMaschineW D} {u : Faden} {c : D.Tab ⊕ D.Glob}
    {m : NachrichtW D} (h : HbSeen W u c m) : ¬ HbRace W u c m :=
  fun hr => hr.2 h.2

theorem hbSeen_or_race {W : RufMaschineW D} {u : Faden} {c : D.Tab ⊕ D.Glob}
    {m : NachrichtW D} (h : m ∈ W.hist c) : HbSeen W u c m ∨ HbRace W u c m := by
  by_cases hv : m.ts ≤ W.sicht u c
  · exact Or.inl ⟨h, hv⟩
  · exact Or.inr ⟨h, hv⟩

/-- **Happens-before is monotone along W runs**: messages stay and views grow. -/
theorem hbSeen_laufW {W W' : RufMaschineW D} (hr : RufErreichbarW P O passes ord W W')
    {u : Faden} {c : D.Tab ⊕ D.Glob} {m : NachrichtW D} (h : HbSeen W u c m) :
    HbSeen W' u c m :=
  ⟨(laufW_waechst hr).1 c m h.1, Nat.le_trans h.2 ((laufW_waechst hr).2 u c)⟩

/-- **A read at or above a seen write**: a read of `c` by `u` in a state where the write `m` is
    seen returns a message at or above `m`. -/
theorem hbSeen_lesen {W W' : RufMaschineW D} {u : Faden} {σ : Speicher D}
    {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D} {neu : D.Tab ⊕ D.Glob → Nat}
    (h : SchrittW P O passes ord W u W' σ M'' wahl neu) {c : D.Tab ⊕ D.Glob}
    (hl : LiestG (mitSpeicher W.g σ) M'' u c) {m : NachrichtW D} (hb : HbSeen W u c m) :
    m.ts ≤ (wahl c).ts :=
  Nat.le_trans hb.2 (schrittW_lies_ab h hl)

/-- Runs compose. -/
theorem erreichbarW_trans {W1 W2 W3 : RufMaschineW D}
    (h12 : RufErreichbarW P O passes ord W1 W2) (h23 : RufErreichbarW P O passes ord W2 W3) :
    RufErreichbarW P O passes ord W1 W3 := by
  induction h23 with
  | start => exact h12
  | schritt X X' v _ hs ih => exact .schritt X X' v ih hs

/-- One step is a run. -/
theorem erreichbarW_schritt {W W' : RufMaschineW D} {v : Faden}
    (hs : RufSchrittW P O passes ord W v W') : RufErreichbarW P O passes ord W W' :=
  .schritt W W' v .start hs

/-! ## 2. The payload write -/

/-- **The writer of a payload sees its own write**: the step writes `c`; the message it adds
    is at the head of the history, carries the memory after the step, happens before the
    writer's next access, and lies strictly above every message the writer had seen. -/
theorem payload_schreib {W W' : RufMaschineW D} {u : Faden} {σ : Speicher D}
    {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D} {neu : D.Tab ⊕ D.Glob → Nat}
    (h : SchrittW P O passes ord W u W' σ M'' wahl neu) {c : D.Tab ⊕ D.Glob}
    (hw : SchreibG (mitSpeicher W.g σ) M'' u c) :
    ∃ m : NachrichtW D, W'.hist c = m :: W.hist c ∧ m.ts = neu c ∧ m.wert = W'.g.speicher ∧
      HbSeen W' u c m ∧ ∀ m' ∈ W.hist c, m'.ts ≤ W.sicht u c → m'.ts < m.ts := by
  have hh := h.histS c hw
  refine ⟨_, hh, rfl, rfl, ⟨?_, ?_⟩, ?_⟩
  · rw [hh]; exact List.mem_cons_self
  · rw [h.sichtS c hw]; exact Nat.le_refl _
  · intro m' _ hm'
    exact Nat.lt_of_le_of_lt (Nat.le_trans hm' (vorSicht_ge (ord := ord) W u σ M'' wahl c))
      (h.frisch c hw).1

/-! ## 3. The message-passing theorem -/

/-- **The run of the pattern** (the premises of `payload_mp` in one place):
    `t` writes the payload `c` (`Wa → Wb`), runs on (`Wb ⇝ W1`), PUBLISHES the flag `f` with
    order `freigabe` (`W1 → W2`); the world moves (`W2 ⇝ W3`); `u` AWAITS: it reads the message
    of `f` that `t`'s publish wrote, with acquire (`W3 → W4`). -/
structure MpAblauf (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (c f : D.Tab ⊕ D.Glob) (t u : Faden) (Wa Wb W1 W2 W3 W4 : RufMaschineW D) : Prop where
  verschieden : c ≠ f
  schreibt : ∃ σ N wahl neu, SchrittW P O passes ord Wa t Wb σ N wahl neu ∧
    SchreibG (mitSpeicher Wa.g σ) N t c
  lauf1 : RufErreichbarW P O passes ord Wb W1
  publiziert : ∃ σ N wahl neu, SchrittW P O passes ord W1 t W2 σ N wahl neu ∧
    SchreibG (mitSpeicher W1.g σ) N t f
  freigabe : ordVon ord f = .freigabe
  lauf2 : RufErreichbarW P O passes ord W2 W3
  erwartet : ∃ σ N wahl neu, SchrittW P O passes ord W3 u W4 σ N wahl neu ∧
    LiestG (mitSpeicher W3.g σ) N u f ∧ wahl f ∈ W2.hist f ∧ wahl f ∉ W1.hist f

/-- The pattern's states form one run `Wb ⇝ W4`. -/
theorem MpAblauf.lauf {c f : D.Tab ⊕ D.Glob} {t u : Faden}
    {Wa Wb W1 W2 W3 W4 : RufMaschineW D}
    (hp : MpAblauf P O passes ord c f t u Wa Wb W1 W2 W3 W4) :
    RufErreichbarW P O passes ord Wb W4 := by
  obtain ⟨σ1, N1, w1, n1, h1, _⟩ := hp.publiziert
  obtain ⟨σ3, N3, w3, n3, h3, _⟩ := hp.erwartet
  exact erreichbarW_trans (erreichbarW_trans (erreichbarW_trans hp.lauf1
    (erreichbarW_schritt ⟨σ1, N1, w1, n1, h1⟩)) hp.lauf2)
    (erreichbarW_schritt ⟨σ3, N3, w3, n3, h3⟩)

/-- **MESSAGE PASSING with a plain payload under release/acquire, on every program.** After the
    await, the message `t` wrote at the payload happens before `u`'s next access to it, and so
    on every later state of the run. -/
theorem payload_mp {c f : D.Tab ⊕ D.Glob} {t u : Faden} {Wa Wb W1 W2 W3 W4 : RufMaschineW D}
    (hp : MpAblauf P O passes ord c f t u Wa Wb W1 W2 W3 W4) :
    ∃ m : NachrichtW D, Wb.hist c = m :: Wa.hist c ∧ m.wert = Wb.g.speicher ∧
      m.ts ≤ W4.sicht u c ∧
      HbSeen W4 u c m ∧ ∀ W5, RufErreichbarW P O passes ord W4 W5 → HbSeen W5 u c m := by
  obtain ⟨σa, Na, wa, na, hA, hwA⟩ := hp.schreibt
  obtain ⟨σ1, N1, w1, n1, h1, hw1⟩ := hp.publiziert
  obtain ⟨σ3, N3, w3, n3, h3, hl3, hm2, hm1⟩ := hp.erwartet
  obtain ⟨m, hhist, _, hwert, hseen, _⟩ := payload_schreib hA hwA
  have e1 : HbSeen W1 t c m := hbSeen_laufW hp.lauf1 hseen
  have e2 : m ∈ W4.hist c := by
    have a2 := schrittW_hist ⟨σ1, N1, w1, n1, h1⟩ c e1.1
    have a3 := (laufW_waechst hp.lauf2).1 c m a2
    exact schrittW_hist ⟨σ3, N3, w3, n3, h3⟩ c a3
  have hb := (hb_uebergabe h1 hw1 hp.freigabe h3 hl3 hm2 hm1 hp.verschieden).1
  have e4 : HbSeen W4 u c m := ⟨e2, Nat.le_trans e1.2 hb⟩
  exact ⟨m, hhist, hwert, e4.2, e4, fun W5 h5 => hbSeen_laufW h5 e4⟩

/-- **A read after the await is at or above the payload write.** -/
theorem payload_mp_lesen {c f : D.Tab ⊕ D.Glob} {t u : Faden}
    {Wa Wb W1 W2 W3 W4 W5 W6 : RufMaschineW D}
    (hp : MpAblauf P O passes ord c f t u Wa Wb W1 W2 W3 W4)
    (h45 : RufErreichbarW P O passes ord W4 W5) {σ5 : Speicher D} {N5 : RufMaschineG D}
    {wahl5 : D.Tab ⊕ D.Glob → NachrichtW D} {neu5 : D.Tab ⊕ D.Glob → Nat}
    (h5 : SchrittW P O passes ord W5 u W6 σ5 N5 wahl5 neu5)
    (hl5 : LiestG (mitSpeicher W5.g σ5) N5 u c) :
    ∃ m : NachrichtW D, Wb.hist c = m :: Wa.hist c ∧ m.wert = Wb.g.speicher ∧
      m.ts ≤ (wahl5 c).ts := by
  obtain ⟨m, hh, hw, _, _, hall⟩ := payload_mp hp
  exact ⟨m, hh, hw, hbSeen_lesen h5 hl5 (hall W5 h45)⟩

/-- **No race on the payload after the await.** -/
theorem payload_kein_rennen {c f : D.Tab ⊕ D.Glob} {t u : Faden}
    {Wa Wb W1 W2 W3 W4 : RufMaschineW D}
    (hp : MpAblauf P O passes ord c f t u Wa Wb W1 W2 W3 W4) :
    ∃ m : NachrichtW D, Wb.hist c = m :: Wa.hist c ∧
      ∀ W5, RufErreichbarW P O passes ord W4 W5 → ¬ HbRace W5 u c m := by
  obtain ⟨m, hh, _, _, _, hall⟩ := payload_mp hp
  exact ⟨m, hh, fun W5 h5 => hbSeen_not_race (hall W5 h5)⟩

/-! ## 4. The value: the reader reads what the writer wrote -/

/-- Nobody adds a message at `c` along a run from `W` (the memory form of "not written after
    the publish until it is published again"): the history is the same. -/
theorem hist_gleich_lauf {W W' : RufMaschineW D} {c : D.Tab ⊕ D.Glob}
    (hstill : ∀ X X' v, RufErreichbarW P O passes ord W X → RufSchrittW P O passes ord X v X' →
      X'.hist c = X.hist c)
    (hr : RufErreichbarW P O passes ord W W') : W'.hist c = W.hist c := by
  induction hr with
  | start => rfl
  | schritt X X' v hr hs ih => rw [hstill X X' v hr hs, ih]

/-- **THE READER READS THE PAYLOAD.** With the two memory facts of the footprint rule --
    (i) the publisher had seen every message of `c` before its write (it is the only writer of
    the epoch), (ii) no step after the write adds a message at `c` -- a read of `c` after the
    await returns THE message `t` wrote, so the memory the step presents at `c` is the memory
    `t` produced. -/
theorem payload_mp_wert {c f : D.Tab ⊕ D.Glob} {t u : Faden}
    {Wa Wb W1 W2 W3 W4 W5 W6 : RufMaschineW D}
    (hp : MpAblauf P O passes ord c f t u Wa Wb W1 W2 W3 W4)
    (hgesehen : ∀ m ∈ Wa.hist c, m.ts ≤ Wa.sicht t c)
    (hstill : ∀ X X' v, RufErreichbarW P O passes ord Wb X → RufSchrittW P O passes ord X v X' →
      X'.hist c = X.hist c)
    (h45 : RufErreichbarW P O passes ord W4 W5) {σ5 : Speicher D} {N5 : RufMaschineG D}
    {wahl5 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu5 : D.Tab ⊕ D.Glob → Nat}
    (h5 : SchrittW P O passes ord W5 u W6 σ5 N5 wahl5 neu5)
    (hl5 : LiestG (mitSpeicher W5.g σ5) N5 u c) :
    TraegerGleich σ5 Wb.g.speicher c := by
  obtain ⟨σa, Na, wa, na, hA, hwA⟩ := hp.schreibt
  obtain ⟨m, hhist, _, hwert, _, hunter⟩ := payload_schreib hA hwA
  obtain ⟨m2, hh2, _, _, _, hall⟩ := payload_mp hp
  have hmm : m2 = m := (List.cons.inj (hh2.symm.trans hhist)).1
  subst hmm
  have hr5 : RufErreichbarW P O passes ord Wb W5 := erreichbarW_trans hp.lauf h45
  have hgl : W5.hist c = Wb.hist c := hist_gleich_lauf hstill hr5
  have hlesbar := (h5.lies c hl5).1
  have hmem : wahl5 c ∈ m2 :: Wa.hist c := by
    rw [← hh2, ← hgl]; exact hlesbar.1
  have hge : m2.ts ≤ (wahl5 c).ts := hbSeen_lesen h5 hl5 (hall W5 h45)
  have heq : wahl5 c = m2 := by
    rcases List.mem_cons.mp hmem with e | e
    · exact e
    · exact absurd (hunter _ e (hgesehen _ e)) (Nat.not_lt.mpr hge)
  have := (h5.lies c hl5).2
  rw [heq, hwert] at this
  exact this

/-- **The two memory facts of `payload_mp_wert` from two thread-level facts.** (i) If only
    thread `t` ever writes `c` on the runs from the start (`hnur`: the single-writer part of the
    footprint rule), then at every machine W reaches `t` has seen every message of `c`: the
    initial message sits at timestamp 0, and `t`'s own write sets its view to its timestamp. -/
theorem gesehen_einzelschreiber {M0 : RufMaschineG D} {t : Faden} {c : D.Tab ⊕ D.Glob}
    (hnur : ∀ X v X' σ M'' wahl neu, RufErreichbarW P O passes ord (RufStartW M0) X →
      SchrittW P O passes ord X v X' σ M'' wahl neu → SchreibG (mitSpeicher X.g σ) M'' v c →
      v = t)
    {W : RufMaschineW D} (hr : RufErreichbarW P O passes ord (RufStartW M0) W) :
    ∀ m ∈ W.hist c, m.ts ≤ W.sicht t c := by
  induction hr with
  | start =>
      intro m hm
      simp only [RufStartW, List.mem_singleton] at hm
      subst hm
      exact Nat.zero_le _
  | schritt X X' v hr hs ih =>
      obtain ⟨σ, M'', wahl, neu, h⟩ := hs
      intro m hm
      by_cases hw : SchreibG (mitSpeicher X.g σ) M'' v c
      · have hvt := hnur X v X' σ M'' wahl neu hr h hw
        subst hvt
        rw [h.histS c hw] at hm
        rcases List.mem_cons.mp hm with rfl | hm
        · rw [h.sichtS c hw]; exact Nat.le_refl _
        · exact Nat.le_trans (ih m hm) (sicht_waechst h _ c)
      · rw [h.histU c hw] at hm
        exact Nat.le_trans (ih m hm) (sicht_waechst h _ c)

/-- (ii) If no step after `Wb` writes `c`, no step adds a message at `c`
    (`SchrittW.histU`): the `hstill` premise of `payload_mp_wert`. -/
theorem still_of_kein_schreiben {Wb : RufMaschineW D} {c : D.Tab ⊕ D.Glob}
    (hkein : ∀ X v X' σ M'' wahl neu, RufErreichbarW P O passes ord Wb X →
      SchrittW P O passes ord X v X' σ M'' wahl neu → ¬ SchreibG (mitSpeicher X.g σ) M'' v c) :
    ∀ X X' v, RufErreichbarW P O passes ord Wb X → RufSchrittW P O passes ord X v X' →
      X'.hist c = X.hist c := by
  intro X X' v hX hs
  obtain ⟨σ, M'', wahl, neu, h⟩ := hs
  exact h.histU c (hkein X v X' σ M'' wahl neu hX h)

/-! ## 5. The branch fact: a confirmed awaited value identifies the publish -/

/-- **A confirming value identifies the published message** (the Lean side of SPRACHE §11.5 rule 2,
    "visibility is a branch fact"). `p` is the confirming predicate on the memory (it reads only
    the flag `f`: `hpcongr`). If no message of `f` before the publish confirms (`hnicht`: the
    initial value and every earlier write are non-confirming), nobody writes `f` between the
    publish and the await (`hstill`), and the reader's step read `f` with the branch `p`
    confirmed on the memory it presented (`hconf`), then the message it read is one the publish
    added: exactly the premise `erwartet` of `MpAblauf`. A reader that branches on a value the
    initial message also carries gets NO such conclusion (`mp_vor_erwartung_erlaubt` is the
    counter-model). -/
theorem erwartet_bestaetigt {u : Faden} {f : D.Tab ⊕ D.Glob} {W1 W2 W3 W4 : RufMaschineW D}
    {p : Speicher D → Prop} (hpcongr : ∀ s s', p s → TraegerGleich s s' f → p s')
    (hnicht : ∀ m ∈ W1.hist f, ¬ p m.wert)
    (hr2 : RufErreichbarW P O passes ord W2 W3)
    (hstill : ∀ X X' v, RufErreichbarW P O passes ord W2 X → RufSchrittW P O passes ord X v X' →
      X'.hist f = X.hist f)
    {σ3 : Speicher D} {N3 : RufMaschineG D} {wahl3 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu3 : D.Tab ⊕ D.Glob → Nat}
    (h3 : SchrittW P O passes ord W3 u W4 σ3 N3 wahl3 neu3)
    (hl : LiestG (mitSpeicher W3.g σ3) N3 u f) (hconf : p σ3) :
    wahl3 f ∈ W2.hist f ∧ wahl3 f ∉ W1.hist f := by
  have hlies := h3.lies f hl
  have hmem : wahl3 f ∈ W2.hist f := by
    have := hlies.1.1
    rwa [hist_gleich_lauf hstill hr2] at this
  have hp : p (wahl3 f).wert := hpcongr σ3 _ hconf hlies.2
  exact ⟨hmem, fun h => hnicht _ h hp⟩

end Payload

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.payload_mp
#print axioms Gabbro.Grammatik.payload_mp_lesen
#print axioms Gabbro.Grammatik.payload_mp_wert
#print axioms Gabbro.Grammatik.payload_kein_rennen
#print axioms Gabbro.Grammatik.erwartet_bestaetigt
#print axioms Gabbro.Grammatik.gesehen_einzelschreiber
#print axioms Gabbro.Grammatik.still_of_kein_schreiben
