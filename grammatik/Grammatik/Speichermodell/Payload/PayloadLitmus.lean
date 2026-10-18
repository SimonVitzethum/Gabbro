import Grammatik.Speichermodell.Maschine.Sicht

/-
  File:      Grammatik/Speichermodell/Payload/PayloadLitmus.lean
  Subject:   PHASE B, ITEM 1 (OFFEN O25): the COUNTER-MODELS of the payload message-passing
             theorem (`PayloadHb.lean`) and the standard LITMUS TESTS, as kernel-checked facts
             about the weak memory model of `Sicht.lean` (the same primitives machine W uses).

  A SMALL RUN CHECKER. `Sicht.lean` proves its litmus facts with hand-built states. Here a
  run is a LIST OF CHOICES -- `(thread, k)`: for a read, the index `k` into the location's
  history (index 0 is the newest message in LIST order, not in timestamp order), for a write
  the fresh timestamp `k`. `LZustand.gehe` performs one step iff `Lesbar`/`Frisch` hold, and
  `gehe_schritt` shows that such a step IS an `LSchritt`; so `erlaubt_of` turns a computed run
  into a reachable state (an ALLOWED outcome, by `decide`), and a refused read is `isNone`.
  FORBIDDEN outcomes are never decided by search (timestamps are free): they are invariant
  proofs, `Sicht.lean` (`mp_ra_verboten`, `corr_verboten`, `sb_sc_verboten`) and
  `lb_verboten` (`PayloadLB.lean`).

  WHAT IS HERE (x = payload, y = flag unless said otherwise):
  * `mp_zeuge`                -- NON-DEGENERATE witness of the theorem's premises and
                                 conclusion: release flag, acquire flag, the reader sees the
                                 flag AND the payload; reading the stale payload there is
                                 refused (`mp_alt_abgelehnt`).
  * `mp_vor_erwartung_erlaubt` -- COUNTER-MODEL: the payload is read BEFORE the await; the flag
                                 is seen (acquire) and the payload is the initial value.
  * `mp_flagge_lesen_entspannt_erlaubt`, `mp_flagge_schreiben_entspannt_erlaubt` -- COUNTER-
                                 MODELS: a relaxed flag read, a relaxed flag write; with
                                 `mp_rlx_erlaubt` (both relaxed, Sicht.lean) all three ways to
                                 lose the release/acquire pair.
  * `mp_umgeschrieben_erlaubt` -- COUNTER-MODEL of the VALUE claim: the payload is rewritten
                                 after the release; the reader sees the flag and the NEWER
                                 value. At or above holds (`payload_mp_lesen`), equality does
                                 not: the rule needs "not written after the publish".
  * `iriw_erlaubt`             -- IRIW with release/acquire: the two readers disagree on the
                                 order of the two independent writes (allowed; the model
                                 gives `seq_cst` no total order, `Sicht.lean` header).
  * `lb_verboten` (PayloadLB.lean) -- load buffering: both reads returning the other thread's
                                 LATER write is unreachable (no promises).
  * with `Sicht.lean`: `mp_ra_verboten`, `mp_rlx_erlaubt` (MP), `sb_erlaubt`, `sb_sc_verboten`
    (SB), `corr_verboten` (CoRR).
-/

namespace Gabbro.Grammatik.Speichermodell

open Befehl LOrt Ordnung

/-! ## 1. The run checker -/

/-- A program of several threads, thread `t` running the `t`-th list. -/
def faeden (ps : List (List (Befehl LOrt))) : Nat → List (Befehl LOrt) := fun t => ps.getD t []

/-- The effect of one instruction by thread `t` with choice `k` (see the header). -/
def Befehl.geh (b : Befehl LOrt) (Z : LZustand LOrt) (t k : Nat) : Option (LZustand LOrt) :=
  match b with
  | .schreib loc w o =>
      if Z.sicht t loc < k ∧ (Z.hist loc).all (fun m => m.ts != k) = true then
        some (Z.nachSchreib t loc w o k)
      else none
  | .lies loc r o =>
      match (Z.hist loc)[k]? with
      | none => none
      | some m => if Z.sicht t loc ≤ m.ts then some (Z.nachLies t loc r o m) else none

/-- One step by thread `t` with choice `k`, or `none` if it is not a step. -/
def LZustand.gehe (prog : Nat → List (Befehl LOrt)) (Z : LZustand LOrt) (t k : Nat) :
    Option (LZustand LOrt) :=
  match (prog t)[Z.pc t]? with
  | none => none
  | some b => b.geh Z t k

/-- A checked step is a step of the weak machine. -/
theorem gehe_schritt {prog : Nat → List (Befehl LOrt)} {Z Z' : LZustand LOrt} {t k : Nat}
    (h : Z.gehe prog t k = some Z') : LSchritt prog Z Z' := by
  unfold LZustand.gehe at h
  cases hb : (prog t)[Z.pc t]? with
  | none => rw [hb] at h; simp at h
  | some b =>
      rw [hb] at h
      dsimp only at h
      cases b with
      | schreib loc w o =>
          unfold Befehl.geh at h
          dsimp only at h
          split at h
          · rename_i hc
            cases h
            exact .schreib Z t loc w o k hb
              ⟨hc.1, fun m hm => bne_iff_ne.mp (List.all_eq_true.mp hc.2 m hm)⟩
          · simp at h
      | lies loc r o =>
          unfold Befehl.geh at h
          dsimp only at h
          cases hm : (Z.hist loc)[k]? with
          | none => rw [hm] at h; simp at h
          | some m =>
              rw [hm] at h
              dsimp only at h
              split at h
              · rename_i hc
                cases h
                exact .lies Z t loc r o m hb ⟨List.mem_of_getElem? hm, hc⟩
              · simp at h

/-- A list of choices, run from `Z`. -/
def lauf (prog : Nat → List (Befehl LOrt)) : LZustand LOrt → List (Nat × Nat) →
    Option (LZustand LOrt)
  | Z, [] => some Z
  | Z, a :: r => (Z.gehe prog a.1 a.2).bind fun Z' => lauf prog Z' r

theorem lauf_erreichbar {prog : Nat → List (Befehl LOrt)} :
    ∀ (acts : List (Nat × Nat)) {Z Z' : LZustand LOrt}, LErreichbar (LSchritt prog) Z →
      lauf prog Z acts = some Z' → LErreichbar (LSchritt prog) Z'
  | [], Z, Z', hz, h => by simp [lauf] at h; subst h; exact hz
  | a :: r, Z, Z', hz, h => by
      simp only [lauf] at h
      cases hg : Z.gehe prog a.1 a.2 with
      | none => simp [hg] at h
      | some Z1 =>
          simp only [hg, Option.bind_some] at h
          exact lauf_erreichbar r (.schritt hz (gehe_schritt hg)) h

/-- **An outcome computed by a run is reachable.** -/
theorem erlaubt_of {prog : Nat → List (Befehl LOrt)} {acts : List (Nat × Nat)}
    {p : LZustand LOrt → Bool}
    (h : (lauf prog (LZustand.start LOrt) acts).map p = some true) :
    ∃ Z, LErreichbar (LSchritt prog) Z ∧ p Z = true := by
  cases hl : lauf prog (LZustand.start LOrt) acts with
  | none => simp [hl] at h
  | some Z =>
      simp only [hl, Option.map_some] at h
      exact ⟨Z, lauf_erreichbar acts .start hl, Option.some.inj h⟩

/-! ## 2. Message passing with a payload: the premises hold, and what breaks without them -/

/-- Writer: payload `x := 1` (plain), then the flag `y := 1` with release (`publishes`).
    Reader: the flag with acquire (`awaits`), then the payload. The theorem's pattern. -/
def mpAcq : Nat → List (Befehl LOrt) :=
  faeden [[schreib .x 1 .entspannt, schreib .y 1 .freigabe],
          [lies .y 0 .freigabe, lies .x 1 .entspannt]]

/-- **NON-DEGENERATE.** The pattern has a run in which the reader sees the flag AND the payload
    (so the conclusion of `payload_mp_lesen` is about a real run, not a vacuous one). -/
theorem mp_zeuge : ∃ Z, LErreichbar (LSchritt mpAcq) Z ∧
    Z.pc 1 = 2 ∧ Z.reg 1 0 = 1 ∧ Z.reg 1 1 = 1 := by
  obtain ⟨Z, hZ, hp⟩ := erlaubt_of (prog := mpAcq)
    (acts := [(0, 1), (0, 1), (1, 0), (1, 0)])
    (p := fun Z => Z.pc 1 == 2 && Z.reg 1 0 == 1 && Z.reg 1 1 == 1) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨Z, hZ, hp.1.1, hp.1.2, hp.2⟩

/-- In that run the reader's second read cannot return the initial payload: after the acquire
    the view of `x` is 1, the initial message (timestamp 0) is below it. -/
theorem mp_alt_abgelehnt :
    (lauf mpAcq (LZustand.start LOrt) [(0, 1), (0, 1), (1, 0), (1, 1)]).isNone = true := by
  decide

/-- **COUNTER-MODEL: the payload is read BEFORE the await.** The reader loads `x` first and
    the flag after: it sees the flag (`r0 = 1`) and the INITIAL payload (`r1 = 0`) although the
    writer stored the payload before the release. The conclusion of the theorem needs the
    payload read AFTER the acquire. -/
def mpVor : Nat → List (Befehl LOrt) :=
  faeden [[schreib .x 1 .entspannt, schreib .y 1 .freigabe],
          [lies .x 1 .entspannt, lies .y 0 .freigabe]]

theorem mp_vor_erwartung_erlaubt : ∃ Z, LErreichbar (LSchritt mpVor) Z ∧
    Z.pc 1 = 2 ∧ Z.reg 1 0 = 1 ∧ Z.reg 1 1 = 0 := by
  obtain ⟨Z, hZ, hp⟩ := erlaubt_of (prog := mpVor)
    (acts := [(0, 1), (0, 1), (1, 1), (1, 0)])
    (p := fun Z => Z.pc 1 == 2 && Z.reg 1 0 == 1 && Z.reg 1 1 == 0) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨Z, hZ, hp.1.1, hp.1.2, hp.2⟩

/-- **COUNTER-MODEL: the flag is READ relaxed** (the writer releases). The reader's view gains
    only the flag, not the writer's payload view. -/
def mpLesenEntspannt : Nat → List (Befehl LOrt) :=
  faeden [[schreib .x 1 .entspannt, schreib .y 1 .freigabe],
          [lies .y 0 .entspannt, lies .x 1 .entspannt]]

theorem mp_flagge_lesen_entspannt_erlaubt : ∃ Z, LErreichbar (LSchritt mpLesenEntspannt) Z ∧
    Z.pc 1 = 2 ∧ Z.reg 1 0 = 1 ∧ Z.reg 1 1 = 0 := by
  obtain ⟨Z, hZ, hp⟩ := erlaubt_of (prog := mpLesenEntspannt)
    (acts := [(0, 1), (0, 1), (1, 0), (1, 1)])
    (p := fun Z => Z.pc 1 == 2 && Z.reg 1 0 == 1 && Z.reg 1 1 == 0) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨Z, hZ, hp.1.1, hp.1.2, hp.2⟩

/-- **COUNTER-MODEL: the flag is WRITTEN relaxed** (the reader acquires): the message carries
    no view. -/
def mpSchreibenEntspannt : Nat → List (Befehl LOrt) :=
  faeden [[schreib .x 1 .entspannt, schreib .y 1 .entspannt],
          [lies .y 0 .freigabe, lies .x 1 .entspannt]]

theorem mp_flagge_schreiben_entspannt_erlaubt :
    ∃ Z, LErreichbar (LSchritt mpSchreibenEntspannt) Z ∧
      Z.pc 1 = 2 ∧ Z.reg 1 0 = 1 ∧ Z.reg 1 1 = 0 := by
  obtain ⟨Z, hZ, hp⟩ := erlaubt_of (prog := mpSchreibenEntspannt)
    (acts := [(0, 1), (0, 1), (1, 0), (1, 1)])
    (p := fun Z => Z.pc 1 == 2 && Z.reg 1 0 == 1 && Z.reg 1 1 == 0) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨Z, hZ, hp.1.1, hp.1.2, hp.2⟩

/-- **COUNTER-MODEL of the VALUE claim: the payload is rewritten after the publish.** The
    reader sees the flag and then the NEWER payload `2`, not the one published (`1`). The read is
    still at or above the published write; only "no step after the write adds a message"
    (`payload_mp_wert`'s second premise) makes the value the published one. -/
def mpUmgeschrieben : Nat → List (Befehl LOrt) :=
  faeden [[schreib .x 1 .entspannt, schreib .y 1 .freigabe, schreib .x 2 .entspannt],
          [lies .y 0 .freigabe, lies .x 1 .entspannt]]

theorem mp_umgeschrieben_erlaubt : ∃ Z, LErreichbar (LSchritt mpUmgeschrieben) Z ∧
    Z.pc 1 = 2 ∧ Z.reg 1 0 = 1 ∧ Z.reg 1 1 = 2 := by
  obtain ⟨Z, hZ, hp⟩ := erlaubt_of (prog := mpUmgeschrieben)
    (acts := [(0, 1), (0, 1), (0, 2), (1, 0), (1, 0)])
    (p := fun Z => Z.pc 1 == 2 && Z.reg 1 0 == 1 && Z.reg 1 1 == 2) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨Z, hZ, hp.1.1, hp.1.2, hp.2⟩

/-! ## 3. IRIW -/

/-- IRIW with release/acquire: two independent writes, two readers reading them in opposite
    orders. -/
def iriw : Nat → List (Befehl LOrt) :=
  faeden [[schreib .x 1 .freigabe], [schreib .y 1 .freigabe],
          [lies .x 0 .freigabe, lies .y 1 .freigabe],
          [lies .y 0 .freigabe, lies .x 1 .freigabe]]

/-- **IRIW is ALLOWED**: the readers disagree (reader 2 sees `x` and not `y`, reader 3 sees `y`
    and not `x`). RC11 allows it for release/acquire; the model keeps it for `seq_cst` too,
    where RC11 forbids it (the over-approximation of the header of `Sicht.lean`). -/
theorem iriw_erlaubt : ∃ Z, LErreichbar (LSchritt iriw) Z ∧
    Z.pc 2 = 2 ∧ Z.pc 3 = 2 ∧ Z.reg 2 0 = 1 ∧ Z.reg 2 1 = 0 ∧ Z.reg 3 0 = 1 ∧
      Z.reg 3 1 = 0 := by
  obtain ⟨Z, hZ, hp⟩ := erlaubt_of (prog := iriw)
    (acts := [(0, 1), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1)])
    (p := fun Z => Z.pc 2 == 2 && Z.pc 3 == 2 && Z.reg 2 0 == 1 && Z.reg 2 1 == 0 &&
      Z.reg 3 0 == 1 && Z.reg 3 1 == 0) (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨Z, hZ, hp.1.1.1.1.1, hp.1.1.1.1.2, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩

end Gabbro.Grammatik.Speichermodell

#print axioms Gabbro.Grammatik.Speichermodell.gehe_schritt
#print axioms Gabbro.Grammatik.Speichermodell.mp_zeuge
#print axioms Gabbro.Grammatik.Speichermodell.mp_alt_abgelehnt
#print axioms Gabbro.Grammatik.Speichermodell.mp_vor_erwartung_erlaubt
#print axioms Gabbro.Grammatik.Speichermodell.mp_flagge_lesen_entspannt_erlaubt
#print axioms Gabbro.Grammatik.Speichermodell.mp_flagge_schreiben_entspannt_erlaubt
#print axioms Gabbro.Grammatik.Speichermodell.mp_umgeschrieben_erlaubt
#print axioms Gabbro.Grammatik.Speichermodell.iriw_erlaubt
