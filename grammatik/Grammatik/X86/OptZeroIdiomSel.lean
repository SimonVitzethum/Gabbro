/-
  File:      Grammatik/X86/OptZeroIdiomSel.lean
  Subject:   Zero-idiom selection rule (lane 885).

  DESIGN section 7 "Flags-aware peepholes" row: local premise "rule in
  register, flag-liveness, disp-fits-i32, no token op in pure window",
  certificate "A" (local rewrite record plus recomputed analysis
  citations), failure case "`x-x -> 0` dropping invalid flag" (here: the
  XOR-zero idiom selected where a flag survives), phase L, cost
  O(windows).

  What is proved here, over the REUSED canonical vocabulary
  (`ZeroIdiomXor`: `encodeZero`/`decodeZero`/`zeroSchritt`/`FlagBedarf`/
  `darfNullen`/`Lebendig`/`ersetzeDurchNull`, `Ausfuehrung.schritt` and
  its equations, `Codec.encode`/`decode`, `ExtendedExecution.stepExt`,
  `CostSummary.targetWork`, `ReferenzB`): the XOR-zero idiom is
  selected only with a flag-liveness proof at the site, survivor-flag
  sites keep the wide `movImm64 r, 0` form. Value, fault and
  observation preservation are proved over arbitrary values. No
  `ensures` is derived, no refusal becomes a warning, no faulting form
  is speculated above its guard.
-/
import Grammatik.X86.ZeroIdiomXor
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.CostSummary
import Grammatik.ReferenzB

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Validator-decided side conditions for one zero-idiom selection site
    (DESIGN section 7 row): recomputed flag liveness at the site, a
    rechecked disp-fits-i32 fact (trivially carried here: neither form
    has a memory operand), and a recomputed pure-window fact (no token
    op in the window). -/
structure NullSelCert where
  bedarf : FlagBedarf
  dispOk : Bool
  reineFenster : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation keeps the wide form, never a warning. -/
def nullSelZulassen (c : NullSelCert) : Bool :=
  darfNullen c.bedarf && c.dispOk && c.reineFenster

/-! ## 1. Selection: the idiom only with a liveness proof.

    The wide form `movImm64 r, 0` (10 bytes, flags preserved) is the
    default. The zero idiom `xorReg64 r r` (3 bytes, flags clobbered)
    is selected only where the validator admits the site. -/

/-- Site selection: the zero idiom where admitted, the wide form
    everywhere else. Survivor-flag sites keep the wide form. -/
def nullWaehle (r : Register) (c : NullSelCert) : Befehl :=
  if nullSelZulassen c then .xorReg64 r r else .movImm64 r 0

/-- Admission carries dead demand: every admitted site proves no flag
    is live. -/
theorem nullSelZulassen_tot (c : NullSelCert)
    (h : nullSelZulassen c = true) :
    ¬ Lebendig c.bedarf := by
  have hd : darfNullen c.bedarf = true := by
    unfold nullSelZulassen at h
    cases hbed : darfNullen c.bedarf with
    | true => rfl
    | false =>
      cases hdsp : c.dispOk with
      | true =>
        cases hrein : c.reineFenster with
        | true => simp [hbed] at h
        | false => simp [hbed] at h
      | false => simp [hbed] at h
  exact (darfNullen_heisst c.bedarf).mp hd

/-- REFUSAL 1 (the DESIGN failure case): a live flag demand refuses
    the idiom. Selecting here would drop a surviving flag. -/
theorem nullSelVerweigert_lebendig (c : NullSelCert)
    (h : Lebendig c.bedarf) :
    nullSelZulassen c = false := by
  cases hz : nullSelZulassen c with
  | true =>
    have hnl := nullSelZulassen_tot c hz
    exact absurd h hnl
  | false => rfl

/-- REFUSAL 2: a failing disp check refuses, even with dead flags. -/
theorem nullSelVerweigert_disp (c : NullSelCert)
    (h : c.dispOk = false) :
    nullSelZulassen c = false := by
  simp [nullSelZulassen, h]

/-- REFUSAL 3: a token op in the window refuses, even with dead flags. -/
theorem nullSelVerweigert_fenster (c : NullSelCert)
    (h : c.reineFenster = false) :
    nullSelZulassen c = false := by
  simp [nullSelZulassen, h]

/-- A refused site keeps the wide form: no silent idiom. -/
theorem nullWaehle_behaelt_weit (r : Register) (c : NullSelCert)
    (h : nullSelZulassen c = false) :
    nullWaehle r c = .movImm64 r 0 := by
  unfold nullWaehle
  simp [h]

/-- An admitted site takes the idiom. -/
theorem nullWaehle_nimmt_idiom (r : Register) (c : NullSelCert)
    (h : nullSelZulassen c = true) :
    nullWaehle r c = .xorReg64 r r := by
  unfold nullWaehle
  simp [h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_nullSelZulassen_ok :
    nullSelZulassen ⟨⟨false, false, false, false, false⟩, true, true⟩ =
      true := by
  decide

/-- Probe: a ZF-live certificate is refused. -/
theorem probe_nullSelZulassen_lebt :
    nullSelZulassen ⟨⟨false, false, true, false, false⟩, true, true⟩ =
      false := by
  decide

/-! ## 2. The wide form: one step that writes zero, keeps flags.

    The survivor form `movImm64 r, 0` at the canonical length 10: the
    accepted pilot step, never a second implementation. It writes zero
    into `r`, preserves every flag, touches no memory, advances RIP
    past 10 bytes, and keeps every other register. -/

/-- One wide-form step: the accepted pilot step on `MOV r, 0`. -/
def nullWeitSchritt (r : Register) (s : Zustand) : Option Zustand :=
  schritt (⟨.movImm64 r 0, 10⟩ : Decodiert) s

/-- The wide-form encoding is 10 bytes, within the 1..15 bound. -/
theorem nullWeitLaenge_zehn (r : Register) :
    (encode (.movImm64 r 0)).length = 10 := by
  cases r <;> decide

/-- The wide length passes the pilot length guard. -/
theorem nullWeitSchritt_laenge_ok : laengeOk 10 = true := by
  decide

/-- A successful wide step writes zero into the register. -/
theorem nullWeitSchritt_wert (r : Register) (s s' : Zustand)
    (h : nullWeitSchritt r s = some s') :
    s'.register r = 0 := by
  have hok : laengeOk 10 = true := by decide
  have hstep := schritt_movImm64 (⟨.movImm64 r 0, 10⟩ : Decodiert) s r 0
    hok rfl
  unfold nullWeitSchritt at h
  rw [hstep] at h
  cases h
  exact regSet_gleich _ _ _

/-- A successful wide step preserves every flag. -/
theorem nullWeitSchritt_flags (r : Register) (s s' : Zustand)
    (h : nullWeitSchritt r s = some s') :
    s'.flags = s.flags := by
  have hok : laengeOk 10 = true := by decide
  have hstep := schritt_movImm64 (⟨.movImm64 r 0, 10⟩ : Decodiert) s r 0
    hok rfl
  unfold nullWeitSchritt at h
  rw [hstep] at h
  cases h
  exact schrittRegister_flags _ _ _ _ _

/-- A successful wide step never touches memory. -/
theorem nullWeitSchritt_speicher (r : Register) (s s' : Zustand)
    (h : nullWeitSchritt r s = some s') :
    s'.speicher = s.speicher := by
  have hok : laengeOk 10 = true := by decide
  have hstep := schritt_movImm64 (⟨.movImm64 r 0, 10⟩ : Decodiert) s r 0
    hok rfl
  unfold nullWeitSchritt at h
  rw [hstep] at h
  cases h
  exact schrittRegister_speicher _ _ _ _ _

/-- A successful wide step advances RIP past the 10 wide bytes. -/
theorem nullWeitSchritt_rip (r : Register) (s s' : Zustand)
    (h : nullWeitSchritt r s = some s') :
    s'.rip = ripNach s.rip 10 := by
  have hok : laengeOk 10 = true := by decide
  have hstep := schritt_movImm64 (⟨.movImm64 r 0, 10⟩ : Decodiert) s r 0
    hok rfl
  unfold nullWeitSchritt at h
  rw [hstep] at h
  cases h
  exact schrittRegister_rip _ _ _ _ _

/-- A successful wide step keeps every other register. -/
theorem nullWeitSchritt_fremd (r : Register) (s s' : Zustand)
    (h : nullWeitSchritt r s = some s') (q : Register)
    (hq : q ≠ r) :
    s'.register q = s.register q := by
  have hok : laengeOk 10 = true := by decide
  have hstep := schritt_movImm64 (⟨.movImm64 r 0, 10⟩ : Decodiert) s r 0
    hok rfl
  unfold nullWeitSchritt at h
  rw [hstep] at h
  cases h
  exact regSet_fremd _ _ _ _ hq

/-- The idiom is 7 bytes shorter than the wide form it replaces. -/
theorem nullSpart_gegen_weit (r : Register) :
    (encodeZero r).length + 7 = (encode (.movImm64 r 0)).length := by
  have h1 := (encodeZero_laenge r).1
  have h2 := nullWeitLaenge_zehn r
  omega

/-! ## 3. Byte-facing dispatcher: both forms run unified, FP untouched.

    Both the idiom and the wide form step through `laufAlt` (the
    accepted lift of `schritt` to `FpZustand`) and hence through the
    accepted unified dispatcher `stepExt`: XMM and the FP context are
    untouched on either side, `kern` carries the respective successor.
    This is the IEEE preservation leg: scalar FP state is identical
    whichever form the site selects. -/

/-- The wide step lifts to the accepted old-state lift with the wide
    successor on `kern`. -/
theorem nullWeitSchritt_laufAlt (r : Register) (t : FpZustand) (w' : Zustand)
    (h : nullWeitSchritt r t.kern = some w') :
    laufAlt (⟨.movImm64 r 0, 10⟩ : Decodiert) t =
      some { t with kern := w' } := by
  have h2 : schritt (⟨.movImm64 r 0, 10⟩ : Decodiert) t.kern = some w' := h
  unfold laufAlt
  rw [h2]

/-- The wide form runs through the accepted unified dispatcher. -/
theorem nullWeitSchritt_stepExt (r : Register) (t : FpZustand)
    (b : BereitProfil) (w' : Zustand)
    (h : nullWeitSchritt r t.kern = some w') :
    stepExt (.pilot (⟨.movImm64 r 0, 10⟩ : Decodiert)) t b =
      .weiter { t with kern := w' } :=
  stepExt_pilot _ _ _ b (nullWeitSchritt_laufAlt r t w' h)

/-- The admitted idiom runs through the accepted unified dispatcher:
    the pilot arm IS the zero-idiom successor on `kern`. -/
theorem nullSchritt_stepExt (r : Register) (t : FpZustand)
    (b : BereitProfil) (s' : Zustand)
    (h : zeroSchritt (⟨r, 3⟩ : ZeroDecodiert) t.kern = some s') :
    stepExt (.pilot (⟨.xorReg64 r r, 3⟩ : Decodiert)) t b =
      .weiter { t with kern := s' } :=
  zeroSchritt_stepExt r t b s' h

/-! ## 4. Certificate shape and cost.

    The exact certificate the Rust backend emits per site: a local
    rewrite record (which register, wide form to idiom) plus the
    recomputed analysis citations (flag liveness re-decided at the
    site, disp rechecked, pure window rechecked). Machine work is
    unchanged by the selection: one target instruction either way, so
    step-budget accounting is identical and only final bytes shrink. -/

/-- The exact per-site certificate: a local rewrite record (`reg`,
    `von`, `nach`) plus recomputed analysis citations (`cert`). -/
structure NullSelNachweis where
  reg : Register
  von : Befehl
  nach : Befehl
  cert : NullSelCert
  deriving DecidableEq, Repr

/-- A valid certificate rewrites exactly `MOV r, 0` to `XOR r, r`
    under an admitted site analysis. -/
def nullNachweisOk (n : NullSelNachweis) : Bool :=
  decide (n.von = .movImm64 n.reg 0 ∧ n.nach = .xorReg64 n.reg n.reg) &&
    nullSelZulassen n.cert

/-- A valid certificate cites dead flag demand. -/
theorem nullNachweisOk_tot (n : NullSelNachweis)
    (h : nullNachweisOk n = true) :
    ¬ Lebendig n.cert.bedarf := by
  have hz : nullSelZulassen n.cert = true := by
    unfold nullNachweisOk at h
    rw [Bool.and_eq_true] at h
    exact h.2
  exact nullSelZulassen_tot n.cert hz

/-- A valid certificate selects the idiom. -/
theorem nullNachweisOk_waehlt (n : NullSelNachweis)
    (h : nullNachweisOk n = true) :
    nullWaehle n.reg n.cert = .xorReg64 n.reg n.reg := by
  have hz : nullSelZulassen n.cert = true := by
    unfold nullNachweisOk at h
    rw [Bool.and_eq_true] at h
    exact h.2
  exact nullWaehle_nimmt_idiom n.reg n.cert hz

/-- Machine work is unchanged by the selection: one retired target
    instruction either way, so the `CostSummary` work bound neither
    grows nor shrinks behind the validator's back. -/
theorem nullWaehle_arbeit (r : Register) (c : NullSelCert) :
    targetWork [nullWaehle r c] = 1 := by
  unfold nullWaehle targetWork
  by_cases hz : nullSelZulassen c = true
  · simp [hz]
  · have hf : nullSelZulassen c = false := by
      cases hdec : nullSelZulassen c with
      | true => exact absurd hdec hz
      | false => rfl
    simp [hf]

/-! ## 5. Site connection: the selected idiom matches the wide form.

    From the validator-decided admission, the idiom bytes, and both
    successful steps from the same start state: the bytes are the pilot
    XOR-self row (no re-decision, so every admitted final byte
    executes through the common architecture), both successors hold
    zero in `r` with identical full register files (every contract at
    its place reads the same values), neither touches memory (no shared
    access added or removed for concurrency, no call event on either
    register-only step), both steps succeed (no fault added or
    removed), the idiom carries the zero flag snapshot with the
    accepted validity while the wide form keeps the incoming flags
    (unobservable downstream: no flag is live), the certificate cites
    dead demand, the selection takes the idiom, and RIP advances past
    the respective lengths (3 vs 10: the budget accounting of
    `nullWaehle_arbeit` is unchanged, only final bytes shrink). -/

/-- Both successors agree on the full register file: the site
    observes zero in `r` and the old values everywhere else,
    whichever form executes. -/
theorem nullGleichtWeit_register (r : Register) (s s' w' : Zustand)
    (hstep : zeroSchritt (⟨r, 3⟩ : ZeroDecodiert) s = some s')
    (hwide : nullWeitSchritt r s = some w') :
    s'.register = w'.register := by
  have hs : ∀ q, s'.register q = regSet s.register r 0 q := by
    intro q
    by_cases hq : q = r
    · rw [hq, regSet_gleich]
      exact zeroSchritt_wert _ _ _ hstep
    · rw [regSet_fremd _ _ _ _ hq]
      exact zeroSchritt_fremd _ _ _ hstep q hq
  have hw : ∀ q, w'.register q = regSet s.register r 0 q := by
    intro q
    by_cases hq : q = r
    · rw [hq, regSet_gleich]
      exact nullWeitSchritt_wert _ _ _ hwide
    · rw [regSet_fremd _ _ _ _ hq]
      exact nullWeitSchritt_fremd _ _ _ hwide q hq
  funext q
  rw [hs q, hw q]

/-- CONNECTION: selecting the XOR-zero idiom under an admitted site
    analysis preserves value, fault behaviour and every observation
    of the wide `movImm64 r, 0` form. -/
theorem OptZeroIdiomSel_verbindung (r : Register) (s s' w' : Zustand)
    (cert : NullSelCert) (pfx rest : List Byte)
    (hz : nullSelZulassen cert = true)
    (hdec : decodeZero pfx = some ((⟨r, 3⟩ : ZeroDecodiert), rest))
    (hstep : zeroSchritt (⟨r, 3⟩ : ZeroDecodiert) s = some s')
    (hwide : nullWeitSchritt r s = some w') :
    decode pfx = some ((⟨.xorReg64 r r, 3⟩ : Decodiert), rest) ∧
      s'.register r = 0 ∧
      w'.register r = 0 ∧
      s'.register = w'.register ∧
      s'.speicher = s.speicher ∧
      w'.speicher = s.speicher ∧
      s'.speicher = w'.speicher ∧
      s'.flags = Flags.mk false true none true false false ∧
      LogikGueltig 0 s'.flags ∧
      w'.flags = s.flags ∧
      ¬ Lebendig cert.bedarf ∧
      ersetzeDurchNull r cert.bedarf = some (⟨r, 3⟩ : ZeroDecodiert) ∧
      nullWaehle r cert = .xorReg64 r r ∧
      s'.rip = ripNach s.rip 3 ∧
      w'.rip = ripNach s.rip 10 := by
  have htot : ¬ Lebendig cert.bedarf := nullSelZulassen_tot cert hz
  have hmem : s'.speicher = w'.speicher := by
    rw [zeroSchritt_speicher _ _ _ hstep, nullWeitSchritt_speicher _ _ _ hwide]
  have hfl := zeroSchritt_flags (⟨r, 3⟩ : ZeroDecodiert) s s' hstep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact decodeZero_ist_pilot pfx ⟨r, 3⟩ rest hdec
  · exact zeroSchritt_wert ⟨r, 3⟩ s s' hstep
  · exact nullWeitSchritt_wert r s w' hwide
  · exact nullGleichtWeit_register r s s' w' hstep hwide
  · exact zeroSchritt_speicher _ _ _ hstep
  · exact nullWeitSchritt_speicher _ _ _ hwide
  · exact hmem
  · exact hfl
  · rw [hfl]
    have hg := xor_selbst_gueltig (s.register r)
    rw [xor_selbst_null, xor_selbst_flags] at hg
    exact hg
  · exact nullWeitSchritt_flags r s w' hwide
  · exact htot
  · exact ersetze_erlaubt_bei_tot r cert.bedarf htot
  · exact nullWaehle_nimmt_idiom r cert hz
  · exact zeroSchritt_rip _ _ _ hstep
  · exact nullWeitSchritt_rip _ _ _ hwide

/-! ## 6. Joint witness: admitted site, both zeroes, live system.

    ALL premises of `OptZeroIdiomSel_verbindung` instantiated JOINTLY:
    the all-dead certificate on `rax` from the zero witness start state
    (42 in `rax`, zeroed memory, stack top at 8192), both steps firing
    to zero with identical register files and memories, beside the
    reached three-step run that stores 7 observably (data byte 0 to 7)
    AND the NON-DEGENERATE reference program `refD` (whose `einzahlen`
    writes its table, `refEin_schreibt`) with its reached F-machine run
    `MB` that changes memory (`refB_erreicht`, `refB_schreibt`: slot
    `0 -> 100`). -/

/-- The admitted witness certificate: every flag dead, disp and window
    clean. -/
def nullSelZeugeCert : NullSelCert :=
  ⟨⟨false, false, false, false, false⟩, true, true⟩

/-- JOINT WITNESS for `OptZeroIdiomSel_verbindung`: admitted site,
    both forms zeroing `rax` alike, a store-changing reached run, and
    a table-writing program with a memory-changing reached run. -/
theorem OptZeroIdiomSel_verbindung_zeuge :
    ∃ (s s' w' : Zustand) (cert : NullSelCert),
      nullSelZulassen cert = true ∧
      decodeZero (encodeZero .rax) = some ((⟨.rax, 3⟩ : ZeroDecodiert), []) ∧
      zeroSchritt (⟨.rax, 3⟩ : ZeroDecodiert) s = some s' ∧
      nullWeitSchritt .rax s = some w' ∧
      s'.register .rax = 0 ∧
      w'.register .rax = 0 ∧
      s'.register = w'.register ∧
      s'.speicher = w'.speicher ∧
      (lauf progZero s).map
          (fun t => t.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 8 7) ∧
      s.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 0 ∧
      (vertragVon refD refEin).schreibt () = true ∧
      RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
      MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hstep := schritt_xorReg64
    (⟨.xorReg64 .rax .rax, 3⟩ : Decodiert) zeroZeugeStart .rax .rax
    (by decide) rfl
  obtain ⟨s', hs'⟩ : ∃ s', schritt (⟨.xorReg64 .rax .rax, 3⟩ : Decodiert)
      zeroZeugeStart = some s' := ⟨_, hstep⟩
  have hs'' : zeroSchritt (⟨.rax, 3⟩ : ZeroDecodiert) zeroZeugeStart =
      some s' := hs'
  have hok : laengeOk 10 = true := by decide
  have hwide0 := schritt_movImm64 (⟨.movImm64 .rax 0, 10⟩ : Decodiert)
    zeroZeugeStart .rax 0 hok rfl
  obtain ⟨w', hw'⟩ : ∃ w', schritt (⟨.movImm64 .rax 0, 10⟩ : Decodiert)
      zeroZeugeStart = some w' := ⟨_, hwide0⟩
  have hw'' : nullWeitSchritt .rax zeroZeugeStart = some w' := hw'
  refine ⟨zeroZeugeStart, s', w', nullSelZeugeCert, ?_, ?_, hs'', hw'',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · have h := roundtripZero .rax []
    simpa using h
  · exact zeroSchritt_wert _ _ _ hs''
  · exact nullWeitSchritt_wert _ _ _ hw''
  · exact nullGleichtWeit_register .rax _ _ _ hs'' hw''
  · rw [zeroSchritt_speicher _ _ _ hs'', nullWeitSchritt_speicher _ _ _ hw'']
  · decide
  · rfl
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    Proved here (all over the REUSED canonical `ZeroIdiomXor`
    vocabulary, `Ausfuehrung.schritt` and its equations,
    `Codec.encode`/`decode`, `ScalarFloat.laufAlt`, the accepted
    unified dispatcher `ExtendedExecution.stepExt`,
    `CostSummary.targetWork` and `ReferenzB` -- no new machine, no new
    arithmetic, no new decoder, no source claim):
    - validator-decided side conditions (`NullSelCert`: recomputed
      flag liveness, rechecked disp, rechecked pure window) with
      admission (`nullSelZulassen`) carrying dead demand
      (`nullSelZulassen_tot`) and three explicit refusals (live
      demand, failing disp, token op in window);
    - site selection (`nullWaehle`): the idiom where admitted, the
      wide form everywhere else (survivor-flag sites keep the wide
      form), with probes for the admitted and the ZF-live case;
    - the wide form (`nullWeitSchritt` IS the pilot step on
      `MOV r, 0`): zero value, preserved flags, untouched memory,
      RIP past 10 bytes, frame facts, and 7 saved bytes vs the idiom;
    - the byte-facing dispatcher links for BOTH forms
      (`nullWeitSchritt_laufAlt`/`nullWeitSchritt_stepExt`,
      `nullSchritt_stepExt`): XMM and the FP context untouched, `kern`
      carries the respective successor (the IEEE leg);
    - the exact certificate shape (`NullSelNachweis`: local rewrite
      record plus recomputed analysis citations) with validity
      (`nullNachweisOk`) citing dead demand and selecting the idiom;
    - unchanged machine work (`nullWaehle_arbeit`: one retired target
      instruction either way);
    - full register-file agreement (`nullGleichtWeit_register`) and
      the site connection (`OptZeroIdiomSel_verbindung`): pilot
      bytes, zero on both sides, identical register files and
      memories, the zero flag snapshot with validity, preserved wide
      flags, dead demand with the admitted replacement, the taken
      idiom, and RIP past the respective lengths;
    - the joint witness (`OptZeroIdiomSel_verbindung_zeuge`): every
      premise of the connection instantiated jointly (admitted
      all-dead certificate, canonical bytes, both executed zeroes
      from 42), a store-changing reached run (data byte 0 to 7), and
      the non-degenerate source program `refD` with its
      memory-changing reached F-machine run.
    NOT proved here, and not claimed:
    - No hardware correspondence: encodings and flag effects follow
      the stated Intel SDM rows as modelled in `Wort.lean`, checked
      here only as self-consistency, not silicon.
    - No liveness/available-flags analysis implementation: the demand
      is validator-recomputed site data cited by the certificate,
      never a program-wide result proved here.
    - No source refinement, no TSO/GX bridge (both steps are
      register-only with no store-buffer effect by construction), no
      cost/time claim beyond one-for-one machine work and 7 saved
      bytes, no checker, Spec or goal claim; validator refusal keeps
      the wide form and is never an architectural fault.
-/

#print axioms nullSelZulassen
#print axioms nullSelZulassen_tot
#print axioms nullSelVerweigert_lebendig
#print axioms nullSelVerweigert_disp
#print axioms nullSelVerweigert_fenster
#print axioms nullWaehle_behaelt_weit
#print axioms nullWaehle_nimmt_idiom
#print axioms probe_nullSelZulassen_ok
#print axioms probe_nullSelZulassen_lebt
#print axioms nullWeitLaenge_zehn
#print axioms nullWeitSchritt_laenge_ok
#print axioms nullWeitSchritt_wert
#print axioms nullWeitSchritt_flags
#print axioms nullWeitSchritt_speicher
#print axioms nullWeitSchritt_rip
#print axioms nullWeitSchritt_fremd
#print axioms nullSpart_gegen_weit
#print axioms nullWeitSchritt_laufAlt
#print axioms nullWeitSchritt_stepExt
#print axioms nullSchritt_stepExt
#print axioms nullNachweisOk_tot
#print axioms nullNachweisOk_waehlt
#print axioms nullWaehle_arbeit
#print axioms nullGleichtWeit_register
#print axioms OptZeroIdiomSel_verbindung
#print axioms OptZeroIdiomSel_verbindung_zeuge

end Gabbro.Grammatik.X86
