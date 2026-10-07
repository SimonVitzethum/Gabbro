/-
  File:      Grammatik/X86/GvAtomRely.lean
  Subject:   GabbroV bridge: the shared-atomic rely (lane 1385).

  Family V5 `the shared-atomic rely` (TODO 0f): premise (b) of the goal is
  `NutzerPflichtA` (every body against EVERY value a shared atomic read may
  return), while GabbroV duties assume values of a plain read. V5 closed the
  bridge only for the parser's fragment (104, 108), where no shared atomic
  exists (`bruecke_nutzerA` via `nutzerPflichtA_ohne_atomar`).

  WHAT THIS FILE ADDS (generic over every declaration, no new interpreter:
  `execEndHA`/`HavocA` are reused from `AtomarSem`, never redefined):
  * `GvRelyDuty` -- the duty statement of a body whose shared-atomic reads
    are ARBITRARY values: the per-body triple over every atomic environment
    in `HavocA T` (the GabbroV reading of `KoerperGutSA`/`InvGutSA`/
    `InvGutGrundA`);
  * `GvDutyA` -- the user-level GabbroV duty with the rely (over `GeteiltA`)
    plus the start duty;
  * `gvDutyA_gibt_nutzerA` -- per-body GabbroV duties plus locality give (b);
  * `gv_plain_gibt_relyDuty_parserfragment` -- on the parser fragment (no
    atomic global, V5 `declOf_kein_atomar`) GabbroV's PLAIN duty implies the
    arbitrary-values duty;
  * `gv_rely_braucht_atomfreiheit` -- the precise obstruction: without
    atomic-freedom the transfer FAILS (`hP`: `zaehlB` reads shared `konfig`
    into a branch, the sequential duty holds, the rely duty fails).

  WHAT STAYS OPEN (see CUTS): duties for atomic-bearing units constructed
  from `Pflichten src`, the per-access TSO refinement, payload hand-off.
-/
import Grammatik.Zielsatz.Kern.Spec
import Grammatik.Speichermodell.Atomar.AtomarSem
import Grammatik.Speichermodell.Atomar.AtomarRec
import Grammatik.Zielsatz.Atomar.AtomarPflicht
import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.Zielsatz.Atomar.AtomarAkzeptiertZeuge
import Grammatik.Korrespondenz.Allgemein.Pflicht104

namespace Gabbro.Grammatik.X86.GvAtomRely

open Gabbro.Grammatik Zielsatz

variable {D : Deklaration}

/-! ## 1. The GabbroV rely duty: shared-atomic reads are arbitrary values -/

/-- **GabbroV rely duty for one body**: at every budget, the body's run meets
    its contract against EVERY atomic environment over `T` -- i.e. against
    every value another thread or the weak memory may show at a read of a
    shared atomic (`HavocA T A`, `AtomarSem`). This is the GabbroV reading of
    the rely triple; the engine `execEndHA` is reused, never duplicated. -/
def GvRelyDuty (P : Programm D) (S : SperrInv D) (Q : AxEns D)
    (T : D.Tab ⊕ D.Glob → Prop) (passes : Nat) (f : D.Fn) : Prop :=
  KoerperGutSA P passes Q S T f ∧ InvGutSA P passes Q S T f ∧ InvGutGrundA P passes Q S T f

/-- **The user-level GabbroV duty with the rely**: the arbitrary-values duty
    over the unit's shared atomics, plus the start duty. Locality of the lock
    family and axiom ensures stays checker-side (see `gvDutyA_gibt_nutzerA`). -/
structure GvDutyA [DecidableEq D.Fn] (E : Einheit D) : Prop where
  logik : ∀ (passes : Nat) (f : D.Fn), GvRelyDuty E.P E.S E.Q (GeteiltA E.P E.ws) passes f
  start : StartPflicht E

/-! ## 2. The bridge: GabbroV duties give premise (b) -/

/-- **Per-body GabbroV duties plus locality give (b) with the rely.** Assembly
    only: every premise is used, nothing is re-proved. -/
theorem gvDutyA_gibt_nutzerA {E : Einheit D} [DecidableEq D.Fn]
    (h : GvDutyA E) (hlokS : SperrInvLokal E.S) (hlokQ : AxEnsLokal E.Q) :
    NutzerPflichtA E :=
  ⟨⟨h.logik, hlokS, hlokQ⟩, h.start⟩

/-- **On the parser fragment GabbroV's PLAIN duty implies the
    arbitrary-values duty.** The fragment has no atomic global (V5
    `declOf_kein_atomar`: the parser elaborates `Glob := Empty`), so no read
    of a shared atomic exists and the plain duty is the rely duty
    (`nutzerPflichtA_ohne_atomar`, as `oblig_nutzerA` does for 104). -/
theorem gv_plain_gibt_relyDuty_parserfragment {E : Einheit D} [DecidableEq D.Fn]
    (hat : ∀ g : D.Glob, D.atomar g = false)
    (h : NutzerPflicht E) : GvDutyA E :=
  ⟨(nutzerPflichtA_ohne_atomar hat h).logik.1, h.start⟩

/-- **No atomic global on 104's exported declaration** (its `Glob` is
    `Empty`; the same term `oblig_nutzerA` uses). Standalone so a failure
    here reports at this proposition instead of inside a tuple. -/
theorem gv_104_ohne_atomar :
    (∀ g : G104_referenz_oblig.gD.Glob, G104_referenz_oblig.gD.atomar g = false) :=
  fun g => nomatch g

/-- **`einzahlen` writes `Konto` on 104** (`gSig_einzahlen.schreibt` is
    constantly `true`; decided computation through `D.signatur`). -/
theorem gv_104_einzahlen_schreibt :
    TraegerSchreibt (D := G104_referenz_oblig.gD) G104_referenz_oblig.g_einzahlen
      (.inl G104_referenz_oblig.GTab.Konto) = true := by decide

/-- **Joint witness for `gv_plain_gibt_relyDuty_parserfragment`**: on 104's
    exported unit both premises hold jointly -- no global exists, the plain
    duty is proved (`oblig_nutzer`) -- on a non-degenerate fixture: `einzahlen`
    writes `Konto` beside a reached run that moves memory
    (`oblig_ruf_bewegt`: `einzahlen` moves the slot `0 -> 100`). -/
theorem gv_plain_gibt_relyDuty_parserfragment_zeuge :
    (∀ g : G104_referenz_oblig.gD.Glob, G104_referenz_oblig.gD.atomar g = false) ∧
    NutzerPflicht G104_referenz_oblig.gE ∧
    TraegerSchreibt (D := G104_referenz_oblig.gD) G104_referenz_oblig.g_einzahlen
      (.inl G104_referenz_oblig.GTab.Konto) = true ∧
    (∃ σ' : World G104_referenz_oblig.gD,
      rufAt G104_referenz_oblig.gE.P Gabbro.Grammatik.oO 0 2
        G104_referenz_oblig.g_einzahlen
        (G104_referenz_oblig.gE.sp0.welt []) Gabbro.Grammatik.rho7 = .ok σ' () ∧
      ((G104_referenz_oblig.gE.sp0.welt []).slots G104_referenz_oblig.GTab.Konto 0
        G104_referenz_oblig.GKontoFeld.stand).n = 0 ∧
      (σ'.slots G104_referenz_oblig.GTab.Konto 0
        G104_referenz_oblig.GKontoFeld.stand).n = 100) :=
  ⟨gv_104_ohne_atomar, Gabbro.Grammatik.oblig_nutzer, gv_104_einzahlen_schreibt,
    Gabbro.Grammatik.oblig_ruf_bewegt⟩

/-! ## 3. The precise obstruction: the rely is strictly stronger -/

/-- **Without atomic-freedom the transfer FAILS in general.** The plain
    sequential duty does not imply the rely duty: `hP`'s `zaehlB` stores the
    shared `konfig` and branches on its second read (`hRumpf`/`hTest`), so the
    sequential triple holds (`hP_seq`) while an environment answering `5`
    (`aFuenf`) breaks the contract (`hP_rely_nicht`). -/
theorem gv_rely_braucht_atomfreiheit :
    ¬ ∀ (ws : List NIZeuge.nD.Fn) (f : NIZeuge.nD.Fn),
      KoerperGutS AtomarXZeuge.hP 0 (axWahr NIZeuge.nD) SchwachZeuge.nS f →
      KoerperGutSA AtomarXZeuge.hP 0 (axWahr NIZeuge.nD) SchwachZeuge.nS
        (GeteiltA AtomarXZeuge.hP ws) f := by
  intro hall
  exact AtomarXZeuge.hP_rely_nicht
    (hall AtomarXZeuge.hws NIZeuge.NFn.zaehlB (AtomarXZeuge.hP_seq 0))

/-- **Joint witness for `gv_rely_braucht_atomfreiheit`**: the sequential duty
    of `zaehlB` holds, the rely duty fails, `konfig` is shared, a table is
    written (`hauptA` writes `tabA`), and `aFuenf` is a member of the rely
    class -- all premises jointly on the non-degenerate fixture. -/
theorem gv_rely_braucht_atomfreiheit_zeuge :
    KoerperGutS AtomarXZeuge.hP 0 (axWahr NIZeuge.nD) SchwachZeuge.nS
      NIZeuge.NFn.zaehlB ∧
    ¬ KoerperGutSA AtomarXZeuge.hP 0 (axWahr NIZeuge.nD) SchwachZeuge.nS
      (GeteiltA AtomarXZeuge.hP AtomarXZeuge.hws) NIZeuge.NFn.zaehlB ∧
    GeteiltA AtomarXZeuge.hP AtomarXZeuge.hws
      (.inr NIZeuge.NGlob.konfig) ∧
    TraegerSchreibt (D := NIZeuge.nD) NIZeuge.NFn.hauptA
      (.inl NIZeuge.NTab.tabA) = true ∧
    HavocA (GeteiltA AtomarXZeuge.hP AtomarXZeuge.hws)
      AtomarXZeuge.aFuenf := by
  exact ⟨AtomarXZeuge.hP_seq 0, AtomarXZeuge.hP_rely_nicht,
    AtomarXZeuge.hP_konfig_geteilt, by decide, AtomarXZeuge.aFuenf_havoc⟩

/-
  CUTS (lane 1385 -- the shared-atomic rely):
  1. PROVED here: the GabbroV rely-duty statements (`GvRelyDuty`, `GvDutyA`);
     the assembly of per-body GabbroV duties plus locality into (b)
     (`gvDutyA_gibt_nutzerA`); the parser-fragment bridge from GabbroV's
     plain duty to the arbitrary-values duty (`gv_plain_gibt_relyDuty_...`,
     generic over every declaration, witnessed on 104); and the precise
     obstruction without atomic-freedom (`gv_rely_braucht_atomfreiheit`,
     witnessed on `hP`/`zaehlB`, whose shared-atomic read steers a branch).
  2. NOT proved: constructing rely duties for atomic-bearing units from
     `Pflichten src` (the duty-construction side stays with `bruecke/`,
     which covers atomic-free units only); the per-access x86-TSO refinement
     into W/GX; any payload hand-off correspondence.
  3. Both witnesses now carry an explicit `TraegerSchreibt ... = true`
     conjunct (review 1386, finding 2): `einzahlen`/`Konto` on 104 (via
     `gSig_einzahlen.schreibt`, constantly `true`) and `hauptA`/`tabA` on
     `hP` (the accepted `atomar_nichtleer.1` proposition, now with the same
     explicit `(D := nD)` as there). Green measurement itself remains OPEN
     (review 1386, finding 1: the shared `lean-slot` yielded no output on
     five attempts, ~150 min).
-/

#print axioms Gabbro.Grammatik.X86.GvAtomRely.gvDutyA_gibt_nutzerA
#print axioms Gabbro.Grammatik.X86.GvAtomRely.gv_plain_gibt_relyDuty_parserfragment
#print axioms Gabbro.Grammatik.X86.GvAtomRely.gv_104_ohne_atomar
#print axioms Gabbro.Grammatik.X86.GvAtomRely.gv_104_einzahlen_schreibt
#print axioms Gabbro.Grammatik.X86.GvAtomRely.gv_plain_gibt_relyDuty_parserfragment_zeuge
#print axioms Gabbro.Grammatik.X86.GvAtomRely.gv_rely_braucht_atomfreiheit
#print axioms Gabbro.Grammatik.X86.GvAtomRely.gv_rely_braucht_atomfreiheit_zeuge

end Gabbro.Grammatik.X86.GvAtomRely
