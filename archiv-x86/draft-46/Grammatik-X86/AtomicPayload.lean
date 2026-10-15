/-
  File:      Grammatik/X86/AtomicPayload.lean
  Subject:   Atomic-payload audit: decided footprint-membership checks for admitted shared
             atomics, and the duty-side audit of the atomic fragment.

  Lane 350 (organisation plan C6). Closes QUELLBRUECKE section 3.3, checker half.
  Reviewer: lane 388.

  DEPENDENCIES (reused, never redefined): `Spec` (`AkzeptiertSpecX`/`FussSX`/`GeteiltV`/
  `GeteiltA`, `LogikPflichtA`), `AtomarSem` (`HavocA`), `AtomarRec` (`KoerperGutSA` and the
  mono transfer lemmas), the decided checker Bools `vertragsFreiB`/`geteiltVB` with
  `vertragsFreiB_ok` (`Zielsatz/AtomarAkzeptiert.lean`), `atomarB_iff`
  (`Speichermodell/AtomarZeuge.lean`), and the bridge `nutzerA_aus_quelle` side
  (`bruecke/Bruecke/Atomar.lean`, audited here, not edited).

  WHAT THIS FILE ADDS (all generic over every declaration/program):
  * `atomarFussB`: the decided footprint-membership check for an admitted shared atomic
    at one footprint -- footprint member (`istIn (fussOrteG P f)`), `atomic`
    (`atomarB`), unguarded (`waechterVon` empty), in no contract (`vertragsFreiB`).
    `geteiltVB` decides admission without the footprint conjunct; the footprint side is
    the new checker-half piece of section 3.3.
  * `atomarFussB_ok` / `geteiltV_von_atomarFuss`: the check implies the footprint fact,
    `AtomarAusgenommen`, guard absence and `VertragsFrei`, hence `GeteiltV`. Thread
    non-locality (`¬ GetrenntR`) stays an explicit Prop premise: it is not decidable
    from syntax alone.
  * `vertrag_erwaehnung_verweigert` / `vertrag_bool_verweigert`: PROVED refusals -- a
    carrier mentioned by any contract (`requires`/`ensures`/owed invariant) is neither
    contract-free nor admitted, as Prop and as Bool.
  * `audit_pflicht_deckt_aufgenommen`: the duty-side audit -- a duty over the shared
    atomics `GeteiltA` transfers to the admitted set `GeteiltV` (narrowing via the mono
    lemmas, never by re-proving or by guessing).
  * `audit_beobachtung_menge`: the rely policy -- observations are preserved as a SET
    (whole trace plus every non-rely carrier), never narrowed to one value.
  * `nutzlast_nicht_aufgenommen`: a publish payload is NOT an admitted atomic, even
    beside an atomic publication -- the plain-payload hand-off stays OPEN (no TSO
    atomicity claimed here).

  WHAT STAYS OPEN (see CUTS): the per-access x86-TSO refinement into W/GX, the source
  bridge for atomic-bearing units (`nutzerA_aus_quelle` covers atomic-free units only),
  and any payload hand-off correspondence.
-/
import Grammatik.Speichermodell.AtomarSem
import Grammatik.Speichermodell.AtomarRec
import Grammatik.Speichermodell.AtomarZeuge
import Grammatik.Zielsatz.AtomarAkzeptiert
import Grammatik.Zielsatz.AtomarAkzeptiertZeuge
import Grammatik.Speichermodell.Zeuge
import Grammatik.Nichtinterferenz.Zeuge

namespace Gabbro.Grammatik.X86.AtomicPayload

open Gabbro.Grammatik Zielsatz Speichermodell NIZeuge SchwachZeuge AtomarXZeuge

variable {D : Deklaration}

/-! ## 1. The decided footprint-membership check for an admitted shared atomic -/

/-- **Admitted-shared-atomic candidate at one footprint, decided**: a footprint member that
    is `atomic`, has no guard lock, and occurs in no contract of the member list. -/
def atomarFussB (P : Programm D) (fs : List D.Fn) (f : D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  istIn (fussOrteG P f) c && atomarB c && (waechterVon c).isEmpty && vertragsFreiB P fs c

/-- **The check implies the footprint fact, the atomic flag, guard absence and
    contract freedom** (checker half of QUELLBRUECKE section 3.3). -/
theorem atomarFussB_ok {P : Programm D} {fs : List D.Fn} {f : D.Fn} {c : D.Tab ⊕ D.Glob}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (h : atomarFussB P fs f c = true) :
    c ∈ fussOrteG P f ∧ AtomarAusgenommen c ∧ (∀ L, ¬ Bewacht c L) ∧ VertragsFrei P c := by
  simp only [atomarFussB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hmem, hatom⟩, hun⟩, hfrei⟩ := h
  refine ⟨istIn_iff.mp hmem, atomarB_iff.mp hatom, fun L hL => ?_,
    vertragsFreiB_ok hvoll hfrei⟩
  have hw := waechterVon_mem.mpr hL
  rw [List.isEmpty_iff.mp hun] at hw
  exact List.not_mem_nil hw

/-! ## 2. The joint non-degenerate witness fixture -/

/-- **Non-degeneracy, once**: on the two-tenant fixture a table is written (`hauptA`
    writes `tabA`), and a W run from the zero memory reaches a machine whose `konfig`
    is 3 while the start memory has 0 -- a memory-changing run through the guard
    discipline (no lock anywhere: the atomic carries the sharing). -/
theorem atomar_nichtleer :
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true ∧
    ∃ W1 : RufMaschineW nD,
      RufErreichbarW nP nO 0 (fun _ => Ordnung.entspannt)
        (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (sp0.globs NGlob.konfig).n = 0 := by
  refine ⟨by decide, ?_⟩
  obtain ⟨W1, _, hW1, _, _, hk, _, _⟩ := w_nicht_sc (fun _ => Ordnung.entspannt)
  exact ⟨W1, hW1, hk, rfl⟩

/-- **Joint witness for `atomarFussB_ok`**: every premise together on the fixture --
    full enumeration, the decided check firing on `hauptA`/`konfig` -- plus the
    non-degenerate run. -/
theorem atomarFussB_ok_zeuge :
    (∀ g : nD.Fn, g ∈ nFs) ∧
    atomarFussB nP nFs NFn.hauptA (.inr NGlob.konfig) = true ∧
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true ∧
    ∃ W1 : RufMaschineW nD,
      RufErreichbarW nP nO 0 (fun _ => Ordnung.entspannt)
        (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (sp0.globs NGlob.konfig).n = 0 := by
  refine ⟨nFs_voll, by decide, atomar_nichtleer.1, ?_⟩
  obtain ⟨_, hrun⟩ := atomar_nichtleer
  exact hrun

/-! ## 3. Admission: from the decided check to `GeteiltV` -/

variable [DecidableEq D.Fn]

/-- **From the decided check to the admitted shared atomic**: the check gives the atomic
    flag, guard absence and contract freedom; thread non-locality stays an explicit Prop
    premise, since no syntax Bool decides the call closure. -/
theorem geteiltV_von_atomarFuss {P : Programm D} {fs ws : List D.Fn} {f : D.Fn}
    {c : D.Tab ⊕ D.Glob} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : atomarFussB P fs f c = true) (hsep : ¬ GetrenntR P ws c) : GeteiltV P ws c := by
  obtain ⟨-, hatom, hun, hfrei⟩ := atomarFussB_ok hvoll h
  exact ⟨⟨hatom, hun, hsep⟩, hfrei⟩

/-- **Joint witness for `geteiltV_von_atomarFuss`**: the check, the enumeration and the
    non-locality together on `konfig`, plus the non-degenerate run. -/
theorem geteiltV_von_atomarFuss_zeuge :
    (∀ g : nD.Fn, g ∈ nFs) ∧
    atomarFussB nP nFs NFn.hauptA (.inr NGlob.konfig) = true ∧
    ¬ GetrenntR nP n1ws (.inr NGlob.konfig) ∧
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true ∧
    ∃ W1 : RufMaschineW nD,
      RufErreichbarW nP nO 0 (fun _ => Ordnung.entspannt)
        (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (sp0.globs NGlob.konfig).n = 0 := by
  refine ⟨nFs_voll, by decide, n1_konfig_geteilt.1.2.2, atomar_nichtleer.1, ?_⟩
  obtain ⟨_, hrun⟩ := atomar_nichtleer
  exact hrun

/-! ## 4. Refusals: a contract-mentioning atomic is not admitted -/

/-- **PROVED REFUSAL, as Prop**: a carrier mentioned by any contract -- `requires`,
    `ensures` or an owed invariant -- is neither contract-free nor admitted. This is the
    checker-half refusal of QUELLBRUECKE section 3.3 (witnessed at `vP`/`kern` below;
    `vertrag_atomar_abgelehnt` shows the Bool firing there). -/
theorem vertrag_erwaehnung_verweigert {P : Programm D} {ws : List D.Fn} {g : D.Fn}
    {c : D.Tab ⊕ D.Glob}
    (h : c ∈ (P.requires g).orte ∨ c ∈ (P.ensures g).orte ∨ c ∈ invOrteP P g) :
    ¬ VertragsFrei P c ∧ ¬ GeteiltV P ws c := by
  have hnF : ¬ VertragsFrei P c := by
    intro hF
    obtain ⟨h1, h2, h3⟩ := hF g
    rcases h with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  exact ⟨hnF, fun hV => hnF hV.2⟩

/-- **Joint witness for `vertrag_erwaehnung_verweigert`**: on `vP`, `kern` ensures
    `konfig == 3`, so the mention premise holds jointly with a written table. (A reached
    run is not part of this checker-side refusal; the run leg is witnessed at `nP`,
    whose bodies `vP` shares.) -/
theorem vertrag_erwaehnung_verweigert_zeuge :
    ((.inr NGlob.konfig : nD.Tab ⊕ nD.Glob) ∈ (AtomarXZeuge.vP.ensures NFn.kern).orte ∨
      (.inr NGlob.konfig : nD.Tab ⊕ nD.Glob) ∈ (AtomarXZeuge.vP.requires NFn.kern).orte ∨
      (.inr NGlob.konfig : nD.Tab ⊕ nD.Glob) ∈ invOrteP AtomarXZeuge.vP NFn.kern) ∧
    TraegerSchreibt (D := nD) NFn.kern (.inr NGlob.konfig) = true ∧
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true :=
  ⟨Or.inl AtomarXZeuge.vertrag_atomar_echt.1, by decide, atomar_nichtleer.1⟩

/-- **PROVED REFUSAL, as Bool**: under a full enumeration the same mention forces both
    the contract-freedom check and the footprint-admission check to `false`. -/
theorem vertrag_bool_verweigert {P : Programm D} {fs : List D.Fn} {f g : D.Fn}
    {c : D.Tab ⊕ D.Glob} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : c ∈ (P.requires g).orte ∨ c ∈ (P.ensures g).orte ∨ c ∈ invOrteP P g) :
    vertragsFreiB P fs c = false ∧ atomarFussB P fs f c = false := by
  have hne : vertragsFreiB P fs c ≠ true := by
    intro ht
    exact (vertrag_erwaehnung_verweigert (ws := []) h).1 (vertragsFreiB_ok hvoll ht)
  have hV : vertragsFreiB P fs c = false := by
    cases hB : vertragsFreiB P fs c with
    | true => exact (hne hB).elim
    | false => rfl
  refine ⟨hV, ?_⟩
  simp only [atomarFussB, hV, Bool.and_false]

/-- **Joint witness for `vertrag_bool_verweigert`**: on `vP` the enumeration is full and
    `kern`'s `ensures` mentions `konfig`, so both Bools refuse -- beside a written table.
    (Checker-side refusal; the run leg is witnessed at `nP`, whose bodies `vP` shares.) -/
theorem vertrag_bool_verweigert_zeuge :
    (∀ g : nD.Fn, g ∈ nFs) ∧
    ((.inr NGlob.konfig : nD.Tab ⊕ nD.Glob) ∈ (AtomarXZeuge.vP.ensures NFn.kern).orte ∨
      (.inr NGlob.konfig : nD.Tab ⊕ nD.Glob) ∈ (AtomarXZeuge.vP.requires NFn.kern).orte ∨
      (.inr NGlob.konfig : nD.Tab ⊕ nD.Glob) ∈ invOrteP AtomarXZeuge.vP NFn.kern) ∧
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true :=
  ⟨nFs_voll, Or.inl AtomarXZeuge.vertrag_atomar_echt.1, atomar_nichtleer.1⟩

/-! ## 5. The duty-side audit: the atomic fragment -/

/-- **The duty-side audit**: a user duty proved over the shared atomics `GeteiltA` covers
    the admitted set `GeteiltV` -- narrowing through the mono transfer (`GeteiltV ⊆
    `GeteiltA`), never by re-proving a body and never by a compiler-guessed contract. -/
theorem audit_pflicht_deckt_aufgenommen {P : Programm D} {S : SperrInv D} {Q : AxEns D}
    {ws : List D.Fn} (h : LogikPflichtA P S Q (GeteiltA P ws)) :
    LogikPflichtA P S Q (GeteiltV P ws) :=
  ⟨fun passes f => ⟨koerperGutSA_mono (fun _ hc => hc.1) ((h.1 passes f).1),
    invGutSA_mono (fun _ hc => hc.1) ((h.1 passes f).2.1),
    invGutGrundA_mono (fun _ hc => hc.1) ((h.1 passes f).2.2)⟩, h.2.1, h.2.2⟩

/-- **Joint witness for `audit_pflicht_deckt_aufgenommen`**: configuration 1 discharges
    the duty over every rely set (`n1_logikA`), in particular over its one shared atomic,
    beside the non-degenerate run. -/
theorem audit_pflicht_deckt_aufgenommen_zeuge :
    LogikPflichtA nP SchwachZeuge.nS (axWahr nD) (GeteiltA nP n1ws) ∧
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true ∧
    ∃ W1 : RufMaschineW nD,
      RufErreichbarW nP nO 0 (fun _ => Ordnung.entspannt)
        (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (sp0.globs NGlob.konfig).n = 0 := by
  refine ⟨n1_logikA _, atomar_nichtleer.1, ?_⟩
  obtain ⟨_, hrun⟩ := atomar_nichtleer
  exact hrun

omit [DecidableEq D.Fn] in
/-- **The rely policy, as a theorem**: whatever an atomic environment answers at the rely
    set, the observations are preserved as a SET -- the whole trace, and every carrier
    outside the rely set --     never narrowed to one value. -/
theorem audit_beobachtung_menge {T : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D}
    {X : List (D.Tab ⊕ D.Glob)} {σ : World D} (hA : HavocA T A) :
    (A X σ).spur = σ.spur ∧
      ∀ c, ¬ T c → TraegerGleich (A X σ).speicher σ.speicher c := by
  refine ⟨(hA X σ).1, fun c hc => (hA X σ).2 c ?_⟩
  intro hcon
  exact hc hcon.2

omit [DecidableEq D.Fn] in
/-- **Joint witness for `audit_beobachtung_menge`**: the identity environment is in the
    fixture's rely class, and the preservation fires at every read list and world --
    beside the non-degenerate run. -/
theorem audit_beobachtung_menge_zeuge (X : List (nD.Tab ⊕ nD.Glob)) (σ : World nD) :
    HavocA (GeteiltA nP n1ws) (idA (D := nD)) ∧
    (idA (D := nD) X σ).spur = σ.spur ∧
    (∀ c, ¬ GeteiltA nP n1ws c → TraegerGleich (idA (D := nD) X σ).speicher σ.speicher c) ∧
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true ∧
    ∃ W1 : RufMaschineW nD,
      RufErreichbarW nP nO 0 (fun _ => Ordnung.entspannt)
        (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (sp0.globs NGlob.konfig).n = 0 := by
  obtain ⟨hspur, hmem⟩ := audit_beobachtung_menge (havocA_id (GeteiltA nP n1ws))
  exact ⟨havocA_id _, hspur, hmem, atomar_nichtleer.1, atomar_nichtleer.2⟩

/-! ## 6. The payload boundary: no TSO atomicity claimed here -/

/-- **A non-atomic carrier is refused everywhere**: not atomically excepted, refused by the
    footprint-admission check, and never admitted. Every publish payload is such a carrier
    (payloads are non-atomic: `ausgenommenB` has no payload exemption since verdict P3),
    so an unguarded payload hand-off is refused by this check -- admitting it needs the
    residue proof, which stays OPEN (see CUTS). -/
theorem nichtatomar_verweigert {P : Programm D} {fs : List D.Fn} {f : D.Fn}
    {ws : List D.Fn} {c : D.Tab ⊕ D.Glob} (hna : atomarB c = false) :
    ¬ AtomarAusgenommen c ∧ atomarFussB P fs f c = false ∧ ¬ GeteiltV P ws c := by
  have hnaP : ¬ AtomarAusgenommen c := by
    intro hA
    have ht : atomarB c = true := atomarB_iff.mpr hA
    rw [ht] at hna
    exact Bool.noConfusion hna
  refine ⟨hnaP, ?_, fun hV => hnaP hV.1.1⟩
  simp only [atomarFussB, hna, Bool.false_and, Bool.and_false]

/-- **Joint witness for `nichtatomar_verweigert`**: `tabA` is no atomic, beside the
    non-degenerate run. -/
theorem nichtatomar_verweigert_zeuge :
    atomarB (.inl NTab.tabA : nD.Tab ⊕ nD.Glob) = false ∧
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true ∧
    ∃ W1 : RufMaschineW nD,
      RufErreichbarW nP nO 0 (fun _ => Ordnung.entspannt)
        (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (sp0.globs NGlob.konfig).n = 0 :=
  ⟨rfl, atomar_nichtleer.1, atomar_nichtleer.2⟩

/-- **The payload declaration**: `nD` with one publication -- `konfig` (atomic) publishes
    `zaehler` made non-atomic. No in-tree fixture has a payload (`nutzlast` is empty
    everywhere); this is the smallest declaration that has one. Only `atomar` and
    `nutzlast` move, so every dependent proof field of `nD` still checks. -/
def pD : Deklaration :=
  { nD with
    atomar := fun
      | .konfig => true
      | .zaehler => false,
    nutzlast := fun
      | .konfig => [NGlob.zaehler]
      | .zaehler => [],
    ggeteilt_bewacht := fun _ h => Bool.noConfusion h }

/-- **A publish payload is not an admitted atomic**: even beside an atomic publication, a
    non-atomic payload is neither shared-atomic nor admitted, and the decided check
    refuses it. The hand-off needs its residue proof -- OPEN (see CUTS). -/
theorem nutzlast_braucht_restbeweis {P : Programm D} {ws : List D.Fn} {c : D.Tab ⊕ D.Glob}
    (hp : PaarungAusgenommen (D := D) c)
    (hnatom : ∀ p : D.Glob, c = .inr p → D.atomar p = false) :
    ¬ GeteiltA P ws c ∧ ¬ GeteiltV P ws c ∧ atomarB c = false := by
  obtain ⟨-, p, e, -, -⟩ := hp
  subst e
  have hpf : D.atomar p = false := hnatom p rfl
  have hna : ¬ AtomarAusgenommen (D := D) (.inr p) := by
    rintro ⟨g, e2, h⟩
    have heq : g = p := by cases e2; rfl
    rw [heq, hpf] at h
    exact Bool.noConfusion h
  refine ⟨fun h => hna h.1, fun h => hna h.1.1, ?_⟩
  show D.atomar p = false
  exact hpf

/-- **Joint witness for `nutzlast_braucht_restbeweis`**: over `pD`, `zaehler` is the
    payload of the atomic `konfig` and is itself non-atomic -- both premises together,
    beside a table some function writes. (Checker-side: no run statements, hence the
    table leg only; the memory-changing run over the same tables/functions is witnessed
    at `nP` above.) -/
theorem nutzlast_braucht_restbeweis_zeuge :
    PaarungAusgenommen (D := pD) (.inr NGlob.zaehler) ∧
    (∀ p : pD.Glob, ((.inr NGlob.zaehler : pD.Tab ⊕ pD.Glob) = .inr p) →
      pD.atomar p = false) ∧
    TraegerSchreibt (D := pD) NFn.hauptA (.inl NTab.tabA) = true := by
  refine ⟨⟨NGlob.konfig, NGlob.zaehler, rfl, List.mem_cons_self, rfl⟩,
    fun p he => by cases he; rfl, by decide⟩

/-! ## CUTS: what is not proved here -/

/-
  CUTS (lane 350, organisation plan C6 -- the checker half of QUELLBRUECKE section 3.3):

  1. No per-access x86-TSO refinement into W/GX is claimed anywhere in this file. The
     admitted set `GeteiltV` is the source-side set a future bridge must map per access;
     the bridge itself (TSO bridge, lane 274 business) stays OPEN.
  2. No aligned multi-byte atomicity and no LOCK/RMW hardware correspondence is claimed:
     the audit is over source carriers, never over target byte sequences.
  3. The source bridge for atomic-bearing units stays OPEN on the duty-construction side:
     `nutzerA_aus_quelle` (`bruecke/Bruecke/Atomar.lean`) covers atomic-free units only.
     This file audits the duty that such a bridge must discharge (`audit_pflicht_...`),
     it does not construct duties from `Pflichten src` for atomic-bearing units.
  4. The plain-payload hand-off stays OPEN: `nutzlast_braucht_restbeweis` refuses the
     payload at the admitted-atomic check; the residue proof that would admit it does
     not exist here.
  5. Thread non-locality (`¬ GetrenntR`) is a Prop premise of `geteiltV_von_atomarFuss`,
     never a Bool: no syntax check decides the call closure.
  6. No IR, no validator `Bool`, no lowering, no optimisation admission is defined here;
     the shared IR (lane 287) is consumed as a pending interface, never invented.
-/

#print axioms Gabbro.Grammatik.X86.AtomicPayload.atomarFussB_ok
#print axioms Gabbro.Grammatik.X86.AtomicPayload.geteiltV_von_atomarFuss
#print axioms Gabbro.Grammatik.X86.AtomicPayload.vertrag_erwaehnung_verweigert
#print axioms Gabbro.Grammatik.X86.AtomicPayload.vertrag_bool_verweigert
#print axioms Gabbro.Grammatik.X86.AtomicPayload.audit_pflicht_deckt_aufgenommen
#print axioms Gabbro.Grammatik.X86.AtomicPayload.audit_beobachtung_menge
#print axioms Gabbro.Grammatik.X86.AtomicPayload.nichtatomar_verweigert
#print axioms Gabbro.Grammatik.X86.AtomicPayload.nutzlast_braucht_restbeweis

end Gabbro.Grammatik.X86.AtomicPayload
