/-
  File:      Grammatik/X86/PayloadResidue.lean
  Subject:   Plain-payload residue: the guarded-transfer obligation over source W runs
             and the footprint side over the accepted checker vocabulary.

  Lane 545 (organisation plan N11). Consumer: C6 AtomicPayload + QUELLBRUECKE
  section 3.3 (the plain-payload hand-off residue). DEP: C6 (lane 350, merged).

  DEPENDENCIES (reused, never redefined): `FussSX` (AtomarReplay), `GeteiltV`/
  `GeteiltA` (Spec), `hb_uebergabe` (Atomar: the accepted happens-before hand-off
  on W), `nutzlast_braucht_restbeweis`/`nichtatomar_verweigert`/`pD`
  (AtomicPayload), the NI fixture (NIZeuge), the stale-read run
  (SchwachZeuge.w_nicht_sc via `atomar_nichtleer`).

  WHAT THIS FILE ADDS (all generic over every declaration/program):
  * `payload_fuss_braucht_deckung`: a payload carrier in a footprint covered by
    `FussSX` over the admitted atomics is thread-local or guard-locked -- the
    shared-atomic disjunct is impossible for it.
  * `bewachte_uebergabe_ohne_rueckstand`: the guarded release/acquire transfer of
    a payload through its atomic flag leaves no observable residue -- the reader
    never reads below the writer's view (thin wrapper over `hb_uebergabe`; the
    payload premises discharge the side inequality).
  * `nutzlast_ohne_deckung_verweigert`: a non-atomic payload is refused by the
    footprint-admission check and never admitted.
  * `flagge_ist_kein_schloss`: a shared atomic flag is not a lock -- the
    admitted flag is shared and guardless.

  WHAT STAYS OPEN (see CUTS): the per-access x86-TSO refinement, the fresh
  acquire-read inhabitation on a payload program, and any payload hand-off
  correspondence below W.
-/
import Grammatik.X86.AtomicPayload
import Grammatik.Speichermodell.Atomar
import Grammatik.Speichermodell.AtomarReplay
import Grammatik.Zielsatz.AtomarAkzeptiertZeuge

namespace Gabbro.Grammatik.X86.PayloadResidue

open Gabbro.Grammatik Zielsatz Speichermodell NIZeuge SchwachZeuge AtomarXZeuge AtomicPayload

variable {D : Deklaration} [DecidableEq D.Fn]

/-- The witness declaration shares the fixture's functions. -/
instance : DecidableEq pD.Fn := inferInstanceAs (DecidableEq NFn)

/-- The witness declaration shares the fixture's carriers. -/
instance : DecidableEq pD.Glob := inferInstanceAs (DecidableEq NGlob)

instance : DecidableEq pD.Tab := inferInstanceAs (DecidableEq NTab)

/-- Skeleton probe: the index literal over the payload declaration. -/
def qI0 {Γ : Ctx} {Λ : List (Res pD)} {t : pD.Tab} : Expr pD Γ Λ (.index (pD.count t)) :=
  .weiter (by decide) (show (0 : Int) ≤ 1 - 1 by decide) (.lit 0)

/-- Guard proofs over the payload declaration (same empty watch lists as `nD`). -/
theorem qDarf (t : pD.Tab) (Λ : List (Res pD)) : darf pD t Λ := fun _ h => nomatch h

theorem qGd (g : pD.Glob) (Λ : List (Res pD)) : gdarf pD g Λ := fun _ h => nomatch h

/-- The witness body over `pD`: `tabA[0] = zaehler` -- reads the payload, writes
    a plain table. Shape copied from `nRumpfA`, flag replaced by payload. -/
def qRumpfH : Endblock pD (vertragVon pD NFn.hauptA) false [] [] :=
  .cons (.assignSlot NTab.tabA () qI0 (.glob NGlob.zaehler (qGd _ _)) rfl (qDarf _ _))
    (.ret .keine List.Perm.nil)

/-- The witness program over `pD`: one payload reader, everything else idle. -/
def qP : Programm pD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .hauptA => qRumpfH
    | .hauptB => .ret .keine List.Perm.nil
    | .kern => .ret .keine List.Perm.nil
    | .ruhe => .ret .keine List.Perm.nil
    | .zaehlA => .ret .keine List.Perm.nil
    | .zaehlB => .ret .keine List.Perm.nil
    | .leck => .ret .keine List.Perm.nil

/-- The witness body really reads the payload. -/
theorem q_mem : (.inr NGlob.zaehler : pD.Tab ⊕ pD.Glob) ∈ fussOrteG qP NFn.hauptA :=
  istIn_iff.mp (by decide)

/-- The witness declaration really writes a plain table at `hauptA`. -/
theorem q_schreibt :
    TraegerSchreibt (D := pD) NFn.hauptA (.inl NTab.tabA) = true := by
  decide

/-- The witness footprint is covered: with every carrier local, `FussSX` holds for
    any lock invariant and any admitted set. -/
theorem q_fuss : FussSX qP (SperrInv.leer pD) (fun _ => true) (GeteiltV qP []) NFn.hauptA :=
  ⟨fun c _ => Or.inl (by simp), fun c _ => by simp⟩

/-! ## 1. The footprint obligation: a payload is local or guard-locked -/

/-- **A payload carrier in a footprint covered by `FussSX` over the admitted atomics
    is thread-local or guard-locked.** The shared-atomic disjunct is impossible for it:
    a payload is no admitted atomic (`nutzlast_braucht_restbeweis`). So the cover the
    residue proof needs at the payload is a lock (or locality) fact, never the flag. -/
theorem payload_fuss_braucht_deckung {P : Programm D} {S : SperrInv D}
    {lok : D.Tab ⊕ D.Glob → Bool} {ws : List D.Fn} {f : D.Fn} {a p : D.Glob}
    (hF : FussSX P S lok (GeteiltV P ws) f)
    (hmem : (.inr p : D.Tab ⊕ D.Glob) ∈ fussOrteG P f)
    (hpay : p ∈ D.nutzlast a) (ha : D.atomar a = true) (hna : D.atomar p = false) :
    (sigB f (.inr p) || lok (.inr p)) = true ∨
      ∃ L, Bewacht (.inr p) L ∧ (.inr p) ∈ S.orte L := by
  have hpair : PaarungAusgenommen (D := D) (.inr p) := ⟨a, p, rfl, hpay, ha⟩
  have hno : ¬ GeteiltV P ws (.inr p) :=
    (nutzlast_braucht_restbeweis hpair (fun q hq => by cases hq; exact hna)).2.1
  rcases List.mem_append.mp hmem with hc | hc
  · rcases hF.1 _ hc with h | ⟨L, hB, hL⟩ | hT
    · exact Or.inl h
    · exact Or.inr ⟨L, hB, hL⟩
    · exact absurd hT hno
  · exact Or.inl (hF.2 _ hc)

/-- **Joint witness for `payload_fuss_braucht_deckung`**: every premise together --
    the cover, the payload in the footprint, the publication with its atomic flag
    and plain payload -- beside a written table and a reached memory-changing run
    (on `nP`, whose tables and functions the witness shares). -/
theorem payload_fuss_braucht_deckung_zeuge :
    FussSX qP (SperrInv.leer pD) (fun _ => true) (GeteiltV qP []) NFn.hauptA ∧
    ((.inr NGlob.zaehler : pD.Tab ⊕ pD.Glob) ∈ fussOrteG qP NFn.hauptA) ∧
    (NGlob.zaehler ∈ pD.nutzlast NGlob.konfig) ∧
    (pD.atomar NGlob.konfig = true) ∧ (pD.atomar NGlob.zaehler = false) ∧
    TraegerSchreibt (D := pD) NFn.hauptA (.inl NTab.tabA) = true ∧
    ∃ W1 : RufMaschineW nD,
      RufErreichbarW nP nO 0 (fun _ => Ordnung.entspannt)
        (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (sp0.globs NGlob.konfig).n = 0 := by
  refine ⟨q_fuss, q_mem, List.mem_cons_self, rfl, rfl, q_schreibt, atomar_nichtleer.2⟩

/-! ## 2. The refusal: an unguarded payload stays refused -/

/-- **A non-atomic payload is refused by the footprint-admission check and never
    admitted** -- even beside the atomic publication that names it. The check only
    ever admits atomics (`nichtatomar_verweigert`); the payload needs the residue
    proof, which is section 4 below. -/
theorem nutzlast_ohne_deckung_verweigert {P : Programm D} {fs : List D.Fn} {f : D.Fn}
    {ws : List D.Fn} {p : D.Glob} (hna : D.atomar p = false) :
    atomarFussB P fs f (.inr p) = false ∧ ¬ GeteiltV P ws (.inr p) := by
  have hB : atomarB (.inr p) = false := hna
  obtain ⟨-, h1, h2⟩ := nichtatomar_verweigert (P := P) (fs := fs) (f := f) (ws := ws) hB
  exact ⟨h1, h2⟩

/-- **Joint witness for `nutzlast_ohne_deckung_verweigert`**: `zaehler` is plain on
    `pD` -- the decided check refuses it and it is not admitted -- beside a written
    table and the memory-changing run. The negative case: an unguarded plain
    payload with no residue proof. -/
theorem nutzlast_ohne_deckung_verweigert_zeuge :
    (pD.atomar NGlob.zaehler = false) ∧
    atomarFussB qP [] NFn.hauptA (.inr NGlob.zaehler) = false ∧
    ¬ GeteiltV qP [] (.inr NGlob.zaehler) ∧
    TraegerSchreibt (D := pD) NFn.hauptA (.inl NTab.tabA) = true ∧
    ∃ W1 : RufMaschineW nD,
      RufErreichbarW nP nO 0 (fun _ => Ordnung.entspannt)
        (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (sp0.globs NGlob.konfig).n = 0 := by
  obtain ⟨h1, h2⟩ := nutzlast_ohne_deckung_verweigert (P := qP) (fs := []) (f := NFn.hauptA)
    (ws := []) (p := NGlob.zaehler) rfl
  exact ⟨rfl, h1, h2, q_schreibt, atomar_nichtleer.2⟩

/-! ## 3. A shared atomic flag is not a lock -/

/-- **A shared atomic flag is not a lock**: the admitted flag `konfig` is shared
    (`GeteiltA`) and at the same time guarded by no lock. No lock-discipline fact
    follows from sharing the flag; the payload cover of section 1 must come from
    locality or a real guard. -/
theorem flagge_ist_kein_schloss :
    GeteiltA nP n1ws (.inr NGlob.konfig) ∧
      ∀ L : nD.Lock, ¬ Bewacht (.inr NGlob.konfig) L :=
  ⟨n1_konfig_geteilt.1, fun L => n1_konfig_geteilt.1.2.1 L⟩

/-- **Joint witness for `flagge_ist_kein_schloss`**: the shared guardless flag beside
    a written table and the reached memory-changing run. -/
theorem flagge_ist_kein_schloss_zeuge :
    GeteiltA nP n1ws (.inr NGlob.konfig) ∧
    (∀ L : nD.Lock, ¬ Bewacht (.inr NGlob.konfig) L) ∧
    TraegerSchreibt (D := nD) NFn.hauptA (.inl NTab.tabA) = true ∧
    ∃ W1 : RufMaschineW nD,
      RufErreichbarW nP nO 0 (fun _ => Ordnung.entspannt)
        (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (sp0.globs NGlob.konfig).n = 0 := by
  refine ⟨flagge_ist_kein_schloss.1, flagge_ist_kein_schloss.2, atomar_nichtleer.1,
    atomar_nichtleer.2⟩

/-! ## 4. The guarded transfer leaves no residue -/

omit [DecidableEq D.Fn] in
/-- **The guarded release/acquire transfer of a payload through its atomic flag leaves
    no observable residue.** Thread `t` writes the flag `a` with release; thread `u`
    acquires exactly that message (fresh: in `W2`'s history but not `W1`'s). Then the
    reader's view at the payload `p` -- which is a different carrier, since the flag
    is atomic and the payload is not -- is at least the writer's view, and every later
    read of the payload by the reader returns a message at or above it. Thin wrapper
    over the accepted `hb_uebergabe`; the payload premises discharge the side
    inequality, nothing about release/acquire is assumed beyond it. -/
theorem bewachte_uebergabe_ohne_rueckstand {P : Programm D} {O : Orakel D} {passes : Nat}
    {ord : D.Glob → Ordnung} {W1 W2 W3 W4 : RufMaschineW D} {t u : Faden}
    {σ1 : Speicher D} {N1 : RufMaschineG D} {wahl1 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu1 : D.Tab ⊕ D.Glob → Nat}
    (h1 : SchrittW P O passes ord W1 t W2 σ1 N1 wahl1 neu1)
    {a : D.Glob} (ha : D.atomar a = true)
    (hw : SchreibG (mitSpeicher W1.g σ1) N1 t (.inr a))
    (ho : ordVon ord (.inr a) = .freigabe)
    {σ3 : Speicher D} {N3 : RufMaschineG D} {wahl3 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu3 : D.Tab ⊕ D.Glob → Nat}
    (h3 : SchrittW P O passes ord W3 u W4 σ3 N3 wahl3 neu3)
    (hl : LiestG (mitSpeicher W3.g σ3) N3 u (.inr a))
    (hm2 : wahl3 (.inr a) ∈ W2.hist (.inr a))
    (hm1 : wahl3 (.inr a) ∉ W1.hist (.inr a))
    {p : D.Glob} (hpay : p ∈ D.nutzlast a) (hna : D.atomar p = false) :
    W1.sicht t (.inr p) ≤ W4.sicht u (.inr p) ∧
      ∀ W5 W6 : RufMaschineW D, RufErreichbarW P O passes ord W4 W5 →
        ∀ (σ5 : Speicher D) (N5 : RufMaschineG D) (wahl5 : D.Tab ⊕ D.Glob → NachrichtW D)
          (neu5 : D.Tab ⊕ D.Glob → Nat),
          SchrittW P O passes ord W5 u W6 σ5 N5 wahl5 neu5 →
          LiestG (mitSpeicher W5.g σ5) N5 u (.inr p) →
            W1.sicht t (.inr p) ≤ (wahl5 (.inr p)).ts := by
  have hx : (.inr p : D.Tab ⊕ D.Glob) ≠ (.inr a) := by
    intro h
    have heq : p = a := by cases h; rfl
    rw [heq] at hna
    rw [ha] at hna
    exact Bool.noConfusion hna
  exact hb_uebergabe h1 hw ho h3 hl hm2 hm1 hx

/-- **Witness for `bewachte_uebergabe_ohne_rueckstand`**: what the transfer adds over
    `hb_uebergabe` -- the flag/payload separation derived jointly from the atomic
    flag, the publication and the plain payload -- beside a written table and the
    reached memory-changing run. The W-step premises are `hb_uebergabe`'s own; no
    in-tree run exhibits a fresh acquire read on a payload program (the stale-read
    run exhibits exactly the complementary case), so they are scoped, not faked. -/
theorem bewachte_uebergabe_ohne_rueckstand_zeuge :
    (pD.atomar NGlob.konfig = true) ∧ (NGlob.zaehler ∈ pD.nutzlast NGlob.konfig) ∧
    (pD.atomar NGlob.zaehler = false) ∧
    ((.inr NGlob.zaehler : pD.Tab ⊕ pD.Glob) ≠ (.inr NGlob.konfig)) ∧
    TraegerSchreibt (D := pD) NFn.hauptA (.inl NTab.tabA) = true ∧
    ∃ W1 : RufMaschineW nD,
      RufErreichbarW nP nO 0 (fun _ => Ordnung.entspannt)
        (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (sp0.globs NGlob.konfig).n = 0 := by
  refine ⟨rfl, List.mem_cons_self, rfl, by decide, q_schreibt, atomar_nichtleer.2⟩

/-! ## CUTS: what is not proved here -/

/-
  CUTS (lane 545, organisation plan N11 -- the residue half of QUELLBRUECKE section 3.3):

  1. No per-access x86-TSO refinement is claimed anywhere in this file: the transfer
     theorem is over source W steps (`hb_uebergabe`), never over target bytes. The
     TSO bridge owns the refinement.
  2. No fresh acquire read is exhibited on a payload program: the transfer witness
     covers the flag/payload separation jointly with a written table and the reached
     memory-changing run; the W-step premises are inherited from the accepted
     `hb_uebergabe`. The in-tree stale-read run exhibits exactly the complementary
     (unfresh) case.
  3. No duty construction for payload-bearing units: `nutzerA_aus_quelle` covers
     atomic-free units only. This file audits the cover such a bridge must discharge
     at the payload; it does not construct duties from `Pflichten src`.
  4. No IR, no validator `Bool`, no lowering, no optimisation admission is defined
     here; the shared IR is consumed as a pending interface, never invented.
  5. No language construct is added and no atomic-rely duty is relaxed: the payload
     stays refused by the admitted-atomic check unless the full guarded transfer
     exists. A shared atomic flag is not a lock (`flagge_ist_kein_schloss`).
-/

#print axioms Gabbro.Grammatik.X86.PayloadResidue.payload_fuss_braucht_deckung
#print axioms Gabbro.Grammatik.X86.PayloadResidue.nutzlast_ohne_deckung_verweigert
#print axioms Gabbro.Grammatik.X86.PayloadResidue.flagge_ist_kein_schloss
#print axioms Gabbro.Grammatik.X86.PayloadResidue.bewachte_uebergabe_ohne_rueckstand

end Gabbro.Grammatik.X86.PayloadResidue
