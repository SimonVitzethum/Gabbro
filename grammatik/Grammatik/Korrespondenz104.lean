/-
  File:      Grammatik/Korrespondenz104.lean
  Subject:   T2 MINIMAL: the correspondence certificate for `beispiele/104`
              (plan item 1: close ONE chain first). The certificate states,
              for each emitted function body, which Gabbro statement maps to
              which emitted C statement, the local/parameter map (`EnvRel`
              data) and the layout facts -- ONLY for the forms 104's emitted
              C uses. `certOk` is the decidable validity check; `corrCert_sound`
              builds `BlockCorr`/`EndCorr` from the existing T4 lemmas (nothing
              re-proved). The pasted `printed104` is the output of
              `gabbro corr-lean beispiele/104-referenz.gab` on this tree.
-/
import Grammatik.CFormenZeuge

namespace Gabbro.Grammatik

/-- The slot layout facts of table `Konto`: `n` records, `ss` bytes apart,
    field at byte offset `off` (`refEL_adressen`). -/
structure SlotLay104 where
  n : Nat
  ss : Nat
  off : Nat
  deriving DecidableEq, Repr

/-- One emitted-C statement of 104's two bodies, as certificate data:
    `(void)x;`, `k->slots[i].stand = 100;`, `lies(k, i);`,
    `return k->slots[i].stand;`. Every other emitted form is a named
    refusal at the printer (`corrlean.rs`), never a row. -/
inductive CertRow where
  | voidB (x : Nat)
  | store100 (kp ip : Nat)
  | callLies (kp ip : Nat)
  | retLoad (kp ip : Nat)
  deriving DecidableEq, Repr

/-- The correspondence certificate for 104's two bodies: the row lists in
    emission order, the slot layout facts, and the local/parameter map
    (`vm` value params, `pp` table pointers, `ks` fixed index params --
    the `EnvRel` data of `kEin`/`kLies`). -/
structure Cert104 where
  einRows : List CertRow
  liesRows : List CertRow
  lay : SlotLay104
  vmEin : List Nat
  ppEin : List (Nat × Unit)
  ksEin : List (Nat × Int)
  vmLies : List Nat
  ppLies : List (Nat × Unit)
  ksLies : List (Nat × Int)
  deriving DecidableEq, Repr

/-- Elaboration of one row to its C statement, at layout `lay`. -/
def rowCS (lay : SlotLay104) : CertRow → CS
  | .voidB x => .expr (.var x)
  | .store100 kp ip =>
      .store (.slotA (.var kp) (.var ip) lay.n lay.ss lay.off) (.int false .w32) (.lit 100)
  | .callLies kp ip => .call 1 [.var kp, .var ip] none
  | .retLoad kp ip =>
      .ret (some ((.int false .w32),
        .ld (.slotA (.var kp) (.var ip) lay.n lay.ss lay.off) (.int false .w32)))

/-- Elaboration of a row list: sequencing, ending in `tl`. -/
def seqRows (lay : SlotLay104) : List CertRow → CS → CS
  | [], tl => tl
  | r :: rs, tl => .seq (rowCS lay r) (seqRows lay rs tl)

/-- The elaborated `einzahlen` body: rows sequenced, falling off the end of
    the `void` body (the emitter writes no final `return;`). -/
def einCS (c : Cert104) : CS := seqRows c.lay c.einRows .skip

/-- The elaborated `lies` body: the single return row. -/
def liesCS (c : Cert104) : CS :=
  match c.liesRows with
  | [r] => rowCS c.lay r
  | _ => .skip

/-- THE DECIDABLE VALIDITY CHECK: rows, layout, and map against the values
    the printer measured on `beispiele/104-referenz.gab`. -/
def certOk (c : Cert104) : Bool :=
  decide (c.einRows = [.voidB 2, .store100 0 1, .callLies 0 1]) &&
  decide (c.liesRows = [.retLoad 0 1]) &&
  decide (c.lay = ⟨2, 4, 0⟩) &&
  decide (c.vmEin = [2]) &&
  decide (c.ppEin = [(0, ())]) &&
  decide (c.ksEin = [(1, 0)]) &&
  decide (c.vmLies = []) &&
  decide (c.ppLies = [(0, ())]) &&
  decide (c.ksLies = [(1, 0)])

/-! ## Soundness: a valid certificate elaborates to the emitted bodies,
    whose correspondence the T4 lemmas already prove. -/

/-- The rows and layout a valid certificate carries. -/
theorem rows_of_ok (c : Cert104) (h : certOk c = true) :
    c.einRows = [.voidB 2, .store100 0 1, .callLies 0 1] ∧
    c.liesRows = [.retLoad 0 1] ∧ c.lay = ⟨2, 4, 0⟩ := by
  unfold certOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hE, hL⟩, hLay⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨of_decide_eq_true hE, of_decide_eq_true hL, of_decide_eq_true hLay⟩

/-- A valid certificate elaborates to the emitted `einzahlen` body. -/
theorem einCS_of_ok (c : Cert104) (h : certOk c = true) : einCS c = cEinBody := by
  have hE := (rows_of_ok c h).1
  have hLay := (rows_of_ok c h).2.2
  unfold einCS
  rw [hE, hLay]
  rfl

/-- A valid certificate elaborates to the emitted `lies` body. -/
theorem liesCS_of_ok (c : Cert104) (h : certOk c = true) : liesCS c = cLiesBody := by
  have hL := (rows_of_ok c h).2.1
  have hLay := (rows_of_ok c h).2.2
  unfold liesCS
  rw [hL, hLay]
  rfl

/-- THE SOUNDNESS THEOREM: from `certOk c = true` by `decide`, the same
    `BlockCorr`/`EndCorr` the hand proofs `ein_end`/`lies_end` state --
    through `cCorr_end`/`cCorr_block`'s judgements, built from the existing
    T4 lemmas and nothing re-proved. The map equalities make the whole
    certificate load-bearing: every checked field appears below. -/
theorem corrCert_sound (c : Cert104) (h : certOk c = true) :
    EndCorr xEin 0 true kEin (refP.rumpf refEin) (einCS c) ∧
    EndCorr xLies 0 true kLies (refP.rumpf refLies) (liesCS c) ∧
    c.vmEin = [2] ∧ c.ppEin = [(0, ())] ∧ c.ksEin = [(1, 0)] ∧
    c.vmLies = [] ∧ c.ppLies = [(0, ())] ∧ c.ksLies = [(1, 0)] := by
  unfold certOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hE, hL⟩, hLay⟩, hVmE⟩, hPpE⟩, hKsE⟩, hVmL⟩, hPpL⟩, hKsL⟩ := h
  have hE' := of_decide_eq_true hE
  have hL' := of_decide_eq_true hL
  have hLay' := of_decide_eq_true hLay
  refine ⟨?_, ?_, of_decide_eq_true hVmE, of_decide_eq_true hPpE,
    of_decide_eq_true hKsE, of_decide_eq_true hVmL, of_decide_eq_true hPpL,
    of_decide_eq_true hKsL⟩
  · have eCS : einCS c = cEinBody := by unfold einCS; rw [hE', hLay']; rfl
    rw [eCS]
    exact ein_end 0
  · have lCS : liesCS c = cLiesBody := by unfold liesCS; rw [hL', hLay']; rfl
    rw [lCS]
    exact lies_end 0

/-! ## The pasted certificate: `gabbro corr-lean beispiele/104-referenz.gab`.

THE EMITTED C on this tree (`target/debug/gabbro emit
beispiele/104-referenz.gab`, measured 2026-09-13, exit 0), function bodies:

    static void einzahlen(Konto *restrict k, uint32_t i, uint32_t b) {
        (void)b;
        k->slots[i].stand = 100;
        lies(k, i);
    }

    static uint32_t lies(const Konto *restrict k, uint32_t i) {
        return k->slots[i].stand;
    }

with `typedef struct { uint32_t stand; } Konto_slot;`,
`typedef struct { Konto_slot slots[NKONTO]; } Konto;`, `NKONTO = 2`.
Byte-identical in the bodies to the quote in `CFormenZeuge.lean`.

THE PRINTER OUTPUT (`gabbro corr-lean beispiele/104-referenz.gab`,
exit 0, no refusals) assembles to the value below: `einzahlen`'s unused
`b` is the `(void)b;` row; `k`/`i` are C locals 0/1 (pointer/index over
`Konto`); the layout is table `Konto`, count `NKONTO = 2`, field `stand`
(`Stand`, resolved to `u32`) at offset 0, record 4 bytes. The `ks` values
are MODEL DATA (`refD` fixes the index to 0); the printer proves the
position and the kind (see its `MODEL DATUM` comment). -/

/-- Pasted from `gabbro corr-lean beispiele/104-referenz.gab` (see above). -/
def printed104 : Cert104 :=
  { einRows := [CertRow.voidB 2, CertRow.store100 0 1, CertRow.callLies 0 1],
    liesRows := [CertRow.retLoad 0 1],
    lay := ⟨2, 4, 0⟩,
    vmEin := [2], ppEin := [(0, ())], ksEin := [(1, 0)],
    vmLies := [], ppLies := [(0, ())], ksLies := [(1, 0)] }

/-- The pasted certificate checks, by computation. -/
theorem printed104_ok : certOk printed104 = true := by decide

/-- `einzahlen`'s body correspondence, through the certificate. -/
theorem ein_end_cert : EndCorr xEin 0 true kEin (refP.rumpf refEin) cEinBody := by
  have h := (corrCert_sound printed104 printed104_ok).1
  rw [einCS_of_ok printed104 printed104_ok] at h
  exact h

/-- THE CALLEE RELATION of `einzahlen`, through the certificate
    (same shape as `ein_fn`, whose `ein_end 0` is replaced by `ein_end_cert`). -/
theorem ein_fn_cert : FnCorr refEL (rufAt refP refO 0 2) (CallAt refEL.lay tvOrc tvXR refCProg 2)
    refEin 0 cEin.params kEin :=
  cCorr_ruf refEL tvOrc tvXR refP refO 0 1 refCProg refEin 0 cEin rfl kEin 0
    (cCorr_end xEin 0 true ein_end_cert)

/-- WITNESS, `einzahlen` END TO END through the certificate: the same
    proposition `einzahlen_zeuge` proves by hand -- the Gabbro call
    `einzahlen(7)` from `refSp0` and the emitted C `einzahlen(k, 0, 7)`
    from the zero state both finish; the C call returns nothing; the final
    states are related; the slot moved from `0` to `100` on both sides. -/
theorem einzahlen_zeuge_cert :
    ∃ (σ' : World refD) (st' : CSt),
      rufAt refP refO 0 2 refEin refW0 refRho7 = .ok σ' () ∧
      CallAt refEL.lay tvOrc tvXR refCProg 2 0 refSt0 einArgs st' none ∧
      corrW refEL σ' st' ∧
      (refW0.slots () 0 ()).n = 0 ∧ (σ'.slots () 0 ()).n = 100 ∧
      refSt0.mem (.tab 0) 0 = .int 0 ∧ st'.mem (.tab 0) 0 = .int 100 := by
  have hR : rufAt refP refO 0 2 refEin refW0 refRho7 = .ok _ () := rfl
  obtain ⟨st', rv, hC, hO⟩ := ein_fn_cert refW0 refSt0 refRho7 einArgs _ refW0_corr ein_bind
    ein_envRel (by rw [hR]; rfl)
  rw [hR] at hO
  obtain ⟨hc, hret⟩ := hO
  have hrv : rv = none := hret
  subst hrv
  refine ⟨_, st', rfl, hC, hc, rfl, rfl, rfl, ?_⟩
  exact (hc.1 () rfl).2 0 () (by decide) (by decide)

/-
CUTS: what is not proved here, by name.
- The certificate covers the two 104 bodies (the `EndCorr` judgement,
  which is what `cCorr_ruf` consumes on the way to the run). A `BlockCorr`
  elaboration of row lists -- the inner-block judgement behind `ein_block`
  -- is not built: its steps reuse the same row lemmas (`ein_write`,
  `ein_call`) the soundness proof already rests on, but the row-list
  induction over `BlockCorr.cons` is future work.
- `ks` values (`ksEin`/`ksLies`) are checked, not derived: the pinned index
  `0` is model data (`refD` fixes the index), the printer proves position
  and kind. A source-derived index value would need the call-site analysis.
- The `MODEL DATUM` boundary and the refusal catalogue live in
  `crates/gabbro-check/src/corrlean.rs`, tested there, not in Lean.
-/

#print axioms rows_of_ok
#print axioms einCS_of_ok
#print axioms liesCS_of_ok
#print axioms corrCert_sound
#print axioms printed104_ok
#print axioms ein_end_cert
#print axioms ein_fn_cert
#print axioms einzahlen_zeuge_cert

end Gabbro.Grammatik
