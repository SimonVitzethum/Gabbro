/-
  File:      Grammatik/X86/AccessList.lean
  Subject:   Single owner for the access list of one G step (wave-B item B1).

  One proved `accessList` extraction over the REAL source model: the reads
  (carrier plus pre-state value), the writes (carrier plus post-state value)
  and the RMW targets of one `RufSchrittG` step, with completeness stated
  ONCE against `LiestG`/`SchreibG`/`ZugriffG` (RennfreiVoll.lean). Both
  consumers -- the TSO bridge (D-access/L-access-complete) and the IR
  lowering map -- cite this owner instead of proving their own inversion
  (review finding REVIEW-TSO.md section 5.2). No new evaluator: the
  extraction reads the decided `zugriffe`/`ereignisse` trace delta plus the
  endpoint memories. A step shape with no covered access is the explicit
  constructor `ZugriffBefund.luecke`, never a silent empty list.
-/
import Grammatik.RennfreiVoll
import Grammatik.Speichermodell.RMW
import Grammatik.TravAwaitsLauf

namespace Gabbro.Grammatik.X86

variable {D : Deklaration}

/-- The value held by one carrier: the whole slot function of a table,
    the single value of a global. The TYPE depends only on `D` and the
    carrier; the CONTENT is read from an endpoint memory. -/
def TraegerWert (D : Deklaration) : D.Tab ⊕ D.Glob → Type
  | .inl t => Int → ∀ f : D.Feld t, Wert D (D.typ t f)
  | .inr g => Wert D (D.gtyp g)

/-- The value of one carrier in one memory. -/
def traegerWert (s : Speicher D) (c : D.Tab ⊕ D.Glob) : TraegerWert D c :=
  match c with
  | .inl t => s.slots t
  | .inr g => s.globs g

/-! ## 1. The single-owner extraction. -/

/-- One covered access: a read carries the PRE-state value (what the step
    observed), a write carries the POST-state value (what the step left).
    No silent shapes: anything this type cannot name is `luecke` below. -/
inductive ZugriffEintrag (D : Deklaration) where
  | liest (c : D.Tab ⊕ D.Glob) (v : TraegerWert D c)
  | schreibt (c : D.Tab ⊕ D.Glob) (v : TraegerWert D c)

/-- The finding of one step: either the complete entry list, or the
    EXPLICIT refusal `luecke` (an uncovered access shape). `luecke` is a
    constructor, never an empty list passed off as complete: incompleteness
    is unsoundness, recorded OPEN (policy of WORK-ALLOCATION.md item B1). -/
inductive ZugriffBefund (D : Deklaration) where
  | voll : List (ZugriffEintrag D) → ZugriffBefund D
  | luecke : ZugriffBefund D

/-- The entries of one step, from the decided trace delta plus the endpoint
    memories. Reads take the pre-state value, writes the post-state value. -/
def eintraege (M M' : RufMaschineG D) (f : Faden) : List (ZugriffEintrag D) :=
  (zugriffe M M' f).map fun (c, w) =>
    match w with
    | true => .schreibt c (traegerWert M'.speicher c)
    | false => .liest c (traegerWert M.speicher c)

/-- THE single owner: the access list of one G step. Both the TSO bridge
    (D-access) and the IR lowering map cite this function. -/
def accessList (M M' : RufMaschineG D) (f : Faden) : ZugriffBefund D :=
  .voll (eintraege M M' f)

/-- A read-modify-write target of one step: the step head is an `exchange`
    of `g` (RMW.lean pattern). Behavioural read-plus-write on one global
    without an exchange head is NOT an RMW: no local token makes two atomic
    reads equal and no silent RMW is manufactured here. -/
def IstRMW (M : RufMaschineG D) (u : Faden) (g : D.Glob) : Prop :=
  ExchangeKopf M u g

/-- Validator admission: only a complete finding passes. The bridge and the
    IR may consume a finding only where this `Bool` is `true`. -/
def pruefeBefund : ZugriffBefund D → Bool
  | .voll _ => true
  | .luecke => false

/-! ## 2. Completeness, stated once. -/

/-- Reads are exactly the `liest` entries (with the observed pre-value). -/
theorem eintraege_liest (M M' : RufMaschineG D) (f : Faden) (c : D.Tab ⊕ D.Glob) :
    LiestG M M' f c ↔ ∃ v, ZugriffEintrag.liest c v ∈ eintraege M M' f := by
  unfold LiestG eintraege
  constructor
  · intro h
    exact ⟨_, List.mem_map.mpr ⟨(c, false), h, rfl⟩⟩
  · rintro ⟨v, h⟩
    obtain ⟨⟨c', w⟩, hm, he⟩ := List.mem_map.mp h
    cases w <;> cases he
    exact hm

/-- Recorded writes are exactly the `schreibt` entries (with the left
    post-value). -/
theorem eintraege_schreibt_aufgezeichnet (M M' : RufMaschineG D) (f : Faden)
    (c : D.Tab ⊕ D.Glob) :
    (c, true) ∈ zugriffe M M' f ↔
      ∃ v, ZugriffEintrag.schreibt c v ∈ eintraege M M' f := by
  unfold eintraege
  constructor
  · intro h
    exact ⟨_, List.mem_map.mpr ⟨(c, true), h, rfl⟩⟩
  · rintro ⟨v, h⟩
    obtain ⟨⟨c', w⟩, hm, he⟩ := List.mem_map.mp h
    cases w <;> cases he
    exact hm

/-- Writes are exactly the `schreibt` entries plus the changed-memory
    disjunct, stated and never dropped: an unrecorded change (oracle or
    device memory outside the trace) stays visible as `TraegerGleich`. -/
theorem schreibG_voll (M M' : RufMaschineG D) (f : Faden) (c : D.Tab ⊕ D.Glob) :
    SchreibG M M' f c ↔
      (∃ v, ZugriffEintrag.schreibt c v ∈ eintraege M M' f) ∨
        ¬ TraegerGleich M'.speicher M.speicher c := by
  unfold SchreibG
  rw [eintraege_schreibt_aufgezeichnet]

/-- Accesses are exactly the read or write entries plus the changed-memory
    disjunct. This is the completeness lemma both consumers cite. -/
theorem zugriffG_voll (M M' : RufMaschineG D) (f : Faden) (c : D.Tab ⊕ D.Glob) :
    ZugriffG M M' f c ↔
      (∃ v, ZugriffEintrag.liest c v ∈ eintraege M M' f) ∨
        (∃ v, ZugriffEintrag.schreibt c v ∈ eintraege M M' f) ∨
          ¬ TraegerGleich M'.speicher M.speicher c := by
  unfold ZugriffG
  constructor
  · rintro (⟨w, h⟩ | h)
    · cases w with
      | true =>
        exact Or.inr (Or.inl
          ((eintraege_schreibt_aufgezeichnet M M' f c).mp h))
      | false =>
        exact Or.inl ((eintraege_liest M M' f c).mp h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl ⟨false, (eintraege_liest M M' f c).mpr h⟩
    · exact Or.inl ⟨true,
        (eintraege_schreibt_aufgezeichnet M M' f c).mpr h⟩
    · exact Or.inr h

/-! ## 3. The owner never refuses its own extraction. -/

/-- The owner never emits `luecke`: every step has a complete finding. -/
theorem accessList_kein_luecke (M M' : RufMaschineG D) (f : Faden) :
    accessList M M' f ≠ .luecke := by
  unfold accessList
  intro h
  cases h

/-- The owner's finding always passes admission. -/
theorem accessList_besteht (M M' : RufMaschineG D) (f : Faden) :
    pruefeBefund (accessList M M' f) = true := by
  unfold accessList pruefeBefund
  rfl

/-- PROVED REFUSAL: the explicit `luecke` constructor fails admission.
    A bridge or IR consumer that meets `luecke` must refuse; there is no
    silent complete reading of it. -/
theorem luecke_faellt : pruefeBefund (.luecke : ZugriffBefund D) = false := by
  rfl

/-! ## 4. The multi-access leaf: `exchange` (RMW pattern reuse). -/

/-- Every `exchange` step reads and writes its global: the read entry is in
    the list, the write is covered (recorded entry or changed memory), and
    the step is an RMW target. This reuses `exchange_liest_schreibt`
    (RMW.lean) instead of duplicating its rule inversion: the owner cites
    the pattern, single-owner principle of REVIEW-TSO.md section 5.2. -/
theorem exchange_rmw_voll {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {u : Faden} {g : D.Glob}
    (hk : ExchangeKopf M u g) (hs : RufSchrittG P O passes M u M') :
    IstRMW M u g ∧
      (∃ v, ZugriffEintrag.liest (.inr g : D.Tab ⊕ D.Glob) v ∈
        eintraege M M' u) ∧
      SchreibG M M' u (.inr g) := by
  have h := exchange_liest_schreibt hk hs
  exact ⟨hk, (eintraege_liest M M' u _).mp h.1, h.2⟩

/-- An `exchange` step with a second recorded read carrier lists two
    distinct read carriers: the exchanged global and the footprint carrier
    the new value was computed from (`neuE.orte`). All premises are used:
    `hk`/`hs` for the exchange's own read, `h2` for the second carrier's
    read entry, `hne` for distinctness. -/
theorem exchange_zwei_liest {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {u : Faden} {g : D.Glob} {c : D.Tab ⊕ D.Glob}
    (hk : ExchangeKopf M u g) (hs : RufSchrittG P O passes M u M')
    (h2 : LiestG M M' u c) (hne : c ≠ .inr g) :
    (∃ v₁, ZugriffEintrag.liest (.inr g : D.Tab ⊕ D.Glob) v₁ ∈
      eintraege M M' u) ∧
      (∃ v₂, ZugriffEintrag.liest c v₂ ∈ eintraege M M' u) ∧
        c ≠ .inr g := by
  have h := exchange_liest_schreibt hk hs
  exact ⟨(eintraege_liest M M' u _).mp h.1,
    (eintraege_liest M M' u c).mp h2, hne⟩

/-! ## 5. Concrete witness: reached memory-changing run. -/

/-- CONCRETE WITNESS on the reached `taP` run (29 steps, thread 0 then
    thread 1): step 24 reads `flag` (recorded read event, hence a `liest`
    entry with the observed pre-value); step 16 publishes `flag` (`0 -> 1`,
    a memory change); the same run writes the table `tab[0]` (`0 -> 1`),
    so the program is nondegenerate; the post-write value of `flag` is `1`.
    Jointly: a reached run with memory-changing steps on a program whose
    tables are written. -/
theorem accessList_ta_zeuge :
    ∃ (ms : Nat → RufMaschineG taD) (fs : Nat → Faden),
      LaufG taP taO 0 (RufStartG taP taSp taInit) ms fs 29 ∧
      fs 16 = 0 ∧ fs 24 = 1 ∧
      LiestG (ms 24) (ms 25) (fs 24) (Sum.inr ()) ∧
      (∃ v, ZugriffEintrag.liest (Sum.inr ()) v ∈
        eintraege (ms 24) (ms 25) (fs 24)) ∧
      SchreibG (ms 16) (ms 17) (fs 16) (Sum.inr ()) ∧
      ¬ TraegerGleich (ms 17).speicher (ms 16).speicher (Sum.inr ()) ∧
      ¬ TraegerGleich (ms 5).speicher (ms 4).speicher (Sum.inl ()) ∧
      (traegerWert (ms 17).speicher (Sum.inr ())).n = 1 := by
  obtain ⟨ms, fs, hl, _, _, hf16, hf24, _, _, _, hm4, hm5, _, _, hm16, hm17, _,
      _, hread, _⟩ := taLauf
  have hr : LiestG (ms 24) (ms 25) (fs 24) (Sum.inr ()) := by
    rw [hf24]
    exact hread
  have hflag : ¬ TraegerGleich (ms 17).speicher (ms 16).speicher (Sum.inr ()) := by
    intro h
    have h' : (ms 17).speicher.globs () = (ms 16).speicher.globs () := h
    have hcon := congrArg Zahl.n h'
    rw [hm16, hm17] at hcon
    exact absurd hcon (by decide)
  have htab : ¬ TraegerGleich (ms 5).speicher (ms 4).speicher (Sum.inl ()) := by
    intro h
    have h' : (ms 5).speicher.slots () = (ms 4).speicher.slots () := h
    have hcon := congrArg Zahl.n (congrFun (congrFun h' 0) ())
    rw [hm4, hm5] at hcon
    exact absurd hcon (by decide)
  have hwert : (traegerWert (ms 17).speicher (Sum.inr ())).n = 1 := hm17
  exact ⟨ms, fs, hl, hf16, hf24, hr, (eintraege_liest _ _ _ _).mp hr,
    Or.inr hflag, hflag, htab, hwert⟩

/- CUTS:
    - Generic completeness (`eintraege_liest`, `eintraege_schreibt_aufgezeichnet`,
      `schreibG_voll`, `zugriffG_voll`) holds for EVERY step uniformly, hence for
      every `RufSchrittG` rule, without per-rule inversion. The per-rule SYNTACTIC
      classification (which rule yields which access shape, the micro-event labels
      of D-lower) stays OPEN for the non-exchange rules (~69 of ~70): consumers
      cite the generic lemmas, not a rule table.
    - The recorded-write entry of an `exchange` step is not re-derived here: that
      would duplicate the 70-case inversion of `exchange_liest_schreibt`
      (single-owner principle, REVIEW-TSO.md section 5.2). The `SchreibG` form
      (recorded entry or changed memory) is kept instead.
    - No concrete two-carrier `exchange` RULE application is constructed (it would
      need the full rule premises: head, permissions, holdings, evaluation).
      The two-carrier shape is proved conditionally (`exchange_zwei_liest`, all
      premises used) and the memory-changing reached run concretely
      (`accessList_ta_zeuge` on `taP`).
    - Values are whole-carrier slices (a table's slot function, a global's value)
      from the endpoint memories; the canonical events carry no values, so this
      file does not invent any. Byte-level values, alignment, tearing and TSO
      visibility stay OPEN (lanes B2/B4); per-byte TSO proves byte facts only.
    - No TSO bridge (D-tso/L-read/L-write/L-view/L-step/L-run), no IR lowering
      map, no source-to-final-bytes claim. The shared IR (lane 287) is pending;
      no substitute IR is invented here.
    - Consumer interface (OPEN until cited): the bridge D-access/L-access-complete
      and the IR lowering map cite `accessList`, `eintraege_liest`,
      `eintraege_schreibt_aufgezeichnet`, `schreibG_voll`, `zugriffG_voll` and
      admit only findings with `pruefeBefund = true`. The refusal `Bool` is
      validator/profile admission, never an invented hardware fault.
    - No cost, contract, progress, timing, float, ABI or whole-image claim.
-/

#print axioms eintraege_liest
#print axioms eintraege_schreibt_aufgezeichnet
#print axioms schreibG_voll
#print axioms zugriffG_voll
#print axioms accessList_kein_luecke
#print axioms accessList_besteht
#print axioms luecke_faellt
#print axioms exchange_rmw_voll
#print axioms exchange_zwei_liest
#print axioms accessList_ta_zeuge

end Gabbro.Grammatik.X86
