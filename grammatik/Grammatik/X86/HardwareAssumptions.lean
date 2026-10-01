/-
  File:      Grammatik/X86/HardwareAssumptions.lean
  Subject:   Selected-profile hardware-assumption records and conservative
    target step-cost aggregation over actual finite runs.

  Lane 434 (continuous reserve): generic named hardware assumptions for the
  single direct-compiler architecture -- per-context FP control word,
  per-instruction target cost bounds with explicit refusal (`none` is
  unbounded/refused, never zero), and conservative aggregation (append
  split, explicit per-step bound) over the same finite decoded sequences
  that `lauf` folds. Timing is named separately from source budget-stop
  preservation, physical realization and OS/software user obligations.
  No source-to-target simulation, no LOCK constant latency, no guaranteed
  progress and no ignored waiting is assumed here.
-/
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Gleitprofil

namespace Gabbro.Grammatik.X86

/-- Selected hardware profile: the FP control word the silicon runs under
    plus a per-instruction target cost bound. `kosten b = none` means the
    form has no constant bound here (unbounded/refused), never zero cost.
    Data and admission are separate (`profilGueltig`) so a refused profile
    stays statable. -/
structure HardwareProfil where
  mxcsr : MXCSR
  kosten : Befehl → Option Nat

/-- Profile admission: the carried MXCSR meets the target FP profile.
    Data and admission are separate so a refused profile stays statable. -/
def profilGueltig (p : HardwareProfil) : Bool :=
  mxcsrGueltig p.mxcsr

/-- Target cost of one decoded instruction under the profile: `none` is an
    explicit unbounded/refused form, never silent zero cost. -/
def schrittKosten (p : HardwareProfil) (d : Decodiert) : Option Nat :=
  p.kosten d.befehl

/-- Conservative cost aggregation over a finite decoded sequence: `none`
    propagates, so one unbounded form refuses the whole sum. -/
def laufKosten : HardwareProfil → List Decodiert → Option Nat
  | _, [] => some 0
  | p, d :: rest =>
    match schrittKosten p d with
    | some k =>
      match laufKosten p rest with
      | some t => some (k + t)
      | none => none
    | none => none

/-- Empty sequence costs zero under every profile. -/
theorem laufKosten_nil (p : HardwareProfil) : laufKosten p [] = some 0 := rfl
/-- Unfolding equation for the cons case, proved by `rfl` (definitional).
    All cons-case proofs rewrite with this instead of `simp [laufKosten]`,
    whose recursive equation loops the simplifier (see CUTS). -/
theorem laufKosten_cons (p : HardwareProfil) (d : Decodiert)
    (rest : List Decodiert) :
    laufKosten p (d :: rest) =
      match schrittKosten p d with
      | some k => match laufKosten p rest with
        | some t => some (k + t)
        | none => none
      | none => none := rfl

/-- A refused head refuses the whole aggregation. -/
theorem laufKosten_kopf_verweigert (p : HardwareProfil) (d : Decodiert)
    (rest : List Decodiert) (h : schrittKosten p d = none) :
    laufKosten p (d :: rest) = none := by
  rw [laufKosten_cons, h]

/-- A refused tail refuses the whole aggregation. -/
theorem laufKosten_rest_verweigert (p : HardwareProfil) (d : Decodiert)
    (rest : List Decodiert) (k : Nat) (h : schrittKosten p d = some k)
    (ht : laufKosten p rest = none) :
    laufKosten p (d :: rest) = none := by
  rw [laufKosten_cons, h, ht]

/-- Success head adds its cost to the tail sum. -/
theorem laufKosten_kopf_erfolg (p : HardwareProfil) (d : Decodiert)
    (rest : List Decodiert) (k t : Nat) (h : schrittKosten p d = some k)
    (ht : laufKosten p rest = some t) :
    laufKosten p (d :: rest) = some (k + t) := by
  rw [laufKosten_cons, h, ht]

/-- Cost of an appended sequence splits: the conservative bound of a
    concatenated target sequence is the sum of the two bounds. Both
    success premises are used (head part by induction, tail part at
    the empty prefix). -/
theorem laufKosten_anhang_erfolg (p : HardwareProfil) (l1 l2 : List Decodiert)
    (t1 t2 : Nat) (h1 : laufKosten p l1 = some t1)
    (h2 : laufKosten p l2 = some t2) :
    laufKosten p (l1 ++ l2) = some (t1 + t2) := by
  induction l1 generalizing t1 with
  | nil =>
    rw [laufKosten_nil] at h1
    cases h1
    simp [h2]
  | cons d rest ih =>
    cases hkd : schrittKosten p d with
    | none =>
      rw [laufKosten_cons, hkd] at h1
      dsimp only at h1
      cases h1
    | some k =>
      cases htr : laufKosten p rest with
      | none =>
        rw [laufKosten_cons, hkd, htr] at h1
        dsimp only at h1
        cases h1
      | some tr =>
        have hsplit : laufKosten p (d :: rest) = some (k + tr) := by
          rw [laufKosten_cons, hkd, htr]
        rw [hsplit] at h1
        cases h1
        have hstep : laufKosten p ((d :: rest) ++ l2) = some (k + (tr + t2)) := by
          have e : (d :: rest) ++ l2 = d :: (rest ++ l2) := rfl
          rw [e, laufKosten_cons, hkd]
          have hi := ih tr htr
          rw [hi]
        rw [hstep]
        congr 1
        omega

/-- Conservative target step-cost aggregation with an explicit bound:
    when every decoded step of the finite sequence carries a named cost
    of at most `B`, a successful aggregation totals at most `B` per step.
    The bound hypothesis pins every head cost, the success hypothesis
    pins every head and tail outcome; the conclusion is a genuine
    inequality, not a restatement. Timing only: no execution success,
    progress or waiting claim follows from a cost total. -/
theorem laufKosten_schranke (p : HardwareProfil) (prog : List Decodiert)
    (B t : Nat)
    (hb : ∀ d ∈ prog, ∃ k, schrittKosten p d = some k ∧ k ≤ B)
    (ht : laufKosten p prog = some t) :
    t ≤ B * prog.length := by
  induction prog generalizing t with
  | nil =>
    rw [laufKosten_nil] at ht
    cases ht
    simp
  | cons d rest ih =>
    obtain ⟨k, hk, hkle⟩ := hb d (List.mem_cons.mpr (Or.inl rfl))
    have hbtail : ∀ d' ∈ rest, ∃ k, schrittKosten p d' = some k ∧ k ≤ B :=
      fun d' hm => hb d' (List.mem_cons.mpr (Or.inr hm))
    cases hkd : schrittKosten p d with
    | none =>
      rw [hkd] at hk
      cases hk
    | some k' =>
      cases htr : laufKosten p rest with
      | none =>
        rw [laufKosten_cons, hkd, htr] at ht
        dsimp only at ht
        cases ht
      | some t' =>
        rw [laufKosten_cons, hkd, htr] at ht
        dsimp only at ht
        cases ht
        have hkk : k = k' := Option.some_inj.mp (hk.symm.trans hkd)
        subst hkk
        have hi := ih t' hbtail htr
        rw [List.length_cons, Nat.mul_succ]
        omega

/-! ## Witness profile: named constant bounds, `ret` explicitly refused.

    The bounds are named assumptions for the selected profile, never
    measured silicon latencies. `ret` carries `none`: its target cost
    depends on stack-memory traffic, which no constant named here covers.
    Locked/RMW forms live in `LockedOps` with their own shape count
    (`lockKosten`, never a latency); no LOCK constant latency is assumed. -/

/-- Witness cost table: one constant bound per pilot form, `ret` refused. -/
def zeugeKosten : Befehl → Option Nat
  | .movImm64 _ _ => some 1
  | .movReg64 _ _ => some 1
  | .addReg64 _ _ => some 2
  | .subReg64 _ _ => some 2
  | .xorReg64 _ _ => some 2
  | .cmpReg64 _ _ => some 2
  | .load64 _ _ _ => some 3
  | .store64 _ _ _ => some 3
  | .jump32 _ => some 1
  | .jumpIf32 _ _ => some 1
  | .push64 _ => some 2
  | .pop64 _ => some 2
  | .call32 _ => some 3
  | .ret => none

/-- Witness profile: the architectural reset MXCSR with the witness table. -/
def profilZeuge : HardwareProfil :=
  { mxcsr := 0x1F80, kosten := zeugeKosten }

/-- The witness profile is admitted: its MXCSR meets the target FP profile. -/
theorem profilZeuge_gueltig : profilGueltig profilZeuge = true := by
  decide

/-- Validity is per selected profile, never a global silicon claim: an
    admitted and a refused profile coexist as data. -/
theorem profil_nicht_global : ∃ pOk pNein : HardwareProfil,
    profilGueltig pOk = true ∧ profilGueltig pNein = false :=
  ⟨profilZeuge, ⟨0x9F80, zeugeKosten⟩, by decide, by decide⟩

/-! ## Joint witnesses over the actual reached run.

    The success witness reuses the real store-changing program `zeigeProg`
    and its proved memory change (`zeige_speicher_aendert_sich`): the same
    decoded sequence that aggregates to cost 7 reaches a state whose
    register holds the stored value and whose memory byte observably moved
    from zero to 42. No empty run, no table-free program. -/

/-- The witness run aggregates to cost 1 + 3 + 3 = 7 AND reaches the
    proved store-changing state: joint cost, execution and memory change. -/
theorem laufKosten_zeuge_erfolg :
    laufKosten profilZeuge zeugeProg = some 7 ∧
    ((lauf zeugeProg zeugeZustand).map (fun s => s.register Register.rbx)
      = some 42) ∧
    ((lauf zeugeProg zeugeZustand).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8192))
      = some (BitVec.ofNat 8 42)) ∧
    (zeugeZustand.speicher.bytes (BitVec.ofNat 64 8192)
      = BitVec.ofNat 8 0) := by
  refine ⟨by decide, zeuge_speicher_aendert_sich⟩

/-- Refusal witness: `ret` carries no constant bound, so a lone `ret`
    refuses the aggregation. -/
theorem laufKosten_zeuge_verweigert :
    laufKosten profilZeuge [{ befehl := Befehl.ret, laenge := 1 }] = none := by
  decide

/-! ## Joint instantiations of every generic lemma.

    Each `_zeuge` below instantiates ALL premises of its lemma with joint
    concrete values and proves them: the head/tail costs by `decide`, the
    memory change by the real reached run. -/

/-- `kopf_erfolg` at the witness: `mov` costs 1, the tail costs 6. -/
theorem laufKosten_kopf_erfolg_zeuge :
    laufKosten profilZeuge
      ({ befehl := Befehl.movImm64 Register.rax 42, laenge := 3 } ::
       [{ befehl := Befehl.store64 Register.rsp Register.rax
            (BitVec.ofNat 32 0), laenge := 4 },
        { befehl := Befehl.load64 Register.rbx Register.rsp
            (BitVec.ofNat 32 0), laenge := 4 }]) = some (1 + 6) :=
  laufKosten_kopf_erfolg profilZeuge _ _ 1 6 (by decide) (by decide)

/-- `kopf_verweigert` at the witness: a refused `ret` head refuses. -/
theorem laufKosten_kopf_verweigert_zeuge :
    laufKosten profilZeuge
      ({ befehl := Befehl.ret, laenge := 1 } :: zeugeProg) = none :=
  laufKosten_kopf_verweigert profilZeuge _ _ (by decide)

/-- `rest_verweigert` at the witness: a good `mov` head, refused tail. -/
theorem laufKosten_rest_verweigert_zeuge :
    laufKosten profilZeuge
      [{ befehl := Befehl.movImm64 Register.rax 42, laenge := 3 },
       { befehl := Befehl.ret, laenge := 1 }] = none :=
  laufKosten_rest_verweigert profilZeuge _ _ 1 (by decide) (by decide)

/-- `anhang_erfolg` at the witness: 1 + 6 across the split. -/
theorem laufKosten_anhang_zeuge :
    laufKosten profilZeuge
      ([{ befehl := Befehl.movImm64 Register.rax 42, laenge := 3 }] ++
       [{ befehl := Befehl.store64 Register.rsp Register.rax
            (BitVec.ofNat 32 0), laenge := 4 },
        { befehl := Befehl.load64 Register.rbx Register.rsp
            (BitVec.ofNat 32 0), laenge := 4 }]) = some (1 + 6) :=
  laufKosten_anhang_erfolg profilZeuge _ _ 1 6 (by decide) (by decide)

/-- The per-step bound hypothesis holds jointly on the witness program:
    every step costs at most 3. -/
theorem laufKosten_schranke_zeuge_hbound :
    ∀ d ∈ zeugeProg, ∃ k, schrittKosten profilZeuge d = some k ∧ k ≤ 3 := by
  have e : zeugeProg =
      [{ befehl := Befehl.movImm64 Register.rax 42, laenge := 3 },
       { befehl := Befehl.store64 Register.rsp Register.rax
          (BitVec.ofNat 32 0), laenge := 4 },
       { befehl := Befehl.load64 Register.rbx Register.rsp
          (BitVec.ofNat 32 0), laenge := 4 }] := rfl
  rw [e]
  intro d hd
  rw [List.mem_cons, List.mem_cons, List.mem_cons] at hd
  rcases hd with rfl | rfl | rfl | hnil
  · exact ⟨1, rfl, by decide⟩
  · exact ⟨3, rfl, by decide⟩
  · exact ⟨3, rfl, by decide⟩
  · cases hnil

/-- `schranke` at the witness: 7 ≤ 3 · 3 on the real program. -/
theorem laufKosten_schranke_zeuge : 7 ≤ 3 * zeugeProg.length :=
  laufKosten_schranke profilZeuge zeugeProg 3 7
    laufKosten_schranke_zeuge_hbound (by decide)

/- CUTS: what is not proved here.
    - No source-to-target simulation, lowering or correspondence: costs are
      named per decoded target form only. Nothing connects a total to source
      `ops` budget stops (`Budget.lean`), and a cost total preserves no
      source stop.
    - No LOCK constant latency and no latency claim at all: the table holds
      named bounds, never measured silicon cycles. Locked/RMW forms live in
      `LockedOps` (`SperrBefehl`) with their own shape count (`lockKosten`,
      never a latency); `ret` is explicitly refused (`none`).
    - No guaranteed progress, no ignored waiting: a finite total over a
      finite list says nothing about liveness; halt and waiting shapes are
      unmodelled.
    - Timing is named separately from physical realization (no hardware is
      measured), from OS/software obligations (context save/restore is user
      logic per `Gleitprofil`; syscalls are out of scope), and from source
      budget-stop preservation.
    - Per-byte TSO is not multi-byte atomicity: aggregation is sequential
      over the decoded list (`lauf`-shaped, contemporaneous, not concurrent);
      tearing and interleavings stay open.
    - Narrower operand widths (8/16/32-bit forms) do not exist in `Befehl`,
      so they have no rows: an extension needs new constructors plus rows,
      never a silent reuse.
    - Flag undefinedness (`Flags.af = none`), sticky MXCSR bits and NaN
      payloads are unmodelled: admission checks the control word, not the
      sticky flags (as in `Gleitprofil`); payload equality is never concluded.
    - Code immutability: `laufKosten` folds a fixed decoded list;
      self-modifying code is out of scope.
    - Budget stops and observation channels: no claim the bounds are
      observable or measurable at runtime, and none that a refusal is
      reported anywhere but in the `Option`.
    - Hardware faults and profile admission refusals differ: a failed memory
      access (`Ausfuehrung` step `none`) and an unbounded cost form (here
      `none`) are two separate refusal channels; one never stands in for
      the other.
    - Proof-engineering note (not a semantic gap): `simp only [laufKosten]`
      on success-shape cons goals loops the simplifier on the recursive
      equation and kills the worker; all cons proofs rewrite with the `rfl`
      equation `laufKosten_cons` instead.
-/

#print axioms laufKosten_nil
#print axioms laufKosten_cons
#print axioms laufKosten_kopf_verweigert
#print axioms laufKosten_rest_verweigert
#print axioms laufKosten_kopf_erfolg
#print axioms laufKosten_anhang_erfolg
#print axioms laufKosten_schranke
#print axioms profilZeuge_gueltig
#print axioms profil_nicht_global
#print axioms laufKosten_zeuge_erfolg
#print axioms laufKosten_zeuge_verweigert
#print axioms laufKosten_kopf_erfolg_zeuge
#print axioms laufKosten_kopf_verweigert_zeuge
#print axioms laufKosten_rest_verweigert_zeuge
#print axioms laufKosten_anhang_zeuge
#print axioms laufKosten_schranke_zeuge_hbound
#print axioms laufKosten_schranke_zeuge

end Gabbro.Grammatik.X86
