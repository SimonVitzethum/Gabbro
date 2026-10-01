/-
  File:      Grammatik/X86/RegisterInterference.lean
  Subject:   Canonical register reads/writes and fail-closed interference
             certificates for the actual pilot instructions.

  Lane 427 (continuous reserve): reusable facts over the canonical
  `Befehl`/`Zustand`/`schritt` vocabulary only (`Typen`, `Ausfuehrung`,
  `Zugriffe`). No second IR, no invented liveness: interference edges
  and live sets are DECLARED inputs the future accepted IR supplies
  with validation; this file checks them fail-closed. Actual source
  allocation refinement stays OPEN.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Zugriffe

namespace Gabbro.Grammatik.X86

/-- Canonical register reads of one pilot instruction, pre-state view.
    Stack forms read `rsp`; `call` reads `rsp`; memory address bases read. -/
def regLiest : Befehl → List Register
  | .movImm64 _ _ => []
  | .movReg64 _ src => [src]
  | .addReg64 dst src => [dst, src]
  | .subReg64 dst src => [dst, src]
  | .xorReg64 dst src => [dst, src]
  | .cmpReg64 lhs rhs => [lhs, rhs]
  | .load64 _ base _ => [base]
  | .store64 base src _ => [base, src]
  | .jump32 _ => []
  | .jumpIf32 _ _ => []
  | .push64 src => [src, .rsp]
  | .pop64 _ => [.rsp]
  | .call32 _ => [.rsp]
  | .ret => [.rsp]

/-- Canonical register writes of one pilot instruction.
    `cmp`/jumps write none; stack forms write `rsp`. -/
def regSchreibt : Befehl → List Register
  | .movImm64 dst _ => [dst]
  | .movReg64 dst _ => [dst]
  | .addReg64 dst _ => [dst]
  | .subReg64 dst _ => [dst]
  | .xorReg64 dst _ => [dst]
  | .cmpReg64 _ _ => []
  | .load64 dst _ _ => [dst]
  | .store64 _ _ _ => []
  | .jump32 _ => []
  | .jumpIf32 _ _ => []
  | .push64 _ => [.rsp]
  | .pop64 dst => [dst, .rsp]
  | .call32 _ => [.rsp]
  | .ret => [.rsp]

/-! ## 1. Per-form equations (all 14 pilot constructors). -/

theorem reg_movImm64 (dst : Register) (v : Wort) :
    regLiest (.movImm64 dst v) = [] ∧ regSchreibt (.movImm64 dst v) = [dst] :=
  ⟨rfl, rfl⟩

theorem reg_movReg64 (dst src : Register) :
    regLiest (.movReg64 dst src) = [src] ∧
      regSchreibt (.movReg64 dst src) = [dst] :=
  ⟨rfl, rfl⟩

theorem reg_addReg64 (dst src : Register) :
    regLiest (.addReg64 dst src) = [dst, src] ∧
      regSchreibt (.addReg64 dst src) = [dst] :=
  ⟨rfl, rfl⟩

theorem reg_subReg64 (dst src : Register) :
    regLiest (.subReg64 dst src) = [dst, src] ∧
      regSchreibt (.subReg64 dst src) = [dst] :=
  ⟨rfl, rfl⟩

theorem reg_xorReg64 (dst src : Register) :
    regLiest (.xorReg64 dst src) = [dst, src] ∧
      regSchreibt (.xorReg64 dst src) = [dst] :=
  ⟨rfl, rfl⟩

theorem reg_cmpReg64 (lhs rhs : Register) :
    regLiest (.cmpReg64 lhs rhs) = [lhs, rhs] ∧
      regSchreibt (.cmpReg64 lhs rhs) = [] :=
  ⟨rfl, rfl⟩

theorem reg_load64 (dst base : Register) (disp : BitVec 32) :
    regLiest (.load64 dst base disp) = [base] ∧
      regSchreibt (.load64 dst base disp) = [dst] :=
  ⟨rfl, rfl⟩

theorem reg_store64 (base src : Register) (disp : BitVec 32) :
    regLiest (.store64 base src disp) = [base, src] ∧
      regSchreibt (.store64 base src disp) = [] :=
  ⟨rfl, rfl⟩

theorem reg_jump32 (disp : BitVec 32) :
    regLiest (.jump32 disp) = [] ∧ regSchreibt (.jump32 disp) = [] :=
  ⟨rfl, rfl⟩

theorem reg_jumpIf32 (cond : Bedingung) (disp : BitVec 32) :
    regLiest (.jumpIf32 cond disp) = [] ∧
      regSchreibt (.jumpIf32 cond disp) = [] :=
  ⟨rfl, rfl⟩

theorem reg_push64 (src : Register) :
    regLiest (.push64 src) = [src, .rsp] ∧
      regSchreibt (.push64 src) = [.rsp] :=
  ⟨rfl, rfl⟩

theorem reg_pop64 (dst : Register) :
    regLiest (.pop64 dst) = [.rsp] ∧
      regSchreibt (.pop64 dst) = [dst, .rsp] :=
  ⟨rfl, rfl⟩

theorem reg_call32 (disp : BitVec 32) :
    regLiest (.call32 disp) = [.rsp] ∧
      regSchreibt (.call32 disp) = [.rsp] :=
  ⟨rfl, rfl⟩

theorem reg_ret :
    regLiest .ret = [.rsp] ∧ regSchreibt .ret = [.rsp] :=
  ⟨rfl, rfl⟩

/-! ## 2. Declared allocation vocabulary and fail-closed check.

    Values are abstract declared-live ids (`Wert := Nat`); liveness and
    interference edges are DECLARED inputs the future accepted IR supplies
    with validation, never inferred here. `rsp` is the one pinned register
    the allocator must never hand to a general value (stack pointer, read
    and written by every stack/control form in §1). Richer ABI pinning
    (callee-saved, argument registers) stays OPEN. -/

/-- Declared-live value id supplied by the future accepted IR. -/
abbrev Wert := Nat

/-- Canonical assignment: each declared value maps to at most one register.
    Named `RegBelegung`: `Stapel.Belegung` (spill-frame layout) already owns
    the short name for a different concept. -/
abbrev RegBelegung := Wert → Option Register

/-- The pinned register set: `rsp` only. The stack pointer is read and
    written by every stack/control pilot form, so no general value may
    live in it. -/
def reserviertReg : Register → Bool
  | .rsp => true
  | _ => false

/-- One interference edge checks: both ends live, both assigned, distinct. -/
def kanteOk (zu : RegBelegung) : Wert × Wert → Bool
  | (u, v) =>
    match zu u, zu v with
    | some ru, some rv => decide (ru ≠ rv)
    | _, _ => false

/-- One pinned binding checks: the value carries exactly that register. -/
def bindungOk (zu : RegBelegung) : Wert × Register → Bool
  | (u, r) => match zu u with
    | some ru => decide (ru = r)
    | none => false

/-- One live value checks: assigned, and never to the pinned register. -/
def lebtOk (zu : RegBelegung) : Wert → Bool
  | u => match zu u with
    | some r => !reserviertReg r
    | none => false

/-- Fail-closed certificate check: every live value assigned outside the
    pinned set, every declared edge distinct, every pinned binding kept.
    Anything missing or conflicting is `false`, never a silent pass. -/
def belegungOk (zu : RegBelegung) (lebendig : List Wert)
    (kanten : List (Wert × Wert)) (bindung : List (Wert × Register)) : Bool :=
  lebendig.all (lebtOk zu) && kanten.all (kanteOk zu) &&
    bindung.all (bindungOk zu)

/-! ## 3. Fail-closed refusal probes (decided negatives). -/

/-- Empty assignment refuses a live value. -/
theorem belegungOk_verweigert_leer :
    belegungOk (fun _ => none) [0] [(0, 1)] [] = false := by
  decide

/-- Conflicting edge (same register) refuses. -/
theorem belegungOk_verweigert_konflikt :
    belegungOk (fun _ => some .rax) [0, 1] [(0, 1)] [] = false := by
  decide

/-- Allocation of the pinned stack pointer refuses. -/
theorem belegungOk_verweigert_rsp :
    belegungOk (fun _ => some .rsp) [0] [] [] = false := by
  decide

/-- Broken pinned binding refuses. -/
theorem belegungOk_verweigert_bindung :
    belegungOk (fun _ => some .rax) [0] [] [(0, .rcx)] = false := by
  decide

/-- Positive probe: distinct general registers with a kept binding pass. -/
theorem belegungOk_positiv :
    belegungOk (fun u => if u = 0 then some .rax else if u = 1 then some .rcx else none)
      [0, 1] [(0, 1)] [(0, .rax)] = true := by
  decide

/-! ## 4. Check-implies allocation facts.

    Every premise is used: the `= true` check hypothesis supplies the
    conjunct, the membership hypothesis selects the element. Edges check
    fail-closed without requiring liveness: an edge with an unassigned
    end is `false`, never an assumed pass. -/

/-- Helper: the edge conjunct of a passing check passes. -/
theorem belegungOk_kanten_alle (zu : RegBelegung) (lebendig : List Wert)
    (kanten : List (Wert × Wert)) (bindung : List (Wert × Register))
    (h : belegungOk zu lebendig kanten bindung = true) :
    kanten.all (kanteOk zu) = true := by
  unfold belegungOk at h
  have hk := (Bool.and_eq_true (lebendig.all (lebtOk zu) &&
    kanten.all (kanteOk zu)) (bindung.all (bindungOk zu))).mp h
  exact (Bool.and_eq_true (lebendig.all (lebtOk zu))
    (kanten.all (kanteOk zu))).mp hk.1 |>.2

/-- Helper: the liveness conjunct of a passing check passes. -/
theorem belegungOk_lebendig_alle (zu : RegBelegung) (lebendig : List Wert)
    (kanten : List (Wert × Wert)) (bindung : List (Wert × Register))
    (h : belegungOk zu lebendig kanten bindung = true) :
    lebendig.all (lebtOk zu) = true := by
  unfold belegungOk at h
  have hk := (Bool.and_eq_true (lebendig.all (lebtOk zu) &&
    kanten.all (kanteOk zu)) (bindung.all (bindungOk zu))).mp h
  exact (Bool.and_eq_true (lebendig.all (lebtOk zu))
    (kanten.all (kanteOk zu))).mp hk.1 |>.1

/-- Helper: the binding conjunct of a passing check passes. -/
theorem belegungOk_bindung_alle (zu : RegBelegung) (lebendig : List Wert)
    (kanten : List (Wert × Wert)) (bindung : List (Wert × Register))
    (h : belegungOk zu lebendig kanten bindung = true) :
    bindung.all (bindungOk zu) = true := by
  unfold belegungOk at h
  exact (Bool.and_eq_true (lebendig.all (lebtOk zu) &&
    kanten.all (kanteOk zu)) (bindung.all (bindungOk zu))).mp h |>.2

/-- A passing check assigns distinct registers to every declared
    interfering pair, with both witnesses exhibited. -/
theorem belegungOk_kante_verschieden (zu : RegBelegung)
    (lebendig : List Wert) (kanten : List (Wert × Wert))
    (bindung : List (Wert × Register)) (u v : Wert)
    (h : belegungOk zu lebendig kanten bindung = true)
    (hm : (u, v) ∈ kanten) :
    ∃ ru rv, zu u = some ru ∧ zu v = some rv ∧ ru ≠ rv := by
  have hall := belegungOk_kanten_alle zu lebendig kanten bindung h
  have hel := (List.all_eq_true.mp hall) _ hm
  simp only [kanteOk] at hel
  cases h1 : zu u with
  | none =>
    cases h2 : zu v with
    | none => simp only [h1] at hel; exact absurd hel (by decide)
    | some _ => simp only [h1] at hel; exact absurd hel (by decide)
  | some ru =>
    cases h2 : zu v with
    | none => simp only [h1, h2] at hel; exact absurd hel (by decide)
    | some rv =>
      simp only [h1, h2, decide_eq_true_eq] at hel
      exact ⟨_, _, rfl, rfl, hel⟩

/-- A passing check assigns every declared-live value some register. -/
theorem belegungOk_lebt_zugeteilt (zu : RegBelegung)
    (lebendig : List Wert) (kanten : List (Wert × Wert))
    (bindung : List (Wert × Register)) (u : Wert)
    (h : belegungOk zu lebendig kanten bindung = true)
    (hm : u ∈ lebendig) :
    ∃ r, zu u = some r := by
  have hall := belegungOk_lebendig_alle zu lebendig kanten bindung h
  have hel := (List.all_eq_true.mp hall) _ hm
  simp only [lebtOk] at hel
  cases h1 : zu u with
  | none => simp only [h1] at hel; exact absurd hel (by decide)
  | some _ => exact ⟨_, rfl⟩

/-- A passing check never hands a live value the pinned stack pointer. -/
theorem belegungOk_ohne_reserviert (zu : RegBelegung)
    (lebendig : List Wert) (kanten : List (Wert × Wert))
    (bindung : List (Wert × Register)) (u : Wert) (r : Register)
    (h : belegungOk zu lebendig kanten bindung = true)
    (hm : u ∈ lebendig) (hr : zu u = some r) :
    reserviertReg r = false := by
  have hall := belegungOk_lebendig_alle zu lebendig kanten bindung h
  have hel := (List.all_eq_true.mp hall) _ hm
  simp only [lebtOk, hr] at hel
  simpa using hel

/-- A passing check keeps every declared pinned binding exactly. -/
theorem belegungOk_bindung_haelt (zu : RegBelegung)
    (lebendig : List Wert) (kanten : List (Wert × Wert))
    (bindung : List (Wert × Register)) (u : Wert) (r : Register)
    (h : belegungOk zu lebendig kanten bindung = true)
    (hm : (u, r) ∈ bindung) :
    zu u = some r := by
  have hall := belegungOk_bindung_alle zu lebendig kanten bindung h
  have hel := (List.all_eq_true.mp hall) _ hm
  simp only [bindungOk] at hel
  cases h1 : zu u with
  | none => simp only [h1] at hel; exact absurd hel (by decide)
  | some rv =>
    simp only [h1, decide_eq_true_eq] at hel
    exact congrArg some hel

/-! ## 5. Distinct allocation preserves the actual register file.

    The consumer of a passing check is the direct-compiler allocator:
    two declared-interfering values land in distinct physical registers,
    so writing one slot never clobbers the other through the actual
    `regSet`/`schrittRegister` used by every `schritt` equation. -/

/-- Distinct register writes commute, pointwise. -/
theorem regSet_vert_kommutiert (r : Register → Wort)
    (a b : Register) (x y : Wort) (q : Register)
    (hne : a ≠ b) :
    regSet (regSet r a x) b y q = regSet (regSet r b y) a x q := by
  unfold regSet
  by_cases h1 : q = b <;> by_cases h2 : q = a <;> simp_all

/-- Headline: a passing check means writing one interfering value's slot
    through the actual `regSet` never clobbers the other's register. -/
theorem belegung_schreibt_ohne_clobber (zu : RegBelegung)
    (r : Register → Wort) (lebendig : List Wert)
    (kanten : List (Wert × Wert)) (bindung : List (Wert × Register))
    (u v : Wert) (x : Wort)
    (h : belegungOk zu lebendig kanten bindung = true)
    (hm : (u, v) ∈ kanten) :
    ∀ ru rv, zu u = some ru → zu v = some rv →
      (regSet r ru x) rv = r rv := by
  intro ru rv h1 h2
  obtain ⟨ru', rv', g1, g2, hne⟩ :=
    belegungOk_kante_verschieden zu lebendig kanten bindung u v h hm
  have e1 : ru = ru' := Option.some_inj.mp (h1.symm.trans g1)
  have e2 : rv = rv' := Option.some_inj.mp (h2.symm.trans g2)
  subst e1
  subst e2
  exact regSet_fremd r ru rv x (Ne.symm hne)

/-- An actual `schrittRegister` write preserves every other register. -/
theorem schrittRegister_erhaelt_fremd (s : Zustand) (nach : Adresse)
    (f : Flags) (dst q : Register) (v : Wort)
    (hq : q ≠ dst) :
    (schrittRegister s nach f dst v).register q = s.register q := by
  unfold schrittRegister
  simp only
  exact regSet_fremd s.register dst q v hq

/-- A successful `movImm64` step preserves every register outside the
    canonical write set: the write set is exactly the clobber set. -/
theorem reg_schritt_schreibt_nur (d : Decodiert) (s s' : Zustand)
    (dst q : Register) (v : Wort)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .movImm64 dst v)
    (hstep : schritt d s = some s')
    (haussen : q ∉ regSchreibt (.movImm64 dst v)) :
    s'.register q = s.register q := by
  have hq : q ≠ dst := by
    intro heq
    apply haussen
    rw [heq]
    simp [regSchreibt]
  exact schritt_movImm64_reg d s s' dst q v hok h hstep hq

/-- The pinned register is exactly `rsp`. -/
theorem reserviert_rsp : reserviertReg .rsp = true := rfl

/-- A general register is not pinned. -/
theorem nicht_reserviert_rax : reserviertReg .rax = false := rfl

/-! ## 6. Joint concrete witness: the positively checked assignment's
    registers evolve independently through actual `schritt` steps. -/

/-- The positively checked assignment maps value 0 to `rax`. -/
theorem belegung_zeuge_null :
    (fun u => if u = 0 then some .rax else if u = 1 then some .rcx else none :
      RegBelegung) 0 = some .rax := rfl

/-- The positively checked assignment maps value 1 to `rcx`. -/
theorem belegung_zeuge_eins :
    (fun u => if u = 0 then some .rax else if u = 1 then some .rcx else none :
      RegBelegung) 1 = some .rcx := rfl

/-- Two actual steps write the two assigned registers independently:
    `rax` keeps 7 while `rcx` takes 9, through the real `schritt`. -/
theorem probe_belegung_unabhaengig :
    (((schritt { befehl := Befehl.movImm64 Register.rax 7, laenge := 3 }
      zeugeZustand).bind (schritt
      { befehl := Befehl.movImm64 Register.rcx 9, laenge := 3 })).map
      (fun s => (s.register Register.rax, s.register Register.rcx)) =
      some (BitVec.ofNat 64 7, BitVec.ofNat 64 9)) := by
  decide

/- CUTS:
    - Reads/writes cover exactly the 14 pilot `Befehl` constructors (§1);
      narrower widths, RMW/LOCK/fence forms and any future instruction have
      no rows here and are refused by absence, not admitted.
    - Liveness and interference edges are DECLARED inputs: this file never
      infers them. How the future accepted IR supplies validated liveness:
      it must export `lebendig`/`kanten`/`bindung` lists per program point;
      `belegungOk` checks them fail-closed (§3 refuses empties, conflicts,
      `rsp` allocation and broken bindings by `decide`). No validation of
      the liveness itself is proved here.
    - Only `rsp` is pinned (`reserviertReg`); callee-saved, argument and
      fixed-role registers of a future ABI are OPEN and must extend the
      pinned set, never shrink the check.
    - No source allocation refinement: nothing here lowers Gabbro source
      variables to values, and no simulation, cost, contract, timing,
      concurrency (W/GX), TSO bridge or whole-image claim is made.
    - Flags and memory footprints of instructions are owned by
      `Ausfuehrung`/`Zugriffe`; this file adds only the register-file
      (non-)clobber facts the allocator consumes (§5).
-/

#print axioms regLiest
#print axioms regSchreibt
#print axioms belegungOk
#print axioms belegungOk_kante_verschieden
#print axioms belegungOk_lebt_zugeteilt
#print axioms belegungOk_ohne_reserviert
#print axioms belegungOk_bindung_haelt
#print axioms regSet_vert_kommutiert
#print axioms belegung_schreibt_ohne_clobber
#print axioms schrittRegister_erhaelt_fremd
#print axioms reg_schritt_schreibt_nur
#print axioms belegungOk_positiv
#print axioms probe_belegung_unabhaengig

end Gabbro.Grammatik.X86
