/-
  File:      Grammatik/X86/PipelineLoops.lean
  Subject:   Bounded source loops (`Stmt.retry`, the `retry until … bounded n`
    form) lowered to one labelled block with rel8/rel32 branches.

    The schema `schleifeProg` lays a body of fall-through unified
    instructions (`Instr`, `ISA.lean`) between a head conditional exit
    (`jcc`) and a back jump (`jmp`), exactly the shape the bounded
    relaxation (`ISARelax.lean`: `relax`, `relaxLayoutOk`, `bild`) lays out
    and connects to fetched byte runs (`laufBytesL_start`,
    `relax_laufBytes`). Finite source runs (`retryLauf`, `Semantik.lean`)
    transfer their iteration budget `n` to the target step budget
    `schleifeSchritte n m`. Unbounded loops (`forever`, source `while`
    without a bound) get NO finite budget here: only finite-prefix
    unfolding (`ewig_ein_schritt`) and the loud budget stop at zero passes
    (proved in `BudgetExecution.lean`, cited in CUTS).

    Reused, not duplicated: `LProg`/`stepL`/`laufL`/`laufL_add`,
    `relax`/`relax_ok`/`relaxLayoutOk`/`layoutOk_zeile`/`bild`,
    `laufBytesL_start`/`relax_laufBytes`, `kanonischI`, `faelltDurchI`,
    `retryLauf`/`foreverLauf`, `bedingung`.
-/
import Grammatik.X86.ISARelax
import Grammatik.X86.Regionen
import Grammatik.X86.SourceAssignmentLowering
import Grammatik.Semantik

namespace Gabbro.Grammatik.X86.PipelineLoops

open Gabbro.Grammatik
open Gabbro.Grammatik.X86

/-- The loop schema: head `jcc` to the end label, the body as `op` rows,
    one back jump to label 0. Labels: `0` head, `1 .. n` body,
    `n + 1` back jump, `n + 2` end. -/
def schleifeProg (koerper : List Instr) (c : Bedingung) : LProg :=
  LInstr.jcc c (koerper.length + 2) :: (koerper.map LInstr.op) ++ [LInstr.jmp 0]

/-- The schema length: body rows plus the two branch rows. -/
theorem schleifeProg_laenge (koerper : List Instr) (c : Bedingung) :
    (schleifeProg koerper c).length = koerper.length + 2 := by
  simp [schleifeProg]

/-- The head row is the conditional exit to the end label. -/
theorem schleifeProg_kopf (koerper : List Instr) (c : Bedingung) :
    (schleifeProg koerper c)[0]? = some (LInstr.jcc c (koerper.length + 2)) := rfl

/-- The row after the body is the back jump to label 0. -/
theorem schleifeProg_rueck (koerper : List Instr) (c : Bedingung) :
    (schleifeProg koerper c)[koerper.length + 1]? = some (LInstr.jmp 0) := by
  unfold schleifeProg
  have hlen : ((LInstr.jcc c (koerper.length + 2) :: koerper.map LInstr.op)).length
      = koerper.length + 1 := by simp
  rw [List.getElem?_append_right (by omega), hlen]
  simp

/-- A body row sits at its index shifted by one (past the head row). -/
theorem schleifeProg_mitte (koerper : List Instr) (c : Bedingung) (j : Nat)
    (hj : j < koerper.length) :
    (schleifeProg koerper c)[j + 1]? = some (LInstr.op koerper[j]) := by
  unfold schleifeProg
  have h1 : j + 1 < ((LInstr.jcc c (koerper.length + 2) :: koerper.map LInstr.op)).length := by
    simp only [List.length_cons, List.length_map]
    omega
  rw [List.getElem?_append_left h1, List.getElem?_cons_succ,
    List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]

/-! ## 2. Compilation through the existing relaxation, and refusals -/

/-- Compilation: relax the schema (bounded rounds over rel8/rel32) and take
    its byte image. `none` is refusal, never a guess. -/
def schleifeKompilieren (treibstoff : Nat) (koerper : List Instr) (c : Bedingung) :
    Option (List Byte) :=
  match relax treibstoff (schleifeProg koerper c) with
  | some ws => some (bild ws (schleifeProg koerper c))
  | none => none

/-- Whatever the fuel, a relaxed schema layout validates. -/
theorem schleife_relax_ok (treibstoff : Nat) (koerper : List Instr) (c : Bedingung)
    (ws : List Bool) (h : relax treibstoff (schleifeProg koerper c) = some ws) :
    relaxLayoutOk ws (schleifeProg koerper c) = true :=
  relax_ok treibstoff (schleifeProg koerper c) ws h

/-- REFUSAL: a body row that is not canonical fall-through code (a jump, a
    call, `ret`, a non-canonical row) makes even the all-wide layout fail,
    so relaxation answers `none` at every fuel. -/
theorem schleife_verweigert_schlechten_koerper (treibstoff : Nat) (koerper : List Instr)
    (c : Bedingung) (j : Nat) (hj : j < koerper.length)
    (hschlecht : (kanonischI koerper[j] && faelltDurchI koerper[j]) = false) :
    schleifeKompilieren treibstoff koerper c = none := by
  have hmitte := schleifeProg_mitte koerper c j hj
  by_cases hlay : relaxLayoutOk (alleWeit (schleifeProg koerper c)) (schleifeProg koerper c) = true
  · exfalso
    have hz := layoutOk_zeile _ _ hlay (j + 1) (LInstr.op koerper[j]) hmitte
    have hop : zeileOk (alleWeit (schleifeProg koerper c)) (schleifeProg koerper c)
        (j + 1) (LInstr.op koerper[j])
        = (kanonischI koerper[j] && faelltDurchI koerper[j]) := rfl
    rw [hop, hschlecht] at hz
    cases hz
  · have hrel : relax treibstoff (schleifeProg koerper c) = none := by
      unfold relax
      rw [if_neg hlay]
    unfold schleifeKompilieren
    rw [hrel]

/-- Poison probe: `ret` in the body is refused (it does not fall through). -/
theorem schleife_verweigert_ret (treibstoff : Nat) (c : Bedingung) :
    schleifeKompilieren treibstoff [.pilot .ret] c = none :=
  schleife_verweigert_schlechten_koerper treibstoff [.pilot .ret] c 0
    (by decide) (by decide)

/-- Poison probe: a rel32 jump in the body is refused (control stays in the
    schema's two branch rows). -/
theorem schleife_verweigert_sprung (treibstoff : Nat) (c : Bedingung)
    (d : BitVec 32) :
    schleifeKompilieren treibstoff [.pilot (.jump32 d)] c = none :=
  schleife_verweigert_schlechten_koerper treibstoff [.pilot (.jump32 d)] c 0
    (by simp) (by rfl)

/-! ## 3. The target step budget: source rounds to labelled steps -/

/-- One source round is at most `m + 2` labelled steps (head `jcc`, `m`
    body rows, back `jmp`); the final exit check costs one more step. -/
def schleifeSchritte (runden : Nat) (m : Nat) : Nat := runden * (m + 2) + 1

/-- One more round costs one more body segment. -/
theorem schleifeSchritte_succ (n m : Nat) :
    schleifeSchritte (n + 1) m = schleifeSchritte n m + (m + 2) := by
  unfold schleifeSchritte
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The budget splits into one round plus the rest (the shape `laufL_add`
    consumes). -/
theorem schleifeSchritte_add (n m : Nat) :
    schleifeSchritte (n + 1) m = (m + 2) + schleifeSchritte n m := by
  rw [schleifeSchritte_succ]
  omega

/-- Past the end the bounded labelled run stays put. -/
theorem laufL_stop (adr : Nat → Adresse) (p : LProg) (k : Nat) (x : Nat × Zustand)
    (h : p.length ≤ x.1) : laufL adr p k x = some x := by
  induction k with
  | zero => rfl
  | succ k _ =>
    simp only [laufL]
    rw [if_neg (by omega)]

/-! ## 4. The source side: the real `retry`/`forever` runners, unfolded -/

/-- `retry` stops loudly-successfully when the bound predicate holds: no
    body step runs. -/
theorem wiederhol_steht {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (n : Nat) (σ : World D) (ρ : Env D Γ)
    (h : (bis σ ρ).2 = true) :
    retryLauf schritt bis ueberlauf (n + 1) σ ρ = .ok (bis σ ρ).1 ρ := by
  simp [retryLauf, h]

/-- `retry` with a false bound runs one body step and continues with `n`. -/
theorem wiederhol_schritt {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (n : Nat) (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : (bis σ ρ).2 = false)
    (hs : schritt (bis σ ρ).1 ρ = .ok σ' ρ') :
    retryLauf schritt bis ueberlauf (n + 1) σ ρ
      = retryLauf schritt bis ueberlauf n σ' ρ' := by
  simp [retryLauf, h, hs]

/-- FINITE-PREFIX CLAIM for unbounded loops: `forever` at `n + 1` passes
    with a true invariant runs one body step and continues with `n`. What
    is NOT claimed: any finite budget covering all runs. -/
theorem ewig_ein_schritt {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (a : D.Annahme)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (n : Nat) (σ σ' : World D) (ρ ρ' : Env D Γ)
    (hinv : (inv σ ρ).2 = true)
    (hs : schritt (inv σ ρ).1 ρ = .ok σ' ρ') :
    foreverLauf (l := l) a schritt inv (n + 1) σ ρ
      = foreverLauf (l := l) a schritt inv n σ' ρ' := by
  simp [foreverLauf, hinv, hs]

/-! ## 5. Finite-run correctness: source budget to target steps -/

/-- THE LOOP THEOREM (finite runs): if every executed body round continues
    (`.ok` or `.next`) and the labelled round of `m + 2` steps simulates it
    while keeping `Rep`, the condition agrees with the exit jump, the exit
    step leaves the schema, and the overflow block never answers `.ok`
    (it refuses loudly, the refuse-on-full discipline), then a source run
    that finishes `.ok` within `n` rounds is the labelled run of
    `schleifeSchritte n m` steps to the end label, keeping `Rep`.
    The one-round simulation (`hWeiter`) is proved per body by its
    producer; this lifts it to `n` rounds with budget accounting. -/
theorem schleife_korrekt_endlich {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (koerper : List Instr) (c : Bedingung)
    (adr : Nat → Adresse)
    (Rep : World D → Env D Γ → Zustand → Prop)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hLese : ∀ σ ρ s, Rep σ ρ s → Rep (bis σ ρ).1 ρ s)
    (hBisStabil : ∀ σ ρ, bis (bis σ ρ).1 ρ = bis σ ρ)
    (hBed : ∀ σ ρ s, Rep σ ρ s → (bis σ ρ).2 = bedingung c s.flags)
    (hWeiter : ∀ σ ρ s, Rep σ ρ s → (bis σ ρ).2 = false →
      ∃ σ₁ ρ₁ s₁, (schritt (bis σ ρ).1 ρ = .ok σ₁ ρ₁ ∨
          (∃ h : true = true, schritt (bis σ ρ).1 ρ = .next h σ₁ ρ₁)) ∧
        laufL adr (schleifeProg koerper c) (koerper.length + 2) (0, s)
          = some (0, s₁) ∧
        Rep σ₁ ρ₁ s₁)
    (hEnde : ∀ σ ρ s, Rep σ ρ s → (bis σ ρ).2 = true →
      ∃ s', laufL adr (schleifeProg koerper c) 1 (0, s)
        = some (koerper.length + 2, s') ∧ Rep (bis σ ρ).1 ρ s')
    (hUeberlauf : ∀ σ ρ σ' ρ', (bis σ ρ).2 = false →
      ueberlauf (bis σ ρ).1 ρ ≠ .ok σ' ρ') :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (s : Zustand),
      Rep σ ρ s →
      ∀ σ' ρ', retryLauf schritt bis ueberlauf n σ ρ = .ok σ' ρ' →
        ∃ s', laufL adr (schleifeProg koerper c)
            (schleifeSchritte n koerper.length) (0, s)
          = some (koerper.length + 2, s') ∧
          Rep σ' ρ' s' := by
  have hlen : (schleifeProg koerper c).length = koerper.length + 2 :=
    schleifeProg_laenge koerper c
  have hstop : ∀ (k : Nat) (t : Zustand),
      laufL adr (schleifeProg koerper c) k (koerper.length + 2, t)
        = some (koerper.length + 2, t) := by
    intro k t
    exact laufL_stop adr (schleifeProg koerper c) k _ (by simp [hlen])
  intro n
  induction n with
  | zero =>
    intro σ ρ s hRep σ' ρ' hrun
    have hb := hBed σ ρ s hRep
    cases he : (bis σ ρ).2 with
    | true =>
      simp only [retryLauf, he] at hrun
      cases hrun
      have hrepL := hLese σ ρ s hRep
      have heL : (bis (bis σ ρ).1 ρ).2 = true := by
        rw [hBisStabil]
        exact he
      have hexit := hEnde _ _ _ hrepL heL
      have hb0 : schleifeSchritte 0 koerper.length = 1 := by
        simp [schleifeSchritte]
      obtain ⟨s', hrun1, hrep'⟩ := hexit
      rw [hBisStabil] at hrep'
      exact ⟨s', by rw [hb0]; exact hrun1, hrep'⟩
    | false =>
      simp only [retryLauf, he] at hrun
      exact absurd hrun (hUeberlauf σ ρ σ' ρ' he)
  | succ n ih =>
    intro σ ρ s hRep σ' ρ' hrun
    have hb := hBed σ ρ s hRep
    cases he : (bis σ ρ).2 with
    | true =>
      rw [wiederhol_steht schritt bis ueberlauf n σ ρ he] at hrun
      cases hrun
      have hrepL := hLese σ ρ s hRep
      have heL : (bis (bis σ ρ).1 ρ).2 = true := by
        rw [hBisStabil]
        exact he
      have hexit := hEnde _ _ _ hrepL heL
      have hm2 : koerper.length + 2 = 1 + (koerper.length + 1) := by omega
      obtain ⟨sx, hrunx, hrepx⟩ := hexit
      rw [hBisStabil] at hrepx
      have hseg1 : laufL adr (schleifeProg koerper c) (koerper.length + 2) (0, s)
          = some (koerper.length + 2, sx) := by
        have e1 : laufL adr (schleifeProg koerper c) (1 + (koerper.length + 1)) (0, s)
            = some (koerper.length + 2, sx) := by
          rw [laufL_add, hrunx]
          exact hstop _ _
        rwa [← hm2] at e1
      refine ⟨sx, ?_, hrepx⟩
      rw [schleifeSchritte_add, laufL_add, hseg1]
      exact hstop _ _
    | false =>
      obtain ⟨σ₁, ρ₁, s₁, hfort, hseg, hrep₁⟩ := hWeiter σ ρ s hRep he
      have hbud : schleifeSchritte (n + 1) koerper.length
          = (koerper.length + 2) + schleifeSchritte n koerper.length :=
        schleifeSchritte_add n koerper.length
      rcases hfort with hok | ⟨_, hnext⟩
      · rw [wiederhol_schritt schritt bis ueberlauf n σ σ₁ ρ ρ₁ he hok] at hrun
        obtain ⟨s', hT, hrep'⟩ := ih σ₁ ρ₁ s₁ hrep₁ σ' ρ' hrun
        exact ⟨s', by rw [hbud, laufL_add, hseg]; simpa using hT, hrep'⟩
      · have hstep : retryLauf schritt bis ueberlauf (n + 1) σ ρ
            = retryLauf schritt bis ueberlauf n σ₁ ρ₁ := by
          simp [retryLauf, he, hnext]
        rw [hstep] at hrun
        obtain ⟨s', hT, hrep'⟩ := ih σ₁ ρ₁ s₁ hrep₁ σ' ρ' hrun
        exact ⟨s', by rw [hbud, laufL_add, hseg]; simpa using hT, hrep'⟩

/-! ## 6. From the labelled run to fetched bytes -/

/-- THE BYTE COROLLARY: a relaxed schema whose image sits at the current
    RIP in W^X memory runs under fetched-bytes execution exactly as the
    labelled program: the same successor state after exactly the steps the
    bounded labelled run executes, with RIP at the reached label's
    address. This is `relax_laufBytes` at the loop schema. -/
theorem schleife_bytes (treibstoff : Nat) (koerper : List Instr) (c : Bedingung)
    (ws : List Bool) (hr : relax treibstoff (schleifeProg koerper c) = some ws)
    (s : Zustand) (hwx : WX s.speicher)
    (hcode : CodeAt s.speicher s.rip (bild ws (schleifeProg koerper c))) (n : Nat) :
    laufBytesI (schritteL (adrL s.rip ws (schleifeProg koerper c))
        (schleifeProg koerper c) n (0, s)) s =
        ausgangVon ((laufL (adrL s.rip ws (schleifeProg koerper c))
          (schleifeProg koerper c) n (0, s)).map Prod.snd) ∧
      ∀ y, laufL (adrL s.rip ws (schleifeProg koerper c))
          (schleifeProg koerper c) n (0, s) = some y →
        y.2.rip = adrL s.rip ws (schleifeProg koerper c) y.1 :=
  relax_laufBytes treibstoff (schleifeProg koerper c) ws hr s hwx hcode n

/-! ## 7. Joint witness on a non-degenerate program -/

/-- One table of two rows with one integer field in `0 .. 1000`, written
    by the loop step (the shape reused from `PipelineWitnesses.pwD`). -/
def zwD : Deklaration where
  Tab := Unit
  count := fun _ => 2
  Feld := fun _ => Unit
  typ := fun _ _ => .int 0 1000
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => false
  ggeteilt := fun g => nomatch g
  Lock := Empty
  rang := fun L => nomatch L
  maskiert := fun L => nomatch L
  Marke := Empty
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => witSig628
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The contract: writes the table, no refusal reasons. -/
def zwV : Vertrag zwD :=
  { schreibt := fun _ => true
    gschreibt := fun g => nomatch g
    erg := none
    gruende := 0
    haelt := []
    produziert := []
    boden := none }

/-- The bound predicate: done exactly when row 0 holds 1. It records no
    read (the world is unchanged), so re-reading is stable by `rfl`. -/
def zwBis : World zwD → Env zwD [] → World zwD × Bool :=
  fun σ _ => (σ, decide ((σ.slots () 0 ()).n = 1))

/-- One body round at source level: write 1 into row 0 (the memory-changing
    step). -/
def zwSchritt : World zwD → Env zwD [] → Ausgang zwV true [] :=
  fun σ ρ => .ok (σ.schreibSlot () [] 0 () ⟨1, by decide, by decide⟩) ρ

/-- The overflow block refuses loudly, always: it never answers `.ok`. -/
def zwUeberlauf : World zwD → Env zwD [] → Ausgang zwV false [] :=
  fun _ _ => .logik .schleife

/-- The target body: `rcx := 1; rax += rcx; [8192] := rax; reload; compare`.
    Six fall-through rows. -/
def zwKoerper : List Instr :=
  [ .pilot (.movImm64 .rcx 1)
  , .pilot (.addReg64 .rax .rcx)
  , .pilot (.movImm64 .rbx (natAdresse 8192))
  , .pilot (.store64 .rbx .rax (BitVec.ofNat 32 0))
  , .pilot (.load64 .rdx .rbx (BitVec.ofNat 32 0))
  , .pilot (.cmpReg64 .rdx .rcx) ]

/-- The body has six rows. -/
theorem zwKoerper_len : zwKoerper.length = 6 := rfl

/-- The label address map of the witness (constant, closed). -/
def zwAdr : Nat → Adresse := fun _ => natAdresse 6000

/-- The witness start state: registers zero, flags say "not equal"
    (`0 - 1 ≠ 0`), all memory readable and writable, bytes zero. -/
def zwS0 : Zustand :=
  { register := fun _ => 0
    flags := (sub64 0 1).2
    rip := natAdresse 6000
    speicher :=
      { bytes := fun _ => 0
        lesbar := fun _ => true
        schreibbar := fun _ => true
        ausfuehrbar := fun _ => false } }

/-- The source start world: row 0 holds 0. -/
def zwSigma0 : World zwD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

/-- The witness relation: exit-flag agreement plus the slot/counter/memory
    correspondence, before the round (pinned start state) and after one
    round (counter set, word stored and reloaded). -/
def zwRep (σ : World zwD) (ρ : Env zwD []) (s : Zustand) : Prop :=
  (zwBis σ ρ).2 = bedingung .e s.flags ∧
  (((σ.slots () 0 ()).n = 0 ∧ s = zwS0) ∨
   ((σ.slots () 0 ()).n = 1 ∧ s.register .rax = 1 ∧
    read64 s.speicher (natAdresse 8192) = some 1))

/-- Reading changes nothing observable: stability by `rfl`. -/
theorem zw_stabil (σ : World zwD) (ρ : Env zwD []) :
    zwBis (zwBis σ ρ).1 ρ = zwBis σ ρ := rfl

/-- The representation survives the (empty) read. -/
theorem zw_lese (σ : World zwD) (ρ : Env zwD []) (s : Zustand) :
    zwRep σ ρ s → zwRep (zwBis σ ρ).1 ρ s := fun h => h

/-- The condition agrees with the exit jump, by definition of the relation. -/
theorem zw_bed (σ : World zwD) (ρ : Env zwD []) (s : Zustand) :
    zwRep σ ρ s → (zwBis σ ρ).2 = bedingung .e s.flags := fun h => h.1

/-- The overflow block never answers `.ok`: it is loudly `.logik`. -/
theorem zw_kein_ueberlauf (σ : World zwD) (ρ : Env zwD [])
    (σ' : World zwD) (ρ' : Env zwD []) (h : (zwBis σ ρ).2 = false) :
    zwUeberlauf (zwBis σ ρ).1 ρ ≠ .ok σ' ρ' := by
  cases he : (zwBis σ ρ).2 with
  | true => rw [he] at h; cases h
  | false => simp [zwUeberlauf]

/-- The written world: row 0 holds 1. -/
def zwSigma1 (σ : World zwD) : World zwD :=
  σ.schreibSlot () [] 0 () ⟨1, by decide, by decide⟩

/-- ONE WITNESS ROUND: from the start state the eight labelled steps run
    the body and return to the head, while the source writes row 0. The
    target segment holds by computation (`rfl` evaluates the closed run). -/
theorem zw_weiter (σ : World zwD) (ρ : Env zwD []) (s : Zustand)
    (hRep : zwRep σ ρ s) (he : (zwBis σ ρ).2 = false) :
    ∃ σ₁ ρ₁ s₁, (zwSchritt (zwBis σ ρ).1 ρ = .ok σ₁ ρ₁ ∨
        (∃ h : true = true, zwSchritt (zwBis σ ρ).1 ρ = .next h σ₁ ρ₁)) ∧
      laufL zwAdr (schleifeProg zwKoerper .e) (zwKoerper.length + 2) (0, s)
        = some (0, s₁) ∧
      zwRep σ₁ ρ₁ s₁ := by
  rcases hRep.2 with ⟨_, rfl⟩ | ⟨hslot1, _, _⟩
  · refine ⟨zwSigma1 σ, ρ, _, Or.inl rfl, rfl, ?_⟩
    have hsl1 : ((zwSigma1 σ).slots () 0 ()).n = 1 := rfl
    have hbis1 : (zwBis (zwSigma1 σ) ρ).2 = true := by
      simp [zwBis, hsl1]
    refine ⟨hbis1.trans ?_, Or.inr ⟨hsl1, ?_, ?_⟩⟩
    · rfl
    · rfl
    · rfl
  · have htrue : (zwBis σ ρ).2 = true := by
      simp [zwBis, hslot1]
    rw [htrue] at he
    cases he

/-
CUTS:
- Pilot ISA only through `Instr`; one core, model memory, no time, no TSO:
  inherited from `ISARelax.lean`.
- No unbounded-loop budget: `forever` at any positive pass count unfolds
  one step (`ewig_ein_schritt` below); exhaustion is loud at zero passes
  (`BudgetExecution.forever_erschoepft_benannt`, not restated here).
- Per-iteration body correspondence (`hSeg` of `schleife_korrekt_endlich`)
  is a premise proved per body by its producer (straight-line bodies by
  the `Pipeline.lean` lemmas); this file lifts it to `n` rounds.
-/
