/-
  Generic checked source-assignment byte certificate (lane 648).

  A NEW generic finite-data certificate/check for the admitted actual
  typed `assignSlot` fragment, parameterised over declaration, table,
  field, source expression, environment and data layout. The fixed
  single-witness connection of lane 632 stays untouched and off the
  generic trust path: every generic result below is proved `forall` the
  declaration and reuses only the accepted interfaces (`SourceMemory`
  representation, `ValidatorExecution` strengthened entry admission,
  `LoadedExecution` image, fetched byte step, realised footprints).
-/
import Grammatik.X86.SourceMemory
import Grammatik.X86.ValidatorExecution
import Grammatik.X86.AccessExecution
import Grammatik.X86.EffectiveAddress

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Finite checked generic source/byte certificate: pure data only.
    `lo`/`hi` name the admitted integer range, `vval` the expected
    source value number, `vbyte` its expected lowest target byte
    (redundant on purpose: mutating one without the other refuses),
    `basis`/`len`/`off` the layout extent, `rbase` the expected base
    register content (redundant with `basis + off`: a wrong layout
    base refuses even though admission still holds there), `profil`,
    `bild`, `bias`, `eintritt` the checked image side. No proof-valued
    field, no assumed simulation, no trusted external print. -/
structure GenByteCert where
  profil : Profil
  bild : Bild
  bias : Nat
  eintritt : Nat
  basis : Nat
  len : Nat
  off : Nat
  rbase : Nat
  lo : Int
  hi : Int
  vval : Int
  vbyte : Byte

/-- Register file named by the certificate: `rax` carries the expected
    value number, `rbx` the expected base address, everything else zero.
    Finite data determines the whole file; no function-valued field. -/
def genCertReg (c : GenByteCert) : Register → Wort :=
  fun q => if q = Register.rax then BitVec.ofNat 64 c.vval.toNat
    else if q = Register.rbx then BitVec.ofNat 64 c.rbase
    else BitVec.ofNat 64 0

/-- Loaded start state named by the certificate. -/
def genCertStart (c : GenByteCert) : Zustand :=
  bildZustand c.bild c.bias (BitVec.ofNat 64 c.eintritt) (genCertReg c)
    storeFlags

/-- The checked generic certificate Bool: representation admission,
    profile scope pin, strengthened entry admission, fetched-decode
    shape, base-register/layout consistency, value/byte consistency,
    cell readability and the observed target byte. Every side is
    recomputed in Lean from the certificate data. -/
def genCertOk (c : GenByteCert) : Bool :=
  repOk (.int c.lo c.hi) c.basis c.len c.off &&
  decide (c.profil = .p48) &&
  valEintrittStark c.profil c.bild c.bias c.eintritt (genCertReg c)
    storeFlags &&
  decide (fetchDekodiert (genCertStart c) =
    some (⟨.store64 .rbx .rax 0, 7⟩, List.replicate 8 (natByte 0))) &&
  decide (c.rbase = c.basis + c.off) &&
  decide (natByte c.vval.toNat = c.vbyte) &&
  lesbar8 (genCertStart c).speicher (slotAddr c.basis c.off) &&
  decide (ausgangByte (slotAddr c.basis c.off)
    (byteschritt (genCertStart c)) = some c.vbyte)

/-! ## Generic certificate soundness: the accepted Bool implies the
    joint source/target representation, for ANY declaration. -/

/-- GENERIC CERTIFICATE SOUNDNESS: from the accepted Bool and the
    actual source step, the covered `assignSlot` (any repOk-admitted
    `.int` field, any value expression) and the decoded loaded step
    agree on the admitted slot: the representation holds at the joint
    post-states, the target word reads back and parses to the source
    value, the image stays accepted with its entry contained, and the
    realised footprint is exactly the slot. The source/target value
    link is finite identity (`hvCert`: the evaluated number IS the
    certificate number); the correspondence itself (`RepSlot`,
    read-back, footprint) is DERIVED, never a premise. Every premise
    is used: `hT` links the field type, `hLoEq`/`hHiEq` move the
    certificate range onto it, `hLese`/`hk`/`hv` name the evaluated
    index and value for the accepted step, `hExec` is the source step,
    `hvCert` ties the stored word to the source value, `h` supplies
    admission, entry, decode, consistency, readability and the
    observed byte. -/
theorem genCert_sound {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (t : D.Tab) (f : D.Feld t)
    (lo hi : Int) (hT : D.typ t f = .int lo hi)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ)
    (σL : World D) (hLese : σL = σ.lese Λ (i.orte ++ e.orte))
    (k : Int) (v : Zahl lo hi)
    (hk : (eval σL i σL ρ).n = k)
    (hv : (cast (congrArg (Wert D) hT) (eval σL e σL ρ)) = v)
    (c : GenByteCert)
    (hLoEq : c.lo = lo) (hHiEq : c.hi = hi) (hvCert : v.n = c.vval)
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes R (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok σ' ρ')
    (h : genCertOk c = true) :
    ∃ (s' : Zustand),
      byteschritt (genCertStart c) = .weiter s' ∧
      RepSlot t k f lo hi hT (slotAddr c.basis c.off) s'.speicher σ' ∧
      read64 s'.speicher (slotAddr c.basis c.off) = some (zahlWort v) ∧
      wortZahl lo hi (zahlWort v) = some v ∧
      wohlgeformt .p48 c.bild = true ∧
      eintragEnthalten c.bias c.bild.abschnitte c.eintritt = true ∧
      (zugriff ⟨.store64 .rbx .rax 0, 7⟩ (genCertStart c)).schreiben =
        Fuss (slotAddr c.basis c.off) := by
  have hSplit := h
  unfold genCertOk at hSplit
  simp only [Bool.and_eq_true_iff] at hSplit
  obtain ⟨⟨⟨⟨⟨⟨⟨hRep, hProf⟩, hVal⟩, hFetch⟩, hRbase⟩, hVByte⟩, hLesbar⟩,
    hByte⟩ := hSplit
  have hProfEq : c.profil = .p48 := of_decide_eq_true hProf
  rw [hProfEq] at hVal
  have hWf : wohlgeformt .p48 c.bild = true :=
    valStark_wohlgeformt .p48 c.bild c.bias c.eintritt (genCertReg c)
      storeFlags hVal
  have hEintrag : eintragEnthalten c.bias c.bild.abschnitte c.eintritt = true :=
    valStark_eintrag .p48 c.bild c.bias c.eintritt (genCertReg c)
      storeFlags hVal
  have hRepI : repOk (.int lo hi) c.basis c.len c.off = true := by
    rw [← hLoEq, ← hHiEq]; exact hRep
  have hOk : repOk (D.typ t f) c.basis c.len c.off = true := by
    rw [hT]; exact hRepI
  obtain ⟨hLoB, hHiB, -, -⟩ := repOk_klingt hRepI
  have hFetchEq : fetchDekodiert (genCertStart c) =
      some (⟨.store64 .rbx .rax 0, 7⟩, List.replicate 8 (natByte 0)) :=
    of_decide_eq_true hFetch
  have hRbaseEq : c.rbase = c.basis + c.off := of_decide_eq_true hRbase
  have hVByteEq : natByte c.vval.toNat = c.vbyte := of_decide_eq_true hVByte
  have hByteEq : ausgangByte (slotAddr c.basis c.off)
      (byteschritt (genCertStart c)) = some (natByte c.vval.toNat) := by
    rw [hVByteEq]; exact of_decide_eq_true hByte
  have hRax : genCertReg c .rax = BitVec.ofNat 64 c.vval.toNat := by
    simp [genCertReg]
  have hRegEq : (genCertStart c).register .rax = zahlWort v := by
    show genCertReg c .rax = zahlWort v
    rw [hRax]
    show BitVec.ofNat 64 c.vval.toNat = zahlWort v
    unfold zahlWort
    rw [← hvCert]
  have hRbx : (genCertStart c).register .rbx =
      slotAddr c.basis c.off := by
    show genCertReg c .rbx = slotAddr c.basis c.off
    have hRb : genCertReg c .rbx = BitVec.ofNat 64 c.rbase := by
      simp [genCertReg]
    rw [hRb, hRbaseEq]
    rfl
  have hAddrEq : effAddr (genCertStart c) .rbx 0 =
      slotAddr c.basis c.off :=
    (effAddr_null _ _).trans hRbx
  match hs : byteschritt (genCertStart c) with
  | .weiter s' =>
    have hDecomp := byte_aus_weiter (genCertStart c) s' hs
    obtain ⟨d', rest', hf, hst⟩ := hDecomp
    have hPair : (d', rest') =
        (⟨.store64 .rbx .rax 0, 7⟩, List.replicate 8 (natByte 0)) :=
      Option.some_inj.mp (by rw [← hf]; exact hFetchEq)
    have hdEq : d' = ⟨.store64 .rbx .rax 0, 7⟩ := congrArg Prod.fst hPair
    have hbef : d'.befehl = .store64 .rbx .rax 0 := by rw [hdEq]
    have hlen : d'.laenge = 7 := by rw [hdEq]
    have hok7 : laengeOk d'.laenge = true := by rw [hlen]; decide
    have hFound := realisiert_store64_gefunden d' (genCertStart c) s'
      .rbx .rax 0 hok7 hbef hst
    obtain ⟨m, hTgt0, -, -, -⟩ := hFound
    have hTgt : write64 (genCertStart c).speicher (slotAddr c.basis c.off)
        (zahlWort v) = some m := by
      rw [← hAddrEq, ← hRegEq]
      exact hTgt0
    have hSchritt := schritt_store64_erfolg d' (genCertStart c) .rbx .rax 0 m
      hok7 hbef hTgt0
    have hMem : s'.speicher = m := by
      have hEq := hst.symm.trans hSchritt
      have hInj := Option.some_inj.mp hEq
      have h2 := congrArg Zustand.speicher hInj
      simpa using h2
    have hTgt' : write64 (genCertStart c).speicher (slotAddr c.basis c.off)
        (zahlWort v) = some s'.speicher := by
      rw [hMem]; exact hTgt
    have hRepMain := rep_schritt_bleibt O passes R t f lo hi hT
      c.basis c.len c.off hOk i e hw hL σ ρ σL hLese
      k v hk hv (slotAddr c.basis c.off) _ _ σ' ρ' hExec hTgt' hLesbar
    have hRead : read64 s'.speicher (slotAddr c.basis c.off) =
        some (zahlWort v) :=
      read64_nach_write64 _ _ _ _ hTgt' hLesbar
    have hRound : wortZahl lo hi (zahlWort v) = some v :=
      zahlWort_wortZahl v hLoB hHiB
    have hFuss := realisiert_store64_fuss d' (genCertStart c) s' .rbx .rax 0
      hok7 hbef hst
    have hFussEq : (zugriff ⟨.store64 .rbx .rax 0, 7⟩
        (genCertStart c)).schreiben = Fuss (slotAddr c.basis c.off) := by
      have h2 := hFuss.2.1
      rw [hdEq, hAddrEq] at h2
      exact h2
    exact ⟨s', rfl, hRepMain.1, hRead, hRound, hWf, hEintrag, hFussEq⟩
  | .verweigert =>
    have hNone : ausgangByte (slotAddr c.basis c.off) .verweigert = none :=
      rfl
    rw [hs] at hByteEq
    rw [hNone] at hByteEq
    cases hByteEq

/-! ## Witnesses: two distinct declarations through the SAME checker.

    Declaration A reuses the accepted `SourceMemory` witness fragment
    (one `.int 0 100` table, value 42); declaration B below is a fresh
    one (one `.int 10 60` table, value 17). Both pass the SAME
    `genCertOk`. The fixed lane-632 witness stays untouched and is
    never a premise of the generic soundness above. -/

/-- Witness-B signature: parameterless, no answer, writes the table. -/
def witSigB : Signatur Unit Empty Empty Empty :=
  { params := [], erg := none, gruende := 0, haelt := [],
    schreibt := fun _ => true, gschreibt := fun g => (nomatch g),
    konsumiert := [], produziert := [], boden := none }

/-- Witness-B declaration: one table with one `.int 10 60` field, one
    parameterless function whose contract writes it, nothing else. -/
def witDB : Deklaration where
  Tab := Unit
  count := fun _ => 1
  Feld := fun _ => Unit
  typ := fun _ _ => .int 10 60
  erlaubt := fun _ _ _ _ => true
  tabNr := fun _ => some ()
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
  sigNr := fun _ => witSigB
  eigner_nie_erzeugt := fun n t m s _ => nomatch m
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
  invarianten_gehalten := fun n i _ => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The witness-B contract: writes the table. -/
def witVB : Vertrag witDB :=
  { schreibt := fun _ => true
    gschreibt := fun g => nomatch g
    erg := none
    gruende := 0
    haelt := []
    produziert := []
    boden := none }

/-- The witness-B oracle: no axioms, registers or globals to answer. -/
def witOB : Orakel witDB where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- The witness-B callee table: every call succeeds without moving memory. -/
def witRB : ∀ f : witDB.Fn, World witDB → Env witDB (witDB.params f) →
    RufAusgang f :=
  fun _ σ _ => .ok σ ()

/-- The witness-B index: row 0. -/
def witIB : Expr witDB [] [] (.index (witDB.count ())) := Expr.lit 0

/-- The witness-B value: 17 in `10 .. 60`. -/
def witEB : Expr witDB [] [] (witDB.typ () ()) :=
  Expr.weiter (by decide) (by decide) (Expr.lit 17)

/-- The witness-B world: every slot is 10, no trace yet. -/
def witSigmaB : World witDB where
  slots := fun t _ f => by cases t; cases f; exact ⟨10, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

/-- The witness-B read world: the trace entries of the two reads. -/
def witSLB : World witDB := witSigmaB.lese [] (witIB.orte ++ witEB.orte)

/-- The witness-B value at the target: 17. -/
def witValB : Zahl 10 60 := ⟨17, by decide, by decide⟩

/-- The witness-B field type. -/
theorem witHTB : witDB.typ () () = .int 10 60 := rfl

/-- The witness-B contract writes the table. -/
theorem witHwB : witVB.schreibt () = true := rfl

/-- The witness-B table needs no guards. -/
theorem witHLB : darf witDB () [] :=
  fun _ h => False.elim (List.not_mem_nil h)

/-- The witness-B source statement: write 17 into row 0. -/
def witStmtB :=
  Stmt.assignSlot (l := false) (t := ()) (f := ()) witIB witEB witHwB witHLB

/-- SOURCE EXECUTION B (recomputed in Lean): the statement runs on the
    witness-B world, writing 17 into row 0 (10 before). -/
theorem witStmtB_ausgefuehrt :
    ∃ (σ' : World witDB) (ρ' : Env witDB []),
      execStmt witOB 0 witRB witStmtB witSigmaB Env.nil = .ok σ' ρ' ∧
      (witSigmaB.slots () 0 ()).n = 10 ∧
      (σ'.slots () 0 ()).n = 17 := by
  have hExecFull : ∃ σ' ρ',
      execStmt witOB 0 witRB witStmtB witSigmaB Env.nil = .ok σ' ρ' := by
    simp only [witStmtB, execStmt]
    exact ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hExec⟩ := hExecFull
  refine ⟨σ', ρ', hExec, rfl, ?_⟩
  cases hExec
  rfl

/-! ## Certificates: two acceptances through the SAME checker. -/

/-- Certificate A: profile 48, the accepted store image at its checked
    bias/entry, layout extent base `0x102000` length 16 offset 0 with
    the matching base register, range `0 .. 100`, value 42. -/
def genCertA : GenByteCert :=
  ⟨.p48, bildStore, 0x100000, 0x101000, 0x102000, 16, 0, 0x102000,
    0, 100, 42, natByte 42⟩

/-- Certificate B: the same image side, range `10 .. 60`, value 17 --
    a distinct source assignment through the same checker. -/
def genCertB : GenByteCert :=
  ⟨.p48, bildStore, 0x100000, 0x101000, 0x102000, 16, 0, 0x102000,
    10, 60, 17, natByte 17⟩

/-- ACCEPTANCE A: every recomputed check passes for value 42. -/
theorem genCertA_ok : genCertOk genCertA = true := by
  decide

/-- ACCEPTANCE B: every recomputed check passes for value 17. -/
theorem genCertB_ok : genCertOk genCertB = true := by
  decide

/-! ## Mutated witnesses: opcode, entry, layout, value, profile, map. -/

/-- Mutated opcode: the forged-opcode image at the same bias/entry. -/
def genCertMutBytes : GenByteCert :=
  ⟨.p48, bildStoreMutiert, 0x100000, 0x101000, 0x102000, 16, 0, 0x102000,
    0, 100, 42, natByte 42⟩

/-- Mutated entry: the same image started in the data section. -/
def genCertFalschEintritt : GenByteCert :=
  ⟨.p48, bildStore, 0x100000, 0x102000, 0x102000, 16, 0, 0x102000,
    0, 100, 42, natByte 42⟩

/-- Mutated layout: the same image and base register, but the layout
    base names `4096` instead of the store target. Admission still
    holds there; the base-register consistency does not. -/
def genCertFalschBasis : GenByteCert :=
  ⟨.p48, bildStore, 0x100000, 0x101000, 4096, 16, 0, 0x102000,
    0, 100, 42, natByte 42⟩

/-- Mutated source value: the certificate claims 43 while the expected
    byte still names 42. -/
def genCertFalschWert : GenByteCert :=
  ⟨.p48, bildStore, 0x100000, 0x101000, 0x102000, 16, 0, 0x102000,
    0, 100, 43, natByte 42⟩

/-- Mutated profile: the same image under `.p57`, outside the scope. -/
def genCertProfil57 : GenByteCert :=
  ⟨.p57, bildStore, 0x100000, 0x101000, 0x102000, 16, 0, 0x102000,
    0, 100, 42, natByte 42⟩

/-- Mutated map: the writable-code image refuses the mapping leg. -/
def genCertWx : GenByteCert :=
  ⟨.p48, bildStoreWx, 0x100000, 0x101000, 0x102000, 16, 0, 0x102000,
    0, 100, 42, natByte 42⟩

/-- OPCODE REFUSAL: the forged opcode byte defeats fetch-and-decode. -/
theorem genCert_mutiert_bytes_verweigert :
    genCertOk genCertMutBytes = false := by
  decide

/-- ENTRY REFUSAL: starting in the data section admits no fetch. -/
theorem genCert_falschEintritt_verweigert :
    genCertOk genCertFalschEintritt = false := by
  decide

/-- LAYOUT REFUSAL: the wrong layout base breaks the base-register
    consistency. -/
theorem genCert_falschBasis_verweigert :
    genCertOk genCertFalschBasis = false := by
  decide

/-- SOURCE-VALUE REFUSAL: the mutated value number breaks the
    value/byte consistency. -/
theorem genCert_falschWert_verweigert :
    genCertOk genCertFalschWert = false := by
  decide

/-- PROFILE REFUSAL: `.p57` is outside the pinned scope. -/
theorem genCert_profil57_verweigert :
    genCertOk genCertProfil57 = false := by
  decide

/-- MAP REFUSAL: writable code is not an accepted image. -/
theorem genCert_wx_verweigert :
    genCertOk genCertWx = false := by
  decide

/-! ## Joint witness: both declarations through the same checker, with
    reached memory-changing runs on both sides and planted refusals. -/

/-- The witness-A source statement, recomputed in Lean. -/
def witStmtA :=
  Stmt.assignSlot (l := false) (t := ()) (f := ()) witI witE witHw witHL

/-- SOURCE EXECUTION A (recomputed in Lean): writes 42 into row 0. -/
theorem witStmtA_ausgefuehrt :
    ∃ (σ' : World witD) (ρ' : Env witD []),
      execStmt witO 0 witR witStmtA witSigma Env.nil = .ok σ' ρ' ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 42 := by
  have hExecFull : ∃ σ' ρ',
      execStmt witO 0 witR witStmtA witSigma Env.nil = .ok σ' ρ' := by
    simp only [witStmtA, execStmt]
    exact ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hExec⟩ := hExecFull
  refine ⟨σ', ρ', hExec, rfl, ?_⟩
  cases hExec
  rfl

/-- JOINT WITNESS for `genCert_sound`: both certificates pass the same
    checker; declaration A (one table its function writes) runs a
    reached source step `0 → 42` and a reached loaded step moving the
    target byte `0 → 42` with the representation at the joint
    post-states; declaration B (a distinct table, range and value)
    runs a reached source step `10 → 17` with the representation at
    its joint post-state; all six planted refusals hold. Both runs
    reach a memory-changing step: non-degenerate on both sides. -/
theorem genCert_sound_zeuge :
    ∃ (σA' : World witD) (ρA' : Env witD []) (sA' : Zustand)
      (σB' : World witDB) (ρB' : Env witDB []) (sB' : Zustand),
      genCertOk genCertA = true ∧
      genCertOk genCertB = true ∧
      witV.schreibt () = true ∧
      witVB.schreibt () = true ∧
      execStmt witO 0 witR witStmtA witSigma Env.nil = .ok σA' ρA' ∧
      byteschritt (genCertStart genCertA) = .weiter sA' ∧
      RepSlot () 0 () 0 100 witHT (slotAddr genCertA.basis genCertA.off)
        sA'.speicher σA' ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (σA'.slots () 0 ()).n = 42 ∧
      (genCertStart genCertA).speicher.bytes
        (slotAddr genCertA.basis genCertA.off) = BitVec.ofNat 8 0 ∧
      ausgangByte (slotAddr genCertA.basis genCertA.off)
        (byteschritt (genCertStart genCertA)) = some (natByte 42) ∧
      execStmt witOB 0 witRB witStmtB witSigmaB Env.nil = .ok σB' ρB' ∧
      byteschritt (genCertStart genCertB) = .weiter sB' ∧
      RepSlot () 0 () 10 60 witHTB (slotAddr genCertB.basis genCertB.off)
        sB'.speicher σB' ∧
      (witSigmaB.slots () 0 ()).n = 10 ∧
      (σB'.slots () 0 ()).n = 17 ∧
      ausgangByte (slotAddr genCertB.basis genCertB.off)
        (byteschritt (genCertStart genCertB)) = some (natByte 17) ∧
      genCertOk genCertMutBytes = false ∧
      genCertOk genCertFalschEintritt = false ∧
      genCertOk genCertFalschBasis = false ∧
      genCertOk genCertFalschWert = false ∧
      genCertOk genCertProfil57 = false ∧
      genCertOk genCertWx = false := by
  obtain ⟨σA', ρA', hExecA, hPreA, hPostA⟩ := witStmtA_ausgefuehrt
  obtain ⟨σB', ρB', hExecB, hPreB, hPostB⟩ := witStmtB_ausgefuehrt
  have hMainA := genCert_sound witO 0 witR () () 0 100 witHT
    witI witE witHw witHL witSigma Env.nil witSL rfl 0 witVal rfl rfl
    genCertA rfl rfl rfl σA' ρA' hExecA genCertA_ok
  have hMainB := genCert_sound witOB 0 witRB () () 10 60 witHTB
    witIB witEB witHwB witHLB witSigmaB Env.nil witSLB rfl 0 witValB rfl rfl
    genCertB rfl rfl rfl σB' ρB' hExecB genCertB_ok
  obtain ⟨sA', hStepA, hRepA, -, -, -, -, -⟩ := hMainA
  obtain ⟨sB', hStepB, hRepB, -, -, -, -, -⟩ := hMainB
  have hPreByteA : (genCertStart genCertA).speicher.bytes
      (slotAddr genCertA.basis genCertA.off) = BitVec.ofNat 8 0 := by
    decide
  have hPostByteA : ausgangByte (slotAddr genCertA.basis genCertA.off)
      (byteschritt (genCertStart genCertA)) = some (natByte 42) := by
    decide
  have hPostByteB : ausgangByte (slotAddr genCertB.basis genCertB.off)
      (byteschritt (genCertStart genCertB)) = some (natByte 17) := by
    decide
  exact ⟨σA', ρA', sA', σB', ρB', sB', genCertA_ok, genCertB_ok,
    witHw, witHwB, hExecA, hStepA, hRepA, hPreA, hPostA, hPreByteA,
    hPostByteA, hExecB, hStepB, hRepB, hPreB, hPostB, hPostByteB,
    genCert_mutiert_bytes_verweigert, genCert_falschEintritt_verweigert,
    genCert_falschBasis_verweigert, genCert_falschWert_verweigert,
    genCert_profil57_verweigert, genCert_wx_verweigert⟩

/- CUTS:
     Proved here, over the ACTUAL accepted vocabulary
     (`SourceMemory.repOk`/`zahlWort`/`wortZahl`/`RepSlot`/
     `rep_schritt_bleibt` with an ARBITRARY declaration, the goal's
     own `execStmt`/`eval`, `ValidatorExecution.valEintrittStark`/
     `valStark_wohlgeformt`/`valStark_eintrag`,
     `LoadedExecution.bildStore`/`bildZustand`,
     `Byteschritt.fetchDekodiert`/`byteschritt`/`ausgangByte`,
     `AccessExecution.byte_aus_weiter`/
     `realisiert_store64_gefunden`/`realisiert_store64_fuss`,
     `Ausfuehrung.schritt_store64_erfolg`,
     `EffectiveAddress.effAddr_null`,
     `Speicher.read64_nach_write64`): a generic finite-data
     certificate (`GenByteCert`: profile, image, bias, entry, layout
     extent, redundant base register, range, value number, redundant
     value byte -- pure data, no proof-valued field, no assumed
     simulation) with its recomputed Bool (`genCertOk`: admission,
     profile scope, strengthened entry admission, fetched-decode
     shape, base/layout consistency, value/byte consistency, cell
     readability, observed byte), the generic soundness theorem
     (`genCert_sound`, `forall` the declaration/table/field/
     expression/environment: the covered source step and the decoded
     loaded step agree -- representation at the joint post-states,
     target word read-back and parse, mapping and entry legs,
     realised footprint exactly the slot), two acceptances through
     the SAME checker (values 42 and 17, ranges `0 .. 100` and
     `10 .. 60`, distinct declarations), six planted refusals
     (mutated opcode, mutated entry, mutated layout base, mutated
     source-value number, mutated profile, mutated map) and one joint
     nondegenerate memory-changing witness on both declarations.
     The fixed lane-632 witness is untouched and never a premise of
     the generic claim; the finite examples here are witnesses only,
     off the generic trust path.
     NOT proved here, and not claimed:
     - No `valX86_sound`: nothing here claims an admitted image is the
       emitted form of an arbitrary source program. The connection
       covers exactly one fragment: one `.int lo hi` slot with
       `0 <= lo`, `hi < 2 ^ 64` (checked by `repOk`), one
       `assignSlot` form, one decoded store image. Other statement
       forms, widths, sums, floats, bools, globals, pointers, calls,
       loops and concurrency stay OPEN.
     - No multi-step control-flow, relocation re-decode, gate/OS
       contract (user logic, never an assumption), cost/time,
       budget-stop or termination claim. `verweigert` is the absence
       of a transition.
     - No hardware claim: bytes are model `Byte` lists, memory the
       model `Speicher`; silicon, caches, TLBs, store buffers,
       interrupts, faults beyond the decoded refusal and timing are
       OPEN. Only named hardware behaviour is ever assumed.
     - No TSO/GX bridge: every step is sequential over one
       `Speicher`; per-access target-to-W/GX simulation stays OPEN
       with its owner.
     - No optimiser/loader closure: `genCertOk` is the honest Bool
       interface for it (source AST determines the checked numbers,
       certificates carry finite data only), but whole-unit lowering,
       image construction and the source-to-final-loaded-bytes
       closing theorem stay OPEN.
     - Profile scope is pinned to `.p48`: `.p57` accepts the same map,
       so the certificate refuses it by an explicit scope leg, not by
       a mapping difference.
     - Values above 255 need a wider observation than the single
       lowest byte checked here; the admitted ranges already cover
       them but the byte leg pins the low byte only.
-/

#print axioms genCertOk
#print axioms genCert_sound
#print axioms genCertA_ok
#print axioms genCertB_ok
#print axioms genCert_mutiert_bytes_verweigert
#print axioms genCert_falschEintritt_verweigert
#print axioms genCert_falschBasis_verweigert
#print axioms genCert_falschWert_verweigert
#print axioms genCert_profil57_verweigert
#print axioms genCert_wx_verweigert
#print axioms witStmtA_ausgefuehrt
#print axioms witStmtB_ausgefuehrt
#print axioms genCert_sound_zeuge

end Gabbro.Grammatik.X86
