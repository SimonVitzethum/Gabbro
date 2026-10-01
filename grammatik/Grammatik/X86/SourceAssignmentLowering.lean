/-
  File:      Grammatik/X86/SourceAssignmentLowering.lean
  Subject:   Direct typed-source assignment to pilot machine code (lane 628).

  Lower the actually covered typed `Stmt.assignSlot` (an `.int lo hi` field
  admitted by the accepted `SourceMemory570` `repOk`, with its value
  expression in the accepted `ExpressionLowering599` `senkFrag` fragment)
  into generated pilot instructions (`prog ++ [store64]`), and prove the
  source `execStmt` world update matches the target `lauf` execution under
  the one representation map (`zahlWort`/`intWort` bridge). No second IR,
  no new interpreter, no source/checker/emitter edit.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.ScalarFloat
import Grammatik.X86.SourceMemory
import Grammatik.X86.ExpressionLowering
import Grammatik.X86.EffectiveAddress

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Direct lowering of one admitted assignment: the value fragment lowered
    by `senkFrag` (599), followed by one `store64` through the admitted
    slot base register. `none` is the explicit unsupported-expression
    refusal; admission of the slot itself stays with `repOk` (570). -/
def senkAssign {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp base : Register) (disp : BitVec 32) :
    Option (List Befehl) :=
  match senkFrag abb e dst tmp with
  | some prog => some (prog ++ [Befehl.store64 base dst disp])
  | none => none

/-- VALUE BRIDGE: on a `repOk`-admitted nonnegative range below
    `2 ^ 64`, the modular expression word (`intWort`, reused from 599) is
    the representation word (`zahlWort`, reused from 570). Both bounds
    are used: `hLo`/`hHi` place the value for the modulo identity. -/
theorem intWort_zahlWort {lo hi : Int} (v : Zahl lo hi)
    (hLo : 0 ≤ lo) (hHi : hi < 2 ^ 64) :
    intWort v.n = zahlWort v := by
  obtain ⟨n, hlo, hhi⟩ := v
  have hnn : 0 ≤ n := by omega
  have hlt : n < 2 ^ 64 := by omega
  have hmod : n % (2 ^ 64 : Int) = n := by omega
  simp only [intWort, zahlWort, hmod]

/-- SHAPE: a successful fragment lowering extends with the slot store. -/
theorem senkAssign_ok {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp base : Register) (disp : BitVec 32)
    (prog : List Befehl) (h : senkFrag abb e dst tmp = some prog) :
    senkAssign abb e dst tmp base disp =
      some (prog ++ [Befehl.store64 base dst disp]) := by
  unfold senkAssign
  rw [h]

/-- PLANTED REFUSAL (unsupported expression): multiplication has no
    lowering, so no assignment sequence is generated for it. -/
theorem senkAssign_verweigert_mul {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp base : Register) (disp : BitVec 32) :
    senkAssign abb
      (Expr.mul (Expr.lit (Γ := Γ) (Λ := Λ) 2) (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst tmp base disp = none := by
  unfold senkAssign
  rw [senkFrag_verweigert_mul]

/-- PLANTED REFUSAL (unsupported nesting): a depth-two add has no
    lowering, so no assignment sequence is generated for it. -/
theorem senkAssign_verweigert_tief {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp base : Register) (disp : BitVec 32) :
    senkAssign abb
      (Expr.add
        (Expr.add (Expr.lit (Γ := Γ) (Λ := Λ) 1) (Expr.lit (Γ := Γ) (Λ := Λ) 2))
        (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst tmp base disp = none := by
  unfold senkAssign
  rw [senkFrag_verweigert_tief]

/-- RANGE REFUSAL: a range starting below zero is refused by the checked
    admission (the modular word mapping would clip the negative part). -/
theorem assignRepOk_negativ_verweigert :
    repOk (.int (-5) 100) 8192 16 0 = false := by
  decide

/-- CODE-ALIAS REFUSAL at region level: a code extent overlapping the
    admitted slot extent shares bytes, so image/region separation refuses
    it (`regionDisjunkt = false`). -/
theorem assignCodeAlias_verweigert :
    regionDisjunkt
      (alsRegion { tab := 0, basis := 4096, len := 32, ausr := 8 })
      (alsRegion { tab := 1, basis := 4120, len := 16, ausr := 8 }) =
      false := by
  decide

/-- TRANSPORT (expression): evaluation commutes with a type
    ascription cast. Both sides of `g` are variables, so `cases` applies;
    callers instantiate with the stuck field-type equation. -/
theorem evalTrans {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (σ₀ : World D) {τ1 τ2 : Ty} (g : τ2 = τ1) (e : Expr D Γ Λ τ2)
    (σ : World D) (ρ : Env D Γ) :
    eval σ₀ (cast (congrArg (Expr D Γ Λ) g) e) σ ρ =
      cast (congrArg (Wert D) g) (eval σ₀ e σ ρ) := by
  cases g
  rfl

/-- TRANSPORT (value round trip): casting there and back is the identity.
    Both sides of `g` are variables, so `cases` applies. -/
theorem paarCancel {D : Deklaration} {σ1 σ2 : Ty} (g : σ1 = σ2)
    (x : Wert D σ2) :
    cast (congrArg (Wert D) g) (cast (congrArg (Wert D) g.symm) x) = x := by
  cases g
  rfl

/-- MAIN: one admitted `assignSlot` whose value expression is in the 599
    fragment lowers to generated pilot code plus one slot store, and the
    source world update matches the target run under the one
    representation map. The statement carries the transported expression
    `e2` (the same syntax at the field type); the fragment lowering runs
    on the constructor-headed `e`, so the generated sequence comes from
    the admitted statement itself. Value flow is derived: `senkung_korrekt`
    proves the register holds `intWort` of the actual evaluation,
    `heval` names that source value, and `intWort_zahlWort` turns it into
    the representation word. Every premise is used: `hOk` admits range,
    width and region; `hLese`/`hk`/`heval` name the evaluated index and
    value; `hExec` is the source step; `hsenk`/`hrenv`/`hFr`/`hrsp` drive
    the expression run; `hBasis`/`hBaseR`/`hdisp`/`ha` fix the slot
    address; `hTgt`/`hRd` give the target write and its read-back. -/
theorem senkAssign_korrekt {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (t : D.Tab) (f : D.Feld t)
    (lo hi : Int) (hT : D.typ t f = .int lo hi)
    (base len off : Nat)
    (hOk : repOk (D.typ t f) base len off = true)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (.int lo hi))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ)
    (σL : World D) (hLese : σL = σ.lese Λ (i.orte ++
      (cast (congrArg (Expr D Γ Λ) hT.symm) e).orte))
    (k : Int) (v : Zahl lo hi)
    (hk : (eval σL i σL ρ).n = k)
    (heval : (eval σL e σL ρ).n = v.n)
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp baseR : Register) (disp : BitVec 32)
    (hdisp : disp = BitVec.ofNat 32 0)
    (hFr : Frisch abb dst tmp)
    (hrsp : dst ≠ Register.rsp ∧ tmp ≠ Register.rsp)
    (hBasis : baseR ≠ dst ∧ baseR ≠ tmp)
    (s : Zustand) (m' : Speicher)
    (hBaseR : s.register baseR = slotAddr base off)
    (a : Adresse) (ha : a = slotAddr base off)
    (hTgt : write64 s.speicher a (zahlWort v) = some m')
    (hRd : lesbar8 s.speicher a = true)
    (prog : List Befehl) (hsenk : senkFrag abb e dst tmp = some prog)
    (hrenv : EnvRepr ρ s.register abb)
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes R
      (Stmt.assignSlot (l := l) t f i
        (cast (congrArg (Expr D Γ Λ) hT.symm) e) hw hL) σ ρ =
      .ok σ' ρ') :
    ∃ s', lauf ((prog ++ [Befehl.store64 baseR dst disp]).map
        fun b => (⟨b, (encode b).length⟩ : Decodiert)) s = some s' ∧
      s'.register dst = intWort (eval σL e σL ρ).n ∧
      s'.speicher = m' ∧
      RepSlot t k f lo hi hT a m' σ' ∧
      (∃ w, read64 m' a = some w ∧ wortZahl lo hi w = some v) := by
  have hOkI : repOk (.int lo hi) base len off = true := hT ▸ hOk
  obtain ⟨hLo, hHi, -, -⟩ := repOk_klingt hOkI
  -- 1. The generated expression code runs: derived value, kept memory.
  obtain ⟨s1, hrun1, hval1, hmem1, hregs1, _⟩ :=
    senkung_korrekt abb e dst tmp ρ σL σL s hFr hrsp hrenv prog hsenk
  -- 2. The base register survives the expression run (freshness).
  have hbase1 : s1.register baseR = slotAddr base off := by
    rw [hregs1 baseR hBasis.1 hBasis.2, hBaseR]
  -- 3. Zero displacement addresses the admitted slot itself.
  have heff : effAddr s1 baseR disp = a := by
    rw [hdisp, effAddr_null, hbase1, ha]
  -- 4. The computed register is the representation word (derived).
  have hword : s1.register dst = zahlWort v := by
    rw [hval1, heval, ← intWort_zahlWort v hLo hHi]
  -- 5. The store step writes it.
  have hwr : write64 s1.speicher (effAddr s1 baseR disp)
      (s1.register dst) = some m' := by
    rw [hmem1, heff, hword]
    exact hTgt
  have hlen : laengeOk (encode (Befehl.store64 baseR dst disp)).length =
      true :=
    laengeOk_encode _
  have hstore : schritt (⟨Befehl.store64 baseR dst disp, (encode (Befehl.store64 baseR dst disp)).length⟩ : Decodiert) s1 = some ({ s1 with speicher := m', rip := ripNach s1.rip (encode (Befehl.store64 baseR dst disp)).length }) :=
    schritt_store64_erfolg _ s1 baseR dst disp m' hlen rfl hwr
  -- 6. The value link the source side consumes (transport, then name).
  have e2val : eval σL (cast (congrArg (Expr D Γ Λ) hT.symm) e) σL ρ =
      cast (congrArg (Wert D) hT.symm) (eval σL e σL ρ) :=
    evalTrans σL hT.symm e σL ρ
  have hcancel := paarCancel (D := D) (g := hT) (eval σL e σL ρ)
  have hve : eval σL e σL ρ = v := by
    revert heval
    obtain ⟨n, hlo, hhi⟩ := eval σL e σL ρ
    obtain ⟨m, glo, ghi⟩ := v
    intro heval
    have hnm : n = m := heval
    subst hnm
    rfl
  have hv : (cast (congrArg (Wert D) hT)
      (eval σL (cast (congrArg (Expr D Γ Λ) hT.symm) e) σL ρ) :
      Wert D (.int lo hi)) = v := by
    rw [e2val, hcancel]
    exact hve
  -- 7. The source world update matches (accepted 570 step).
  have hRep := rep_schritt_bleibt O passes R t f lo hi hT base len off hOk
    i (cast (congrArg (Expr D Γ Λ) hT.symm) e) hw hL σ ρ σL hLese
    k v hk hv a s.speicher m' σ' ρ' hExec hTgt hRd
  -- 8. Expression run and store compose over the generated sequence.
  have hmap : ((prog ++ [Befehl.store64 baseR dst disp]).map
      fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
      (prog.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
      [⟨Befehl.store64 baseR dst disp,
        (encode (Befehl.store64 baseR dst disp)).length⟩] := by
    simp [List.map_append]
  have hrun : lauf ((prog ++ [Befehl.store64 baseR dst disp]).map fun b => (⟨b, (encode b).length⟩ : Decodiert)) s = some ({ s1 with speicher := m', rip := ripNach s1.rip (encode (Befehl.store64 baseR dst disp)).length }) := by
    rw [hmap, lauf_anhang _ _ _ _ hrun1, lauf_einzeln_gleich]
    exact hstore
  refine ⟨_, hrun, hval1, rfl, hRep.1, hRep.2⟩
/-! ## Witness: one table, one writing function, one step. -/

/-- Witness signature: parameterless, no answer, writes the table. -/
def witSig628 : Signatur Unit Empty Empty Empty :=
  { params := [], erg := none, gruende := 0, haelt := [],
    schreibt := fun _ => true, gschreibt := fun g => (nomatch g),
    konsumiert := [], produziert := [], boden := none }

/-- Witness declaration: one table with one `.int 12 100` field, one
    parameterless function whose contract writes it, nothing else. -/
def witD628 : Deklaration where
  Tab := Unit
  count := fun _ => 1
  Feld := fun _ => Unit
  typ := fun _ _ => .int 12 100
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

/-- The witness contract: writes the table. -/
def witV628 : Vertrag witD628 :=
  { schreibt := fun _ => true
    gschreibt := fun g => nomatch g
    erg := none
    gruende := 0
    haelt := []
    produziert := []
    boden := none }

/-- The witness oracle: no axioms, registers or globals to answer. -/
def witO628 : Orakel witD628 where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- The witness callee table: every call succeeds without moving memory. -/
def witR628 : ∀ f : witD628.Fn, World witD628 →
    Env witD628 (witD628.params f) → RufAusgang f :=
  fun _ σ _ => .ok σ ()

/-- Witness context: one integer variable in `0 .. 88`. -/
def witCtx628 : Ctx := [.int 0 88]

/-- The witness index: row 0 (in the statement context). -/
def witI628 : Expr witD628 witCtx628 [] (.index (witD628.count ())) :=
  Expr.lit 0

/-- The witness value: `x + 12` with `x = 30`, hence `42` in `12 .. 100`.
    The computed range is definitionally the field type, so the fragment
    lowering sees the constructor-headed addition itself. -/
def witE628 : Expr witD628 witCtx628 [] (.int 12 100) :=
  .add (.var .hier) (.lit 12)

/-- Witness environment: `x = 30`. -/
def witEnv628 : Env witD628 witCtx628 :=
  .cons ⟨30, by decide, by decide⟩ .nil

/-- The witness world: the slot holds 12, no trace yet. -/
def witSigma628 : World witD628 where
  slots := fun t _ f => by cases t; cases f; exact ⟨12, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

/-- The witness field type. -/
theorem witHT628 : witD628.typ () () = .int 12 100 := rfl

/-- The witness contract writes the table. -/
theorem witHw628 : witV628.schreibt () = true := rfl

/-- The witness table needs no guards. -/
theorem witHL628 : darf witD628 () [] :=
  fun _ h => False.elim (List.not_mem_nil h)

/-- The witness value at the target: 42. -/
def witVal628 : Zahl 12 100 := ⟨42, by decide, by decide⟩

/-- Admission holds on the witness layout. -/
theorem witOk628 : repOk (witD628.typ () ()) 8192 16 0 = true := by
  decide

/-- The witness index evaluates to row 0. -/
theorem witHk628 :
    (eval witSigma628 witI628 witSigma628 witEnv628).n = 0 :=
  rfl

/-- The read world of the witness run (transported value places). -/
def witSL628 : World witD628 :=
  witSigma628.lese []
    (witI628.orte ++
      (cast (congrArg (Expr witD628 witCtx628 []) witHT628.symm)
        witE628).orte)

/-- The witness value evaluates to 42 in the single source model. -/
theorem witHeval628 :
    (eval witSL628 witE628 witSL628 witEnv628).n = witVal628.n :=
  rfl

/-- Witness register assignment: the source variable lives in `r10`. -/
def witAbb628 : ∀ (τ : Ty), Var witCtx628 τ → Register :=
  fun _ _ => .r10

/-- Witness register file: `r10` holds the source value 30, `rbx` the
    admitted slot base 8192, everything else zero. -/
def witReg628 : Register → Wort :=
  fun q => if q = Register.r10 then intWort 30
    else if q = Register.rbx then natAdresse 8192
    else BitVec.ofNat 64 0

/-- The generated witness program: lowered addition plus the slot store. -/
def witProg628 : List Befehl :=
  [Befehl.movReg64 Register.rax Register.r10,
   Befehl.movImm64 Register.rcx (intWort 12),
   Befehl.addReg64 Register.rax Register.rcx,
   Befehl.store64 Register.rbx Register.rax (BitVec.ofNat 32 0)]

/-- Witness program bytes from the canonical encodings. -/
def witBytes628 : List Byte := (witProg628.map encode).flatten

/-- Witness memory: program bytes at 4096 (executable), data cell at 8192
    (readable/writable) -- the `Byteschritt` layout vocabulary reused.
    Code `[4096, 4128)` and data `[8192, 8200)` are disjoint. -/
def witMem628 : Speicher :=
  { bytes := bytesAusProg witBytes628 4096
    lesbar := ketteDaten
    schreibbar := ketteDaten
    ausfuehrbar := ketteExec }

/-- Witness start state. -/
def witStart628 : Zustand :=
  { register := witReg628
    flags := witnessFlags
    rip := BitVec.ofNat 64 4096
    speicher := witMem628 }

/-- The witness slot address: layout base 8192, offset 0. -/
def witA628 : Adresse := slotAddr 8192 0

/-- The witness target memory after the word write. -/
def witM628' : Speicher :=
  { witMem628 with bytes := writeBytes witMem628 witA628 (zahlWort witVal628) }

/-- The witness expression lowers to the three pilot instructions. -/
theorem witSenk628 :
    senkFrag witAbb628 witE628 Register.rax Register.rcx =
      some [Befehl.movReg64 Register.rax Register.r10,
        Befehl.movImm64 Register.rcx (intWort 12),
        Befehl.addReg64 Register.rax Register.rcx] := rfl

/-- The lowered assignment is the generated program plus the store. -/
theorem witSenkAssign628 :
    senkAssign witAbb628 witE628 Register.rax Register.rcx
      Register.rbx (BitVec.ofNat 32 0) = some witProg628 :=
  senkAssign_ok witAbb628 witE628 _ _ _ _ _ witSenk628

/-- Environment representation holds on the witness registers. -/
theorem witUmgebung628 :
    EnvRepr witEnv628 witStart628.register witAbb628 := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

/-- Register freshness holds: no variable lives in `rax`/`rcx`. -/
theorem witFrisch628 : Frisch witAbb628 Register.rax Register.rcx := by
  refine ⟨fun τ x => ⟨?_, ?_⟩, by decide⟩
  · show Register.r10 ≠ Register.rax
    decide
  · show Register.r10 ≠ Register.rcx
    decide

/-- Neither working register is the stack pointer. -/
theorem witHRsp628 :
    Register.rax ≠ Register.rsp ∧ Register.rcx ≠ Register.rsp :=
  ⟨by decide, by decide⟩

/-- The slot base register is neither working register. -/
theorem witHBasis628 :
    Register.rbx ≠ Register.rax ∧ Register.rbx ≠ Register.rcx :=
  ⟨by decide, by decide⟩

/-- The base register holds the admitted slot address. -/
theorem witHBaseR628 :
    witStart628.register Register.rbx = slotAddr 8192 0 := by
  decide

/-- The target address is the admitted slot address. -/
theorem witHa628 : witA628 = slotAddr 8192 0 := rfl

/-- The target word write succeeds on the witness memory. -/
theorem witHTgt628 :
    write64 witMem628 witA628 (zahlWort witVal628) = some witM628' := by
  simp only [write64, witM628']
  rw [if_pos (by decide : schreibbar8 witMem628 witA628 = true)]

/-- The witness slot is readable. -/
theorem witHRd628 : lesbar8 witMem628 witA628 = true := by
  decide

/-- Code/data separation holds on the witness layout. -/
theorem witRegionGetrennt628 :
    regionDisjunkt
      (alsRegion { tab := 0, basis := 4096, len := 32, ausr := 8 })
      (alsRegion { tab := 1, basis := 8192, len := 16, ausr := 8 }) =
      true := by
  decide

/-- FETCHED-VALUE witness: four byte steps from actual memory put the
    exact source value 42 into `rax`. -/
theorem witBytesWert628 :
    ausgangReg Register.rax (laufBytes 4 witStart628) =
      some (intWort 42) := by
  decide

/-- MEMORY-CHANGING fetched run: the fourth fetched byte step stores
    `rax` through `rbx`, observably changing the data cell from zero. -/
theorem witBytesSpeicher628 :
    ausgangByte (natAdresse 8192) (laufBytes 4 witStart628) =
      some (natByte 42) ∧
    witStart628.speicher.bytes (natAdresse 8192) = BitVec.ofNat 8 0 := by
  decide

/-- The fetched run observably changes memory (non-degenerate run). -/
theorem witLaufAendert628 :
    ∃ a : Adresse, ausgangByte a (laufBytes 4 witStart628) ≠
      some (witStart628.speicher.bytes a) := by
  refine ⟨natAdresse 8192, ?_⟩
  rw [witBytesSpeicher628.1, witBytesSpeicher628.2]
  decide

/-- Witness with the second executed opcode byte forged (137 to 0). -/
def witBytesFalsch628 : List Byte := witBytes628.set 1 (natByte 0)

def witStartFalsch628 : Zustand :=
  { witStart628 with speicher := { witMem628 with bytes := bytesAusProg witBytesFalsch628 4096 } }

/-- PLANTED FETCHED REFUSAL: forging the executed opcode byte admits no
    transition -- the changed byte governs the run. -/
theorem witByteFaelschung628 :
    ausgangRip (byteschritt witStartFalsch628) = none := by
  decide

/-- JOINT WITNESS for `senkAssign_korrekt`: every premise holds jointly
    on the witness declaration -- one table that the witness function
    writes (`witD628.schreibt`), a reached one-step source run that
    changes the slot `12 -> 42`, the generated lowered sequence with its
    fetched-byte run that changes the mapped target bytes, and code/data
    separation -- and so does the conclusion. Sums, floats, bools,
    globals and function pointers stay outside the fragment (the planted
    refusals above). -/
theorem senkAssign_korrekt_zeuge :
    ∃ (σ' : World witD628) (ρ' : Env witD628 witCtx628) (m' : Speicher)
      (s' : Zustand),
      repOk (witD628.typ () ()) 8192 16 0 = true ∧
      witD628.schreibt () () = true ∧
      (eval witSL628 witI628 witSL628 witEnv628).n = 0 ∧
      (eval witSL628 witE628 witSL628 witEnv628).n = witVal628.n ∧
      execStmt witO628 0 witR628
        (Stmt.assignSlot (l := false) () () witI628
          (cast (congrArg (Expr witD628 witCtx628 []) witHT628.symm)
            witE628) witHw628 witHL628)
        witSigma628 witEnv628 = .ok σ' ρ' ∧
      senkFrag witAbb628 witE628 Register.rax Register.rcx =
        some [Befehl.movReg64 Register.rax Register.r10,
          Befehl.movImm64 Register.rcx (intWort 12),
          Befehl.addReg64 Register.rax Register.rcx] ∧
      senkAssign witAbb628 witE628 Register.rax Register.rcx
        Register.rbx (BitVec.ofNat 32 0) = some witProg628 ∧
      EnvRepr witEnv628 witStart628.register witAbb628 ∧
      Frisch witAbb628 Register.rax Register.rcx ∧
      (Register.rax ≠ Register.rsp ∧ Register.rcx ≠ Register.rsp) ∧
      (Register.rbx ≠ Register.rax ∧ Register.rbx ≠ Register.rcx) ∧
      witStart628.register Register.rbx = slotAddr 8192 0 ∧
      witA628 = slotAddr 8192 0 ∧
      write64 witStart628.speicher witA628 (zahlWort witVal628) =
        some m' ∧
      lesbar8 witStart628.speicher witA628 = true ∧
      lauf (([Befehl.movReg64 Register.rax Register.r10,
          Befehl.movImm64 Register.rcx (intWort 12),
          Befehl.addReg64 Register.rax Register.rcx] ++
          [Befehl.store64 Register.rbx Register.rax
            (BitVec.ofNat 32 0)]).map
        fun b => (⟨b, (encode b).length⟩ : Decodiert))
        witStart628 = some s' ∧
      s'.register Register.rax = intWort 42 ∧
      s'.speicher = m' ∧
      RepSlot () 0 () 12 100 witHT628 witA628 m' σ' ∧
      (∃ w, read64 m' witA628 = some w ∧
        wortZahl 12 100 w = some witVal628) ∧
      (∃ a : Adresse, ausgangByte a (laufBytes 4 witStart628) ≠
        some (witStart628.speicher.bytes a)) ∧
      (witSigma628.slots () 0 ()).n = 12 ∧
      (σ'.slots () 0 ()).n = 42 ∧
      witStart628.speicher.bytes witA628 ≠ m'.bytes witA628 := by
  have hExecW : ∃ σ' ρ', execStmt witO628 0 witR628
      (Stmt.assignSlot (l := false) () () witI628
        (cast (congrArg (Expr witD628 witCtx628 []) witHT628.symm)
          witE628) witHw628 witHL628)
      witSigma628 witEnv628 = .ok σ' ρ' := by
    simp only [execStmt]
    exact ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hExec⟩ := hExecW
  have hMain := senkAssign_korrekt witO628 0 witR628 () () 12 100
    witHT628 8192 16 0 witOk628 witI628 witE628 witHw628 witHL628
    witSigma628 witEnv628 witSL628 rfl 0 witVal628 witHk628 witHeval628
    witAbb628 Register.rax Register.rcx Register.rbx
    (BitVec.ofNat 32 0) rfl witFrisch628 witHRsp628 witHBasis628
    witStart628 witM628' witHBaseR628 witA628 witHa628 witHTgt628
    witHRd628 _ witSenk628 witUmgebung628 σ' ρ' hExec
  obtain ⟨s2, hrunW, hvalW, hmemW, hRepW, hreadW⟩ := hMain
  have hval42 : s2.register Register.rax = intWort 42 := by
    rw [witHeval628] at hvalW
    exact hvalW
  have hBefore : (witSigma628.slots () 0 ()).n = 12 := rfl
  have h0 : witStart628.speicher.bytes witA628 = BitVec.ofNat 8 0 := by
    decide
  have h1 : witM628'.bytes witA628 = wortByte (zahlWort witVal628) 0 := by
    have h := writeBytesN_hit witMem628 witA628 (zahlWort witVal628) 8 0
      (by decide) (by decide)
    rw [addrOff_null] at h
    show writeBytes witMem628 witA628 (zahlWort witVal628) witA628 = _
    unfold writeBytes
    exact h
  have hBytes : witStart628.speicher.bytes witA628 ≠
      witM628'.bytes witA628 := by
    rw [h0, h1]
    decide
  refine ⟨σ', ρ', witM628', s2, witOk628, rfl, witHk628, witHeval628,
    hExec, witSenk628, witSenkAssign628, witUmgebung628, witFrisch628,
    witHRsp628, witHBasis628, witHBaseR628, witHa628, witHTgt628,
    witHRd628, hrunW, hval42, hmemW, hRepW, hreadW, witLaufAendert628,
    hBefore, ?hAfter, hBytes⟩
  case hAfter =>
    cases hExec
    rfl

/- CUTS:
     - Proved: value bridge, lowering shape, transport helpers,
       unsupported-expression/nesting refusals, negative-range and
       code-alias region refusals, the statement-level correspondence
       `senkAssign_korrekt` (source `assignSlot` through `execStmt`
       agrees with generated `lauf` plus `RepSlot` read-back), and the
       joint non-degenerate witness `senkAssign_korrekt_zeuge` (one
       table its function writes; source slot `12 -> 42` and mapped
       target bytes both change; fetched-byte run with value and
       memory observations; forged-opcode fetched refusal).
     - Multi-step fetched-byte induction (`laufBytes` agreement for an
       ARBITRARY generated sequence) OPEN; single steps agree by
       `kanonisch_schritt_ueberein`, the concrete generated bytes agree
       by `decide` (`witBytesWert628`, `witBytesSpeicher628`).
     - Pilot integer fragment only: value must lower via `senkFrag`
       (lit/var/one add/sub over atoms); sums, FP, locks, calls, loops,
       globals, pointers and non-zero displacements outside.
     - No TSO/concurrency claim; no validator soundness; no hardware
       claim. Full source-to-final-loaded-bytes remains OPEN.
-/

#print axioms senkAssign
#print axioms intWort_zahlWort
#print axioms senkAssign_ok
#print axioms senkAssign_verweigert_mul
#print axioms senkAssign_verweigert_tief
#print axioms assignRepOk_negativ_verweigert
#print axioms assignCodeAlias_verweigert
#print axioms evalTrans
#print axioms paarCancel
#print axioms senkAssign_korrekt
#print axioms witSenkAssign628
#print axioms witRegionGetrennt628
#print axioms witBytesWert628
#print axioms witBytesSpeicher628
#print axioms witByteFaelschung628
#print axioms senkAssign_korrekt_zeuge

end Gabbro.Grammatik.X86
