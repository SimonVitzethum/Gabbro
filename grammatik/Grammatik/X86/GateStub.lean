/-
  Caller-side gate-stub checks (lane 346, C2).

  Decided declaration checks mirroring the source gate shape N063-N066 plus
  the total `errors` map (N067), Linux caller clobbers (rcx/r11), and
  caller-stub byte-shape obligations with C186/C187/M140 as refusal
  predicates. Callee-side contract (obligation (c)) stays OPEN; the
  declaration alone admits nothing.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Codec

namespace Gabbro.Grammatik.X86

/-- Gate kind: ordinary value, region answer, or stack (clone) gate. -/
inductive TorArt where
  | normal
  | region
  | stapel
  deriving DecidableEq, Repr

/-- Caller-side gate declaration over canonical registers. -/
structure TorDekl where
  nummer : Nat
  ein : List (Register × Nat)
  aus : Register
  clobber : List Register
  errors : List (Nat × Nat)
  gruende : Nat
  hatOr : Bool
  art : TorArt
  paramAnzahl : Nat
  deriving DecidableEq, Repr

/-! ## 1. Decided declaration checks (N063-N066 + N067 + Linux clobbers). -/

/-- N063: in-registers pairwise distinct. -/
def regsDistinctB (t : TorDekl) : Bool :=
  decide ((t.ein.map Prod.fst).Nodup)

/-- All indices `0 .. n-1` occur in the bound list. -/
def alleGebundenB : Nat → List Nat → Bool
  | 0, _ => true
  | n + 1, xs => (xs.contains n) && alleGebundenB n xs

/-- N065 + arity: every parameter bound exactly once. -/
def paramsAbgedecktB (t : TorDekl) : Bool :=
  decide (t.ein.length = t.paramAnzahl) &&
  decide ((t.ein.map Prod.snd).Nodup) &&
  alleGebundenB t.paramAnzahl (t.ein.map Prod.snd)

/-- N064: out-register never clobbered. -/
def ausNichtClobberB (t : TorDekl) : Bool :=
  !decide (t.aus ∈ t.clobber)

/-- Linux caller clobbers: rcx and r11 destroyed by `syscall`. -/
def linuxClobberB (t : TorDekl) : Bool :=
  decide (Register.rcx ∈ t.clobber) && decide (Register.r11 ∈ t.clobber)

/-- N067: `errors` keys distinct, every target a declared reason case. -/
def fehlerOkB (t : TorDekl) : Bool :=
  decide (((t.errors.map Prod.fst).Nodup)) &&
  t.errors.all (fun p => decide (p.2 < t.gruende)) &&
  (decide (t.errors = []) || t.hatOr)

/-- Full caller-side admission: every decided check at once. -/
def torOkB (t : TorDekl) : Bool :=
  regsDistinctB t && paramsAbgedecktB t && ausNichtClobberB t &&
  linuxClobberB t && fehlerOkB t

/-! ## 2. Witness gate: distinct registers, decoded errno channel. -/

/-- Witness: `write`-shaped gate, number 1, three params, total errors map. -/
def schreibTor : TorDekl :=
  { nummer := 1
    ein := [(Register.rdi, 0), (Register.rsi, 1), (Register.rdx, 2)]
    aus := Register.rax
    clobber := [Register.rcx, Register.r11]
    errors := [(9, 0), (4, 1), (11, 2)]
    gruende := 3
    hatOr := true
    art := .normal
    paramAnzahl := 3 }

/-- The witness gate is admitted by every decided check. -/
theorem schreibTor_ok : torOkB schreibTor = true := by
  decide

/-! ## 3. Refusal predicates: C186 / C187 / M140. -/

/-- C186: a region answer without its `or R` channel is refused. -/
def c186VerweigertB (t : TorDekl) : Bool :=
  decide (t.art = .region) && !t.hatOr

/-- Trampoline pool exactly as the emitter pins it (`emit.rs::syscall_stumpf`:
    `["r12", "r13", "r14", "r15", "rbx"]`): `rbp` is never pinned (frame
    pointer), and the pool never meets the fixed-destroyed set (`rcx`,
    `r11`, `memory`), so only the gate's own bindings occupy it. -/
def trampolinVorrat : List Register :=
  [Register.r12, Register.r13, Register.r14, Register.r15, Register.rbx]

/-- Free trampoline registers: the pool minus everything the gate occupies
    (in-registers, the answer register, clobbers), mirroring the emitter's
    `belegt = regs_in + regs_out + clobbers + fest_zerstoert`. -/
def freieTrampolin (t : TorDekl) : List Register :=
  trampolinVorrat.filter (fun r =>
    !decide (r ∈ t.ein.map Prod.fst) && decide (r ≠ t.aus) &&
    !decide (r ∈ t.clobber))

/-- C187: a stack gate with fewer than two free trampoline registers
    has no trampoline and is refused. -/
def c187VerweigertB (t : TorDekl) : Bool :=
  decide (t.art = .stapel) && decide ((freieTrampolin t).length < 2)

/-- M140 site mirror: a stub operand as a tagged value. A `zahl` carries a
    bare word; a `zeiger` carries base and extent (never a bare word cast).
    The tag assignment itself is the checker's business (`m1.rs`); this
    mirror only decides the refusal shape once tags are given. -/
inductive StubenWert where
  | zahl (w : Wort)
  | zeiger (basis len : Nat)
  deriving DecidableEq, Repr

/-- M140: a call-site operand list `(parameter index, tagged value)` against
    the indices that expect a pointer. A number where a pointer is expected
    is forged and refused at that site. -/
def m140VerweigertB (wartetZeiger : List Nat)
    (werte : List (Nat × StubenWert)) : Bool :=
  werte.any (fun p => match p.2 with
    | .zahl _ => decide (p.1 ∈ wartetZeiger)
    | .zeiger _ _ => false)

/-! ## 4. Concrete refusals: each check fails on its own shape. -/

/-- N063 refusal: duplicate in-register. -/
def torDoppelt : TorDekl :=
  { schreibTor with ein := [(Register.rdi, 0), (Register.rdi, 1)] }

/-- A duplicate in-register is refused. -/
theorem torDoppelt_verweigert : regsDistinctB torDoppelt = false := by
  decide

/-- N064 refusal: out-register clobbered. -/
def torAusClobber : TorDekl :=
  { schreibTor with clobber := [Register.rax, Register.rcx, Register.r11] }

/-- A clobbered out-register is refused. -/
theorem torAusClobber_verweigert :
    ausNichtClobberB torAusClobber = false := by
  decide

/-- N065 refusal: parameter 1 never bound. -/
def torUngebunden : TorDekl :=
  { schreibTor with ein := [(Register.rdi, 0), (Register.rsi, 2)] }

/-- An unbound parameter is refused. -/
theorem torUngebunden_verweigert :
    paramsAbgedecktB torUngebunden = false := by
  decide

/-- Linux clobber refusal: r11 missing. -/
def torOhneR11 : TorDekl :=
  { schreibTor with clobber := [Register.rcx] }

/-- A gate that keeps r11 is refused on the Linux path. -/
theorem torOhneR11_verweigert : linuxClobberB torOhneR11 = false := by
  decide

/-- N067 refusal: errno listed twice. -/
def torDoppelErrno : TorDekl :=
  { schreibTor with errors := [(9, 0), (9, 1)] }

/-- A doubled errno is refused. -/
theorem torDoppelErrno_verweigert :
    fehlerOkB torDoppelErrno = false := by
  decide

/-- N067 refusal: reason target outside the declared channel. -/
def torFremdGrund : TorDekl :=
  { schreibTor with errors := [(9, 7)] }

/-- An undeclared reason target is refused. -/
theorem torFremdGrund_verweigert :
    fehlerOkB torFremdGrund = false := by
  decide

/-- C186 refusal: region answer without `or R`. -/
def torRegionOhneOr : TorDekl :=
  { schreibTor with art := .region, hatOr := false }

/-- A region answer without its channel is refused. -/
theorem torRegionOhneOr_verweigert :
    c186VerweigertB torRegionOhneOr = true := by
  decide

/-- The witness (non-region, channel present) is not a C186 refusal. -/
theorem schreibTor_kein_c186 : c186VerweigertB schreibTor = false := by
  decide

/-- C187 refusal: stack gate whose clobbers eat the trampoline pool. -/
def torStapelOhneTrampolin : TorDekl :=
  { nummer := 1
    ein := [(Register.rdi, 0), (Register.rsi, 1), (Register.rdx, 2)]
    aus := Register.rax
    clobber := [Register.rcx, Register.r11, Register.rbx,
      Register.r12, Register.r13, Register.r14, Register.r15]
    errors := [(9, 0), (4, 1), (11, 2)]
    gruende := 3
    hatOr := true
    art := TorArt.stapel
    paramAnzahl := 3 }

/-- A stack gate without two free trampoline registers is refused. -/
theorem torStapelOhneTrampolin_verweigert :
    c187VerweigertB torStapelOhneTrampolin = true := by
  decide

/-- C187 divergence witness: the answer register occupies the pool.
    With `aus = rbx` and `r12`-`r15` clobbered, only `rbx` looks free --
    but the answer register is occupied (`belegt` holds `regs_out`), so no
    two trampoline registers remain. The pre-fix model cleared this gate. -/
def torStapelAntwortBelegt : TorDekl :=
  { nummer := 1
    ein := [(Register.rdi, 0), (Register.rsi, 1), (Register.rdx, 2)]
    aus := Register.rbx
    clobber := [Register.rcx, Register.r11,
      Register.r12, Register.r13, Register.r14, Register.r15]
    errors := [(9, 0), (4, 1), (11, 2)]
    gruende := 3
    hatOr := true
    art := TorArt.stapel
    paramAnzahl := 3 }

/-- An answer register inside the pool counts as occupied: refused. -/
theorem torStapelAntwortBelegt_verweigert :
    c187VerweigertB torStapelAntwortBelegt = true := by
  decide

/-- The witness stack shape with free registers is not a C187 refusal. -/
def torStapelZeuge : TorDekl :=
  { schreibTor with art := TorArt.stapel }

/-- The witness stack shape with free registers is not a C187 refusal. -/
theorem schreibTor_stapel_kein_c187 :
    c187VerweigertB torStapelZeuge = false := by
  decide

/-- M140 refusal: buffer parameter 1 handed a bare number is forged. -/
theorem m140_geschmiedet :
    m140VerweigertB [1] [(0, .zahl 5), (1, .zahl 7)] = true := by
  decide

/-- M140 negative: a genuine pointer with its extent is not forged. -/
theorem m140_echt_kein_fund :
    m140VerweigertB [1] [(0, .zahl 5), (1, .zeiger 0x2000 8)] = false := by
  decide

/-- M140 negative: a number where no pointer is expected is not forged. -/
theorem m140_zahl_erlaubt :
    m140VerweigertB [] [(0, .zahl 5)] = false := by
  decide

/-! ## 5. Caller-stub byte-shape obligations. -/

/-- The `syscall` trap bytes (`0F 05`): checked literally, never decoded
    through the pilot decoder (the trap has no `Befehl` form there). -/
def trapBytes : List Byte := [natByte 15, natByte 5]

/-- Pinned trap bytes. -/
theorem trapBytes_pin : trapBytes = [natByte 15, natByte 5] := rfl

/-- The stub ends in the trap: the last two bytes are `0F 05`. -/
def stubEndsTrapB (stub : List Byte) : Bool :=
  decide (stub.drop (stub.length - 2) = trapBytes)

/-- Every bound parameter is established by a 64-bit move into its
    declared in-register (register or immediate form). -/
def bindungErstelltB (t : TorDekl) (moves : List Befehl) : Bool :=
  t.ein.all (fun p => moves.any (fun b => match b with
    | .movReg64 dst _ => decide (dst = p.1)
    | .movImm64 dst _ => decide (dst = p.1)
    | _ => false))

/-- Witness moves: each declared in-register set from a scratch source. -/
def zeugenMoves : List Befehl :=
  [.movReg64 Register.rdi Register.r8, .movReg64 Register.rsi Register.r9,
   .movReg64 Register.rdx Register.r10]

/-- The witness moves establish every bound parameter. -/
theorem zeugenMoves_ok :
    bindungErstelltB schreibTor zeugenMoves = true := by
  decide

/-- The witness stub bytes: canonical mov encodings then the trap. -/
def zeugenStub : List Byte :=
  zeugenMoves.flatMap encode ++ trapBytes

/-- The witness stub ends in the trap. -/
theorem zeugenStub_trap : stubEndsTrapB zeugenStub = true := by
  decide

/-- The first stub move decodes back through the canonical decoder,
    leaving exactly the trap bytes. -/
theorem zeugenStub_prefix_dekodiert :
    decode (encode (.movReg64 Register.rdi Register.r8) ++ trapBytes) =
      some (⟨.movReg64 Register.rdi Register.r8,
        (encode (.movReg64 Register.rdi Register.r8)).length⟩,
        trapBytes) :=
  roundtrip_movReg64 Register.rdi Register.r8 trapBytes

/-! ## 6. Errno-channel decode: the `-4095` fence over the declared table. -/

/-- Decoded class of a raw `rax` answer: value, table reason, or the
    named hardware outcome (unlisted errno, out-of-range value). -/
inductive RohKlasse where
  | ok
  | grund (errno : Nat)
  | hardware
  deriving DecidableEq, Repr

/-- Caller-side decode of the raw answer: a negative `-4095 .. -1`
    against the `errors` map into its reason, an unlisted errno or an
    out-of-range non-negative value into the hardware outcome.
    The kernel-side meaning of the table is user logic and OPEN. -/
def torKlassifiziere (tab : List (Nat × Nat)) (lo hi roh : Int) : RohKlasse :=
  if roh < 0 then
    if _ : 1 ≤ -roh ∧ -roh ≤ 4095 then
      match tab.find? (fun p => decide (p.1 = (-roh).toNat)) with
      | some (_, g) => .grund g
      | none => .hardware
    else .hardware
  else if lo ≤ roh ∧ roh ≤ hi then .ok
  else .hardware

/-- EBADF decodes through the witness table to reason 0. -/
theorem torKlassifiziere_ebadf :
    torKlassifiziere schreibTor.errors 0 8192 (-9) = .grund 0 := by
  decide

/-- An in-range value decodes to `ok`. -/
theorem torKlassifiziere_ok :
    torKlassifiziere schreibTor.errors 0 8192 5 = .ok := by
  decide

/-- An unlisted errno decodes to the hardware outcome, never a reason. -/
theorem torKlassifiziere_unbekannt :
    torKlassifiziere schreibTor.errors 0 8192 (-22) = .hardware := by
  decide

/-- An out-of-range non-negative value decodes to the hardware outcome. -/
theorem torKlassifiziere_ausserhalb :
    torKlassifiziere schreibTor.errors 0 8192 99999 = .hardware := by
  decide

/-- Past the `-4095` fence no errno is read: raw `-5000` is hardware. -/
theorem torKlassifiziere_zaun :
    torKlassifiziere schreibTor.errors 0 8192 (-5000) = .hardware := by
  decide

/-! ## 7. Joint witness: admitted gate, stub shape, decode, memory change. -/

/-- JOINT WITNESS: the witness gate is admitted, its moves establish the
    register map, its stub ends in the trap, EBADF decodes to reason 0,
    and a real eight-byte write reads back with an observable change
    (reuses the canonical `write_read_zeuge` memory witness). -/
theorem torStub_zeuge :
    torOkB schreibTor = true ∧
    bindungErstelltB schreibTor zeugenMoves = true ∧
    stubEndsTrapB zeugenStub = true ∧
    torKlassifiziere schreibTor.errors 0 8192 (-9) = .grund 0 ∧
    (∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a) := by
  refine ⟨schreibTor_ok, zeugenMoves_ok, zeugenStub_trap,
    torKlassifiziere_ebadf, write_read_zeuge⟩

/- CUTS:
   - Caller side only (IMAGE-ABI section 7 caller half): decided
     declaration checks (N063 distinct in-registers, N065/arity exact
     parameter binding, N064 out-register unclobbered, N066 is implicit
     -- `TorDekl` names only canonical `Register`, so an unknown
     register is unrepresentable, not merely refused), the total
     `errors` map (N067: distinct errnos, every target a declared
     reason case, channel present where the map is nonempty), the Linux
     caller clobbers rcx/r11, the mov-establishment plus `0F 05`-suffix
     stub shape, and the `-4095`-fence errno decode. The bare-metal
     `int $0x80` ABI (which destroys nothing but memory) is NOT covered
     by `linuxClobberB`; a bare-metal gate needs its own clobber rule.
   - C186/C187/M140 are validator/profile admission Bools, not hardware
     faults: `c186VerweigertB` (region answer without `or R`),
     `c187VerweigertB` (stack gate with fewer than two free trampoline
     registers from the emitter-exact pool `r12`-`r15`/`rbx` has no
     trampoline; occupancy is in-registers plus the answer register plus
     clobbers, mirroring the emitter's `belegt`; `rbp` is never pinned),
     `m140VerweigertB` (a number at a site index that expects a pointer
     is forged).
   - M140 detection itself stays OPEN: `StubenWert` tags are given, not
     computed -- which site expects a pointer and which value is a number
     is the checker's type business (`m1.rs`), never derived here. The
     mirror decides only the refusal shape over tagged sites.
   - No trap semantics: the `syscall` instruction is checked literally
     (`0F 05` suffix) and never decoded or stepped -- the pilot
     `Befehl` has no trap form and `schritt` is never duplicated here.
     What the kernel does is user logic (obligation (c)), never a
     hardware axiom; the declaration alone admits nothing.
   - No callee-side contract: obligation (c) (binding/kernel logic at
     actual arguments/results/effects) stays OPEN; a gate name, an
     `assume` item, or any named premise alone discharges nothing.
   - No source correspondence beyond the shape mirror: nothing here
     claims the checked numbers, tables, or costs are the kernel's, or
     that any source `syscall` declaration lowers to these bytes.
   - Scalar fallback on refusal is a consumer obligation, not proved
     here: a refused optional fast form must keep a certified scalar
     path where the profile demands one.
-/

#print axioms schreibTor_ok
#print axioms torDoppelt_verweigert
#print axioms torAusClobber_verweigert
#print axioms torUngebunden_verweigert
#print axioms torOhneR11_verweigert
#print axioms torDoppelErrno_verweigert
#print axioms torFremdGrund_verweigert
#print axioms torRegionOhneOr_verweigert
#print axioms schreibTor_kein_c186
#print axioms torStapelOhneTrampolin_verweigert
#print axioms torStapelAntwortBelegt_verweigert
#print axioms schreibTor_stapel_kein_c187
#print axioms m140_geschmiedet
#print axioms m140_echt_kein_fund
#print axioms m140_zahl_erlaubt
#print axioms zeugenMoves_ok
#print axioms zeugenStub_trap
#print axioms zeugenStub_prefix_dekodiert
#print axioms torKlassifiziere_ebadf
#print axioms torKlassifiziere_ok
#print axioms torKlassifiziere_unbekannt
#print axioms torKlassifiziere_ausserhalb
#print axioms torKlassifiziere_zaun
#print axioms torStub_zeuge

end Gabbro.Grammatik.X86
