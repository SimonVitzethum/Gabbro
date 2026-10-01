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
/- CUTS:
     - Proved: value bridge, lowering shape, transport helpers,
       unsupported-expression/nesting refusals, negative-range and
       code-alias region refusals, and the statement-level
       correspondence `senkAssign_korrekt` (source `assignSlot` through
       `execStmt` agrees with generated `lauf` plus `RepSlot` read-back).
     - Joint non-degenerate `_zeuge` witness OPEN (next increment).
     - Multi-step fetched-byte induction (`laufBytes` agreement for the
       whole generated sequence) OPEN; single steps agree by
       `kanonisch_schritt_ueberein`, concrete fetched witnesses by
       `decide` (next increment).
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

end Gabbro.Grammatik.X86
