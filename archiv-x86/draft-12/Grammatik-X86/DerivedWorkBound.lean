/-
  File:      Grammatik/X86/DerivedWorkBound.lean
  Subject:   Derived target work bound for direct source lowering (lane 654).

  Closes the missing `Deckung` producer of `BudgetExecution` for the
  covered source fragment: machine instruction count/work and the admitted
  cost summary are DERIVED from the actual generated expression/assignment
  code (`ExpressionLowering.senkFrag`, `SourceAssignmentLowering.senkAssign`),
  never assumed as `Deckung`/`hWork` premises and never a second cost
  interpreter (`targetWork` is reused untouched). Named per-form hardware
  timing (`HardwareAssumptions.laufKosten`) composes with the derived bound
  (`TimeTransfer.zeitTransfer`); source steps, retired instructions and
  named target time stay three separate counts. Optimiser changes must
  recompute `targetWork` over the new list (one `foldAddLit` connection);
  budget/depth stops stay loud; CAS progress, fairness and zero-cost
  stutter are never promised.
-/
import Grammatik.X86.SourceAssignmentLowering
import Grammatik.X86.CostSummary
import Grammatik.X86.BudgetExecution
import Grammatik.X86.HardwareAssumptions
import Grammatik.X86.TimeTransfer
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Canonical decoding of generated code: each generated `Befehl` with its
    canonical encoding length -- the same map the lowering correctness
    theorems run through `lauf`. No new interpreter. -/
def decodiertZu (prog : List Befehl) : List Decodiert :=
  prog.map fun b => ⟨b, (encode b).length⟩

/-- Decoding preserves the instruction behind each entry: mapping back
    over `befehl` is the identity on the generated list. -/
theorem decodiertZu_befehl (prog : List Befehl) :
    (decodiertZu prog).map (fun d => d.befehl) = prog := by
  induction prog with
  | nil => rfl
  | cons b rest ih =>
    show ((⟨b, (encode b).length⟩ : Decodiert) :: decodiertZu rest).map
      (fun d => d.befehl) = b :: rest
    simp only [List.map_cons]
    rw [ih]

/-- WORK BRIDGE: `targetWork` over canonically decoded generated code is
    the generated instruction count -- the one `targetWork`, reused. -/
theorem arbeit_decodiert (prog : List Befehl) :
    targetWork ((decodiertZu prog).map (fun d => d.befehl)) = prog.length := by
  rw [decodiertZu_befehl]
  rfl

/-- GENERATED WORK (atom): every successful atom lowering emits exactly
    one instruction -- derived by classifying the atom, never stipulated.
    Both the equation and the classification are used. -/
theorem senkAtom_laenge {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ τ) (dst : Register)
    (pa : List Befehl) (ha : senkAtom abb a dst = some pa) :
    pa.length = 1 := by
  match hI : istAtom_von_senkAtom abb a dst pa ha with
  | .lit n =>
    simp only [senkAtom] at ha
    have hpa : pa = [Befehl.movImm64 dst (intWort n)] :=
      Option.some_inj.mp ha.symm
    rw [hpa]
    rfl
  | .var x =>
    simp only [senkAtom] at ha
    have hpa : pa = [Befehl.movReg64 dst (abb _ x)] :=
      Option.some_inj.mp ha.symm
    rw [hpa]
    rfl

/-- GENERATED WORK (fragment): every successful fragment lowering emits
    one instruction (literal/variable) or three (one bounded add/sub over
    two atoms) -- derived from the classification plus the atom count.
    Both the lowering equation and the atom equations are used. -/
theorem senkFrag_laenge {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp : Register)
    (prog : List Befehl) (h : senkFrag abb e dst tmp = some prog) :
    prog.length = 1 ∨ prog.length = 3 := by
  match hI : istFrag_von_senkFrag abb e dst tmp prog h with
  | .lit n => exact Or.inl rfl
  | .var x => exact Or.inl rfl
  | .add a b pa pb ha hb =>
    have hpa := senkAtom_laenge abb a dst pa ha
    have hpb := senkAtom_laenge abb b tmp pb hb
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | .sub a b pa pb ha hb =>
    have hpa := senkAtom_laenge abb a dst pa ha
    have hpb := senkAtom_laenge abb b tmp pb hb
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- GENERATED WORK (assignment): the lowered assignment is the fragment
    plus one slot store -- hence two or four instructions. Both the
    assignment shape and the fragment count are used. -/
theorem senkAssign_laenge {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp baseR : Register) (disp : BitVec 32)
    (prog : List Befehl) (hsenk : senkFrag abb e dst tmp = some prog)
    (code : List Befehl)
    (hcode : senkAssign abb e dst tmp baseR disp = some code) :
    code.length = 2 ∨ code.length = 4 := by
  have hshape := senkAssign_ok abb e dst tmp baseR disp prog hsenk
  rw [hshape] at hcode
  have hcode' : code = prog ++ [Befehl.store64 baseR dst disp] :=
    Option.some_inj.mp hcode.symm
  rw [hcode', List.length_append]
  have h1 : [Befehl.store64 baseR dst disp].length = 1 := rfl
  have hlen := senkFrag_laenge abb e dst tmp prog hsenk
  omega

/-! ## Admitted summary derived from the generated code.

    The fragment emits at most 4 instructions per lowered assignment
    (proved above), so the uniform per-class maximum 4 with no spill,
    no fence, a proved retry bound and no waiting exclusion is admitted
    by the `kostenSummeOk` Bool -- checked, never stipulated. -/

/-- The fragment summary: uniform maximum 4 (the longest generated
    assignment: three fragment instructions plus the slot store), honest
    zero spill/fence counts, a proved retry bound, no exclusions. -/
def fragmentSummary : CostSummary where
  expand := fun _ => some 4
  spillCount := 0
  fenceCount := 0
  retryBound := some 0
  exclusions := []

/-- The fragment summary is admitted by the validator Bool. -/
theorem fragmentSummary_ok : kostenSummeOk fragmentSummary = true := by
  decide

/-- The fragment summary has uniform maximum 4. -/
theorem fragmentSummary_max : alleMax fragmentSummary = some 4 := by
  decide

/-- The fragment summary bounds work over any source budget `src` by
    `src * 4`: the expansion formula with honest zero spill/fence. -/
theorem fragmentSummary_expand (src : Nat) :
    expandBound fragmentSummary src = some (src * 4) := by
  have h := expandBound_keinVerlust fragmentSummary src 4 fragmentSummary_max
  simpa [fragmentSummary] using h

/-- DECKUNG PRODUCER (the missing leg): every generated assignment of the
    covered fragment is covered in machine work by the admitted fragment
    summary over any positive source budget. `Deckung` is DERIVED from the
    fragment admission equation plus the generated length bound -- it is
    never a premise. Both premises are used: `hsenk` bounds the generated
    length, `hsrc` keeps the scaled bound above it. -/
theorem deckung_fragment {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp baseR : Register) (disp : BitVec 32)
    (src : Nat)
    (prog : List Befehl) (hsenk : senkFrag abb e dst tmp = some prog)
    (hsrc : 1 ≤ src) :
    Deckung fragmentSummary src
      (decodiertZu (prog ++ [Befehl.store64 baseR dst disp])) := by
  have hlen := senkFrag_laenge abb e dst tmp prog hsenk
  intro k hk
  rw [fragmentSummary_expand] at hk
  cases hk
  have hwork : targetWork
      ((decodiertZu (prog ++ [Befehl.store64 baseR dst disp])).map
        fun d => d.befehl) =
      prog.length + 1 := by
    rw [arbeit_decodiert]
    simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-! ## Time composition with derived work.

    The named per-form hardware bound over the executed generated prefix
    plus the DERIVED summary coverage give target-time coverage. No
    `Deckung`/`hWork` premise: the work side comes from `deckung_fragment`.
    Units stay separate: `src` counts source steps (the `Budget` ops side),
    `targetWork` counts retired generated instructions (the formula above),
    `t` counts named target time (the `laufKosten` sum). All four premises
    are used: `hsenk`/`hsrc` feed the derived coverage, `hCost`/`hb` feed
    the hardware aggregation. -/

/-- MAIN: a lowered assignment of the covered fragment whose generated
    code aggregates to named time `t` under profile `p` is covered in
    target time by the admitted fragment summary over the source budget. -/
theorem senkAssign_zeit_schranke {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp baseR : Register) (disp : BitVec 32)
    (p : HardwareProfil) (src B t : Nat)
    (prog : List Befehl) (hsenk : senkFrag abb e dst tmp = some prog)
    (hsrc : 1 ≤ src)
    (hCost : laufKosten p
      (decodiertZu (prog ++ [Befehl.store64 baseR dst disp])) = some t)
    (hb : ∀ d ∈ decodiertZu (prog ++ [Befehl.store64 baseR dst disp]),
      ∃ c, schrittKosten p d = some c ∧ c ≤ B) :
    ∀ k, expandBound fragmentSummary src = some k → t ≤ B * k := by
  have hDeck := deckung_fragment abb e dst tmp baseR disp src prog hsenk hsrc
  exact budgetAusfuehrung_transfer fragmentSummary p _ src B t hCost hb hDeck

/-- UNIT PINNING (generic): the three counts in the main theorem are three
    separate numbers with three separate counters -- source steps `src`
    feed the summary expansion, retired instructions feed `targetWork`,
    named per-form costs feed `laufKosten`. Restating the roles from the
    definitions: the expansion scales `src`, the work counts the decoded
    generated list, the time sums the profile costs. -/
theorem einheiten_getrennt {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp baseR : Register) (disp : BitVec 32)
    (src : Nat)
    (prog : List Befehl) (hsenk : senkFrag abb e dst tmp = some prog) :
    expandBound fragmentSummary src = some (src * 4) ∧
    targetWork ((decodiertZu (prog ++ [Befehl.store64 baseR dst disp])).map
      fun d => d.befehl) = prog.length + 1 ∧
    (prog.length = 1 ∨ prog.length = 3) := by
  refine ⟨fragmentSummary_expand src, ?_, senkFrag_laenge abb e dst tmp prog hsenk⟩
  rw [arbeit_decodiert]
  simp only [List.length_append, List.length_cons, List.length_nil]

/-! ## Optimiser recomputation.

    The one applicable generic optimisation connection: constant folding
    (`InvariantenOpt.foldAddLit`, value-preserving by
    `InvariantenOpt.eval_foldAddLit`)
    changes the generated instruction count (three before, one after) for
    the SAME source value. An optimisation that folds (or removes, or
    strength-reduces) MUST recompute `targetWork` over the new generated
    list -- inheriting the old count overcounts the folded code. Every
    premise is used: `abb`/`dst`/`tmp` pin both lowerings, `a`/`b` the
    folded literals, the worlds the shared value. -/

/-- FOLD RECOMPUTATION: folding `lit a + lit b` keeps the source value
    (`eval_foldAddLit`) but shrinks generated work 3 → 1. -/
theorem arbeit_nach_faltung {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a b : Int) (dst tmp : Register)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    ∃ (vor nach : List Befehl),
      senkFrag abb
        (Expr.add (Expr.lit (Γ := Γ) (Λ := Λ) a)
          (Expr.lit (Γ := Γ) (Λ := Λ) b)) dst tmp = some vor ∧
      senkFrag abb
        (InvariantenOpt.foldAddLit (D := D) (Γ := Γ) (Λ := Λ) a b)
        dst tmp = some nach ∧
      eval σ₀
        (Expr.add (Expr.lit (Γ := Γ) (Λ := Λ) a)
          (Expr.lit (Γ := Γ) (Λ := Λ) b)) σ ρ =
        eval σ₀
          (InvariantenOpt.foldAddLit (D := D) (Γ := Γ) (Λ := Λ) a b)
          σ ρ ∧
      vor.length = 3 ∧ nach.length = 1 ∧ vor.length ≠ nach.length := by
  refine ⟨[Befehl.movImm64 dst (intWort a),
      Befehl.movImm64 tmp (intWort b), Befehl.addReg64 dst tmp],
    [Befehl.movImm64 dst (intWort (a + b))], rfl, rfl,
    (InvariantenOpt.eval_foldAddLit (D := D) (Γ := Γ) (Λ := Λ) a b σ₀ σ ρ).symm,
    rfl, rfl, by simp⟩

/-! ## Loud stops preserved, no hidden stutter.

    Source budget exhaustion (`foreverLauf` at zero passes, `rufAt` at
    zero depth, `runOps` past the bound) stays loud by the actual model
    equations reused in the joint witness below; the transfer bounds only
    successful aggregations. Here: a successful transfer instance names a
    cost for every generated step (no executed step hides) AND meets the
    derived time bound -- both from the same premises. -/

/-- NO HIDDEN STUTTER plus derived bound: transfer success prices every
    generated step and respects the summary time bound. -/
theorem arbeit_ohne_versteck {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp baseR : Register) (disp : BitVec 32)
    (p : HardwareProfil) (src B t : Nat)
    (prog : List Befehl) (hsenk : senkFrag abb e dst tmp = some prog)
    (hsrc : 1 ≤ src)
    (hCost : laufKosten p
      (decodiertZu (prog ++ [Befehl.store64 baseR dst disp])) = some t)
    (hb : ∀ d ∈ decodiertZu (prog ++ [Befehl.store64 baseR dst disp]),
      ∃ c, schrittKosten p d = some c ∧ c ≤ B) :
    (∀ d ∈ decodiertZu (prog ++ [Befehl.store64 baseR dst disp]),
      ∃ c, schrittKosten p d = some c) ∧
    ∀ k, expandBound fragmentSummary src = some k → t ≤ B * k := by
  refine ⟨zeitTransfer_kosten_benannt p _ t hCost,
    senkAssign_zeit_schranke abb e dst tmp baseR disp p src B t prog
      hsenk hsrc hCost hb⟩

/-! ## Refusals: underestimated work, unsupported form, unbounded retry. -/

/-- UNDERESTIMATED-WORK REFUSAL: no admitted assignment is covered by a
    bound below 2 -- the shortest generated assignment is two
    instructions. Every premise is used: `hsenk`/`hcode` give the length
    formula, `hk` the failed claim. -/
theorem arbeit_knapp_verweigert {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp baseR : Register) (disp : BitVec 32)
    (prog code : List Befehl)
    (hsenk : senkFrag abb e dst tmp = some prog)
    (hcode : senkAssign abb e dst tmp baseR disp = some code)
    (k : Nat) (hk : k < 2) :
    ¬ targetWork ((decodiertZu code).map fun d => d.befehl) ≤ k := by
  have hlen := senkAssign_laenge abb e dst tmp baseR disp prog hsenk code hcode
  rw [arbeit_decodiert]
  omega

/-- UNSUPPORTED-FORM REFUSAL: multiplication is outside the fragment, so
    no assignment sequence -- and hence no work bound -- exists for it. -/
theorem keine_arbeit_ohne_fragment {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp baseR : Register) (disp : BitVec 32) :
    ¬ ∃ code, senkAssign abb
      (Expr.mul (Expr.lit (Γ := Γ) (Λ := Λ) 2)
        (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst tmp baseR disp = some code := by
  rw [senkAssign_verweigert_mul]
  simp

/-- UNBOUNDED-RETRY REFUSAL: the fragment summary with its retry bound
    removed refuses admission AND transfer together -- a CAS retry loop
    never gets a free constant. -/
theorem kein_freier_versuch_fragment (p : HardwareProfil) :
    kostenSummeOk { fragmentSummary with retryBound := none } = false ∧
    zeitTransferZulaessig { fragmentSummary with retryBound := none } p =
      false :=
  kein_freier_versuch _ p 4 rfl rfl

/-! ## Joint witnesses: one table, one writing function, real runs.

    All witnesses below share one non-degenerate package: the `witD628`
    declaration (one table its contract writes), the source run that moves
    the slot `12 -> 42`, and the fetched-byte target run that observably
    changes memory. Planted negative mutations (forged opcode byte,
    negative range, overlapping code region) live in the reused witness
    modules. -/

/-- The witness per-step hardware bound: every generated witness step
    costs at most 3 under the witness profile. -/
theorem hb_wit :
    ∀ d ∈ decodiertZu witProg628,
      ∃ c, schrittKosten profilZeuge d = some c ∧ c ≤ 3 := by
  have hlist : decodiertZu witProg628 =
      [{ befehl := Befehl.movReg64 Register.rax Register.r10,
         laenge := (encode (Befehl.movReg64 Register.rax Register.r10)).length },
       { befehl := Befehl.movImm64 Register.rcx (intWort 12),
         laenge := (encode (Befehl.movImm64 Register.rcx (intWort 12))).length },
       { befehl := Befehl.addReg64 Register.rax Register.rcx,
         laenge := (encode (Befehl.addReg64 Register.rax Register.rcx)).length },
       { befehl := Befehl.store64 Register.rbx Register.rax
           (BitVec.ofNat 32 0),
         laenge := (encode (Befehl.store64 Register.rbx Register.rax
           (BitVec.ofNat 32 0))).length }] := rfl
  rw [hlist]
  intro d hd
  simp only [List.mem_cons, List.mem_nil_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl | hnil
  · exact ⟨1, rfl, by decide⟩
  · exact ⟨1, rfl, by decide⟩
  · exact ⟨2, rfl, by decide⟩
  · exact ⟨3, rfl, by decide⟩
  · cases hnil

/-- The witness aggregation: the four generated steps cost 1+1+2+3 = 7. -/
theorem hCost_wit :
    laufKosten profilZeuge (decodiertZu witProg628) = some 7 := by
  decide

/-- SOURCE MEMORY CHANGE: the witness `assignSlot` runs through actual
    `execStmt` and moves the slot `12 -> 42`. -/
theorem witQuelle_aendert :
    ∃ (σ' : World witD628) (ρ' : Env witD628 witCtx628),
      execStmt witO628 0 witR628
        (Stmt.assignSlot (l := false) () () witI628
          (cast (congrArg (Expr witD628 witCtx628 []) witHT628.symm)
            witE628) witHw628 witHL628)
        witSigma628 witEnv628 = .ok σ' ρ' ∧
      (witSigma628.slots () 0 ()).n = 12 ∧ (σ'.slots () 0 ()).n = 42 := by
  have hExecW : ∃ σ' ρ', execStmt witO628 0 witR628
      (Stmt.assignSlot (l := false) () () witI628
        (cast (congrArg (Expr witD628 witCtx628 []) witHT628.symm)
          witE628) witHw628 witHL628)
      witSigma628 witEnv628 = .ok σ' ρ' := by
    simp only [execStmt]
    exact ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hExec⟩ := hExecW
  refine ⟨σ', ρ', hExec, rfl, ?_⟩
  cases hExec
  rfl

/-- The shared non-degenerate package Prop: a table the contract writes, a
    memory-changing fetched-byte run, and a memory-changing source run. -/
def Paket : Prop :=
    witV628.schreibt () = true ∧
    (∃ a : Adresse, ausgangByte a (laufBytes 4 witStart628) ≠
      some (witStart628.speicher.bytes a)) ∧
    ∃ (σ' : World witD628) (ρ' : Env witD628 witCtx628),
      execStmt witO628 0 witR628
        (Stmt.assignSlot (l := false) () () witI628
          (cast (congrArg (Expr witD628 witCtx628 []) witHT628.symm)
            witE628) witHw628 witHL628)
        witSigma628 witEnv628 = .ok σ' ρ' ∧
      (witSigma628.slots () 0 ()).n = 12 ∧ (σ'.slots () 0 ()).n = 42

/-- The shared non-degenerate package holds. -/
theorem paket_nicht_degeneriert : Paket :=
  ⟨witHw628, witLaufAendert628, witQuelle_aendert⟩

/-! ## Inhabitation: every syntax-premise theorem jointly witnessed.

    Each `_zeuge` below instantiates ALL premises of its theorem on the
    shared non-degenerate package (a table the contract writes, a
    memory-changing source run `12 -> 42`, a memory-changing fetched-byte
    target run) and proves the conclusion. -/

/-- Joint witness for `senkAtom_laenge`. -/
theorem senkAtom_laenge_zeuge :
    ∃ (pa : List Befehl),
      senkAtom ZeugeAbb ZeugeAtomA Register.rax = some pa ∧
      pa.length = 1 ∧
      (∃ f t, (ZeugeD.signatur f).schreibt t = true) ∧
      (∃ a : Adresse, ausgangByte a (laufBytes 4 ZeugeStart) ≠
        some (ZeugeStart.speicher.bytes a)) := by
  refine ⟨[Befehl.movReg64 Register.rax Register.r10], rfl, rfl,
    zeuge_schreibt, zeuge_lauf_aendert_speicher⟩

/-- Joint witness for `senkFrag_laenge`. -/
theorem senkFrag_laenge_zeuge :
    ∃ (prog : List Befehl),
      senkFrag witAbb628 witE628 Register.rax Register.rcx = some prog ∧
      (prog.length = 1 ∨ prog.length = 3) ∧
      Paket := by
  refine ⟨_, witSenk628, Or.inr rfl, paket_nicht_degeneriert⟩

/-- Joint witness for `senkAssign_laenge`. -/
theorem senkAssign_laenge_zeuge :
    ∃ (prog code : List Befehl),
      senkFrag witAbb628 witE628 Register.rax Register.rcx = some prog ∧
      senkAssign witAbb628 witE628 Register.rax Register.rcx Register.rbx
        (BitVec.ofNat 32 0) = some code ∧
      (code.length = 2 ∨ code.length = 4) ∧
      Paket := by
  refine ⟨_, _, witSenk628, witSenkAssign628, Or.inr rfl,
    paket_nicht_degeneriert⟩

/-- Joint witness for `deckung_fragment`, with the derived coverage. -/
theorem deckung_fragment_zeuge :
    ∃ (prog : List Befehl),
      senkFrag witAbb628 witE628 Register.rax Register.rcx = some prog ∧
      1 ≤ 1 ∧
      Deckung fragmentSummary 1
        (decodiertZu (prog ++ [Befehl.store64 Register.rbx Register.rax
          (BitVec.ofNat 32 0)])) ∧
      Paket := by
  refine ⟨_, witSenk628, Nat.le_refl 1,
    deckung_fragment witAbb628 witE628 Register.rax Register.rcx
      Register.rbx (BitVec.ofNat 32 0) 1 _ witSenk628 (Nat.le_refl 1),
    paket_nicht_degeneriert⟩

/-- Joint witness for the main theorem, with the time bound `7 ≤ 3 * k`. -/
theorem senkAssign_zeit_schranke_zeuge :
    ∃ (prog : List Befehl),
      senkFrag witAbb628 witE628 Register.rax Register.rcx = some prog ∧
      1 ≤ 1 ∧
      laufKosten profilZeuge
        (decodiertZu (prog ++ [Befehl.store64 Register.rbx Register.rax
          (BitVec.ofNat 32 0)])) = some 7 ∧
      (∀ d ∈ decodiertZu (prog ++ [Befehl.store64 Register.rbx Register.rax
          (BitVec.ofNat 32 0)]),
        ∃ c, schrittKosten profilZeuge d = some c ∧ c ≤ 3) ∧
      (∀ k, expandBound fragmentSummary 1 = some k → 7 ≤ 3 * k) ∧
      Paket := by
  refine ⟨[Befehl.movReg64 Register.rax Register.r10,
      Befehl.movImm64 Register.rcx (intWort 12),
      Befehl.addReg64 Register.rax Register.rcx],
    witSenk628, Nat.le_refl 1, hCost_wit, hb_wit, ?_,
    paket_nicht_degeneriert⟩
  exact senkAssign_zeit_schranke witAbb628 witE628 Register.rax
    Register.rcx Register.rbx (BitVec.ofNat 32 0) profilZeuge 1 3 7 _
    witSenk628 (Nat.le_refl 1) hCost_wit hb_wit

/-- Joint witness for `einheiten_getrennt`: `src * 4` bounds work, work
    counts the generated list, the fragment is 3 instructions long. -/
theorem einheiten_getrennt_zeuge :
    ∃ (prog : List Befehl),
      senkFrag witAbb628 witE628 Register.rax Register.rcx = some prog ∧
      expandBound fragmentSummary 1 = some (1 * 4) ∧
      targetWork ((decodiertZu (prog ++ [Befehl.store64 Register.rbx
        Register.rax (BitVec.ofNat 32 0)])).map fun d => d.befehl) =
        prog.length + 1 ∧
      (prog.length = 1 ∨ prog.length = 3) ∧
      Paket := by
  obtain ⟨hexp, hwork, hlen⟩ :=
    einheiten_getrennt witAbb628 witE628 Register.rax Register.rcx
      Register.rbx (BitVec.ofNat 32 0) 1 _ witSenk628
  exact ⟨_, witSenk628, hexp, hwork, hlen, paket_nicht_degeneriert⟩

/-- Joint witness for `arbeit_nach_faltung`: same value, work 3 and 1. -/
theorem arbeit_nach_faltung_zeuge :
    ∃ (vor nach : List Befehl),
      senkFrag witAbb628
        (Expr.add
          (Expr.lit (D := witD628) (Γ := witCtx628) (Λ := []) 30)
          (Expr.lit (D := witD628) (Γ := witCtx628) (Λ := []) 12))
        Register.rax Register.rcx = some vor ∧
      senkFrag witAbb628
        (InvariantenOpt.foldAddLit (D := witD628) (Γ := witCtx628)
          (Λ := []) 30 12)
        Register.rax Register.rcx = some nach ∧
      vor.length = 3 ∧ nach.length = 1 ∧
      Paket := by
  obtain ⟨vor, nach, hsenkV, hsenkN, heval, h3, h1, hne⟩ :=
    arbeit_nach_faltung witAbb628 30 12 Register.rax Register.rcx
      witSigma628 witSigma628 witEnv628
  exact ⟨vor, nach, hsenkV, hsenkN, h3, h1, paket_nicht_degeneriert⟩

/-- Joint witness for `arbeit_ohne_versteck`: every step priced, bound met. -/
theorem arbeit_ohne_versteck_zeuge :
    ∃ (prog : List Befehl),
      senkFrag witAbb628 witE628 Register.rax Register.rcx = some prog ∧
      1 ≤ 1 ∧
      laufKosten profilZeuge
        (decodiertZu (prog ++ [Befehl.store64 Register.rbx Register.rax
          (BitVec.ofNat 32 0)])) = some 7 ∧
      (∀ d ∈ decodiertZu (prog ++ [Befehl.store64 Register.rbx Register.rax
          (BitVec.ofNat 32 0)]),
        ∃ c, schrittKosten profilZeuge d = some c ∧ c ≤ 3) ∧
      (∀ d ∈ decodiertZu (prog ++ [Befehl.store64 Register.rbx Register.rax
          (BitVec.ofNat 32 0)]),
        ∃ c, schrittKosten profilZeuge d = some c) ∧
      (∀ k, expandBound fragmentSummary 1 = some k → 7 ≤ 3 * k) ∧
      Paket := by
  obtain ⟨hnamed, hzeit⟩ :=
    arbeit_ohne_versteck witAbb628 witE628 Register.rax Register.rcx
      Register.rbx (BitVec.ofNat 32 0) profilZeuge 1 3 7 _ witSenk628
      (Nat.le_refl 1) hCost_wit hb_wit
  refine ⟨_, witSenk628, Nat.le_refl 1, hCost_wit, hb_wit, hnamed, hzeit,
    paket_nicht_degeneriert⟩

/-- Joint witness for `arbeit_knapp_verweigert`: bound 1 covers nothing. -/
theorem arbeit_knapp_verweigert_zeuge :
    ∃ (prog code : List Befehl),
      senkFrag witAbb628 witE628 Register.rax Register.rcx = some prog ∧
      senkAssign witAbb628 witE628 Register.rax Register.rcx Register.rbx
        (BitVec.ofNat 32 0) = some code ∧
      1 < 2 ∧
      ¬ targetWork ((decodiertZu code).map fun d => d.befehl) ≤ 1 ∧
      Paket := by
  refine ⟨_, _, witSenk628, witSenkAssign628, by decide,
    arbeit_knapp_verweigert witAbb628 witE628 Register.rax Register.rcx
      Register.rbx (BitVec.ofNat 32 0) _ _ witSenk628 witSenkAssign628 1
      (by decide),
    paket_nicht_degeneriert⟩

/-- Joint witness for `keine_arbeit_ohne_fragment`: `2 * 3` lowers to
    nothing. -/
theorem keine_arbeit_ohne_fragment_zeuge :
    (¬ ∃ code, senkAssign witAbb628
      (Expr.mul
        (Expr.lit (D := witD628) (Γ := witCtx628) (Λ := []) 2)
        (Expr.lit (D := witD628) (Γ := witCtx628) (Λ := []) 3))
      Register.rax Register.rcx Register.rbx (BitVec.ofNat 32 0) =
      some code) ∧
    Paket :=
  ⟨keine_arbeit_ohne_fragment witAbb628 Register.rax Register.rcx
    Register.rbx (BitVec.ofNat 32 0), paket_nicht_degeneriert⟩

/-- Joint witness for `kein_freier_versuch_fragment`: no free retry. -/
theorem kein_freier_versuch_fragment_zeuge :
    (kostenSummeOk { fragmentSummary with retryBound := none } = false ∧
    zeitTransferZulaessig { fragmentSummary with retryBound := none }
      profilZeuge = false) ∧
    Paket :=
  ⟨kein_freier_versuch_fragment profilZeuge, paket_nicht_degeneriert⟩

/-- LOUD STOPS WITNESS: `forever` at zero passes and calls at zero depth
    stop under their names for ALL continuations, the over-budget foreign
    edge stops under the budget name while the refused `ret` refuses the
    target aggregation -- jointly with the non-degenerate package. No stop
    is silent, none is reordered behind success. -/
theorem stopp_bleibt_laut_zeuge :
    (∀ (a : witD628.Annahme)
      (schritt : World witD628 → Env witD628 witCtx628 →
        Ausgang witV628 true witCtx628)
      (inv : World witD628 → Env witD628 witCtx628 →
        World witD628 × Bool)
      (σ : World witD628) (ρ : Env witD628 witCtx628),
      foreverLauf (l := false) a schritt inv 0 σ ρ =
        .hardware (.fortschritt a)) ∧
    (∀ (P : Programm witD628) (O : Orakel witD628) (passes : Nat)
      (σ : World witD628) (ρ : Env witD628 []),
      rufAt P O passes 0 () σ ρ = .logik (.abstieg ())) ∧
    (∃ needed, runOps 3 3 [fremdOp 3] = .budget "per_pass.ops" needed 3) ∧
    (laufKosten profilZeuge [{ befehl := Befehl.ret, laenge := 1 }] =
      none) ∧
    Paket := by
  refine ⟨fun a schritt inv σ ρ => forever_erschoepft_benannt a schritt inv σ ρ,
    fun P O passes σ ρ => rufAt_tiefe_erschoepft P O passes () σ ρ, ?_, ?_,
    paket_nicht_degeneriert⟩
  · exact runOps_fremd_exceeds 3 3 3 (by decide)
  · exact laufKosten_zeuge_verweigert

/- CUTS:
    - Proved (generic): generated-work formula per fragment shape
      (atom 1; fragment 1 or 3; assignment 2 or 4) with the `targetWork`
      bridge over canonically decoded code; the admitted fragment summary
      (uniform maximum 4, honest zero spill/fence, proved retry bound, no
      exclusions); the `Deckung` producer derived from fragment admission
      (the leg `BudgetExecution` leaves open); the time composition of
      named per-form hardware costs with the derived bound, pinning
      source steps (`src`), retired instructions (`targetWork`) and named
      target time (`t`) as three separate counts; fold recomputation
      (same value, work 3 -> 1, so costs must be recomputed, never
      inherited); no-hidden-stutter plus bound; underestimated-work
      (below 2 refuses), unsupported-form (`2 * 3` lowers to nothing) and
      unbounded-retry refusals; loud `forever`/depth/ops stops with the
      joint stop-order fact.
    - Witness-only: every `_zeuge` above is joint on the one-table
      `witD628` package (contract writes the table; source slot `12 -> 42`
      through actual `execStmt`; fetched-byte run changes memory
      `0 -> 42`; forged-opcode fetched refusal reused).
    - OPEN (scheduling): which source step the summary's `src` counts when
      several lowered assignments share one budget (`kostenTiefF`
      multiplicities) -- the transfer bounds one generated assignment per
      `src` unit; concurrent interleavings and waiting delays are untouched
      (TSO/bridge lanes own them).
    - OPEN (all-source): the fragment is literals, variables and one
      bounded add/sub over atoms, then one slot store. Sums, floats,
      bools, globals, pointers, calls, loops, branches, non-zero
      displacements and deeper nesting refuse (`none`) and carry no work
      bound here.
    - OPEN (timing-model fidelity): `t` counts NAMED per-form bounds from
      the selected profile, never measured silicon latencies; `ret` stays
      refused; no constant-time claim; no CAS-progress, fairness or
      zero-cost-stutter promise (unbounded retries are refused, never
      bounded).
    - No new interpreter, no second cost model, no IR: the one `targetWork`,
      the one `laufKosten` aggregation, the one `senkFrag`/`senkAssign`
      lowering and the actual `execStmt`/`lauf`/`laufBytes` runs are reused
      untouched. No checker, Spec, goal, emitter or friend-reserved file
      is touched.
-/

#print axioms decodiertZu_befehl
#print axioms arbeit_decodiert
#print axioms senkAtom_laenge
#print axioms senkFrag_laenge
#print axioms senkAssign_laenge
#print axioms fragmentSummary_ok
#print axioms fragmentSummary_max
#print axioms fragmentSummary_expand
#print axioms deckung_fragment
#print axioms senkAssign_zeit_schranke
#print axioms einheiten_getrennt
#print axioms arbeit_nach_faltung
#print axioms arbeit_ohne_versteck
#print axioms arbeit_knapp_verweigert
#print axioms keine_arbeit_ohne_fragment
#print axioms kein_freier_versuch_fragment
#print axioms hb_wit
#print axioms hCost_wit
#print axioms witQuelle_aendert
#print axioms paket_nicht_degeneriert
#print axioms senkAtom_laenge_zeuge
#print axioms senkFrag_laenge_zeuge
#print axioms senkAssign_laenge_zeuge
#print axioms deckung_fragment_zeuge
#print axioms senkAssign_zeit_schranke_zeuge
#print axioms einheiten_getrennt_zeuge
#print axioms arbeit_nach_faltung_zeuge
#print axioms arbeit_ohne_versteck_zeuge
#print axioms arbeit_knapp_verweigert_zeuge
#print axioms keine_arbeit_ohne_fragment_zeuge
#print axioms kein_freier_versuch_fragment_zeuge
#print axioms stopp_bleibt_laut_zeuge

end Gabbro.Grammatik.X86
