/-
  File:      Grammatik/X86/ExpressionLowering.lean
  Subject:   Generic direct typed-source expression to pilot machine code.

  Lane 599: lower the actual typed source AST (`Syntax.Expr` over `Ty.int`
  ranges, `Semantik.eval` over `Zahl`) to canonical pilot `Befehl`
  lists (`Codec.encode`, `Ausfuehrung.schritt`, `Byteschritt` fetch),
  with NO second SSA IR and no new source interpreter. Covered fragment:
  integer literals, integer variables, and one bounded ADD/SUB level over
  atomic operands; every other form refuses with `none`. Environment
  representation (`EnvRepr`), register freshness (`Frisch`) and the
  signed-64 representation bounds are explicit checkable premises.
  No source checker, Spec, goal or friend-reserved optimiser file is touched.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.FlagBeweis
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Modular integer-to-word conversion: `n mod 2^64` as a word.
    Same shape as `ScalarFloat.intWort`; the signed reading is `sint`. -/
def intWort (n : Int) : Wort := BitVec.ofNat 64 (n % (2 ^ 64 : Int)).toNat

/-- Explicit checkable environment representation: every integer variable
    of the context reads, in the pre-state register file, the modular word
    of its actual source value. No Rust-produced AST is trusted: `ρ.get`
    is the single source model. -/
def EnvRepr {D : Deklaration} {Γ : Ctx} (ρ : Env D Γ) (regs : Register → Wort)
    (abb : ∀ (τ : Ty), Var Γ τ → Register) : Prop :=
  ∀ (lo hi : Int) (x : Var Γ (.int lo hi)),
    regs (abb _ x) = intWort (ρ.get x).n

/-- Register freshness: no source variable lives in the two working
    registers (pre-state aliases are refused by premise, not renamed away),
    and the two working registers differ (else `add dst dst` doubles). -/
def Frisch {Γ : Ctx} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp : Register) : Prop :=
  (∀ (τ : Ty) (x : Var Γ τ), abb τ x ≠ dst ∧ abb τ x ≠ tmp) ∧ dst ≠ tmp

/-- Atom lowering: literals and variables lower to one instruction;
    every other form refuses with `none`. Stated over a general `τ` so
    that case analysis substitutes the index variable instead of stalling
    on stuck carrier projections (`gtyp`, `typ`). -/
def senkAtom {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst : Register) : Option (List Befehl) :=
  match e with
  | .lit n => some [.movImm64 dst (intWort n)]
  | .var x => some [.movReg64 dst (abb _ x)]
  | _ => none

/-- Fragment lowering: atoms as above, plus ONE bounded ADD/SUB level over
    atomic operands. Deeper nesting refuses (the atom lowering says `none`),
    as does every non-arithmetic form. No new IR is built: the result is a
    canonical `Befehl` list. -/
def senkFrag {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp : Register) : Option (List Befehl) :=
  match e with
  | .lit n => some [.movImm64 dst (intWort n)]
  | .var x => some [.movReg64 dst (abb _ x)]
  | .add a b =>
    match senkAtom abb a dst, senkAtom abb b tmp with
    | some pa, some pb => some (pa ++ pb ++ [Befehl.addReg64 dst tmp])
    | _, _ => none
  | .sub a b =>
    match senkAtom abb a dst, senkAtom abb b tmp with
    | some pa, some pb => some (pa ++ pb ++ [Befehl.subReg64 dst tmp])
    | _, _ => none
  | _ => none

/-- Shape: literals lower to one immediate move. -/
theorem senkFrag_lit {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (n : Int) (dst tmp : Register) :
    senkFrag abb (Expr.lit (Γ := Γ) (Λ := Λ) n) dst tmp =
      some [.movImm64 dst (intWort n)] := rfl

/-- Shape: variables lower to one register move from their mapped register. -/
theorem senkFrag_var {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (x : Var Γ (.int lo hi)) (dst tmp : Register) :
    senkFrag abb (Expr.var (Λ := Λ) x) dst tmp =
      some [.movReg64 dst (abb _ x)] := rfl

/-- Shape: a bounded ADD over two lowered atoms. -/
theorem senkFrag_add {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (dst tmp : Register) (pa pb : List Befehl)
    (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
    senkFrag abb (Expr.add a b) dst tmp =
      some (pa ++ pb ++ [Befehl.addReg64 dst tmp]) := by
  simp only [senkFrag, ha, hb]

/-- Shape: a bounded SUB over two lowered atoms. -/
theorem senkFrag_sub {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (dst tmp : Register) (pa pb : List Befehl)
    (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
    senkFrag abb (Expr.sub a b) dst tmp =
      some (pa ++ pb ++ [Befehl.subReg64 dst tmp]) := by
  simp only [senkFrag, ha, hb]

/-- PLANTED REFUSAL: multiplication is outside the fragment. -/
theorem senkFrag_verweigert_mul {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (dst tmp : Register) :
    senkFrag abb
      (Expr.mul (Expr.lit (Γ := Γ) (Λ := Λ) 2) (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst tmp = none := rfl

/-- PLANTED REFUSAL: a nested ADD (depth two) is outside the fragment. -/
theorem senkFrag_verweigert_tief {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (dst tmp : Register) :
    senkFrag abb
      (Expr.add
        (Expr.add (Expr.lit (Γ := Γ) (Λ := Λ) 1) (Expr.lit (Γ := Γ) (Λ := Λ) 2))
        (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst tmp = none := rfl

/-- MODULAR HOMOMORPHISM (add): the word sum is the exact sum wrapped.
    Overflow is therefore never silent in the statement: the main theorem
    equates the register with `intWort` of the exact source value. -/
theorem intWort_add (a b : Int) :
    intWort a + intWort b = intWort (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [intWort, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- MODULAR HOMOMORPHISM (sub): the word difference is the exact one wrapped. -/
theorem intWort_sub (a b : Int) :
    intWort a - intWort b = intWort (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [intWort, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- SIGNED ROUNDTRIP: an in-range integer survives the modular conversion
    with its signed reading intact. Out-of-range values wrap (honest
    `bmod` behaviour); the overflow-bound theorem names when that happens. -/
theorem intWort_sint (n : Int) (hlo : -(2 ^ 63 : Int) ≤ n) (hhi : n < 2 ^ 63) :
    sint (intWort n) = n := by
  unfold sint intWort
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat]
  have hnn : 0 ≤ n % (2 ^ 64 : Int) := by omega
  have hlt : (n % (2 ^ 64 : Int)).toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt, Int.toNat_of_nonneg hnn]
  by_cases hn : 0 ≤ n
  · have hv : n % (2 ^ 64 : Int) = n := by omega
    rw [hv]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  · have hv : n % (2 ^ 64 : Int) = n + 2 ^ 64 := by omega
    rw [hv]
    have hb := bmod_high (n + 2 ^ 64) (by omega) (by omega)
    omega

/-- Every canonical encoding has a valid decode length. -/
theorem laengeOk_encode (b : Befehl) : laengeOk (encode b).length = true := by
  unfold laengeOk
  simp only [decide_eq_true_eq]
  exact encode_len b

/-- A single-instruction run is its step. -/
theorem lauf_einzeln (d : Decodiert) (s : Zustand) :
    lauf [d] s = schritt d s := by
  unfold lauf
  cases schritt d s <;> rfl

/-- Sequential runs compose over append: the existing `lauf` needs no
    new interpreter to sequence lowered fragments. -/
theorem lauf_anhang (p q : List Decodiert) (s s' : Zustand)
    (h1 : lauf p s = some s') : lauf (p ++ q) s = lauf q s' := by
  induction p generalizing s with
  | nil => simp_all [lauf]
  | cons d rest ih =>
    simp only [List.cons_append, lauf] at h1 ⊢
    cases h : schritt d s with
    | none => simp [h] at h1
    | some t =>
      simp [h] at h1 ⊢
      exact ih t h1

/-- ATOM CORRECTNESS (literal): the immediate move puts the modular word
    of the exact source value into the destination; memory, other
    registers and flags are untouched. -/
theorem senkAtom_korrekt_lit {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (n : Int) (dst : Register)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (pa : List Befehl) (hsenk : senkAtom abb (Expr.lit (Γ := Γ) (Λ := Λ) n) dst = some pa) :
    ∃ s', lauf (pa.map fun b => ⟨b, (encode b).length⟩) s = some s' ∧
      s'.register dst = intWort (eval σ₀ (Expr.lit (Γ := Γ) (Λ := Λ) n) σ ρ).n ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → s'.register q = s.register q) ∧
      s'.flags = s.flags := by
  simp only [senkAtom] at hsenk
  have hpa : pa = [.movImm64 dst (intWort n)] := Option.some_inj.mp hsenk.symm
  subst hpa
  refine ⟨schrittRegister s (ripNach s.rip (encode (.movImm64 dst (intWort n))).length)
    s.flags dst (intWort n), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, lauf_einzeln]
    exact schritt_movImm64 _ _ _ _ (laengeOk_encode _) rfl
  · exact regSet_gleich _ _ _
  · rfl
  · intro q hq
    exact regSet_fremd s.register dst q (intWort n) hq
  · rfl

/-- ATOM CORRECTNESS (variable): the register move copies the represented
    source value; the `EnvRepr` premise is what makes the read checkable. -/
theorem senkAtom_korrekt_var {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (x : Var Γ (.int lo hi)) (dst : Register)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hrenv : EnvRepr ρ s.register abb)
    (pa : List Befehl) (hsenk : senkAtom abb (Expr.var (Λ := Λ) x) dst = some pa) :
    ∃ s', lauf (pa.map fun b => ⟨b, (encode b).length⟩) s = some s' ∧
      s'.register dst = intWort (eval σ₀ (Expr.var (Λ := Λ) x) σ ρ).n ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → s'.register q = s.register q) ∧
      s'.flags = s.flags := by
  simp only [senkAtom] at hsenk
  have hpa : pa = [.movReg64 dst (abb _ x)] := Option.some_inj.mp hsenk.symm
  subst hpa
  have hx := hrenv lo hi x
  refine ⟨schrittRegister s
    (ripNach s.rip (encode (.movReg64 dst (abb _ x))).length)
    s.flags dst (s.register (abb _ x)), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, lauf_einzeln]
    exact schritt_movReg64 _ _ _ _ (laengeOk_encode _) rfl
  · show regSet s.register dst (s.register (abb _ x)) dst =
      intWort (eval σ₀ (Expr.var (Λ := Λ) x) σ ρ).n
    rw [regSet_gleich]
    exact hx
  · rfl
  · intro q hq
    exact regSet_fremd s.register dst q (s.register (abb _ x)) hq
  · rfl

/-- Shape-only atom classification: a literal or a variable. An
    inductive relation (rather than a match) so that inversion substitutes
    the expression -- stuck carrier projections never appear as indices. -/
inductive IstAtom {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} :
    ∀ {τ : Ty}, Expr D Γ Λ τ → Prop where
  | lit (n : Int) : IstAtom (.lit n)
  | var {t : Ty} (x : Var Γ t) : IstAtom (.var x)

/-- Every successful atom lowering is a literal or a variable. Proved over
    a general index so every arm substitutes; refusal arms close because
    the lowering reduces to `none`. -/
theorem istAtom_von_senkAtom {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ τ) (dst : Register)
    (pa : List Befehl) (ha : senkAtom abb a dst = some pa) :
    IstAtom a := by
  cases a with
  | lit n => exact .lit n
  | var x => exact .var x
  | wahr => simp [senkAtom] at ha
  | falsch => simp [senkAtom] at ha
  | glob g hL => simp [senkAtom] at ha
  | slot t f i hL => simp [senkAtom] at ha
  | durch p t ht f i hL => simp [senkAtom] at ha
  | ptrOf t n ht rw => simp [senkAtom] at ha
  | fnref f n h => simp [senkAtom] at ha
  | altGlob g hL => simp [senkAtom] at ha
  | altSlot t f i hL => simp [senkAtom] at ha
  | weiter h1 h2 e => simp [senkAtom] at ha
  | add a b => simp [senkAtom] at ha
  | sub a b => simp [senkAtom] at ha
  | neg a => simp [senkAtom] at ha
  | mul a b => simp [senkAtom] at ha
  | div h0 h1 a b => simp [senkAtom] at ha
  | rem h0 h1 a b => simp [senkAtom] at ha
  | sdiv hb a b => simp [senkAtom] at ha
  | srem hb a b => simp [senkAtom] at ha
  | leseBytes t f hf n i hlo hhi hL => simp [senkAtom] at ha
  | band h0 h0' a b => simp [senkAtom] at ha
  | bor w h0 h0' hw1 hw2 a b => simp [senkAtom] at ha
  | bxor w h0 h0' hw1 hw2 a b => simp [senkAtom] at ha
  | shl w hw1 hw2 h0 h0' a b => simp [senkAtom] at ha
  | shr w hw1 hw2 h0 h0' a b => simp [senkAtom] at ha
  | lt a b => simp [senkAtom] at ha
  | le a b => simp [senkAtom] at ha
  | eq a b => simp [senkAtom] at ha
  | fllt a b => simp [senkAtom] at ha
  | flle a b => simp [senkAtom] at ha
  | und a b => simp [senkAtom] at ha
  | oder a b => simp [senkAtom] at ha
  | nicht a => simp [senkAtom] at ha
  | none n => simp [senkAtom] at ha
  | some e => simp [senkAtom] at ha
  | istSome e => simp [senkAtom] at ha
  | fall cs i nutz => simp [senkAtom] at ha
  | grund n r => simp [senkAtom] at ha
  | forallSlots t body hL => simp [senkAtom] at ha
  | existsSlots t body hL => simp [senkAtom] at ha
  | reaches t f hf a b hL => simp [senkAtom] at ha

/-- ATOM CORRECTNESS (generic): a successful atom lowering is a literal
    or a variable (everything else refuses); both shapes preserve
    flags, memory and foreign registers. -/
theorem senkAtom_korrekt {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int lo hi)) (dst : Register)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hrenv : EnvRepr ρ s.register abb)
    (pa : List Befehl) (ha : senkAtom abb a dst = some pa) :
    ∃ s', lauf (pa.map fun b => ⟨b, (encode b).length⟩) s = some s' ∧
      s'.register dst = intWort (eval σ₀ a σ ρ).n ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → s'.register q = s.register q) ∧
      s'.flags = s.flags := by
  match istAtom_von_senkAtom abb a dst pa ha with
  | .lit n => exact senkAtom_korrekt_lit abb n dst ρ σ₀ σ s pa ha
  | .var x => exact senkAtom_korrekt_var abb x dst ρ σ₀ σ s hrenv pa ha

/-- FRAGMENT CORRECTNESS (add): the first atom evaluates into `dst`,
    the second into `tmp`, the architectural add combines them. `Frisch`
    keeps the second load from reading the first result; memory is untouched,
    foreign registers and `rsp` are kept, flags are the architectural add
    flags over the two exact source words. -/
theorem senkung_add {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (dst tmp : Register)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hfr : Frisch abb dst tmp) (hrsp : dst ≠ Register.rsp ∧ tmp ≠ Register.rsp)
    (hrenv : EnvRepr ρ s.register abb)
    (pa pb : List Befehl)
    (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
    ∃ s', lauf (((pa ++ pb) ++ [Befehl.addReg64 dst tmp]).map
        fun b => ⟨b, (encode b).length⟩) s = some s' ∧
      s'.register dst = intWort (eval σ₀ (Expr.add a b) σ ρ).n ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → q ≠ tmp → s'.register q = s.register q) ∧
      s'.register Register.rsp = s.register Register.rsp ∧
      s'.flags =
        (add64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2 := by
  obtain ⟨hneu, hne⟩ := hfr
  obtain ⟨hdst, htmp⟩ := hrsp
  obtain ⟨s1, hrun1, hval1, hmem1, hreg1, hfl1⟩ :=
    senkAtom_korrekt abb a dst ρ σ₀ σ s hrenv pa ha
  have hrenv1 : EnvRepr ρ s1.register abb := by
    intro lo' hi' x
    have h1 := hneu _ x
    rw [hreg1 _ h1.1]
    exact hrenv lo' hi' x
  obtain ⟨s2, hrun2, hval2, hmem2, hreg2, hfl2⟩ :=
    senkAtom_korrekt abb b tmp ρ σ₀ σ s1 hrenv1 pb hb
  have hdst2 : s2.register dst = intWort (eval σ₀ a σ ρ).n := by
    rw [hreg2 dst hne]
    exact hval1
  have hlen : laengeOk (encode (Befehl.addReg64 dst tmp)).length = true :=
    laengeOk_encode _
  have hadd : schritt ⟨Befehl.addReg64 dst tmp, (encode (Befehl.addReg64 dst tmp)).length⟩ s2 =
      some (schrittRegister s2 (ripNach s2.rip (encode (Befehl.addReg64 dst tmp)).length)
        (add64 (s2.register dst) (s2.register tmp)).2 dst
        (add64 (s2.register dst) (s2.register tmp)).1) :=
    schritt_addReg64 _ _ _ _ hlen rfl
  have hmap : ((pa ++ pb ++ [Befehl.addReg64 dst tmp]).map
      fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
      (pa.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
      (pb.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
      [⟨Befehl.addReg64 dst tmp, (encode (Befehl.addReg64 dst tmp)).length⟩] := by
    simp [List.map_append]
  refine ⟨schrittRegister s2 (ripNach s2.rip (encode (Befehl.addReg64 dst tmp)).length)
    (add64 (s2.register dst) (s2.register tmp)).2 dst
    (add64 (s2.register dst) (s2.register tmp)).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmap]
    have h12 : lauf ((pa.map fun b => ⟨b, (encode b).length⟩) ++
        (pb.map fun b => ⟨b, (encode b).length⟩)) s = some s2 := by
      rw [lauf_anhang _ _ _ _ hrun1]
      exact hrun2
    rw [lauf_anhang _ _ _ _ h12, lauf_einzeln]
    exact hadd
  · show regSet s2.register dst (add64 (s2.register dst) (s2.register tmp)).1 dst =
        intWort (eval σ₀ (Expr.add a b) σ ρ).n
    rw [regSet_gleich, hdst2, hval2]
    show intWort (eval σ₀ a σ ρ).n + intWort (eval σ₀ b σ ρ).n =
      intWort (eval σ₀ (Expr.add a b) σ ρ).n
    calc intWort (eval σ₀ a σ ρ).n + intWort (eval σ₀ b σ ρ).n
        = intWort ((eval σ₀ a σ ρ).n + (eval σ₀ b σ ρ).n) := intWort_add _ _
      _ = intWort (eval σ₀ (Expr.add a b) σ ρ).n := rfl
  · show s2.speicher = s.speicher
    rw [hmem2, hmem1]
  · intro q hqd hqt
    show regSet s2.register dst (add64 (s2.register dst) (s2.register tmp)).1 q =
      s.register q
    rw [regSet_fremd _ _ _ _ hqd, hreg2 q hqt, hreg1 q hqd]
  · show regSet s2.register dst (add64 (s2.register dst) (s2.register tmp)).1
        Register.rsp = s.register Register.rsp
    rw [regSet_fremd _ _ _ _ (Ne.symm hdst), hreg2 _ (Ne.symm htmp),
      hreg1 _ (Ne.symm hdst)]
  · show (add64 (s2.register dst) (s2.register tmp)).2 =
        (add64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2
    rw [hdst2, hval2]

/-- FRAGMENT CORRECTNESS (sub): mirror of the add case with the
    architectural borrow flags. -/
theorem senkung_sub {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (dst tmp : Register)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hfr : Frisch abb dst tmp) (hrsp : dst ≠ Register.rsp ∧ tmp ≠ Register.rsp)
    (hrenv : EnvRepr ρ s.register abb)
    (pa pb : List Befehl)
    (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
    ∃ s', lauf (((pa ++ pb) ++ [Befehl.subReg64 dst tmp]).map
        fun b => ⟨b, (encode b).length⟩) s = some s' ∧
      s'.register dst = intWort (eval σ₀ (Expr.sub a b) σ ρ).n ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → q ≠ tmp → s'.register q = s.register q) ∧
      s'.register Register.rsp = s.register Register.rsp ∧
      s'.flags =
        (sub64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2 := by
  obtain ⟨hneu, hne⟩ := hfr
  obtain ⟨hdst, htmp⟩ := hrsp
  obtain ⟨s1, hrun1, hval1, hmem1, hreg1, hfl1⟩ :=
    senkAtom_korrekt abb a dst ρ σ₀ σ s hrenv pa ha
  have hrenv1 : EnvRepr ρ s1.register abb := by
    intro lo' hi' x
    have h1 := hneu _ x
    rw [hreg1 _ h1.1]
    exact hrenv lo' hi' x
  obtain ⟨s2, hrun2, hval2, hmem2, hreg2, hfl2⟩ :=
    senkAtom_korrekt abb b tmp ρ σ₀ σ s1 hrenv1 pb hb
  have hdst2 : s2.register dst = intWort (eval σ₀ a σ ρ).n := by
    rw [hreg2 dst hne]
    exact hval1
  have hlen : laengeOk (encode (Befehl.subReg64 dst tmp)).length = true :=
    laengeOk_encode _
  have hsub : schritt ⟨Befehl.subReg64 dst tmp, (encode (Befehl.subReg64 dst tmp)).length⟩ s2 =
      some (schrittRegister s2 (ripNach s2.rip (encode (Befehl.subReg64 dst tmp)).length)
        (sub64 (s2.register dst) (s2.register tmp)).2 dst
        (sub64 (s2.register dst) (s2.register tmp)).1) :=
    schritt_subReg64 _ _ _ _ hlen rfl
  have hmap : ((pa ++ pb ++ [Befehl.subReg64 dst tmp]).map
      fun b => (⟨b, (encode b).length⟩ : Decodiert)) =
      (pa.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
      (pb.map fun b => (⟨b, (encode b).length⟩ : Decodiert)) ++
      [⟨Befehl.subReg64 dst tmp, (encode (Befehl.subReg64 dst tmp)).length⟩] := by
    simp [List.map_append]
  refine ⟨schrittRegister s2 (ripNach s2.rip (encode (Befehl.subReg64 dst tmp)).length)
    (sub64 (s2.register dst) (s2.register tmp)).2 dst
    (sub64 (s2.register dst) (s2.register tmp)).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmap]
    have h12 : lauf ((pa.map fun b => ⟨b, (encode b).length⟩) ++
        (pb.map fun b => ⟨b, (encode b).length⟩)) s = some s2 := by
      rw [lauf_anhang _ _ _ _ hrun1]
      exact hrun2
    rw [lauf_anhang _ _ _ _ h12, lauf_einzeln]
    exact hsub
  · show regSet s2.register dst (sub64 (s2.register dst) (s2.register tmp)).1 dst =
        intWort (eval σ₀ (Expr.sub a b) σ ρ).n
    rw [regSet_gleich, hdst2, hval2]
    show intWort (eval σ₀ a σ ρ).n - intWort (eval σ₀ b σ ρ).n =
      intWort (eval σ₀ (Expr.sub a b) σ ρ).n
    calc intWort (eval σ₀ a σ ρ).n - intWort (eval σ₀ b σ ρ).n
        = intWort ((eval σ₀ a σ ρ).n - (eval σ₀ b σ ρ).n) := intWort_sub _ _
      _ = intWort (eval σ₀ (Expr.sub a b) σ ρ).n := rfl
  · show s2.speicher = s.speicher
    rw [hmem2, hmem1]
  · intro q hqd hqt
    show regSet s2.register dst (sub64 (s2.register dst) (s2.register tmp)).1 q =
      s.register q
    rw [regSet_fremd _ _ _ _ hqd, hreg2 q hqt, hreg1 q hqd]
  · show regSet s2.register dst (sub64 (s2.register dst) (s2.register tmp)).1
        Register.rsp = s.register Register.rsp
    rw [regSet_fremd _ _ _ _ (Ne.symm hdst), hreg2 _ (Ne.symm htmp),
      hreg1 _ (Ne.symm hdst)]
  · show (sub64 (s2.register dst) (s2.register tmp)).2 =
        (sub64 (intWort (eval σ₀ a σ ρ).n) (intWort (eval σ₀ b σ ρ).n)).2
    rw [hdst2, hval2]

/-- Shape-only fragment classification: literal, variable, or one
    bounded ADD/SUB over lowered atoms (carrying the atom equations).
    Inversion substitutes the expression; stuck indices never appear. -/
inductive IstFrag {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (dst tmp : Register) :
    ∀ {τ : Ty}, Expr D Γ Λ τ → List Befehl → Prop where
  | lit (n : Int) : IstFrag abb dst tmp (.lit n) [Befehl.movImm64 dst (intWort n)]
  | var {t : Ty} (x : Var Γ t) :
      IstFrag abb dst tmp (.var x) [Befehl.movReg64 dst (abb _ x)]
  | add {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
      (b : Expr D Γ Λ (.int l2 h2)) (pa pb : List Befehl)
      (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
      IstFrag abb dst tmp (.add a b) (pa ++ pb ++ [Befehl.addReg64 dst tmp])
  | sub {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
      (b : Expr D Γ Λ (.int l2 h2)) (pa pb : List Befehl)
      (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
      IstFrag abb dst tmp (.sub a b) (pa ++ pb ++ [Befehl.subReg64 dst tmp])

/-- Every successful fragment lowering is one of the four shapes. Proved
    over a general index; the add/sub arms case-split the atom equations,
    refusal arms close because the lowering reduces to `none`. -/
theorem istFrag_von_senkFrag {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp : Register)
    (prog : List Befehl) (h : senkFrag abb e dst tmp = some prog) :
    IstFrag abb dst tmp e prog := by
  cases e with
  | lit n =>
    simp only [senkFrag] at h
    have hprog : prog = [Befehl.movImm64 dst (intWort n)] := Option.some_inj.mp h.symm
    subst hprog
    exact .lit n
  | var x =>
    simp only [senkFrag] at h
    have hprog : prog = [Befehl.movReg64 dst (abb _ x)] := Option.some_inj.mp h.symm
    subst hprog
    exact .var x
  | add a b =>
    cases h1 : senkAtom abb a dst with
    | some pa =>
      cases h2 : senkAtom abb b tmp with
      | some pb =>
        simp only [senkFrag, h1, h2] at h
        have hprog : prog = pa ++ pb ++ [Befehl.addReg64 dst tmp] :=
          Option.some_inj.mp h.symm
        subst hprog
        exact .add a b pa pb h1 h2
      | none => simp [senkFrag, h1, h2] at h
    | none => simp [senkFrag, h1] at h
  | sub a b =>
    cases h1 : senkAtom abb a dst with
    | some pa =>
      cases h2 : senkAtom abb b tmp with
      | some pb =>
        simp only [senkFrag, h1, h2] at h
        have hprog : prog = pa ++ pb ++ [Befehl.subReg64 dst tmp] :=
          Option.some_inj.mp h.symm
        subst hprog
        exact .sub a b pa pb h1 h2
      | none => simp [senkFrag, h1, h2] at h
    | none => simp [senkFrag, h1] at h
  | wahr => simp [senkFrag] at h
  | falsch => simp [senkFrag] at h
  | glob g hL => simp [senkFrag] at h
  | slot t f i hL => simp [senkFrag] at h
  | durch p t ht f i hL => simp [senkFrag] at h
  | ptrOf t n ht rw => simp [senkFrag] at h
  | fnref f n h => simp [senkFrag] at h
  | altGlob g hL => simp [senkFrag] at h
  | altSlot t f i hL => simp [senkFrag] at h
  | weiter h1 h2 e => simp [senkFrag] at h
  | neg a => simp [senkFrag] at h
  | mul a b => simp [senkFrag] at h
  | div h0 h1 a b => simp [senkFrag] at h
  | rem h0 h1 a b => simp [senkFrag] at h
  | sdiv hb a b => simp [senkFrag] at h
  | srem hb a b => simp [senkFrag] at h
  | leseBytes t f hf n i hlo hhi hL => simp [senkFrag] at h
  | band h0 h0' a b => simp [senkFrag] at h
  | bor w h0 h0' hw1 hw2 a b => simp [senkFrag] at h
  | bxor w h0 h0' hw1 hw2 a b => simp [senkFrag] at h
  | shl w hw1 hw2 h0 h0' a b => simp [senkFrag] at h
  | shr w hw1 hw2 h0 h0' a b => simp [senkFrag] at h
  | lt a b => simp [senkFrag] at h
  | le a b => simp [senkFrag] at h
  | eq a b => simp [senkFrag] at h
  | fllt a b => simp [senkFrag] at h
  | flle a b => simp [senkFrag] at h
  | und a b => simp [senkFrag] at h
  | oder a b => simp [senkFrag] at h
  | nicht a => simp [senkFrag] at h
  | none n => simp [senkFrag] at h
  | some e => simp [senkFrag] at h
  | istSome e => simp [senkFrag] at h
  | fall cs i nutz => simp [senkFrag] at h
  | grund n r => simp [senkFrag] at h
  | forallSlots t body hL => simp [senkFrag] at h
  | existsSlots t body hL => simp [senkFrag] at h
  | reaches t f hf a b hL => simp [senkFrag] at h

/-- GENERIC FRAGMENT CORRECTNESS: the lowered instruction list, run
    through the existing `lauf` sequencer, puts the modular word of the
    exact source value into the destination; memory is untouched, foreign
    registers and the stack pointer are kept. The per-shape flags facts
    live in the shape theorems (`senkAtom_korrekt_*`, `senkung_add/sub`). -/
theorem senkung_korrekt {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ (.int lo hi)) (dst tmp : Register)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hfr : Frisch abb dst tmp) (hrsp : dst ≠ Register.rsp ∧ tmp ≠ Register.rsp)
    (hrenv : EnvRepr ρ s.register abb)
    (prog : List Befehl) (hsenk : senkFrag abb e dst tmp = some prog) :
    ∃ s', lauf (prog.map fun b => ⟨b, (encode b).length⟩) s = some s' ∧
      s'.register dst = intWort (eval σ₀ e σ ρ).n ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → q ≠ tmp → s'.register q = s.register q) ∧
      s'.register Register.rsp = s.register Register.rsp := by
  match istFrag_von_senkFrag abb e dst tmp prog hsenk with
  | .lit n =>
    have haa : senkAtom abb (Expr.lit (D := D) (Γ := Γ) (Λ := Λ) n) dst =
        some [Befehl.movImm64 dst (intWort n)] := by
      simp only [senkAtom]
    obtain ⟨s', hrun, hval, hmem, hreg, hfl⟩ :=
      senkAtom_korrekt_lit abb n dst ρ σ₀ σ s _ haa
    exact ⟨s', hrun, hval, hmem, fun q hqd hqt => hreg q hqd,
      hreg _ (Ne.symm hrsp.1)⟩
  | .var x =>
    have hab : senkAtom abb (Expr.var (D := D) (Γ := Γ) (Λ := Λ) x) dst =
        some [Befehl.movReg64 dst (abb _ x)] := by
      simp only [senkAtom]
    obtain ⟨s', hrun, hval, hmem, hreg, hfl⟩ :=
      senkAtom_korrekt_var abb x dst ρ σ₀ σ s hrenv _ hab
    exact ⟨s', hrun, hval, hmem, fun q hqd hqt => hreg q hqd,
      hreg _ (Ne.symm hrsp.1)⟩
  | .add a b pa pb ha hb =>
    obtain ⟨s', hrun, hval, hmem, hregs, hrsp', hflags⟩ :=
      senkung_add abb a b dst tmp ρ σ₀ σ s hfr hrsp hrenv pa pb ha hb
    exact ⟨s', hrun, hval, hmem, hregs, hrsp'⟩
  | .sub a b pa pb ha hb =>
    obtain ⟨s', hrun, hval, hmem, hregs, hrsp', hflags⟩ :=
      senkung_sub abb a b dst tmp ρ σ₀ σ s hfr hrsp hrenv pa pb ha hb
    exact ⟨s', hrun, hval, hmem, hregs, hrsp'⟩

/- CUTS:
    Conversion homomorphism (`intWort_add/sub`), the signed roundtrip
    (`intWort_sint`), the lowering-correctness theorems, the overflow-bound
    theorem and the fetched-byte witness are not proved yet.
    Unsupported expression forms refuse with `none` (two planted refusals).
-/

end Gabbro.Grammatik.X86
