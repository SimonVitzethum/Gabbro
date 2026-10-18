/-
  File:      Grammatik/Gen/Erzeuger/Ausdruck.lean
  Subject:   The generator of EXPRESSIONS (`Expr`, `NutzlastExpr`) and its COMPLETENESS: every typed expression of
             size at most `n` is in `genExpr n Γ Λ`. One clause per constructor of the model; the proof of
             completeness cases on the term, so a constructor without a clause stops the build (new syntax shows
             up as a gap by itself).

  The size counts every node, every free number (a literal, a bound of a widening, a width, a count) by its
  magnitude, and every enumeration index by one; what the typing determines (the ranges a sum or a product
  computes) is not counted, because it is read off the subterms' types.
-/
import Grammatik.Gen.Erzeuger.Grund

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable {D : Deklaration}

/-- The size of a sum case: the case once, a payload bound by its magnitude. -/
def groesseFall : Option (Int × Int) → Nat
  | none => 1
  | some (lo, hi) => 1 + lo.natAbs + hi.natAbs

/-- The size of a list of sum cases. -/
def groesseFaelle : List (Option (Int × Int)) → Nat
  | [] => 0
  | c :: cs => groesseFall c + groesseFaelle cs

theorem length_le_groesseFaelle (cs : List (Option (Int × Int))) : cs.length ≤ groesseFaelle cs := by
  induction cs with
  | nil => simp [groesseFaelle]
  | cons c cs ih => cases c <;> simp only [groesseFaelle, groesseFall, List.length_cons] <;> omega

theorem mem_groesseFaelle {cs : List (Option (Int × Int))} {lo hi : Int} (h : some (lo, hi) ∈ cs) :
    lo.natAbs + hi.natAbs ≤ groesseFaelle cs := by
  induction cs with
  | nil => simp at h
  | cons c cs ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp only [groesseFaelle, groesseFall]; omega
    · have := ih h
      cases c <;> simp only [groesseFaelle, groesseFall] <;> omega

mutual
def groesseExpr : ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}, Expr D Γ Λ τ → Nat
  | _, _, _, .lit n => 1 + n.natAbs
  | _, _, _, .tru => 1
  | _, _, _, .fls => 1
  | _, _, _, .var x => 1 + groesseVar x
  | _, _, _, .glob _ _ => 1
  | _, _, _, .slot _ _ i _ => 1 + groesseExpr i
  | _, _, _, .thru p _ _ _ i _ => 1 + groesseExpr p + groesseExpr i
  | _, _, _, .ptrOf _ n _ _ => 1 + n
  | _, _, _, .fnref _ _ _ => 1
  | _, _, _, .oldG _ _ => 1
  | _, _, _, .oldS _ _ i _ => 1 + groesseExpr i
  | _, _, _, @Expr.widen _ lo' _ _ hi' _ _ _ _ e => 1 + lo'.natAbs + hi'.natAbs + groesseExpr e
  | _, _, _, .add a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .sub a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .neg a => 1 + groesseExpr a
  | _, _, _, .mul a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .div _ _ a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .rem _ _ a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .sdiv _ a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .srem _ a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .getBytes _ _ _ n i _ _ _ => 1 + n + groesseExpr i
  | _, _, _, .band _ _ a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .bor w _ _ _ _ a b => 1 + w + groesseExpr a + groesseExpr b
  | _, _, _, .bxor w _ _ _ _ a b => 1 + w + groesseExpr a + groesseExpr b
  | _, _, _, .shl w _ _ _ _ a b => 1 + w + groesseExpr a + groesseExpr b
  | _, _, _, .shr w _ _ _ _ a b => 1 + w + groesseExpr a + groesseExpr b
  | _, _, _, .lt a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .le a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .eq a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .fllt a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .flle a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .and a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .or a b => 1 + groesseExpr a + groesseExpr b
  | _, _, _, .not a => 1 + groesseExpr a
  | _, _, _, .none n => 1 + n.natAbs
  | _, _, _, @Expr.some _ _ _ n e => 1 + n.natAbs + groesseExpr e
  | _, _, _, .istSome e => 1 + groesseExpr e
  | _, _, _, .case cs _ nutz => 1 + groesseFaelle cs + groesseNutz nutz
  | _, _, _, .why n _ => 1 + n
  | _, _, _, .forallSlots _ body _ => 1 + groesseExpr body
  | _, _, _, .existsSlots _ body _ => 1 + groesseExpr body
  | _, _, _, .reaches _ _ _ a b _ => 1 + groesseExpr a + groesseExpr b

def groesseNutz : ∀ {Γ : Ctx} {Λ : List (Res D)} {o : Option (Int × Int)}, NutzlastExpr D Γ Λ o → Nat
  | _, _, _, .empty => 1
  | _, _, _, .num e => 1 + groesseExpr e
end


/-! ## The clauses -/

variable {Γ : Ctx} {Λ : List (Res D)}

/-- A typed expression with its type: the elements the generator lists. -/
abbrev SE (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) : Type := Σ τ, Expr D Γ Λ τ

/-- The integer-typed terms of a list, one at a time. -/
def mitInt (es : List (SE D Γ Λ))
    (f : ∀ {lo hi : Int}, Expr D Γ Λ (.int lo hi) → List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  es.flatMap fun p => match p with
    | ⟨.int _ _, a⟩ => f a
    | _ => []

/-- Pairs of integer-typed terms. -/
def mitInt2 (es : List (SE D Γ Λ))
    (f : ∀ {l1 h1 l2 h2 : Int}, Expr D Γ Λ (.int l1 h1) → Expr D Γ Λ (.int l2 h2) → List (SE D Γ Λ)) :
    List (SE D Γ Λ) :=
  es.flatMap fun p => es.flatMap fun q => match p, q with
    | ⟨.int _ _, a⟩, ⟨.int _ _, b⟩ => f a b
    | _, _ => []

/-- Pairs of float-typed terms. -/
def mitFl2 (es : List (SE D Γ Λ))
    (f : ∀ {l1 h1 l2 h2 : Int × Int}, Expr D Γ Λ (.fl l1 h1) → Expr D Γ Λ (.fl l2 h2) → List (SE D Γ Λ)) :
    List (SE D Γ Λ) :=
  es.flatMap fun p => es.flatMap fun q => match p, q with
    | ⟨.fl _ _, a⟩, ⟨.fl _ _, b⟩ => f a b
    | _, _ => []

theorem mem_mitInt {es : List (SE D Γ Λ)} {f} {lo hi : Int} {a : Expr D Γ Λ (.int lo hi)} {x}
    (ha : (⟨.int lo hi, a⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a) : x ∈ mitInt es f := by
  unfold mitInt
  rw [List.mem_flatMap]
  exact ⟨_, ha, hx⟩

theorem mem_mitInt2 {es : List (SE D Γ Λ)} {f} {l1 h1 l2 h2 : Int} {a : Expr D Γ Λ (.int l1 h1)}
    {b : Expr D Γ Λ (.int l2 h2)} {x}
    (ha : (⟨.int l1 h1, a⟩ : SE D Γ Λ) ∈ es) (hb : (⟨.int l2 h2, b⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a b) :
    x ∈ mitInt2 es f := by
  unfold mitInt2
  rw [List.mem_flatMap]
  refine ⟨_, ha, ?_⟩
  rw [List.mem_flatMap]
  exact ⟨_, hb, hx⟩

theorem mem_mitFl2 {es : List (SE D Γ Λ)} {f} {l1 h1 l2 h2 : Int × Int} {a : Expr D Γ Λ (.fl l1 h1)}
    {b : Expr D Γ Λ (.fl l2 h2)} {x}
    (ha : (⟨.fl l1 h1, a⟩ : SE D Γ Λ) ∈ es) (hb : (⟨.fl l2 h2, b⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a b) :
    x ∈ mitFl2 es f := by
  unfold mitFl2
  rw [List.mem_flatMap]
  refine ⟨_, ha, ?_⟩
  rw [List.mem_flatMap]
  exact ⟨_, hb, hx⟩

/-- Sum-case lists: at most `k` cases, every bound at most `m` in magnitude. -/
def listenBis (m : Nat) : Nat → List (List (Option (Int × Int)))
  | 0 => [[]]
  | k + 1 => [] :: ((none :: ((ints m).flatMap fun lo => (ints m).map fun hi => some (lo, hi))).flatMap
      fun c => (listenBis m k).map (c :: ·))

theorem mem_listenBis (m : Nat) : ∀ (k : Nat) (cs : List (Option (Int × Int))), cs.length ≤ k →
    (∀ c ∈ cs, ∀ lo hi, c = some (lo, hi) → lo.natAbs ≤ m ∧ hi.natAbs ≤ m) → cs ∈ listenBis m k := by
  intro k
  induction k with
  | zero => intro cs h _; cases cs with
    | nil => simp [listenBis]
    | cons c cs => simp at h
  | succ k ih =>
    intro cs h hb
    cases cs with
    | nil => simp [listenBis]
    | cons c cs =>
      have hc : c ∈ (none :: ((ints m).flatMap fun lo => (ints m).map fun hi => some (lo, hi))) := by
        cases c with
        | none => exact List.mem_cons_self
        | some p =>
          obtain ⟨lo, hi⟩ := p
          have := hb (some (lo, hi)) List.mem_cons_self lo hi rfl
          exact List.mem_cons_of_mem _
            (List.mem_flatMap.2 ⟨lo, mem_ints this.1, List.mem_map.2 ⟨hi, mem_ints this.2, rfl⟩⟩)
      have hr := ih cs (by simpa using h) (fun c' hc' => hb c' (List.mem_cons_of_mem _ hc'))
      show _ ∈ [] :: _
      exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨c, hc, List.mem_map.2 ⟨cs, hr, rfl⟩⟩)

/-- The `Nutzlast` terms of an index, from a list of typed terms. -/
def nutzAt (es : List (SE D Γ Λ)) : (o : Option (Int × Int)) → List (NutzlastExpr D Γ Λ o)
  | none => [.empty]
  | some (lo, hi) => (ofTy es (.int lo hi)).map NutzlastExpr.num

theorem mem_nutzAt {es : List (SE D Γ Λ)} {m : Nat}
    (hes : ∀ τ (e : Expr D Γ Λ τ), groesseExpr e ≤ m → (⟨τ, e⟩ : SE D Γ Λ) ∈ es) :
    ∀ (o : Option (Int × Int)) (x : NutzlastExpr D Γ Λ o), groesseNutz x ≤ m + 1 → x ∈ nutzAt es o := by
  intro o x h
  cases x with
  | empty => simp [nutzAt]
  | num e =>
    simp only [nutzAt, List.mem_map]
    simp only [groesseNutz] at h
    exact ⟨e, mem_ofTy (hes _ e (by omega)), rfl⟩

def gLit (m : Nat) : List (SE D Γ Λ) := (ints m).map fun k => ⟨.int k k, .lit k⟩

def gBool : List (SE D Γ Λ) := [⟨.bool, .tru⟩, ⟨.bool, .fls⟩]

def gVar (Γ : Ctx) (Λ : List (Res D)) : List (SE D Γ Λ) := (genVar Γ).map fun p => ⟨p.1, .var p.2⟩

def gGlob [Aufz D] : List (SE D Γ Λ) :=
  Aufz.glob.flatMap fun g => if h : gdarf D g Λ then [⟨D.gtyp g, .glob g h⟩] else []

def gOldG [Aufz D] : List (SE D Γ Λ) :=
  Aufz.glob.flatMap fun g => if h : gdarf D g Λ then [⟨D.gtyp g, .oldG g h⟩] else []

def gSlot [Aufz D] (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  Aufz.tab.flatMap fun t => (Aufz.feld t).flatMap fun f => (ofTy es (.index (D.count t))).flatMap fun i =>
    if h : darf D t Λ then [⟨D.typ t f, .slot t f i h⟩] else []

def gOldS [Aufz D] (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  Aufz.tab.flatMap fun t => (Aufz.feld t).flatMap fun f => (ofTy es (.index (D.count t))).flatMap fun i =>
    if h : darf D t Λ then [⟨D.typ t f, .oldS t f i h⟩] else []

def gThru [Aufz D] (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  es.flatMap fun p => match p with
    | ⟨.ptr n _, q⟩ => Aufz.tab.flatMap fun t => if ht : D.tabNr n = some t then
        (Aufz.feld t).flatMap fun f => (ofTy es (.index (D.count t))).flatMap fun i =>
          if hL : darf D t Λ then [⟨D.typ t f, .thru q t ht f i hL⟩] else []
      else []
    | _ => []

def gPtrOf [Aufz D] (m : Nat) : List (SE D Γ Λ) :=
  (List.range (m + 1)).flatMap fun (n : Nat) => Aufz.tab.flatMap fun t =>
    if ht : D.tabNr n = some t then [true, false].map fun rw => ⟨.ptr n rw, .ptrOf t n ht rw⟩ else []

def gFnref [Aufz D] : List (SE D Γ Λ) := Aufz.fn.map fun f => ⟨.fnptr (D.sig f), .fnref f (D.sig f) rfl⟩

def gWiden (m : Nat) (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  mitInt es fun {lo hi} e => (ints m).flatMap fun lo' => (ints m).flatMap fun hi' =>
    if h1 : lo' ≤ lo then if h2 : hi ≤ hi' then [⟨.int lo' hi', .widen h1 h2 e⟩] else [] else []

def gAdd (es : List (SE D Γ Λ)) : List (SE D Γ Λ) := mitInt2 es fun a b => [⟨_, .add a b⟩]
def gSub (es : List (SE D Γ Λ)) : List (SE D Γ Λ) := mitInt2 es fun a b => [⟨_, .sub a b⟩]
def gMul (es : List (SE D Γ Λ)) : List (SE D Γ Λ) := mitInt2 es fun a b => [⟨_, .mul a b⟩]
def gNeg (es : List (SE D Γ Λ)) : List (SE D Γ Λ) := mitInt es fun a => [⟨_, .neg a⟩]

def gDiv (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  mitInt2 es fun {l1 _ l2 _} a b => if p0 : 0 ≤ l1 then if p1 : 1 ≤ l2 then [⟨_, .div p0 p1 a b⟩] else [] else []

def gRem (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  mitInt2 es fun {l1 _ l2 _} a b => if p0 : 0 ≤ l1 then if p1 : 1 ≤ l2 then [⟨_, .rem p0 p1 a b⟩] else [] else []

def gSdiv (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  mitInt2 es fun {_ _ l2 h2} a b => if hb : 1 ≤ l2 ∨ h2 ≤ -1 then [⟨_, .sdiv hb a b⟩] else []

def gSrem (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  mitInt2 es fun {_ _ l2 h2} a b => if hb : 1 ≤ l2 ∨ h2 ≤ -1 then [⟨_, .srem hb a b⟩] else []

def gGetBytes [Aufz D] (m : Nat) (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  Aufz.tab.flatMap fun t => (Aufz.feld t).flatMap fun f =>
    if hf : D.typ t f = .int 0 255 then (List.range (m + 1)).flatMap fun (n : Nat) =>
      mitInt es fun {lo hi} i => if hlo : 0 ≤ lo then if hhi : hi + (n : Int) ≤ D.count t then
        if hL : darf D t Λ then [⟨_, .getBytes t f hf n i hlo hhi hL⟩] else [] else [] else []
    else []

def gBand (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  mitInt2 es fun {l1 _ l2 _} a b => if p0 : 0 ≤ l1 then if p1 : 0 ≤ l2 then [⟨_, .band p0 p1 a b⟩] else [] else []

def gBor (m : Nat) (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  (List.range (m + 1)).flatMap fun (w : Nat) => mitInt2 es fun {l1 h1 l2 h2} a b =>
    if p0 : 0 ≤ l1 then if p1 : 0 ≤ l2 then if q1 : h1 < 2 ^ w then if q2 : h2 < 2 ^ w then
      [⟨_, .bor w p0 p1 q1 q2 a b⟩] else [] else [] else [] else []

def gBxor (m : Nat) (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  (List.range (m + 1)).flatMap fun (w : Nat) => mitInt2 es fun {l1 h1 l2 h2} a b =>
    if p0 : 0 ≤ l1 then if p1 : 0 ≤ l2 then if q1 : h1 < 2 ^ w then if q2 : h2 < 2 ^ w then
      [⟨_, .bxor w p0 p1 q1 q2 a b⟩] else [] else [] else [] else []

def gShl (m : Nat) (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  (List.range (m + 1)).flatMap fun (w : Nat) => mitInt2 es fun {l1 h1 l2 h2} a b =>
    if q1 : h1 < 2 ^ w then if q2 : h2 < (w : Int) then if p0 : 0 ≤ l1 then if p1 : 0 ≤ l2 then
      [⟨_, .shl w q1 q2 p0 p1 a b⟩] else [] else [] else [] else []

def gShr (m : Nat) (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  (List.range (m + 1)).flatMap fun (w : Nat) => mitInt2 es fun {l1 h1 l2 h2} a b =>
    if q1 : h1 < 2 ^ w then if q2 : h2 < (w : Int) then if p0 : 0 ≤ l1 then if p1 : 0 ≤ l2 then
      [⟨_, .shr w q1 q2 p0 p1 a b⟩] else [] else [] else [] else []

def gLt (es : List (SE D Γ Λ)) : List (SE D Γ Λ) := mitInt2 es fun a b => [⟨.bool, .lt a b⟩]
def gLe (es : List (SE D Γ Λ)) : List (SE D Γ Λ) := mitInt2 es fun a b => [⟨.bool, .le a b⟩]
def gEq (es : List (SE D Γ Λ)) : List (SE D Γ Λ) := mitInt2 es fun a b => [⟨.bool, .eq a b⟩]
def gFllt (es : List (SE D Γ Λ)) : List (SE D Γ Λ) := mitFl2 es fun a b => [⟨.bool, .fllt a b⟩]
def gFlle (es : List (SE D Γ Λ)) : List (SE D Γ Λ) := mitFl2 es fun a b => [⟨.bool, .flle a b⟩]

def gAnd (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  (ofTy es .bool).flatMap fun a => (ofTy es .bool).map fun b => ⟨.bool, .and a b⟩
def gOr (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  (ofTy es .bool).flatMap fun a => (ofTy es .bool).map fun b => ⟨.bool, .or a b⟩
def gNot (es : List (SE D Γ Λ)) : List (SE D Γ Λ) := (ofTy es .bool).map fun a => ⟨.bool, .not a⟩

def gNone (m : Nat) : List (SE D Γ Λ) := (ints m).map fun k => ⟨.opt k, .none k⟩

def gSome (m : Nat) (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  (ints m).flatMap fun k => (ofTy es (.index k)).map fun e => ⟨.opt k, .some e⟩

def gIstSome (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  es.flatMap fun p => match p with
    | ⟨.opt _, e⟩ => [⟨.bool, .istSome e⟩]
    | _ => []

def gCase (m : Nat) (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  (listenBis m m).flatMap fun cs => (List.finRange cs.length).flatMap fun i =>
    (nutzAt es (cs.get i)).map fun nutz => ⟨.sum cs, .case cs i nutz⟩

def gWhy (m : Nat) : List (SE D Γ Λ) :=
  (List.range (m + 1)).flatMap fun (n : Nat) => (List.finRange n).map fun r => ⟨.why n, .why n r⟩

def gForall [Aufz D] (rek : ∀ Γ' : Ctx, List (SE D Γ' Λ)) : List (SE D Γ Λ) :=
  Aufz.tab.flatMap fun t => (ofTy (rek (.index (D.count t) :: Γ)) .bool).flatMap fun body =>
    if h : darf D t Λ then [⟨.bool, .forallSlots t body h⟩] else []

def gExists [Aufz D] (rek : ∀ Γ' : Ctx, List (SE D Γ' Λ)) : List (SE D Γ Λ) :=
  Aufz.tab.flatMap fun t => (ofTy (rek (.index (D.count t) :: Γ)) .bool).flatMap fun body =>
    if h : darf D t Λ then [⟨.bool, .existsSlots t body h⟩] else []

def gReaches [Aufz D] (es : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  Aufz.tab.flatMap fun t => (Aufz.feld t).flatMap fun f =>
    if hf : D.typ t f = .opt (D.count t) then (ofTy es (.index (D.count t))).flatMap fun a =>
      (ofTy es (.index (D.count t))).flatMap fun b =>
        if hL : darf D t Λ then [⟨.bool, .reaches t f hf a b hL⟩] else []
    else []

end Gabbro.Grammatik.Gen
