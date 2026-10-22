/-
  File:      Grammatik/Gen/Fein/Suche.lean
  Subject:   THE SEARCH for fine-cell witnesses (untrusted: what it finds is checked by the kernel in the witness files).

  The clauses of the generator (`exprS`, `stmtS`, `blockS`, `endS`) build the terms of every size from the terms below;
  here every bucket keeps only the terms that bring a fine cell no smaller term of the same context brought
  (`neuFilter`). So the tables stay small, and every fine cell the clauses can reach under the size bound is still in
  some kept term of its context. The tables are the ones of `Gen/Erzeuger/Knoten.lean` with that filter.
-/
import Grammatik.Gen.Fein.Zellen
import Grammatik.Gen.Abdeckung.Waehlen
import Std.Data.HashSet
import Grammatik.Gen.Abdeckung.Satz.ErzeugtMN

namespace Gabbro.Grammatik.Gen.Fein

open Gabbro.Grammatik Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

/-- Keep the elements that bring a cell not yet seen; the cells seen afterwards. -/
def neuFilter {α : Type} (cz : α → List FZelle) (seen : Std.HashSet FZelle) (xs : List α) :
    List α × Std.HashSet FZelle :=
  let r := xs.foldl (fun (acc : Array α × Std.HashSet FZelle) x =>
    let cs := cz x
    if cs.any (fun c => !acc.2.contains c) then (acc.1.push x, cs.foldl (fun s c => s.insert c) acc.2) else acc)
    (#[], seen)
  (r.1.toList, r.2)

deriving instance Hashable for Ty

/-- Keep the elements that bring a cell not yet seen or a key not yet seen (one representative per key). -/
def neuFilterK {α κ : Type} [BEq κ] [Hashable κ] (cz : α → List FZelle) (rk : α → Option κ) (seen : Std.HashSet FZelle)
    (keys : Std.HashSet κ) (xs : List α) : List α :=
  (xs.foldl (fun (acc : Array α × Std.HashSet FZelle × Std.HashSet κ) x =>
    let cs := cz x
    let k := rk x
    if cs.any (fun c => !acc.2.1.contains c) || k.any (fun k => !acc.2.2.contains k) then
      (acc.1.push x, cs.foldl (fun s c => s.insert c) acc.2.1, match k with | some k => acc.2.2.insert k | none => acc.2.2)
    else acc) (#[], seen, keys)).1.toList

/-- The cells of a list of lists. -/
def gesehen {α : Type} (cz : α → List FZelle) (xss : List (List α)) : Std.HashSet FZelle :=
  xss.foldl (fun s xs => xs.foldl (fun s x => (cz x).foldl (fun s c => s.insert c) s) s) {}

variable {D : Deklaration} [Aufz D] [Zahlen]

/-- Buckets `0 .. n`, each step seeing the buckets below. -/
def bucketsL {β : Type} (leer : β) (step : List β → Nat → β) : Nat → List β
  | 0 => [leer]
  | n + 1 => let p := bucketsL leer step n; p ++ [step p (n + 1)]

/-- A cached expression table of one context. -/
structure EEintrag (D : Deklaration) where
  Γ : Ctx
  Λ : List (Res D)
  t : Thunk (List (List (SE D Γ Λ)))

/-- The cached table of a context, if there is one. -/
def findeE (cs : List (EEintrag D)) (Γ : Ctx) (Λ : List (Res D)) : Option (List (List (SE D Γ Λ))) :=
  cs.findSome? fun c => if h : c.Γ = Γ ∧ c.Λ = Λ then some (by obtain ⟨h1, h2⟩ := h; exact h1 ▸ h2 ▸ c.t.get) else none

/-- A singleton integer type: the type of a literal (a divisor, a shift width, a mask needs its value). -/
def einzeln : Ty → Bool
  | .int lo hi => lo == hi
  | _ => false

/-- **What makes a term new**: the cells a term brings, per family (the fine cells; the coverage driver adds the
    register members). -/
structure Kenner (D : Deklaration) where
  e : ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}, Expr D Γ Λ τ → List FZelle
  s : ∀ {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}, Stmt D V l Γ Λ Λ' → List FZelle
  b : ∀ {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}, Block D V l Γ Λ Λ' → List FZelle
  n : ∀ {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}, Endblock D V l Γ Λ → List FZelle

/-- The fine cells. -/
def Kenner.fein : Kenner D := ⟨fzE, fzS, fzB, fzEnd⟩

/-- The key of an expression: its exact type and its constructor (a parent that needs a child of this constructor
    at exactly this type finds one). -/
def eSchl {Γ : Ctx} {Λ : List (Res D)} (p : SE D Γ Λ) : Option (Ty × Nat) :=
  if Zahlen.bindOk p.1 || einzeln p.1 then some (p.1, kE p.2) else none

/-- The filtered expressions of one context by size; the bodies of the quantifiers are built once per table. -/
def genEF (K : Kenner D) : Nat → Nat → (Γ : Ctx) → (Λ : List (Res D)) → List (List (SE D Γ Λ))
  | 0, n, _, _ => List.replicate (n + 1) []
  | f + 1, n, Γ, Λ =>
    let qs : List (EEintrag D) := Aufz.tab.map fun t =>
      ⟨.index (D.count t) :: Γ, Λ, Thunk.mk fun _ => genEF K f n (.index (D.count t) :: Γ) Λ⟩
    bucketsL [] (fun prev k =>
      neuFilterK (fun (p : SE D Γ Λ) => K.e p.2) eSchl (gesehen (fun (p : SE D Γ Λ) => K.e p.2) prev)
        (prev.foldl (fun s b => b.foldl (fun s p => match eSchl p with | some k => s.insert k | none => s) s) {})
        (exprS (fun Γ' j => tab ((findeE qs Γ' Λ).getD (genEF K f j Γ' Λ))) (tab prev) k)) n

section
variable {V : Vertrag D}

/-- One filtered bucket. -/
def schrittF (K : Kenner D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (O : Orakel V) (E : Sz (SE D Γ Λ))
    (prev : List (Eimer V l Γ Λ)) (k : Nat) : Eimer V l Γ Λ :=
  let (s, b, e) := schritt O E prev k
  let cS := fun (p : SS D V l Γ Λ) => K.s p.2
  let cB := fun (p : SB D V l Γ Λ) => K.b p.2
  let cN := fun (x : Endblock D V l Γ Λ) => K.n x
  ((neuFilter cS (gesehen cS (prev.map (·.1))) s).1,
   (neuFilter cB (gesehen cB (prev.map (·.2.1))) b).1,
   (neuFilter cN (gesehen cN (prev.map (·.2.2))) e).1)

/-- The size bound of the expressions in the tables (the expression cells are all reached by size 5). -/
def eGrenze : Nat := 5

/-- **The filtered table of a context by size**, by fuel. -/
def genTF (K : Kenner D) (V : Vertrag D) (cap : Nat) : Nat → Nat → (l : Bool) → (Γ : Ctx) → (Λ : List (Res D)) → List (Eimer V l Γ Λ)
  | _, 0, _, _, _ => [([], [], [])]
  | 0, n + 1, _, _, _ => List.replicate (n + 2) ([], [], [])
  | f + 1, n + 1, l, Γ, Λ =>
    let Et := genEF K (min n eGrenze) (min n eGrenze) Γ Λ
    let gen := fun m l' Γ' Λ' => genTF K V cap f (if l' = l then min m cap else m) l' Γ' Λ'
    let cs := (knotenKeysG (n + 1) l Γ Λ Et).map (CEintrag.neu V gen)
    let exK : List (Ctx × List (Res D)) := (knotenKeysG (n + 1) l Γ Λ Et).map (fun k => (k.2.1, k.2.2.1)) |>.eraseDups
    let ec : List (EEintrag D) := exK.map fun k => ⟨k.1, k.2, Thunk.mk fun _ => genEF K (min n eGrenze) (min n eGrenze) k.1 k.2⟩
    let O : Orakel V :=
      { ex := fun Γ' Λ' m => tab ((findeE ec Γ' Λ').getD (genEF K (min m eGrenze) (min m eGrenze) Γ' Λ'))
        bl := fun l' Γ' Λ' m => tabB (findeOder cs l' Γ' Λ' m fun _ => gen m l' Γ' Λ')
        en := fun l' Γ' Λ' m => tabN (findeOder cs l' Γ' Λ' m fun _ => gen m l' Γ' Λ') }
    bucketsL ([], [], []) (fun prev k => schrittF K O (tab Et) prev k) (n + 1)

end

/-- The filtered bodies of a function, all sizes up to `n`. -/
def rumpfF (f : D.Fn) (n cap : Nat) : List (Rumpf D f) :=
  (genTF Kenner.fein (vertragVon D f) cap n n false (D.params f) (Signatur.anfang D (D.signatur f))).flatMap (·.2.2)

/-- The filtered `requires` and `ensures` of a function. -/
def reqF (f : D.Fn) (n : Nat) : List (Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool) :=
  (genEF Kenner.fein n n _ _).flatMap fun b => b.filterMap fun p => ofTy [p] .bool |>.head?

def ensF (f : D.Fn) (n : Nat) : List (Expr D (ErgCtx (D.params f) (D.erg f)) (vertragVon D f).ende .bool) :=
  (genEF Kenner.fein n n _ _).flatMap fun b => b.filterMap fun p => ofTy [p] .bool |>.head?

/-- **The candidates of a member**: the program whose every body is the first filtered body of its function, and the
    programs that differ from it in one body or one contract. -/
def kandidaten (z : Spez) (nb nc cap : Nat) : List (Programm z.deklaration) :=
  letI : Zahlen := z.zahlen
  let D := z.deklaration
  let tabs : List (Σ f : D.Fn, List (Rumpf D f)) := z.fnListe.map fun f => ⟨f, rumpfF f nb cap⟩
  let basis : ∀ f : D.Fn, Option (Rumpf D f) := fun f => ((ofTy tabs f).headD []).head?
  if hall : z.fnListe.all (fun f => (basis f).isSome) = true then
    let b0 : ∀ f : D.Fn, Rumpf D f := fun f => (basis f).get (by
      have := List.all_eq_true.1 hall f (List.mem_finRange f); simpa using this)
    let P0 : Programm D := Programm.mk (fun _ => .tru) (fun _ => .tru) (fun _ => .tru) b0 (fun _ => false)
    let rs := tabs.flatMap fun ⟨f, bs⟩ => bs.map fun b =>
      { P0 with rumpf := fun g => if h : f = g then h ▸ b else b0 g }
    let vs := z.fnListe.flatMap fun f =>
      (reqF f nc).map (fun e => { P0 with requires := fun g => if h : f = g then h ▸ e else .tru }) ++
      (ensF f nc).map (fun e => { P0 with ensures := fun g => if h : f = g then h ▸ e else .tru })
    rs ++ vs
  else []

/-! ## Packing: many bodies in one program -/

section
variable {V : Vertrag D}

/-- End blocks as the `else` branches of a chain of `check false`. -/
def packe {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : List (Endblock D V l Γ Λ) → Block D V l Γ Λ Λ
  | [] => .nil
  | e :: es => .check .fls e (packe es)

/-- **A packed body**: the end blocks `es` in a branch that is never taken (`if true` around the chain of
    `check false`, each with one of them as its `else`), then the end block `letzt`. -/
def gepackt {Γ : Ctx} {Λ : List (Res D)} (es : List (Endblock D V false Γ Λ)) (letzt : Endblock D V false Γ Λ) :
    Endblock D V false Γ Λ :=
  .cons (.ite .tru (packe es) .nil) letzt

end

/-- A valid program of a member under some start parameter, with its proof. -/
def gutVon (z : Spez) (P : Programm z.deklaration) : Option (Gutes z) :=
  z.parameter.findSome? fun ws => (match z.erzeugeAus P ws with
    | some (.gut g) => some g
    | _ => none)

/-- **The packed programs of a member**: the filtered bodies of every function are added one after the other to the
    packed body of their function as long as the program stays valid; a program is emitted when one function holds
    `k` bodies. Then the contract variants, each alone. -/
def packen (z : Spez) (nb nc cap k : Nat) : List (Gutes z) :=
  letI : Zahlen := z.zahlen
  let D := z.deklaration
  let tabs : List (Σ f : D.Fn, List (Rumpf D f)) := z.fnListe.map fun f => ⟨f, rumpfF f nb cap⟩
  let basis : ∀ f : D.Fn, Option (Rumpf D f) := fun f => ((ofTy tabs f).headD []).head?
  if hall : z.fnListe.all (fun f => (basis f).isSome) = true then
    let b0 : ∀ f : D.Fn, Rumpf D f := fun f => (basis f).get (by
      have := List.all_eq_true.1 hall f (List.mem_finRange f); simpa using this)
    let prog : (∀ f : D.Fn, List (Rumpf D f)) → Programm D := fun L =>
      Programm.mk (fun _ => .tru) (fun _ => .tru) (fun _ => .tru)
        (fun f => if (L f).isEmpty then b0 f else gepackt (L f) (b0 f)) (fun _ => false)
    let leer : ∀ f : D.Fn, List (Rumpf D f) := fun _ => []
    let paare : List (Σ f : D.Fn, Rumpf D f) := tabs.flatMap fun ⟨f, bs⟩ => bs.map fun b => ⟨f, b⟩
    let r := paare.foldl (fun (acc : (∀ f : D.Fn, List (Rumpf D f)) × Nat × Option (Gutes z) × Array (Gutes z)) p =>
      let (L, n, g, out) := acc
      let L' : ∀ f : D.Fn, List (Rumpf D f) := fun f => if h : p.1 = f then L f ++ [h ▸ p.2] else L f
      match gutVon z (prog L') with
      | none => acc
      | some g' =>
        if n + 1 ≥ k then (leer, 0, none, out.push g') else (L', n + 1, some g', out)) (leer, 0, none, #[])
    let out := match r.2.2.1 with | some g => r.2.2.2.push g | none => r.2.2.2
    let P0 := prog leer
    let vs := z.fnListe.flatMap fun f =>
      (reqF f nc).map (fun e => { P0 with requires := fun g => if h : f = g then h ▸ e else .tru }) ++
      (ensF f nc).map (fun e => { P0 with ensures := fun g => if h : f = g then h ▸ e else .tru })
    out.toList ++ vs.filterMap (gutVon z)
  else []

end Gabbro.Grammatik.Gen.Fein
