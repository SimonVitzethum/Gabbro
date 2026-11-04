/- Bridge numeric source old(global) to the existing G constructor without changing the shared parser.
   The ordinary elaborator resolves every name and type; source/side pairs are checked structurally.
   The caller checks the restored program with the full AkzeptiertX, never the temporary program. -/
module
public import Grammatik.Parser.Cover.Differenz
@[expose] public section


namespace Gabbro.Stage0.OldSource
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz Gabbro.Grammatik.Zielsatz

/-- Only these source forms participate in the numeric entry-global bridge. -/
def hasEntry : SExpr → Bool
  | .ext .imp [] [a, b] => hasEntry a || hasEntry b
  | .old (.variable _) => true
  | .bin _ a b => hasEntry a || hasEntry b
  | .un _ a => hasEntry a
  | _ => false

def normalize : SExpr → SExpr
  | .ext .imp [] [a, b] => .ext .imp [] [normalize a, normalize b]
  | .old (.variable g) => .variable g
  | .bin op a b => .bin op (normalize a) (normalize b)
  | .un op a => .un op (normalize a)
  | e => e

def normalizeItem : SItemTief → SItemTief
  | .fnT sig body => .fnT {sig with klauseln := sig.klauseln.map fun k => match k with
      | .gives e => .gives (normalize e)
      | k => k} body
  | item => item

def clauses (items : List SItemTief) (name : String) : List SExpr :=
  match items.find? (fun item => match item with | .fnT sig _ => sig.name == name | _ => false) with
  | some (.fnT sig _) => sig.klauseln.filterMap fun k => match k with | .gives e => some e | _ => none
  | _ => []

/-- Preserve the declared type and guard proof when selecting the existing entry-read constructor. -/
def oldGlobal {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} :
    {τ : Ty} → Expr D Γ Λ τ → Except String (Expr D Γ Λ τ)
  | _, .glob g h => .ok (.oldG g h)
  | _, _ => .error "ir: old(global) did not resolve to a global read"

/-- Reuse the ordinary elaborator for every subtree without an entry-global occurrence. -/
def side (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty) :
    SExpr → USide → Except String (LowSide u Γ Λ)
  | src, val =>
    if !hasEntry src then lowSideEns u Γ Λ fn er val else
    match src, val with
    | .old (.variable name), .glob g => do
        if name != g then throw "ir: old(global) name mismatch"
        let s ← lowGlobSide u Γ Λ g
        let term ← oldGlobal s.term
        pure {s with term}
    | .bin "+" a b, .add x y => do
        pure (LowSide.plus (← side u Γ Λ fn er a x) (← side u Γ Λ fn er b y))
    | .bin "-" a b, .sub x y => do
        pure (LowSide.minus (← side u Γ Λ fn er a x) (← side u Γ Λ fn er b y))
    | .bin "*" a b, .mul x y => do
        pure (LowSide.times (← side u Γ Λ fn er a x) (← side u Γ Λ fn er b y))
    | .bin op a b, .ib2 bi width x y => do
        if uBinEin op != some bi then throw "ir: old(global) integer builtin mismatch"
        lowIb2 bi width (← side u Γ Λ fn er a x) (← side u Γ Λ fn er b y)
    | _, _ => .error "ir: unsupported source expression containing old(global)"
termination_by src _ => sizeOf src

/-- Numeric comparisons and Boolean structure preserve the source occurrence of old. -/
def predicate (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty) :
    SExpr → UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | src, val =>
    if !hasEntry src then lowEns u Γ Λ fn er val else
    match src, val with
    | .bin op a b, .cmp op' x y => do
        if op != op' then throw "ir: old(global) comparison mismatch"
        let a ← side u Γ Λ fn er a x
        let b ← side u Γ Λ fn er b y
        match op with
        | "==" => pure (.eq a.term b.term)
        | "!=" => pure (.not (.eq a.term b.term))
        | "<" => pure (.lt a.term b.term)
        | "<=" => pure (.le a.term b.term)
        | ">" => pure (.lt b.term a.term)
        | ">=" => pure (.le b.term a.term)
        | _ => throw "ir: unsupported old(global) comparison"
    | .ext .imp [] [a, b], .imp x y => do
        u.exportGate
        pure (.impl (← predicate u Γ Λ fn er a x) (← predicate u Γ Λ fn er b y))
    | .bin "&&" a b, .and x y => do
        pure (.and (← predicate u Γ Λ fn er a x) (← predicate u Γ Λ fn er b y))
    | .bin "||" a b, .or x y => do
        pure (.or (← predicate u Γ Λ fn er a x) (← predicate u Γ Λ fn er b y))
    | .un "!" a, .not x => do pure (.not (← predicate u Γ Λ fn er a x))
    | _, _ => .error "ir: unsupported source postcondition containing old(global)"
termination_by src _ => sizeOf src

def predicates (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty) :
    List SExpr → List UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | [], [] => pure .tru
  | a :: rest, x :: xs => do
      pure (.and (← predicate u Γ Λ fn er a x) (← predicates u Γ Λ fn er rest xs))
  | _, _ => .error "ir: old(global) postcondition count mismatch"

def atFunction (items : List SItemTief) (u : UProg) (P : Programm (declOf u))
    (f : Fin u.fns.length) : Except String (EnsTy u f) := do
  let src := clauses items (fnAt u f).name
  if !src.any hasEntry then return P.ensures f
  let e ← predicates u (ErgCtx (ctxOf u f) ((verOf u f).erg)) (verOf u f).ende
    (fnAt u f) (fnAt u f).ergTy src (fnAt u f).gives
  pure (by
    unfold EnsTy
    rw [← ensCtx_eq u f]
    exact e)

/-- Evaluate a dependent family once, retaining each result at its own index. -/
def collect : (n : Nat) → (T : Fin n → Type) → ((i : Fin n) → Except String (T i)) →
    Except String ((i : Fin n) → T i)
  | 0, _, _ => pure (fun i => nomatch i)
  | n + 1, T, get => do
      let head ← get 0
      let tail ← collect n (fun i => T i.succ) (fun i => get i.succ)
      pure (Fin.cases head tail)

def restore (items : List SItemTief) (u : UProg) (P : Programm (declOf u)) :
    Except String (Programm (declOf u)) := do
  let expanded ← expandU items
  let es ← collect u.fns.length (EnsTy u) (atFunction expanded.1 u P)
  pure {P with ensures := es}

/-- Entry-postcondition restoration preserves the exact invariant family. -/
theorem restore_invariante (items : List SItemTief) (u : UProg)
    (P Q : Programm (declOf u)) (h : restore items u P = .ok Q) :
    Q.invariante = P.invariante := by
  unfold restore at h
  cases hx : expandU items with
  | error error => simp only [hx, bind, Except.bind, reduceCtorEq] at h
  | ok expanded =>
    simp only [hx, bind, Except.bind] at h
    cases hs : collect u.fns.length (EnsTy u) (atFunction expanded.1 u P) with
    | error error => simp only [hs, bind, Except.bind, reduceCtorEq] at h
    | ok es =>
      simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst Q
      rfl

/-- The full goal-theorem checker, on the final restored program and all original enumerations. -/
def accepts (u : UProg) (P : Programm (declOf u)) : Except String Bool :=
  letI : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))
  letI : DecidableEq (declOf u).Ax := inferInstanceAs (DecidableEq (Fin u.axs.length))
  do
  if !sperrInvsOk u then throw "lock invariant without G form"
  let ws : List (declOf u).Fn := (u.roots ++ u.gestartet ++ u.gestartet).filterMap fun n => wurzelIdx u n
  let ls : List (declOf u).Lock := List.finRange u.locks.length
  let cs : List ((declOf u).Tab ⊕ (declOf u).Glob) :=
    (List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr
  let guests ← sourceGuests u
  pure (AkzeptiertX P (sperrFamilie u) (List.finRange u.fns.length) ls cs ws [] [] [] guests)

/-- Restoring function postconditions retains the exact foreign contract family. -/
theorem restore_axVertrag (items : List SItemTief) (u : UProg)
    (P Q : Programm (declOf u)) (h : restore items u P = .ok Q) :
    Q.axVertrag = P.axVertrag := by
  unfold restore at h
  cases hx : expandU items with
  | error error => simp only [hx, bind, Except.bind, reduceCtorEq] at h
  | ok expanded =>
    simp only [hx, bind, Except.bind] at h
    cases hs : collect u.fns.length (EnsTy u) (atFunction expanded.1 u P) with
    | error error => simp only [hs, bind, Except.bind, reduceCtorEq] at h
    | ok es =>
      simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst Q
      rfl

/-- Successful production admission retains one canonically admitted descriptor
    per source guest. In particular, an empty adapter cannot hide a guest. -/
theorem accepts_guests (u : UProg) (P : Programm (declOf u))
    (accepted : accepts u P = .ok true) :
    ∃ guests, sourceGuests u = .ok guests ∧ guests.length = u.guests.length ∧
      ∀ guest ∈ guests, guest.admittedB = true := by
  unfold accepts at accepted
  split at accepted
  · cases accepted
  · cases hg : sourceGuests u with
    | error error => simp [hg, Functor.map, Except.map] at accepted
    | ok guests =>
      simp only [hg, bind, Except.bind, Functor.map, Except.map, pure, Except.pure, Except.ok.injEq] at accepted
      refine ⟨guests, rfl, sourceGuests_complete u guests hg, ?_⟩
      unfold AkzeptiertX at accepted
      exact fun guest member =>
        GuestBoundary.admissionB_each ((Bool.and_eq_true _ _).mp accepted).2 guest member

end Gabbro.Stage0.OldSource
