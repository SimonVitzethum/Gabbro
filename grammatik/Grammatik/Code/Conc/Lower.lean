import Grammatik.Code.Lower.Stmt

/-
  File:      Grammatik/Code/Conc/Lower.lean
  Subject:   TRACK L, PHASE L3 (START) -- THE LOWERING OF `publish` AND `await`: a release store and an
             acquire load of the atomic global's cell. A separate folder: these forms are NOT in `lowerS`/`lowerB`,
             because their refinement is not stated against every interface `Sees` (a load of a shared atomic
             is answered by the weak memory), see `Conc/Await.lean`.

    * `publish g = e;`      -- the value, then `astor t v @g release`;
    * `let x = g awaits ..` -- `aload r t @g acquire`, the word becomes a new local, then the rest.

  THE CUT: the global's cell must be word-sized in memory (`atomicOk (memTy τ)`: the model's atomics are on
  word cells, `Model/Semantics.lean`), so a `bool` or a narrow range as an atomic global is refused by name
  (`atomicG`); an atomic global is a `u32` on a 32-bit target, a `u64` or a pointer on a 64-bit one.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Expr Ctx Res Vertrag)

variable {D : Deklaration} {V : Vertrag D}

/-- An atomic global the fragment carries: a type the lowering knows whose memory image is word-sized. -/
def atomicG (τ : GTy) : Bool := supp τ && atomicOk (memTy τ)

/-- **`publish g = e;`**: the value of `e`, then a release store into the cell of `g`. -/
def lowerPublish (lay : Layout D) (cenv : List Reg) (g : D.Glob) {Γ : Ctx} {Λ : List (Res D)}
    (e : Expr D Γ Λ (D.gtyp g)) (lb k : Lbl) (s : St) : Option (List Block × St) :=
  if atomicG (D.gtyp g) then
    match lowerE lay cenv e s.r with
    | some (ce, oe, r1) =>
        some ([⟨lb, [], ce ++ [.astor (memTy (D.gtyp g)) oe (.glob (lay.ggblk g)) .rel], .jmp k⟩],
          { s with r := r1 })
    | none => none
  else none

/-- **`let x = g awaits {..}; rest`**: an acquire load of the cell of `g`, the word a new local, then `rest`
    (entry label `s.l`). -/
def lowerAwait (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (g : D.Glob) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (rest : Gabbro.Grammatik.Block D V l (D.gtyp g :: Γ) Λ Λ') (lb k : Lbl) (s : St) :
    Option (List Block × St) :=
  if atomicG (D.gtyp g) then
    match bindCode (D.gtyp g) (.reg s.r) (s.r + 1) with
    | some (cb, a, r2) =>
        match lowerB lay (a :: cenv) lv rest s.l k ⟨r2, s.l + 1⟩ with
        | some (bo, s1) =>
            some (⟨lb, [], .aload s.r (memTy (D.gtyp g)) (.glob (lay.ggblk g)) .acq :: cb, .jmp s.l⟩ :: bo, s1)
        | none => none
    | none => none
  else none

end Gabbro.Code.Lower
