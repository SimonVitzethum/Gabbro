/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben40.lean
  Subject:   Track P, the open region from source text (PLAN-DYNAMIC 14): `table T from neu` (an open table and its
             provider), `extern fn neu() -> index into T` (the provider answers a reference), `let r = alloc T;` (the
             provider's call, `Block.alloc`) and `r->x = 7;` (`Stmt.assignSlotRef`). The whole Lean pipeline --
             lex, parse, elaborate, lower onto `declOf u` -- runs on the text, and the core checker `Akzeptiert`
             accepts the result, decided by the kernel. The twins are refused: `alloc` of a table without a provider,
             and the write without `writes T.slots`.
-/
import Grammatik.Parser.Elab.UebersetzePipeline
import Grammatik.Zielsatz.Kern.Akzeptiert

namespace Gabbro.Grammatik.Parser.UebersetzeProben40

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- The unit, with its write effect `w` and the table `alloc` names. -/
def quelle (w tab : String) : String := "module zellen::region {
table T from neu {
    slot {
        x : u64 in 0 .. 255,
    }
}
table U count 4 {
    slot {
        y : u64 in 0 .. 255,
    }
}
extern fn neu() -> index into T effects { pure } costs <= 1000 ops;
impl fn f()
    effects { " ++ w ++ " }
    costs   <= 1000 ops
{
    let r = alloc " ++ tab ++ ";
    r->x = 7;
    return;
}
}
"

/-- The accepted unit. -/
def src : String := quelle "writes T.slots" "T"

/-- The core checker on what the pipeline makes of a text (`false` when the pipeline refuses it). -/
def akzeptiertText (s : String) : Bool :=
  match uebersetzeAllg s with
  | .ok ⟨u, P, fs⟩ =>
    Akzeptiert P ⟨fun _ => [], fun _ _ => true⟩ fs [] ((List.finRange u.tabs.length).map Sum.inl) fs
  | .error _ => false

/-- The body elaborates to the provider's call and the write through the reference. -/
theorem region_koerper : (match uebersetzeAllg src with
    | .ok ⟨u, _, _⟩ => u.fns.map (·.body) == [[.bindAx "r" "neu" [], .assignRef "r" "x" (.lit 7)]] &&
        u.tabs.map (·.von) == [some "neu", none] &&
        u.axs.map (·.res) == [some (.ref 0)]
    | .error _ => false) = true := by decide +kernel

/-- **The open region from source text is accepted by the core checker.** -/
theorem region_akzeptiert : akzeptiertText src = true := by decide +kernel

/-- Refused: `alloc U`, a table without a provider. -/
theorem alloc_ohne_anbieter : akzeptiertText (quelle "writes T.slots" "U") = false := by decide +kernel

/-- Refused: the write through the reference without the write right on `T`. -/
theorem schreiben_ohne_recht : akzeptiertText (quelle "pure" "T") = false := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben40
