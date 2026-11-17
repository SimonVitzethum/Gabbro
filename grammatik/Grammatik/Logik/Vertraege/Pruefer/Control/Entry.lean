module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Results
public import Grammatik.Logik.Vertraege.Pruefer.Control.Havoc
public import Grammatik.Logik.Vertraege.Pruefer.Control.Snapshots

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

abbrev Entry (D : Deklaration) (Γ : Ctx) := World D × Env D Γ

def entryContext (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (snapshot : Option (Snapshot.Region D next) := none) : Context (Entry D Γ) next :=
  match snapshot with
  | none => {
      holds := fun valuation item => symbols.Realizes valuation item.1 item.2
      stable := fun valuation other item agree =>
        symbols.realizes_congr next bounded valuation other agree item.1 item.1 item.2 }
  | some region => {
      holds := fun valuation item => symbols.Realizes valuation item.1 item.2 ∧
        Snapshot.Realizes region.start region.names valuation item.1
      stable := fun valuation other item agree => and_congr
        (symbols.realizes_congr next bounded valuation other agree item.1 item.1 item.2)
        (Snapshot.realizes_congr region.names region.start valuation other item.1
          (fun key _ upper => agree key (Nat.lt_of_lt_of_le upper region.within))) }

theorem entryContext_locals (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (snapshot : Option (Snapshot.Region D next)) (valuation : Frag.Assignment Nat) (item : Entry D Γ)
    (present : (entryContext symbols bounded snapshot).holds valuation item) :
    symbols.Realizes valuation item.1 item.2 := by
  cases snapshot with | none => exact present | some region => exact present.1

theorem entryContext_memory (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (snapshot : Option (Snapshot.Region D next)) (valuation : Frag.Assignment Nat) (item : Entry D Γ)
    (present : (entryContext symbols bounded snapshot).holds valuation item) :
    Snapshot.Realizes (Snapshot.regionStart snapshot) (Snapshot.regionNames snapshot) valuation item.1 := by
  cases snapshot with | none => trivial | some region => exact present.2

def envResult : (result : Option Ty) → Env D (ErgCtx [] result) → ErgVal D result
  | none, .nil => ()
  | some _, .cons value .nil => value

theorem envResult_ergEnv (result : Option Ty) (value : ErgVal D result) :
    envResult result (ergEnv result value .nil) = value := by
  cases result <;> rfl

def withResult : (result : Option Ty) → SymEnv D Nat (ErgCtx [] result) → SymEnv D Nat Γ →
    SymEnv D Nat (ErgCtx Γ result)
  | none, .nil, args => args
  | some _, .cons value .nil, args => .cons value args

theorem withResult_bounded (result : Option Ty) (returned : SymEnv D Nat (ErgCtx [] result))
    (args : SymEnv D Nat Γ) (rb : returned.Bounded next) (ab : args.Bounded next) :
    (withResult result returned args).Bounded next := by
  cases result with
  | none => cases returned; exact ab
  | some _ => cases returned with | cons _ tail => cases tail; exact ⟨rb.1, ab⟩

theorem withResult_realizes (result : Option Ty) (returned : SymEnv D Nat (ErgCtx [] result))
    (args : SymEnv D Nat Γ) (valuation : Frag.Assignment Nat) (world : World D)
    (actual : Env D (ErgCtx [] result)) (locals : Env D Γ)
    (rr : returned.Realizes valuation world actual) (ar : args.Realizes valuation world locals) :
    (withResult result returned args).Realizes valuation world (ergEnv result (envResult result actual) locals) := by
  cases result with
  | none => cases returned; cases actual; exact ar
  | some _ =>
      cases returned with | cons value tail =>
        cases tail
        cases actual with | cons value rest => cases rest; exact ⟨rr.1, ar⟩

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
