module

public import Grammatik.Kern.Syntax.Satz.PruefungReplay
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Consumer
public import Grammatik.Kern.Semantik.Semantik

@[expose] public section

namespace Gabbro.Grammatik

/-- Retirement removes the sole physical Duty. No second retirement can be
    constructed at the resulting resource index. This is about the kernel
    resource list, independently of a report's copyable ghost fields. -/
theorem duty_retired_once (D : Deklaration) (c : CheckDecl D) :
    ([Res.vonMarke D c.duty].erase (Res.vonMarke D c.duty)) = [] ∧
      Res.vonMarke D c.duty ∉
        ([Res.vonMarke D c.duty].erase (Res.vonMarke D c.duty)) := by
  simp

/-- Conservation through an actual retiring consumer: its signature moves
    the unique input mark out of the caller and produces none. Owner transfer
    is an explicit, unchanged premise, never inferred from ordinary marks. -/
theorem duty_consumer_conservation (D : Deklaration) (c : CheckDecl D)
    (consumer : Signatur D.Tab D.Glob D.Lock D.Marke)
    (hin : consumer.inputMarks = [c.duty])
    (hout : consumer.outputMarks = []) :
    nachSig D consumer [Res.vonMarke D c.duty] = [] := by
  simp [nachSig, hin, hout]

/-- The producer/consumer cycle has no residual physical Duty. The ordinary
    probe returns its one completed token; the selected consumer retires it.
    Both Bool verdicts have this same resource interface. -/
theorem duty_cycle_conservation (D : Deklaration) (c : CheckDecl D)
    (producer consumer : Signatur D.Tab D.Glob D.Lock D.Marke)
    (pin : producer.inputMarks = [c.duty])
    (pout : producer.outputMarks = [c.duty])
    (cin : consumer.inputMarks = [c.duty])
    (cout : consumer.outputMarks = []) :
    nachSig D consumer (nachSig D producer [Res.vonMarke D c.duty]) = [] := by
  simp [nachSig, pin, pout, cin, cout]

/-- The zero-effect retirement does not read or modify payload or compute a
    new observation. Ghost bookkeeping therefore adds no executable sample. -/
theorem duty_retirement_payload (D : Deklaration) (V : Vertrag D)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (m : D.Marke) (s : Nat) (present : Res.marke m s ∈ Λ)
    (O : Orakel D) (passes : Nat) (calls : Ruf D) (world : World D) (env : Env D Γ) :
    execStmt O passes calls (Stmt.retires (V := V) (l := l) m s present D.a10)
      world env = .ok world env := rfl

end Gabbro.Grammatik
