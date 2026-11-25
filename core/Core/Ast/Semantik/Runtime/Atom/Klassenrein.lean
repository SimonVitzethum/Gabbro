/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Klassenrein.lean
  Subject:   FRAGMENTS WITH ACCESS INSTRUCTIONS (MK-04b). A fragment is FRAME-ONLY (`Fragment.Rein`) when every instruction
             of its code is frame-only. A source form that elaborates to an access instruction
             (`Zugriffsquelle`) makes a fragment that is not. `Fragment.KlassenRein` is the next predicate: every
             instruction is frame-only or an access instruction. The two classes `lesen`/`schreiben`/`rmw`
             of the access instructions are the only non-frame classes the source reaches (the lifecycle instructions
             of MK-07 have no source form), so `KlassenRein` is the predicate the generic proofs of the units of the
             source take once an access form is in the grammar. `Fragment.MitZugriff` is the part that is not
             frame-only: exactly the fragments whose statements rest on the duties of the access classes
             (`KlassenAussagen`, `ZugriffBefehlAussage`, `AtomAussagen`) and on the pinned statements of
             `Ziel/Korrektheit/Zugriff`, and not on the template step of the frame-only classes.
-/
module

public import Core.Ast.Semantik.Runtime.Atom.Rein
public import Core.Ast.Semantik.Runtime.Atom.Form

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- **An instruction is frame-only or an access instruction.** -/
def Befehl.Klassengut (b : Befehl) : Prop := b.Privat ∨ ∃ z, b = .zugriff z

/-- **Every instruction of the fragment is frame-only or an access instruction.** -/
def Fragment.KlassenRein (p : Fragment) : Prop := ∀ b ∈ p.code, b.Klassengut

/-- **The fragments that contain an access instruction**: not frame-only, but with no instruction outside the
    two classes. -/
def Fragment.MitZugriff (p : Fragment) : Prop := p.KlassenRein ∧ ¬ p.Rein

/-- A frame-only fragment has only instructions of the two classes. -/
theorem Fragment.rein_klassenrein {p : Fragment} (h : p.Rein) : p.KlassenRein :=
  fun b mem => Or.inl (h b mem)

/-- A fragment of the two classes is frame-only or has an access instruction. -/
theorem Fragment.klassenrein_rein_oder {p : Fragment} (h : p.KlassenRein) : p.Rein ∨ p.MitZugriff := by
  by_cases r : p.Rein
  · exact Or.inl r
  · exact Or.inr ⟨h, r⟩

/-- An access instruction is not frame-only: the class of every access is `lesen`, `schreiben` or `rmw`. -/
theorem Befehl.zugriff_nicht_privat (z : Zugriffsform) : ¬ (Befehl.zugriff z).Privat := by
  intro h
  exact Befehl.privat_ne_zugriff_klasse _ h z rfl

/-- **The fragment that consists of one access instruction has an access instruction.** The pinned statements about
    the fragments `MitZugriff` quantify over a nonempty set: the unit of a single load is one. -/
theorem Fragment.einzel_zugriff_mitZugriff (z : Zugriffsform) : (Fragment.einzel (.zugriff z)).MitZugriff := by
  refine ⟨?_, ?_⟩
  · intro b mem
    rw [List.mem_singleton.mp mem]
    exact Or.inr ⟨z, rfl⟩
  · intro h
    exact Befehl.zugriff_nicht_privat z ((Fragment.rein_einzel_iff _).mp h)

end Gabbro.Core.Ast.Semantik
