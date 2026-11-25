module

public import Core.Ast.Semantik.Formen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
open Lean (Name)

theorem Quellform.annahme (form : Quellform category Arguments) : form.AnnahmeAussage := by
  intro platform args
  refine ⟨(form.befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, form.befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := (form.befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

theorem Quellform.erhaltung (form : Quellform category Arguments)
    (ohneInvarianten : ∀ args, (form.fragment args).klauseln.invariant = []) :
    form.ErhaltungsAussage := by
  intro platform args
  let p := form.fragment args
  let b := form.befehl args
  exact ⟨b.abgleich p platform, b.fortschritt p, b.komponierbar p platform,
    b.sicherheitsPflichten p platform [] (tabLeer _ (ohneInvarianten args)) (fun b _ => rfl)⟩

def Quellform.eintrag {cat : Scope → Category} {args : Scope → Type}
    (forms : (scope : Scope) → Quellform (cat scope) (args scope)) (joint : Prop) (constructor : Name)
    (parse : ∀ scope, (forms scope).produktion.Entry)
    (atRoot : ∀ scope, (forms scope).RegelAmOrt)
    (ohneInvarianten : ∀ scope a, ((forms scope).fragment a).klauseln.invariant = [])
    (erfuellbar : joint) : RegistryEntry constructor ⟨.surface, Quellform.statements forms joint constructor⟩ where
  realization := .surface
    (fun scope _ _ _ lexed production => (parse scope).parse lexed production)
    (fun _ _ _ => rfl)
    (fun scope platform a s running active atPc => (forms scope).realisiert (atRoot scope) platform a s running active atPc)
  acceptanceRule := fun scope => (forms scope).annahme
  idealRule := fun scope =>
    ⟨atRoot scope, fun a => ⟨((forms scope).befehl a).bestimmt,
      fun c s w plans u => ((forms scope).befehl a).ideal_privat c s w plans u⟩⟩
  unitsAndCommutation := fun scope _ a => ⟨rfl, ((forms scope).befehl a).kommutation⟩
  implementationRule := fun scope a c s w plans u => ((forms scope).befehl a).impl_privat c s w plans u
  preservation := fun scope => (forms scope).erhaltung (ohneInvarianten scope)
  jointlySatisfiable := erfuellbar

private theorem rootLookup (p : Fragment) (b : Befehl) :
    (p.anhaengen (.einzel b)).code[p.code.length]? = some b := by
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

theorem literal_am_ort (scope : Scope) : (literalForm scope).RegelAmOrt :=
  fun _ => rfl

theorem binary_am_ort (scope : Scope) : (binaryForm scope).RegelAmOrt :=
  fun args => rootLookup ((expr 0 args.left).anhaengen (expr 1 args.right)) (.binaer args.op 0)

theorem let_am_ort (scope : Scope) : (letForm scope).RegelAmOrt :=
  fun args => rootLookup (expr 0 args.value) (.binden args.name 0)

theorem Quellform.erfuellbar_aus_erreichbar (form : Quellform category Arguments)
    (platform : Plattform) (start : AussenStart) (args : Arguments) (s : Zustand)
    (reachable : (form.einheit platform args).system.IErreichbar (I.start (form.einheit platform args) start).2 s)
    (occurrence : Realisiert form platform args s)
    (safeGuard : ∀ g, (form.befehl args).guard (s.lokal eintritt) = some g →
      waechterBedarf g.1 g.2) :
    form.ErfuellbarAm platform start args :=
  ⟨Ast.print (category := category) (form.produktion.tree args), s, Ast.parse_print _, rfl,
    reachable, occurrence, safeGuard⟩

end Gabbro.Core.Ast.Semantik
