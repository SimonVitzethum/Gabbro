module

@[expose] public section

namespace Gabbro.Core.Registry

universe u v

/-- The pinned statements for each real constructor. Their case type can
    include the source occurrence, machine states and a matched execution.
    The owner of the underlying definitions fixes these statements before
    the registry supplies proofs. -/
structure Requirements {Form : Type u} (Case : Form → Type v) where
  premises : (form : Form) → Case form → Prop
  parse : (form : Form) → Case form → Prop
  elaborates : (form : Form) → Case form → Prop
  localRule : (form : Form) → Case form → Prop
  ideal : (form : Form) → Case form → Prop
  units : (form : Form) → Case form → Prop
  commutation : (form : Form) → Case form → Prop
  implementation : (form : Form) → Case form → Prop
  preservation : (form : Form) → Case form → Prop
  realisation : (form : Form) → Case form → Prop

/-- Proofs of the constructor's complete obligations. The realisation is a
    source occurrence for a surface form and a checked origin for a core form.
    Every rule uses the same jointly satisfiable bundle of premises. -/
structure Entry {Form : Type u} {Case : Form → Type v}
    (required : Requirements Case) (form : Form) : Prop where
  parse : ∀ c, required.premises form c → required.parse form c
  elaborates : ∀ c, required.premises form c → required.elaborates form c
  localRule : ∀ c, required.premises form c → required.localRule form c
  ideal : ∀ c, required.premises form c → required.ideal form c
  units : ∀ c, required.premises form c → required.units form c
  commutation : ∀ c, required.premises form c → required.commutation form c
  implementation : ∀ c, required.premises form c → required.implementation form c
  preservation : ∀ c, required.premises form c → required.preservation form c
  realisation : ∀ c, required.premises form c → required.realisation form c
  erfuellbar : ∃ c, required.premises form c

/-- Coverage is total over the form index. The inventory is descriptive data
    and cannot supply this index in place of actual constructors. -/
def Complete {Form : Type u} {Case : Form → Type v} (required : Requirements Case) : Prop :=
  ∀ form, Entry required form

end Gabbro.Core.Registry
