/- Joint Boolean and provider capability witnesses for actual foreign lowering. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.AxiomElseProbes
public import Stage0.Senke.Ausdruck.Referenz.Proben
public import Stage0.Senke.Tore.Witness
@[expose] public section

namespace Gabbro.Stage0.Senke.ForeignAnswers
open Gabbro.Grammatik Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev result : Option Ty := some .bool
abbrev D := AxiomElseProbe.D result
abbrev entry : D.Fn := AxiomElseProbe.entry result
abbrev gate : D.Ax := AxiomElseProbe.gate result

def admission : RufPasst D (vertragVon D entry) (D.asignatur gate) [] where
  hw t := Fin.elim0 t
  hg g := Fin.elim0 g
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh l := Fin.elim0 l

def success : Endblock D (vertragVon D entry) false [.bool] [] :=
  .ite (.var .here) (AxiomElseProbe.retN result 17 (by decide) (by decide))
    (AxiomElseProbe.retN result 19 (by decide) (by decide))

def bindEnd (optional : Bool) : Endblock D (vertragVon D entry) false [] [] :=
  if optional then
    .bindAxiomOptElse result gate .nil rfl admission
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (by decide)
      (AxiomElseProbe.handler result) success
  else
    .bindAxiomElse gate .nil rfl (by decide)
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
      (AxiomElseProbe.handler result) success

def successBlock : Block D (vertragVon D entry) false [.bool] [] [] :=
  .cons (.ite (.var .here)
    (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 17))) (.refl [])) .nil)
    (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 19))) (.refl [])) .nil)) .nil

def bindBlock (optional : Bool) : Block D (vertragVon D entry) false [] [] [] :=
  if optional then
    .bindAxiomOptElse result gate .nil rfl admission
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (by decide)
      (AxiomElseProbe.handler result) successBlock
  else
    .bindAxiomElse gate .nil rfl (by decide)
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
      (AxiomElseProbe.handler result) successBlock

def body (optional nested : Bool) : Endblock D (vertragVon D entry) false [] [] :=
  if nested then .cons (.ite .tru (bindBlock optional) .nil)
    (AxiomElseProbe.retN result 99 (by decide) (by decide))
  else bindEnd optional

def program (optional nested : Bool) : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body optional nested

def image (optional nested : Bool) : Except String (List Runner.B) := do
  let emitted ← bild 1 (program optional nested)
    (layU (AxiomElseProbe.u result) (fun _ => some AxiomElseProbe.binding))
    [entry] Fin.val (fun _ => "main") entry .nil [] 1024
  pure emitted.bytes

/-- Both binder APIs, in both contexts, reach complete images. -/
theorem boolean_binder_images_zeuge :
    (image false false).isOk = true ∧ (image false true).isOk = true ∧
    (image true false).isOk = true ∧ (image true true).isOk = true := by
  decide +kernel

def oracle (raw : Runner.W) : Orakel D where
  wirkt _ σ _ := (σ, rohW AxiomElseProbe.binding 1 raw)
  regLies r := Fin.elim0 r
  regSchreib r := Fin.elim0 r
  sichtbar _ _ := true

def observed (optional nested : Bool) (raw : Runner.W) : Int :=
  match execEnd (oracle raw) 1 (AxiomElseProbe.calls result)
      (body optional nested) (AxiomElseProbe.initial result) .nil with
  | .zurueck _ value => value.n
  | _ => -1

/-- False, true and the nominal error all stay live and distinguishable. -/
theorem boolean_binder_paths_zeuge :
    observed false false 0 = 19 ∧ observed false false 7 = 17 ∧
    observed false false (BitVec.ofInt 64 (-9)) = 9 ∧
    observed false true 0 = 19 ∧ observed false true 7 = 17 ∧
    observed false true (BitVec.ofInt 64 (-9)) = 9 ∧
    observed true false 0 = 19 ∧ observed true false 7 = 17 ∧
    observed true false (BitVec.ofInt 64 (-9)) = 9 ∧
    observed true true 0 = 19 ∧ observed true true 7 = 17 ∧
    observed true true (BitVec.ofInt 64 (-9)) = 9 := by
  decide +kernel

/-- The canonical accepted provider fixture now lowers as a whole function,
    including the write through its returned reference into a supplied region. -/
theorem reference_function_zeuge :
    Akzeptiert GRegion.prog ⟨fun l => l.elim, fun l => l.elim⟩ [()] [] [.inl ()] [()] = true ∧
    (lowFun 1 GRegion.prog (fun _ => 0) ReferenceProbe.layout ()).isSome = true ∧
    ReferenceProbe.layout.count () = 2 := by
  exact ⟨GRegion.prog_akzeptiert, by decide +kernel, rfl⟩

/-- The new provider premise is jointly satisfiable on a real represented
    region; it is not hidden in an impossible reference layout. -/
theorem reference_contract_zeuge :
    @TorOK ⟨fun _ _ _ _ => True⟩ GRegion.rD ReferenceProbe.layout (GRegion.oK 0) := by
  refine torOK_zeuge _ _ (by intro a σ ρ; rfl) ?_ ?_
  · intro a n type bound
    have same : n = 0 := by
      have eq : some (.ref 0) = some (.ref n) := type
      cases eq
      rfl
    subst n
    exact ⟨by decide, (), rfl, rfl, by decide⟩
  · apply areaContract_register_only
    intro a binding bound
    have same : some ⟨39, regsIn 0, [], none⟩ = some binding := bound
    cases same
    rfl

/-- Region capabilities keep nominal table identity and the canonical zero
    marker; no physical address is reconstructed from the provider's number. -/
theorem capability_decoders_zeuge :
    (chkC (some (.ptr (.table 0 (false, true)))) 8).isSome = true ∧
    (chkC (some (.ref 0)) 8).isSome = true ∧
    einpassenErg (D := GRegion.rD) (fun _ => none)
      (some (.ref 0)) (-1) = none := by
  exact ⟨by decide +kernel, by decide +kernel, rfl⟩

end Gabbro.Stage0.Senke.ForeignAnswers
