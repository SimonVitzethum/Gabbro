module
public import Bruecke.Anweisung.Zweig.ReasonReturn
public import Bruecke.Kette.Reason.Boundary
public import Bruecke.Kette.Pflichten
@[expose] public section

namespace Gabbro.Bruecke.ReasonReturnZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

def routine : UFn :=
  { name := "reason", params := [], kinds := [], res := none, held := [], puts := [], gives := [],
    gruende := 2, body := [], ret := .why 1 }

def unit : UProg := { tabs := [], locks := [], fns := [routine] }

def caller : Fin unit.fns.length := ⟨0, by simp only [unit, List.length_singleton]; omega⟩

theorem channel_nonempty : (declOf unit).gruende caller = 2 := by
  rw [sigGruende_eq]
  rfl

def second : Fin (verOf unit caller).gruende :=
  ⟨1, by change 1 < (declOf unit).gruende caller; rw [channel_nonempty]; omega⟩

theorem readers_zeuge (ns : BodyNames) :
    namedEnd unit routine ns (.why 1) = some [reasonReturn 1] ∧
      retZ unit routine ns (.why 1) = some (reasonReturn 1) := ⟨rfl, rfl⟩

/-- The nonzero case of a two-case channel is carried with its exact Body value.
    The related world is the only semantic premise, and the following witness supplies it. -/
theorem reasonReturn_zeuge (σ : World (declOf unit)) (s : Gabbro.Body.State)
    (hW : WGRel unit σ s.world)
    (R : ∀ f : (declOf unit).Fn, World (declOf unit) →
      Env (declOf unit) ((declOf unit).params f) → RufAusgang f) :
    AusgangZiel_G (loopMode := false) unit (fun _ => True) caller R routine []
      (Ausgang.why (Γ := []) σ second) s [reasonReturn 1] :=
  ausgangZiel_why second hW

theorem related_world_zeuge (σ : World (declOf unit)) (w : Gabbro.Body.World) :
    WGRel unit σ (encG unit σ w) := wgrel_enc unit σ w

/-- Two actual reasons, and an arbitrary answer world, jointly satisfy the canonical
    handler premise. No frame or normal-result promise is silently added. -/
theorem reasonHandler_zeuge (P : Programm (declOf unit))
    (answer : (declOf unit).Fn → World (declOf unit) → World (declOf unit)) :
    RespektiertRahmen P (fun f σ _ => .why (answer f σ)
      ⟨1, by rcases f with ⟨i, hi⟩
             have hz : i = 0 := by change i < 1 at hi; omega
             subst i
             rw [sigGruende_eq]
             change 1 < 2
             omega⟩) := by
  have hreas : ∀ f : (declOf unit).Fn, Fin ((declOf unit).gruende f) := by
    intro f
    refine ⟨1, ?_⟩
    rcases f with ⟨i, hi⟩
    have hz : i = 0 := by change i < 1 at hi; omega
    subst i
    rw [sigGruende_eq]
    change 1 < 2
    omega
  exact reasonHandler_respektiertRahmen P hreas answer

end Gabbro.Bruecke.ReasonReturnZeuge
