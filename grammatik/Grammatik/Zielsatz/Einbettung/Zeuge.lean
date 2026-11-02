module
public import Grammatik.Zielsatz.Einbettung.Uebertragung
@[expose] public section


/-!
  File:      Grammatik/Zielsatz/Einbettung/Zeuge.lean
  Subject:   **Every library links into a program with a callback** -- the witnesses of the
             embedding theorem, for every library and no particular program.

  For every declaration `D` and every function `g₀` of it, `erweitert D g₀` is `D` with one more
  function outside `D` (`Sum.inr ()`): it has `g₀`'s signature and conforms to every pointer type
  `g₀` conforms to, so it can be handed to `D` as a callback with `g₀` as its head. Everything else
  is `D`'s. `einE` embeds `D`, `programmE` extends a program of `D` by the callback, whose body and
  contract are the images of `g₀`'s. `uebernahmeE` proves every link condition, `RueckVertrag`
  included, for every library; `einbettung_zeuge` is `logikPflicht_E` on it, with the callback real
  (`rueckruf_echt`).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable (D : Deklaration) (g₀ : D.Fn)

/-- Conformance in the extension: a function of `D` as in `D`, the callback where `g₀` conforms. -/
def passtE : D.Fn ⊕ Unit → Nat → Bool
  | .inl f, n => D.passt f n
  | .inr _, n => D.passt g₀ n

/-- A value of the extension back in `D`: the callback stands for `g₀`. -/
def zurueck (τ : Ty) (v : Val (D.Fn ⊕ Unit) (passtE D g₀) τ) : Wert D τ :=
  Val.restrict id id (fun _ value => match value with
    | ⟨.inl f, h⟩ => ⟨f, h⟩
    | ⟨.inr _, h⟩ => ⟨g₀, h⟩) τ ((Ty.mapNumbers_id τ).symm ▸ v)
