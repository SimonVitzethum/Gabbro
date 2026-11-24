module

public import Core.Beobachtung.Fluss.Beschriftung.Schreiben
public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung

theorem schreibform_literal (dst val : Nat) : (Befehl.literal dst val).Schreibform dst [] :=
  ⟨fun _ => some ⟨.int val val, Zahl.literal val⟩, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem schreibform_wahrheitswert (dst : Nat) (value : Bool) :
    (Befehl.wahrheitswert dst value).Schreibform dst [] :=
  ⟨fun _ => some ⟨.bool, value⟩, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem schreibform_negativ (dst magnitude : Nat) :
    (Befehl.negativ dst magnitude).Schreibform dst [] :=
  ⟨fun _ => let value : Int := -(magnitude : Int); some ⟨.int value value, Zahl.literal value⟩,
    fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem schreibform_lesen (dst index : Nat) :
    (Befehl.lesen dst index).Schreibform dst [.lokal index] :=
  ⟨fun r => r.lokale[index]?.join, fun _ _ => rfl,
    fun r₁ r₂ h => h (.lokal index) (List.mem_singleton_self _)⟩

theorem schreibform_negieren (dst : Nat) : (Befehl.negieren dst).Schreibform dst [.temp dst] :=
  ⟨fun r => (r.zahl dst).map fun a => Ganzzahl.pack ⟨_, _, a.zahl.neg⟩, fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp dst = r₂.temp dst := h (.temp dst) (List.mem_singleton_self _)
      simp only [Rahmen.zahl, h0]⟩

theorem schreibform_verneinen (dst : Nat) : (Befehl.verneinen dst).Schreibform dst [.temp dst] :=
  ⟨fun r => ((r.temp dst).bind alsBoolean).map fun bit => ⟨.bool, !bit⟩, fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp dst = r₂.temp dst := h (.temp dst) (List.mem_singleton_self _)
      simp only [h0]⟩

theorem schreibform_binaer (op : Arith) (left : Nat) :
    (Befehl.binaer op left).Schreibform left [.temp left, .temp (left + 1)] :=
  ⟨fun r => do
      let a ← r.zahl left
      let b ← r.zahl (left + 1)
      pure (Ganzzahl.pack ⟨_, _, op.auswerten a.zahl b.zahl⟩),
    fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp left = r₂.temp left := h (.temp left) (List.mem_cons_self ..)
      have h1 : r₁.temp (left + 1) = r₂.temp (left + 1) := h (.temp (left + 1)) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      simp only [Rahmen.zahl, h0, h1]⟩

theorem schreibform_teilen (left : Nat) :
    (Befehl.teilen left).Schreibform left [.temp left, .temp (left + 1)] :=
  ⟨fun r => do
      let a ← r.zahl left
      let b ← r.zahl (left + 1)
      if h : 1 ≤ b.lo ∨ b.hi ≤ -1 then
        pure ⟨quotientType a.lo a.hi b.lo, a.zahl.div b.zahl h⟩
      else none,
    fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp left = r₂.temp left := h (.temp left) (List.mem_cons_self ..)
      have h1 : r₁.temp (left + 1) = r₂.temp (left + 1) := h (.temp (left + 1)) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      simp only [Rahmen.zahl, h0, h1]⟩

theorem schreibform_vergleichen (op : Compare) (left : Nat) :
    (Befehl.vergleichen op left).Schreibform left [.temp left, .temp (left + 1)] :=
  ⟨fun r => do
      let a ← r.zahl left
      let b ← r.zahl (left + 1)
      pure ⟨.bool, op.eval a.zahl.wert b.zahl.wert⟩,
    fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp left = r₂.temp left := h (.temp left) (List.mem_cons_self ..)
      have h1 : r₁.temp (left + 1) = r₂.temp (left + 1) := h (.temp (left + 1)) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      simp only [Rahmen.zahl, h0, h1]⟩

end Gabbro.Core.Ast.Semantik
