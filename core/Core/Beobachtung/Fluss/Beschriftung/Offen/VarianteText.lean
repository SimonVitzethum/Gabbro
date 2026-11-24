module

public import Core.Ast.Aggregate.Runtime
public import Core.Ast.TextValue.Bytes
public import Core.Beobachtung.Fluss.Beschriftung.Variante
public import Core.Beobachtung.Fluss.Beschriftung.Text
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- The view after a binding branch: `pc` moves and the payload is pushed. -/
theorem sicht_zweig_einschieben (β : Beschriftung) (r : Rahmen) (offset : Nat)
    (payload : Option Dynamisch) :
    ({ r with
      pc := r.pc + offset
      lokale := payload :: r.lokale } : Rahmen).sicht β =
      { r.sicht β with
        pc := r.pc + offset
        temp := fun s => if oeffentlich (β.temp (r.pc + offset) s) = true then r.temp s else none
        lokale := maskiere (β.lokal (r.pc + offset)) 0 (payload :: r.lokale) } := rfl

/-- A write of the same value keeps the public view when the labels at the successor are at
    least as secret as at the current position. -/
theorem sicht_schreibe_gleich (β : Beschriftung) (r₁ r₂ : Rahmen) (dst : Nat)
    (v : Option Dynamisch)
    (hT : ∀ s, oeffentlich (β.temp (r₁.pc + 1) s) = true → oeffentlich (β.temp r₁.pc s) = true)
    (hL : ∀ i, oeffentlich (β.lokal (r₁.pc + 1) i) = true → oeffentlich (β.lokal r₁.pc i) = true)
    (h : r₁.sicht β = r₂.sicht β) :
    (r₁.schreibe dst v).sicht β = (r₂.schreibe dst v).sicht β := by
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then
        Function.update r₁.temp dst v s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then
        Function.update r₂.temp dst v s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      by_cases hs : s = dst
      · simp only [hs, Function.update_self]
      · simp only [Function.update_of_ne hs]
        exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hLe : maskiere (β.lokal (r₁.pc + 1)) 0 r₁.lokale =
      maskiere (β.lokal (r₁.pc + 1)) 0 r₂.lokale :=
    maskiere_gleich_mono hL 0 _ _ lokEq
  rw [sicht_schreibe, sicht_schreibe, h, pcEq, hTe, hLe]

theorem waehleVarianteSicht : WaehleVarianteSichtAussage := by
  intro β pc source name labels cases branches hq hbr r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hsrc : r₁.temp source = r₂.temp source := tempPub source hq
  have hwert : (r₁.temp source).bind (wertAls (variantValueType name labels cases)) =
      (r₂.temp source).bind (wertAls (variantValueType name labels cases)) := by
    rw [hsrc]
  cases hval : (r₁.temp source).bind (wertAls (variantValueType name labels cases)) with
  | none =>
      have hval₂ : (r₂.temp source).bind (wertAls (variantValueType name labels cases)) = none := by
        rw [← hwert, hval]
      have e₁ : (Befehl.waehleVariante source name labels cases branches).auswerten r₁ live =
          r₁.halt .ungueltigerWert := by
        simp only [Befehl.auswerten, hval]
        rfl
      have e₂ : (Befehl.waehleVariante source name labels cases branches).auswerten r₂ live =
          r₂.halt .ungueltigerWert := by
        simp only [Befehl.auswerten, hval₂]
        rfl
      rw [e₁, e₂, sicht_halt, sicht_halt, h]
  | some value =>
      have hval₂ : (r₂.temp source).bind (wertAls (variantValueType name labels cases)) = some value := by
        rw [← hwert, hval]
      cases hget : branches[(variantCase cases value).1]? with
      | none =>
          have e₁ : (Befehl.waehleVariante source name labels cases branches).auswerten r₁ live =
              r₁.halt .ungueltigerWert := by
            simp only [Befehl.auswerten, hval, hget]
            rfl
          have e₂ : (Befehl.waehleVariante source name labels cases branches).auswerten r₂ live =
              r₂.halt .ungueltigerWert := by
            simp only [Befehl.auswerten, hval₂, hget]
            rfl
          rw [e₁, e₂, sicht_halt, sicht_halt, h]
      | some b =>
          have hbmem : b ∈ branches := by
            exact List.mem_iff_getElem?.mpr ⟨(variantCase cases value).1, hget⟩
          have hs := hbr b hbmem
          by_cases hb2 : b.2 = true
          · have hT : ∀ s, oeffentlich (β.temp (r₁.pc + b.1) s) = true →
                oeffentlich (β.temp r₁.pc s) = true := hs.1
            have hL : ∀ i, oeffentlich (β.lokal (r₁.pc + b.1) (i + 1)) = true →
                oeffentlich (β.lokal r₁.pc i) = true := by
              intro i hi
              exact hs.2.1 i (by simpa only [hb2, if_true] using hi)
            have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + b.1) s) = true then r₁.temp s else none) =
                (fun s => if oeffentlich (β.temp (r₁.pc + b.1) s) = true then r₂.temp s else none) := by
              funext s
              by_cases hp : oeffentlich (β.temp (r₁.pc + b.1) s) = true
              · simp only [hp, if_true]
                exact tempPub s (hT s hp)
              · simp only [if_neg hp]
            have hLe : maskiere (β.lokal (r₁.pc + b.1)) 0 ((variantCase cases value).2 :: r₁.lokale) =
                maskiere (β.lokal (r₁.pc + b.1)) 0 ((variantCase cases value).2 :: r₂.lokale) :=
              maskiere_einschieben (l₀ := β.lokal r₁.pc) (l₁ := β.lokal (r₁.pc + b.1))
                (xs := r₁.lokale) (ys := r₂.lokale)
                (v₁ := (variantCase cases value).2) (v₂ := (variantCase cases value).2)
                hL (fun _ => rfl) lokEq
            have e₁ : (Befehl.waehleVariante source name labels cases branches).auswerten r₁ live =
                ({ r₁ with
                  pc := r₁.pc + b.1
                  lokale := (variantCase cases value).2 :: r₁.lokale } : Rahmen) := by
              simp only [Befehl.auswerten, hval, hget, hb2, if_true]
              rfl
            have e₂ : (Befehl.waehleVariante source name labels cases branches).auswerten r₂ live =
                ({ r₂ with
                  pc := r₂.pc + b.1
                  lokale := (variantCase cases value).2 :: r₂.lokale } : Rahmen) := by
              simp only [Befehl.auswerten, hval₂, hget, hb2, if_true]
              rfl
            rw [e₁, e₂, sicht_zweig_einschieben, sicht_zweig_einschieben, h, pcEq, hTe, hLe]
          · have hb2f : b.2 = false := eq_false_of_ne_true hb2
            have hT : ∀ s, oeffentlich (β.temp (r₁.pc + b.1) s) = true →
                oeffentlich (β.temp r₁.pc s) = true := hs.1
            have hL : ∀ i, oeffentlich (β.lokal (r₁.pc + b.1) i) = true →
                oeffentlich (β.lokal r₁.pc i) = true := by
              intro i hi
              have hidx : i + (if b.2 then 1 else 0) = i := by
                rw [hb2f]
                rfl
              exact hs.2.1 i (by simpa only [hidx] using hi)
            have e₁ : (Befehl.waehleVariante source name labels cases branches).auswerten r₁ live =
                ({ r₁ with pc := r₁.pc + b.1 } : Rahmen) := by
              simp only [Befehl.auswerten, hval, hget, hb2f, if_false]
              rfl
            have e₂ : (Befehl.waehleVariante source name labels cases branches).auswerten r₂ live =
                ({ r₂ with pc := r₂.pc + b.1 } : Rahmen) := by
              simp only [Befehl.auswerten, hval₂, hget, hb2f, if_false]
              rfl
            rw [e₁, e₂, pcEq]
            exact sicht_pcWechsel (q := r₁.pc + b.1) hT hL h

theorem textIndexSicht : TextIndexSichtAussage := by
  intro β pc basis capacity htext hoff hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have htEq : (r₁.temp basis).bind (wertAls (.text capacity)) =
      (r₂.temp basis).bind (wertAls (.text capacity)) := by
    rw [tempPub basis htext]
  have hoEq : r₁.zahl (basis + 1) = r₂.zahl (basis + 1) := by
    simp only [Rahmen.zahl, tempPub (basis + 1) hoff]
  cases htextv : (r₁.temp basis).bind (wertAls (.text capacity)) with
  | none =>
      have ht₂ : (r₂.temp basis).bind (wertAls (.text capacity)) = none := by
        rw [← htEq, htextv]
      have e₁ : (Befehl.textIndex basis capacity).auswerten r₁ live = r₁.halt .ungueltigerWert := by
        simp only [Befehl.auswerten, htextv]
        rfl
      have e₂ : (Befehl.textIndex basis capacity).auswerten r₂ live = r₂.halt .ungueltigerWert := by
        simp only [Befehl.auswerten, ht₂]
        rfl
      rw [e₁, e₂, sicht_halt, sicht_halt, h]
  | some text =>
      have ht₂ : (r₂.temp basis).bind (wertAls (.text capacity)) = some text := by
        rw [← htEq, htextv]
      cases hoffv : r₁.zahl (basis + 1) with
      | none =>
          have ho₂ : r₂.zahl (basis + 1) = none := by
            rw [← hoEq, hoffv]
          have e₁ : (Befehl.textIndex basis capacity).auswerten r₁ live = r₁.halt .ungueltigerWert := by
            simp only [Befehl.auswerten, htextv, hoffv]
            rfl
          have e₂ : (Befehl.textIndex basis capacity).auswerten r₂ live = r₂.halt .ungueltigerWert := by
            simp only [Befehl.auswerten, ht₂, ho₂]
            rfl
          rw [e₁, e₂, sicht_halt, sicht_halt, h]
      | some offset =>
          have ho₂ : r₂.zahl (basis + 1) = some offset := by
            rw [← hoEq, hoffv]
          by_cases hneg : offset.zahl.wert < 0
          · have e₁ : (Befehl.textIndex basis capacity).auswerten r₁ live = r₁.halt .ungueltigerWert := by
              simp only [Befehl.auswerten, htextv, hoffv, if_pos hneg]
              rfl
            have e₂ : (Befehl.textIndex basis capacity).auswerten r₂ live = r₂.halt .ungueltigerWert := by
              simp only [Befehl.auswerten, ht₂, ho₂, if_pos hneg]
              rfl
            rw [e₁, e₂, sicht_halt, sicht_halt, h]
          · cases hbyte : text.bytes[offset.zahl.wert.toNat]? with
            | none =>
                have e₁ : (Befehl.textIndex basis capacity).auswerten r₁ live =
                    r₁.halt .ungueltigerWert := by
                  simp only [Befehl.auswerten, htextv, hoffv, if_neg hneg, hbyte]
                  rfl
                have e₂ : (Befehl.textIndex basis capacity).auswerten r₂ live =
                    r₂.halt .ungueltigerWert := by
                  simp only [Befehl.auswerten, ht₂, ho₂, if_neg hneg, hbyte]
                  rfl
                rw [e₁, e₂, sicht_halt, sicht_halt, h]
            | some byte =>
                have e₁ : (Befehl.textIndex basis capacity).auswerten r₁ live =
                    r₁.schreibe basis (some ⟨.int 0 255, byteValue byte⟩) := by
                  simp only [Befehl.auswerten, htextv, hoffv, if_neg hneg, hbyte]
                  rfl
                have e₂ : (Befehl.textIndex basis capacity).auswerten r₂ live =
                    r₂.schreibe basis (some ⟨.int 0 255, byteValue byte⟩) := by
                  simp only [Befehl.auswerten, ht₂, ho₂, if_neg hneg, hbyte]
                  rfl
                rw [e₁, e₂]
                exact sicht_schreibe_gleich β r₁ r₂ basis
                  (some ⟨.int 0 255, byteValue byte⟩) hT hL h

theorem substringSicht : SubstringSichtAussage := by
  intro β pc basis capacity htext hfirst hlast hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have htEq : (r₁.temp basis).bind (wertAls (.text capacity)) =
      (r₂.temp basis).bind (wertAls (.text capacity)) := by
    rw [tempPub basis htext]
  have hfEq : r₁.zahl (basis + 1) = r₂.zahl (basis + 1) := by
    simp only [Rahmen.zahl, tempPub (basis + 1) hfirst]
  have hlEq : r₁.zahl (basis + 2) = r₂.zahl (basis + 2) := by
    simp only [Rahmen.zahl, tempPub (basis + 2) hlast]
  cases htextv : (r₁.temp basis).bind (wertAls (.text capacity)) with
  | none =>
      have ht₂ : (r₂.temp basis).bind (wertAls (.text capacity)) = none := by
        rw [← htEq, htextv]
      have e₁ : (Befehl.substring basis capacity).auswerten r₁ live = r₁.halt .ungueltigerWert := by
        simp only [Befehl.auswerten, htextv]
        rfl
      have e₂ : (Befehl.substring basis capacity).auswerten r₂ live = r₂.halt .ungueltigerWert := by
        simp only [Befehl.auswerten, ht₂]
        rfl
      rw [e₁, e₂, sicht_halt, sicht_halt, h]
  | some text =>
      have ht₂ : (r₂.temp basis).bind (wertAls (.text capacity)) = some text := by
        rw [← htEq, htextv]
      cases hfirstv : r₁.zahl (basis + 1) with
      | none =>
          have hf₂ : r₂.zahl (basis + 1) = none := by
            rw [← hfEq, hfirstv]
          have e₁ : (Befehl.substring basis capacity).auswerten r₁ live = r₁.halt .ungueltigerWert := by
            simp only [Befehl.auswerten, htextv, hfirstv]
            rfl
          have e₂ : (Befehl.substring basis capacity).auswerten r₂ live = r₂.halt .ungueltigerWert := by
            simp only [Befehl.auswerten, ht₂, hf₂]
            rfl
          rw [e₁, e₂, sicht_halt, sicht_halt, h]
      | some first =>
          have hf₂ : r₂.zahl (basis + 1) = some first := by
            rw [← hfEq, hfirstv]
          cases hlastv : r₁.zahl (basis + 2) with
          | none =>
              have hl₂ : r₂.zahl (basis + 2) = none := by
                rw [← hlEq, hlastv]
              have e₁ : (Befehl.substring basis capacity).auswerten r₁ live =
                  r₁.halt .ungueltigerWert := by
                simp only [Befehl.auswerten, htextv, hfirstv, hlastv]
                rfl
              have e₂ : (Befehl.substring basis capacity).auswerten r₂ live =
                  r₂.halt .ungueltigerWert := by
                simp only [Befehl.auswerten, ht₂, hf₂, hl₂]
                rfl
              rw [e₁, e₂, sicht_halt, sicht_halt, h]
          | some last =>
              have hl₂ : r₂.zahl (basis + 2) = some last := by
                rw [← hlEq, hlastv]
              by_cases hgültig : 0 ≤ first.zahl.wert ∧ first.zahl.wert ≤ last.zahl.wert ∧
                  last.zahl.wert ≤ (text.bytes.size : Int)
              · have e₁ : (Befehl.substring basis capacity).auswerten r₁ live =
                    r₁.schreibe basis
                      (some ⟨.text capacity, text.slice first.zahl.wert.toNat last.zahl.wert.toNat⟩) := by
                  simp only [Befehl.auswerten, htextv, hfirstv, hlastv, if_pos hgültig]
                  rfl
                have e₂ : (Befehl.substring basis capacity).auswerten r₂ live =
                    r₂.schreibe basis
                      (some ⟨.text capacity, text.slice first.zahl.wert.toNat last.zahl.wert.toNat⟩) := by
                  simp only [Befehl.auswerten, ht₂, hf₂, hl₂, if_pos hgültig]
                  rfl
                rw [e₁, e₂]
                exact sicht_schreibe_gleich β r₁ r₂ basis
                  (some ⟨.text capacity, text.slice first.zahl.wert.toNat last.zahl.wert.toNat⟩) hT hL h
              · have e₁ : (Befehl.substring basis capacity).auswerten r₁ live =
                    r₁.halt .ungueltigerWert := by
                  simp only [Befehl.auswerten, htextv, hfirstv, hlastv, if_neg hgültig]
                  rfl
                have e₂ : (Befehl.substring basis capacity).auswerten r₂ live =
                    r₂.halt .ungueltigerWert := by
                  simp only [Befehl.auswerten, ht₂, hf₂, hl₂, if_neg hgültig]
                  rfl
                rw [e₁, e₂, sicht_halt, sicht_halt, h]

end Gabbro.Core.Ast.Semantik
