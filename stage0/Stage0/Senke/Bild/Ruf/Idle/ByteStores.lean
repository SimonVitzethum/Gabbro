module

public import Stage0.Senke.Bild.Ruf.Idle.Expression
public import Stage0.Senke.Anweisung.Bytes.Span.Code

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

theorem slotA_withIdle (L : Lay D) (table : D.Tab) (field : D.Feld table) (d : Nat)
    (index : List II × Nat) :
    slotA L.withIdle table field d index = slotA L table field d index := rfl

theorem putBytesL_withIdle (L : Lay D) {Γ : Ctx} {Λ : List (Res D)}
    (table : D.Tab) (field : D.Feld table) (a b H : Int) (lower : 0 ≤ a) (reserved : Nat) :
    ∀ (n j : Nat) (upper : b + j + n ≤ D.count table),
      putBytesL L.withIdle (Γ := Γ.map tyR) (Λ := Λ.map resR) table field a b H lower reserved n j upper =
        putBytesL L (Γ := Γ) (Λ := Λ) table field a b H lower reserved n j upper
  | 0, _, _ => by simp only [putBytesL, frei_withIdle]
  | n + 1, j, upper => by
    let word := byteIndex (Γ := Γ) (Λ := Λ) table a b H j lower (by omega)
    have mapped := lowE_withIdle L reserved true word (frei Γ reserved + 3)
    have indexCode : lowE L.withIdle
        (byteIndex (Γ := Γ.map tyR) (Λ := Λ.map resR) table a b H j lower
          (by change b + j < D.count table; omega))
          (frei Γ reserved + 3) reserved = lowE L word (frei Γ reserved + 3) reserved :=
      mapped
    simp only [putBytesL, frei_withIdle, indexCode, slotA_withIdle,
      putBytesL_withIdle L table field a b H lower reserved n (j + 1) (by omega), word]
termination_by structural n _ _ => n

theorem putBytesWordsL_withIdle (L : Lay D) {Γ : Ctx} {Λ : List (Res D)}
    (table : D.Tab) (field : D.Feld table) (a b H : Int) (lower : 0 ≤ a) (reserved : Nat) :
    ∀ (words n q : Nat) (upper : b + 8 * q + n ≤ D.count table),
      putBytesWordsL L.withIdle (Γ := Γ.map tyR) (Λ := Λ.map resR) table field a b H lower reserved
        words n q upper = putBytesWordsL L (Γ := Γ) (Λ := Λ) table field a b H lower reserved words n q upper
  | 0, _, _, _ => by
    simp only [putBytesWordsL, show ByteCapture (Γ.map tyR) a b H = (ByteCapture Γ a b H).map tyR from rfl,
      frei_withIdle]
  | words + 1, n, q, upper => by
    let source := chunkIndex (D := D) (Γ := Γ) (Λ := Λ) a b H q
    have bound := lowE_withIdle L reserved true source (frei (ByteCapture Γ a b H) reserved + 1)
    have compiled : lowE L.withIdle (chunkIndex (Γ := Γ.map tyR) (Λ := Λ.map resR) a b H q)
        (frei (ByteCapture Γ a b H) reserved + 1) reserved =
        lowE L source (frei (ByteCapture Γ a b H) reserved + 1) reserved := bound
    have captured : ByteCapture (Γ.map tyR) a b H = (ByteCapture Γ a b H).map tyR := rfl
    simp only [putBytesWordsL, captured, frei_withIdle, compiled, source, putBytesL_withIdle]
    split
    · rfl
    · by_cases more : 8 < n
      · simp only [dif_pos more,
          putBytesWordsL_withIdle L table field a b H lower reserved words (n - 8) (q + 1) (by omega)]
      · simp only [dif_neg more]
termination_by structural words _ _ _ => words

theorem putBytesWideL_withIdle (L : Lay D) {Γ : Ctx} {Λ : List (Res D)}
    (table : D.Tab) (field : D.Feld table) (a b : Int) (n : Nat) (lower : 0 ≤ a)
    (upper : b + n ≤ D.count table) (value index : Option (List II × Nat)) (reserved : Nat) :
    putBytesWideL L.withIdle (Γ := Γ.map tyR) (Λ := Λ.map resR) table field a b n lower upper value index reserved =
      putBytesWideL L (Γ := Γ) (Λ := Λ) table field a b n lower upper value index reserved := by
  have captured : ByteCapture (Γ.map tyR) a b (256 ^ n - 1) =
      (ByteCapture Γ a b (256 ^ n - 1)).map tyR := rfl
  simp only [putBytesWideL, putBytesWordsL_withIdle, captured, frei_withIdle]

end Gabbro.Stage0.Senke
