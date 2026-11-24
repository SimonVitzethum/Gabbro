module

public import Core.Beobachtung.Fluss.Beschriftung.Aufgaben

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung

theorem sicht_zuweis (β : Beschriftung) (r : Rahmen) (live : Nat → Bool)
    (src index : Nat) (zieltyp : Ty .value) :
    ((Befehl.zuweisen src index zieltyp).auswerten r live).sicht β =
      { r.sicht β with
        pc := r.pc + 1
        temp := fun s => if oeffentlich (β.temp (r.pc + 1) s) = true then r.temp s else none
        lokale := maskiere (β.lokal (r.pc + 1)) 0
          (r.lokale.set index ((r.temp src).bind (wertIn zieltyp))) } :=
  rfl

theorem sicht_binden (β : Beschriftung) (r : Rahmen) (live : Nat → Bool)
    (name : Identifier) (src : Nat) :
    ((Befehl.binden name src).auswerten r live).sicht β =
      { r.sicht β with
        pc := r.pc + 1
        temp := fun s => if oeffentlich (β.temp (r.pc + 1) s) = true then r.temp s else none
        lokale := maskiere (β.lokal (r.pc + 1)) 0 (r.temp src :: r.lokale) } :=
  rfl

theorem sicht_bindeWert (β : Beschriftung) (r : Rahmen) (live : Nat → Bool)
    (src : Nat) (zieltyp : Ty .value) (global : Bool) :
    ((Befehl.bindeWert src zieltyp global).auswerten r live).sicht β =
      { r.sicht β with
        pc := r.pc + 1
        temp := fun s => if oeffentlich (β.temp (r.pc + 1) s) = true then r.temp s else none
        lokale := maskiere (β.lokal (r.pc + 1)) 0
          (((r.temp src).bind (wertIn zieltyp)) :: r.lokale)
        globale := if global then ((r.temp src).bind (wertIn zieltyp)) :: r.globale else r.globale } :=
  rfl

theorem sicht_blockEnde (β : Beschriftung) (r : Rahmen) (live : Nat → Bool) (count : Nat) :
    ((Befehl.blockEnde count).auswerten r live).sicht β =
      { r.sicht β with
        pc := r.pc + 1
        temp := fun s => if oeffentlich (β.temp (r.pc + 1) s) = true then r.temp s else none
        lokale := maskiere (β.lokal (r.pc + 1)) 0 (r.lokale.drop count) } :=
  rfl

theorem maskiere_verschoben (l : Nat → Etikett) :
    ∀ (i : Nat) (xs : List (Option Dynamisch)),
      maskiere l (i + 1) xs = maskiere (fun j => l (j + 1)) i xs := by
  intro i xs
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    change (if oeffentlich (l (i + 1)) = true then x else none) :: maskiere l (i + 1 + 1) xs =
      (if oeffentlich (l (i + 1)) = true then x else none) ::
        maskiere (fun j => l (j + 1)) (i + 1) xs
    rw [ih]

theorem maskiere_gleich_mono_von {l₀ l₁ : Nat → Etikett} :
    ∀ (start : Nat),
      (∀ j, start ≤ j → oeffentlich (l₁ j) = true → oeffentlich (l₀ j) = true) →
      ∀ (xs ys : List (Option Dynamisch)),
        maskiere l₀ start xs = maskiere l₀ start ys → maskiere l₁ start xs = maskiere l₁ start ys
  | _, _, [], ys, e => by
      have laenge : ys.length = 0 := by
        rw [← maskiere_laenge l₀ _ ys, ← e]
        rfl
      cases ys with
      | nil => rfl
      | cons _ _ => cases laenge
  | start, h, x :: xs, ys, e => by
      cases ys with
      | nil =>
        have laenge := congrArg List.length e
        simp only [maskiere, maskiere_laenge, List.length_cons, List.length_nil] at laenge
        cases laenge
      | cons y ys =>
        simp only [maskiere, List.cons.injEq] at e ⊢
        refine ⟨?_, maskiere_gleich_mono_von (start + 1)
          (fun j hj hjpub => h j (by omega) hjpub) xs ys e.2⟩
        by_cases hp : oeffentlich (l₁ start) = true
        · have hq := h start le_rfl hp
          simpa only [hp, hq, if_true] using e.1
        · simp only [if_neg hp]

theorem maskiere_set_hilf {l₀ l₁ : Nat → Etikett} :
    ∀ (i d : Nat) (xs ys : List (Option Dynamisch)) (v₁ v₂ : Option Dynamisch),
      (∀ j, j ≠ i + d → oeffentlich (l₁ j) = true → oeffentlich (l₀ j) = true) →
      (oeffentlich (l₁ (i + d)) = true → v₁ = v₂) →
      maskiere l₀ i xs = maskiere l₀ i ys →
      maskiere l₁ i (xs.set d v₁) = maskiere l₁ i (ys.set d v₂)
  | _, _, [], ys, _, _, hL, hV, e => by
      have laenge : ys.length = 0 := by
        rw [← maskiere_laenge l₀ _ ys, ← e]
        rfl
      cases ys with
      | nil => rfl
      | cons _ _ => cases laenge
  | i, d, x :: xs, ys, v₁, v₂, hL, hV, e => by
      cases ys with
      | nil =>
        have laenge := congrArg List.length e
        simp only [maskiere, maskiere_laenge, List.length_cons, List.length_nil] at laenge
        cases laenge
      | cons y ys =>
        cases d with
        | zero =>
          simp only [Nat.add_zero, List.set_cons_zero, maskiere, List.cons.injEq] at hL hV e ⊢
          refine ⟨?_, ?_⟩
          · by_cases hp : oeffentlich (l₁ i) = true
            · simp only [hp, if_true]
              exact hV hp
            · simp only [if_neg hp]
          · exact maskiere_gleich_mono_von (i + 1)
              (fun j hj hjpub => hL j (by omega) hjpub) xs ys e.2
        | succ d =>
          simp only [List.set_cons_succ, maskiere, List.cons.injEq] at e ⊢
          refine ⟨?_, ?_⟩
          · by_cases hp : oeffentlich (l₁ i) = true
            · have hq := hL i (by omega) hp
              simpa only [hp, hq, if_true] using e.1
            · simp only [if_neg hp]
          · exact maskiere_set_hilf (i + 1) d xs ys v₁ v₂
              (fun j hj hjpub => hL j (by omega) hjpub)
              (fun hp => hV (by
                have hz : i + 1 + d = i + (d + 1) := by omega
                simpa only [hz] using hp))
              e.2

theorem maskiere_set {l₀ l₁ : Nat → Etikett} {index : Nat}
    {xs ys : List (Option Dynamisch)} {v₁ v₂ : Option Dynamisch}
    (hL : ∀ j, j ≠ index → oeffentlich (l₁ j) = true → oeffentlich (l₀ j) = true)
    (hV : oeffentlich (l₁ index) = true → v₁ = v₂)
    (lokEq : maskiere l₀ 0 xs = maskiere l₀ 0 ys) :
    maskiere l₁ 0 (xs.set index v₁) = maskiere l₁ 0 (ys.set index v₂) :=
  maskiere_set_hilf 0 index xs ys v₁ v₂
    (by intro j hj; exact hL j (by simpa only [Nat.zero_add] using hj))
    (by intro hp; exact hV (by simpa only [Nat.zero_add] using hp))
    lokEq

theorem maskiere_einschieben {l₀ l₁ : Nat → Etikett}
    {xs ys : List (Option Dynamisch)} {v₁ v₂ : Option Dynamisch}
    (hL : ∀ i, oeffentlich (l₁ (i + 1)) = true → oeffentlich (l₀ i) = true)
    (hV : oeffentlich (l₁ 0) = true → v₁ = v₂)
    (lokEq : maskiere l₀ 0 xs = maskiere l₀ 0 ys) :
    maskiere l₁ 0 (v₁ :: xs) = maskiere l₁ 0 (v₂ :: ys) := by
  have hSchwanz : maskiere l₁ 1 xs = maskiere l₁ 1 ys :=
    (maskiere_verschoben l₁ 0 xs).trans
      ((maskiere_gleich_mono hL 0 xs ys lokEq).trans (maskiere_verschoben l₁ 0 ys).symm)
  by_cases hp : oeffentlich (l₁ 0) = true
  · simp only [maskiere, hp, if_true, hV hp, hSchwanz]
  · simp only [maskiere, if_neg hp, hSchwanz]

theorem maskiere_drop_gleich {l₀ l₁ : Nat → Etikett} :
    ∀ (count : Nat) (xs ys : List (Option Dynamisch)),
      (∀ i, oeffentlich (l₁ i) = true → oeffentlich (l₀ (count + i)) = true) →
      maskiere l₀ 0 xs = maskiere l₀ 0 ys →
      maskiere l₁ 0 (xs.drop count) = maskiere l₁ 0 (ys.drop count)
  | 0, xs, ys, hL, e => by
      have hL' : ∀ i, oeffentlich (l₁ i) = true → oeffentlich (l₀ i) = true :=
        fun i hi => by simpa only [Nat.zero_add] using hL i hi
      simpa only [Nat.zero_add, List.drop_zero] using (maskiere_gleich_mono hL' 0 xs ys e)
  | count + 1, xs, ys, hL, e => by
      cases xs with
      | nil =>
        have laenge : ys.length = 0 := by
          rw [← maskiere_laenge l₀ _ ys, ← e]
          rfl
        cases ys with
        | nil => rfl
        | cons _ _ => cases laenge
      | cons x xs =>
        cases ys with
        | nil =>
          have laenge := congrArg List.length e
          simp only [maskiere, maskiere_laenge, List.length_cons, List.length_nil] at laenge
          cases laenge
        | cons y ys =>
          simp only [maskiere, List.cons.injEq] at e
          have hL' : ∀ i, oeffentlich (l₁ i) = true →
              oeffentlich ((fun j => l₀ (j + 1)) (count + i)) = true := by
            intro i hi
            have hz : count + 1 + i = count + i + 1 := by omega
            have h := hL i hi
            rwa [hz] at h
          have e' : maskiere (fun j => l₀ (j + 1)) 0 xs = maskiere (fun j => l₀ (j + 1)) 0 ys :=
            (maskiere_verschoben l₀ 0 xs).symm.trans
              (e.2.trans (maskiere_verschoben l₀ 0 ys))
          simpa only [List.drop_succ_cons] using
            (maskiere_drop_gleich (l₀ := fun j => l₀ (j + 1)) (l₁ := l₁) count xs ys hL' e')

theorem zuweisenSicht : ZuweisenSichtAussage := by
  intro β pc quelle index zieltyp hT hL hIndex r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hV : oeffentlich (β.lokal (r₁.pc + 1) index) = true →
      (r₁.temp quelle).bind (wertIn zieltyp) = (r₂.temp quelle).bind (wertIn zieltyp) := by
    intro hi
    rw [tempPub quelle (hIndex hi)]
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hLe := maskiere_set (l₀ := β.lokal r₁.pc) (l₁ := β.lokal (r₁.pc + 1))
    (index := index) (xs := r₁.lokale) (ys := r₂.lokale)
    (v₁ := (r₁.temp quelle).bind (wertIn zieltyp))
    (v₂ := (r₂.temp quelle).bind (wertIn zieltyp)) hL hV lokEq
  rw [sicht_zuweis, sicht_zuweis, h, pcEq, hTe, hLe]

theorem bindenSicht : BindenSichtAussage := by
  intro β pc name quelle hT hL hKopf r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hLe := maskiere_einschieben (l₀ := β.lokal r₁.pc) (l₁ := β.lokal (r₁.pc + 1))
    (xs := r₁.lokale) (ys := r₂.lokale) (v₁ := r₁.temp quelle) (v₂ := r₂.temp quelle)
    hL (fun hp => tempPub quelle (hKopf hp)) lokEq
  rw [sicht_binden, sicht_binden, h, pcEq, hTe, hLe]

theorem bindeWertSicht : BindeWertSichtAussage := by
  intro β pc quelle zieltyp global hT hL hKopf hGlobal r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hLe := maskiere_einschieben (l₀ := β.lokal r₁.pc) (l₁ := β.lokal (r₁.pc + 1))
    (xs := r₁.lokale) (ys := r₂.lokale)
    (v₁ := (r₁.temp quelle).bind (wertIn zieltyp))
    (v₂ := (r₂.temp quelle).bind (wertIn zieltyp))
    hL (fun hp => by rw [tempPub quelle (hKopf hp)]) lokEq
  have globEq : r₁.globale = r₂.globale := by
    simpa only [Rahmen.sicht] using congrArg (fun r : Rahmen => (r.sicht β).globale) h
  have hWert : global = true →
      (r₁.temp quelle).bind (wertIn zieltyp) = (r₂.temp quelle).bind (wertIn zieltyp) := by
    intro hg
    rw [tempPub quelle (hGlobal hg)]
  have hGl : (if global then ((r₁.temp quelle).bind (wertIn zieltyp)) :: r₁.globale else r₁.globale) =
      (if global then ((r₂.temp quelle).bind (wertIn zieltyp)) :: r₂.globale else r₂.globale) := by
    by_cases hg : global = true
    · simp only [if_pos hg, hWert hg, globEq]
    · simp only [if_neg hg, globEq]
  rw [sicht_bindeWert, sicht_bindeWert, h, pcEq, hTe, hLe, hGl]

theorem blockEndeSicht : BlockEndeSichtAussage := by
  intro β pc count hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hLe := maskiere_drop_gleich (l₀ := β.lokal r₁.pc) (l₁ := β.lokal (r₁.pc + 1))
    count r₁.lokale r₂.lokale (fun i hi => by rw [Nat.add_comm]; exact hL i hi) lokEq
  rw [sicht_blockEnde, sicht_blockEnde, h, pcEq, hTe, hLe]

end Gabbro.Core.Ast.Semantik
