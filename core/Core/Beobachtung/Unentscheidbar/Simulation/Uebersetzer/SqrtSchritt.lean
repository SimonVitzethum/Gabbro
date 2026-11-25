module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Grundlagen

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Scratch slots for the square-root search, all at or above `frei`:
    `s` the counter, `u` its successor, `one` the constant one, `v` and `w`
    the squaring operands, `c` the comparison cell, `m` the input copy. -/
def sqrtInit (ein frei : Nat) : List Befehl :=
  [.literal frei 0, .literal (frei + 2) 1]

/-- One search iteration: `u := s + 1`, square it, compare with the input.
    Falls through to the back edge on `u * u ≤ n` and exits (fallthrough past
    the loop) otherwise. Loop entry `L0` is offset 2, exit is offset 25. -/
def sqrtLoop (ein frei : Nat) : List Befehl :=
  kopie (frei + 1) (frei + 0) ++ [.binaer .add (frei + 1)] ++
    kopie (frei + 3) (frei + 1) ++ kopie (frei + 4) (frei + 1) ++
    [.binaer .mul (frei + 3)] ++
    kopie (frei + 5) (frei + 3) ++ kopie (frei + 6) ein ++
    [.vergleichen .le (frei + 5)] ++ [.springeWenn (frei + 5) false 5] ++
    kopie (frei + 0) (frei + 1) ++ [.zurueckSprung 22]

/-- The whole search prefix: initialisation followed by the loop. -/
def sqrtPrefix (ein frei : Nat) : List Befehl :=
  sqrtInit ein frei ++ sqrtLoop ein frei

theorem sqrtInitLaenge (ein frei : Nat) : (sqrtInit ein frei).length = 2 := by
  rfl

theorem sqrtLoopLaenge (ein frei : Nat) : (sqrtLoop ein frei).length = 23 := by
  rfl

theorem sqrtPrefixLaenge (ein frei : Nat) : (sqrtPrefix ein frei).length = 25 := by
  rfl

/-- A literal writes the exact integer and advances by one. -/
theorem schrittLiteral (blk : List Befehl) (r : Rahmen) (p ziel : Nat) (v : Nat)
    (hpc : r.pc = p) (h : blk[p]? = some (.literal ziel v)) :
    Schritt blk (some r) = some { r with pc := r.pc + 1, temp := Function.update r.temp ziel (some (natVal v)) } := by
  have g : blk[r.pc]? = some (.literal ziel v) := by rw [hpc]; exact h
  simp only [Schritt, g]
  rfl

/-- Binding pushes the source slot onto the local scope. -/
theorem schrittBinden (blk : List Befehl) (r : Rahmen) (p quelle : Nat)
    (hpc : r.pc = p) (h : blk[p]? = some (.binden nameX quelle)) :
    Schritt blk (some r) = some { r with pc := r.pc + 1, lokale := r.temp quelle :: r.lokale } := by
  have g : blk[r.pc]? = some (.binden nameX quelle) := by rw [hpc]; exact h
  simp only [Schritt, g]
  rfl

/-- Reading restores the bound value into the target slot. -/
theorem schrittLesen (blk : List Befehl) (r : Rahmen) (p ziel : Nat) (v : Nat)
    (hpc : r.pc = p) (hq : r.lokale[0]?.join = some (natVal v))
    (h : blk[p]? = some (.lesen ziel 0)) :
    Schritt blk (some r) = some { r with pc := r.pc + 1, temp := Function.update r.temp ziel (some (natVal v)) } := by
  have g : blk[r.pc]? = some (.lesen ziel 0) := by rw [hpc]; exact h
  simp only [Schritt, g, Befehl.auswerten, Rahmen.schreibe, hq]

/-- Ending a block drops the given number of locals. -/
theorem schrittBlockEnde (blk : List Befehl) (r : Rahmen) (p count : Nat)
    (hpc : r.pc = p) (h : blk[p]? = some (.blockEnde count)) :
    Schritt blk (some r) = some { r with pc := r.pc + 1, lokale := r.lokale.drop count } := by
  have g : blk[r.pc]? = some (.blockEnde count) := by rw [hpc]; exact h
  simp only [Schritt, g]
  rfl

/-- A copy segment moves one slot into another in three steps, restoring the
    local scope; only the program counter and the target slot change. -/
theorem laufKopie (blk : List Befehl) (r : Rahmen) (p ziel quelle : Nat)
    (x : Option Dynamisch)
    (hpc : r.pc = p) (hq : r.temp quelle = x)
    (h0 : blk[p]? = some (.binden nameX quelle))
    (h1 : blk[p + 1]? = some (.lesen ziel 0))
    (h2 : blk[p + 2]? = some (.blockEnde 1)) :
    (Schritt blk)^[3] (some r) = some { r with pc := p + 3, temp := Function.update r.temp ziel x } := by
  have g0 : blk[r.pc]? = some (.binden nameX quelle) := by rw [hpc]; exact h0
  have e1 : Schritt blk (some r) = some { r with pc := r.pc + 1, lokale := r.temp quelle :: r.lokale } := by
    simp only [Schritt, g0]
    rfl
  have hpc1 : r.pc + 1 = p + 1 := by omega
  have g1 : blk[r.pc + 1]? = some (.lesen ziel 0) := by rw [hpc1]; exact h1
  have hl : ((r.temp quelle :: r.lokale)[0]?.join) = x := by rw [hq]; rfl
  have e2 : Schritt blk (some { r with pc := r.pc + 1, lokale := r.temp quelle :: r.lokale }) = some { r with pc := r.pc + 1 + 1, temp := Function.update r.temp ziel x, lokale := r.temp quelle :: r.lokale } := by
    simp only [Schritt, g1, Befehl.auswerten, Rahmen.schreibe, hl]
  have hpc2 : r.pc + 1 + 1 = p + 2 := by omega
  have g2 : blk[r.pc + 1 + 1]? = some (.blockEnde 1) := by rw [hpc2]; exact h2
  have e3 : Schritt blk (some { r with pc := r.pc + 1 + 1, temp := Function.update r.temp ziel x, lokale := r.temp quelle :: r.lokale }) = some { r with pc := r.pc + 1 + 1 + 1, temp := Function.update r.temp ziel x, lokale := r.lokale } := by
    simp only [Schritt, g2]
    rfl
  have e : (Schritt blk)^[3] (some r) = Schritt blk (Schritt blk (Schritt blk (some r))) := rfl
  have hpc3 : r.pc + 1 + 1 + 1 = p + 3 := by omega
  rw [e, e1, e2, e3, hpc3]

/-- A binary operation consumes the two slots above and writes the result. -/
theorem schrittBinaer (blk : List Befehl) (r : Rahmen) (p links : Nat)
    (op : Arith) (a b : Ganzzahl)
    (hpc : r.pc = p)
    (ha : r.zahl links = some a) (hb : r.zahl (links + 1) = some b)
    (h : blk[p]? = some (.binaer op links)) :
    Schritt blk (some r) = some { r with pc := r.pc + 1, temp := Function.update r.temp links (some (Ganzzahl.pack ⟨_, _, Arith.auswerten op a.zahl b.zahl⟩)) } := by
  have g : blk[r.pc]? = some (.binaer op links) := by rw [hpc]; exact h
  simp only [Schritt, g, Befehl.auswerten, Rahmen.schreibe, ha, hb]
  rfl

/-- A comparison writes the boolean outcome into the same slot. -/
theorem schrittVergleichen (blk : List Befehl) (r : Rahmen) (p links : Nat)
    (op : Compare) (a b : Ganzzahl)
    (hpc : r.pc = p)
    (ha : r.zahl links = some a) (hb : r.zahl (links + 1) = some b)
    (h : blk[p]? = some (.vergleichen op links)) :
    Schritt blk (some r) = some { r with pc := r.pc + 1, temp := Function.update r.temp links (some ⟨.bool, op.eval a.zahl.wert b.zahl.wert⟩) } := by
  have g : blk[r.pc]? = some (.vergleichen op links) := by rw [hpc]; exact h
  simp only [Schritt, g, Befehl.auswerten, Rahmen.schreibe, ha, hb]
  rfl

/-- A conditional jump taken: the value matches, the distance is added. -/
theorem auswertenSpringeWennWahr (r : Rahmen) (c : Nat) (wv : Bool) (dist : Nat)
    (w : Bool) (h : r.temp c = some ⟨.bool, w⟩) (e : w = wv) :
    (Befehl.springeWenn c wv dist).auswerten r = { r with pc := r.pc + dist } := by
  have hb : ((r.temp c).bind alsBoolean) = some w := by rw [h]; rfl
  simp only [Befehl.auswerten, hb, e, eq_self_iff_true, if_true]

/-- A conditional jump not taken: any other value advances by one. -/
theorem auswertenSpringeWennFalsch (r : Rahmen) (c : Nat) (wv : Bool) (dist : Nat)
    (w : Bool) (h : r.temp c = some ⟨.bool, w⟩) (e : w ≠ wv) :
    (Befehl.springeWenn c wv dist).auswerten r = { r with pc := r.pc + 1 } := by
  have hb : ((r.temp c).bind alsBoolean) = some w := by rw [h]; rfl
  simp only [Befehl.auswerten, hb, Option.some_inj, e, if_false]

theorem schrittSpringeWennWahr (blk : List Befehl) (r : Rahmen) (p c : Nat)
    (wv w : Bool) (dist : Nat)
    (hpc : r.pc = p) (h : r.temp c = some ⟨.bool, w⟩) (e : w = wv)
    (g : blk[p]? = some (.springeWenn c wv dist)) :
    Schritt blk (some r) = some { r with pc := r.pc + dist } := by
  have g0 : blk[r.pc]? = some (.springeWenn c wv dist) := by rw [hpc]; exact g
  have e2 := auswertenSpringeWennWahr r c wv dist w h e
  simp only [Schritt, g0, e2]

theorem schrittSpringeWennFalsch (blk : List Befehl) (r : Rahmen) (p c : Nat)
    (wv w : Bool) (dist : Nat)
    (hpc : r.pc = p) (h : r.temp c = some ⟨.bool, w⟩) (e : w ≠ wv)
    (g : blk[p]? = some (.springeWenn c wv dist)) :
    Schritt blk (some r) = some { r with pc := r.pc + 1 } := by
  have g0 : blk[r.pc]? = some (.springeWenn c wv dist) := by rw [hpc]; exact g
  have e2 := auswertenSpringeWennFalsch r c wv dist w h e
  simp only [Schritt, g0, e2]

/-- An unconditional forward jump adds its distance. -/
theorem schrittSpringe (blk : List Befehl) (r : Rahmen) (p dist : Nat)
    (hpc : r.pc = p) (h : blk[p]? = some (.springe dist)) :
    Schritt blk (some r) = some { r with pc := r.pc + dist } := by
  have g : blk[r.pc]? = some (.springe dist) := by rw [hpc]; exact h
  simp only [Schritt, g]
  rfl

/-- An unconditional backward jump subtracts its distance. -/
theorem schrittZurueck (blk : List Befehl) (r : Rahmen) (p dist : Nat)
    (hpc : r.pc = p) (h : blk[p]? = some (.zurueckSprung dist)) :
    Schritt blk (some r) = some { r with pc := r.pc - dist } := by
  have g : blk[r.pc]? = some (.zurueckSprung dist) := by rw [hpc]; exact h
  simp only [Schritt, g]
  rfl

/-- The successor value on machine integers is the cast successor. -/
theorem intSuccCast (s : Nat) : (s : Int) + ((1 : Nat) : Int) = (((s + 1 : Nat)) : Int) := by
  simp only [Nat.cast_add, Nat.cast_one]

/-- Comparing the squared successor with the input decides the loop exit. -/
theorem intSqSuccLe (s n : Nat) :
    ((s : Int) + ((1 : Nat) : Int)) * ((s : Int) + ((1 : Nat) : Int)) ≤ (n : Int) ↔
      (s + 1) * (s + 1) ≤ n := by
  rw [intSuccCast, ← Nat.cast_mul, Nat.cast_le]

/-- A disequality of offsets lifts to a disequality of scratch slots:
    cancelling the common base leaves a closed literal disequality, which
    the decision guard admits. Replaces `omega` on open slot goals. -/
theorem addNeLinks {frei a b : Nat} (h : a ≠ b) : frei + a ≠ frei + b :=
  fun e => h (Nat.add_left_cancel e)

/-- A slot below the scratch base differs from every scratch slot:
    below the base means below the base plus any offset. -/
theorem ltNeAdd {t frei k : Nat} (h : t < frei) : t ≠ frei + k :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right frei k))

/-- Adding one on the machine is the successor as an exact integer. -/
theorem packAddSucc (s : Nat) : (Ganzzahl.pack ⟨_, _,
    Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal ((1 : Nat) : Int))⟩) = natVal (s + 1) := by
  rfl

/-- A scratch slot at or above the base differs from any user slot below. -/
theorem scratchNeAus {frei aus s : Nat} (hle : frei ≤ s) (haus : aus < frei) : s ≠ aus :=
  Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le haus hle))

/-- Reading back an exact integer slot yields its bounds and value. -/
theorem zahlOfNat (t : Rahmen) (s N : Nat) (h : t.temp s = some (natVal N)) :
    t.zahl s = some ⟨((N : Nat) : Int), ((N : Nat) : Int), Zahl.literal ((N : Nat) : Int)⟩ := by
  show (((t.temp s).bind alsGanzzahl) = _
  rw [h]
  rfl

/-- Below the root, the successor square still fits into the input. -/
theorem weiterUnter (s n : Nat) (h : s < Nat.sqrt n) : (s + 1) * (s + 1) ≤ n := by
  have hle : s + 1 ≤ Nat.sqrt n := by omega
  exact Nat.le_trans (Nat.mul_le_mul hle hle) (Nat.sqrt_le n)

/-- At the root, the successor square exceeds the input. -/
theorem exitUeber (n : Nat) : ¬ ((Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ n) := by
  intro h
  have hle : Nat.sqrt n + 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr h
  omega

/-- The machine difference `n - s * s` as a natural number. -/
theorem intSubNat (s n : Nat) (h : s * s ≤ n) :
    (n : Int) - (s : Int) * (s : Int) = (((n - s * s : Nat)) : Int) := by
  have c1 : (s : Int) * (s : Int) = (((s * s : Nat)) : Int) := (Nat.cast_mul s s).symm
  rw [c1, ← Nat.cast_sub h]

/-- The multiplication bounds collapse on equal operands. -/
theorem hmul_lo (s : Nat) : min (min ((s : Int) * (s : Int)) ((s : Int) * (s : Int)))
    (min ((s : Int) * (s : Int)) ((s : Int) * (s : Int))) = (s : Int) * (s : Int) := by
  omega

theorem hmul_hi (s : Nat) : max (max ((s : Int) * (s : Int)) ((s : Int) * (s : Int)))
    (max ((s : Int) * (s : Int)) ((s : Int) * (s : Int))) = (s : Int) * (s : Int) := by
  omega

/-- An exact integer package with computed bounds is the natural value:
    substituting the bound and value equations (all variables) avoids
    rewriting inside dependent proof fields. -/
theorem packEqOfBounds (lo hi : Int) (Z : Zahl lo hi) (C : Nat)
    (hlo : lo = (C : Int)) (hhi : hi = (C : Int)) (hw : Z.wert = (C : Int)) :
    (Ganzzahl.pack ⟨lo, hi, Z⟩ : Dynamisch) = natVal C := by
  subst hlo
  subst hhi
  cases Z with
  | mk w p q =>
    have hw' : w = (((C : Nat)) : Int) := hw
    subst hw'
    rfl

/-- The squared counter as an exact integer. -/
theorem packSqCast (s : Nat) :
    (Ganzzahl.pack ⟨_, _, Arith.auswerten .mul
      (Zahl.literal (s : Int)) (Zahl.literal (s : Int))⟩) = natVal (s * s) := by
  have e : (s : Int) * (s : Int) = (((s * s : Nat)) : Int) := (Nat.cast_mul s s).symm
  have hlo : (Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1 =
      (((s * s : Nat)) : Int) := by
    show min (min ((s : Int) * (s : Int)) ((s : Int) * (s : Int)))
      (min ((s : Int) * (s : Int)) ((s : Int) * (s : Int))) = _
    omega
  have hhi : (Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2 =
      (((s * s : Nat)) : Int) := by
    show max (max ((s : Int) * (s : Int)) ((s : Int) * (s : Int)))
      (max ((s : Int) * (s : Int)) ((s : Int) * (s : Int))) = _
    omega
  have hw : (Arith.auswerten .mul
      (Zahl.literal (s : Int)) (Zahl.literal (s : Int))).wert =
      (((s * s : Nat)) : Int) := e
  exact packEqOfBounds _ _ _ _ hlo hhi hw

/-- The machine difference `n - s * s` as an exact integer. -/
theorem packSubCast (s n : Nat) (h : s * s ≤ n) :
    (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int))
      (Arith.auswerten .mul (Zahl.literal (s : Int)) (Zahl.literal (s : Int)))⟩) =
      natVal (n - s * s) := by
  have e := intSubNat s n h
  have hmul : (s : Int) * (s : Int) = (((s * s : Nat)) : Int) := (Nat.cast_mul s s).symm
  have hlo : (Arith.sub.bounds (n : Int) (n : Int)
      (Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1
      (Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2).1 =
      (((n - s * s : Nat)) : Int) := by
    show (n : Int) - max (max ((s : Int) * (s : Int)) ((s : Int) * (s : Int)))
      (max ((s : Int) * (s : Int)) ((s : Int) * (s : Int))) = _
    omega
  have hhi : (Arith.sub.bounds (n : Int) (n : Int)
      (Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).1
      (Arith.mul.bounds (s : Int) (s : Int) (s : Int) (s : Int)).2).2 =
      (((n - s * s : Nat)) : Int) := by
    show (n : Int) - min (min ((s : Int) * (s : Int)) ((s : Int) * (s : Int)))
      (min ((s : Int) * (s : Int)) ((s : Int) * (s : Int))) = _
    omega
  have hw : (Arith.auswerten .sub (Zahl.literal (n : Int))
      (Arith.auswerten .mul (Zahl.literal (s : Int)) (Zahl.literal (s : Int)))).wert =
      (((n - s * s : Nat)) : Int) := e
  exact packEqOfBounds _ _ _ _ hlo hhi hw
/-- The machine difference reads back as the natural difference. -/
theorem natAusgabeSub (s n : Nat) (h : s * s ≤ n) : NatAusgabe
    (Ganzzahl.pack ⟨_, _, Arith.auswerten .sub (Zahl.literal (n : Int))
      (Arith.auswerten .mul (Zahl.literal (s : Int)) (Zahl.literal (s : Int)))⟩) = some (n - s * s) := by
  have hval : (Arith.auswerten .sub (Zahl.literal (n : Int))
      (Arith.auswerten .mul (Zahl.literal (s : Int)) (Zahl.literal (s : Int)))).wert = (n : Int) - (s : Int) * (s : Int) := rfl
  have h0 : (0 : Int) ≤ (n : Int) - (s : Int) * (s : Int) := by
    have e : (s : Int) * (s : Int) = (((s * s : Nat)) : Int) := (Nat.cast_mul s s).symm
    have hn : ((((s * s : Nat))) : Int) ≤ (n : Int) := Nat.cast_le.mpr h
    omega
  have e := intSubNat s n h
  simp only [NatAusgabe, alsGanzzahl, Ganzzahl.pack]
  rw [hval, if_pos h0, e, Int.toNat_natCast]

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
