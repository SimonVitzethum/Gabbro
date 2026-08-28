import GabbroProgram
set_option autoImplicit false
open Gabbro.Body GabbroProgram

-- GIFT 1: die Spezifikation verlangt Menge 5, der Rumpf setzt 0.
def falsch_geraeumt (f : Int) (s : State) : Prop :=
  s.world (.slot "Faecher" f "menge") = .int 5

theorem gift1 (ρ : Env) (s : State) (f : Int) (hf : s.local' "f" = .int f) :
    ∃ s', finalState (exec ρ raeumen_body s) = some s' ∧ falsch_geraeumt f s' := by
  gabbro_simp [raeumen_body, falsch_geraeumt, hf]

-- GIFT 2: die Spezifikation verlangt, dass JEDES Fach unberuehrt bleibt -- auch `f`.
def falscher_rahmen (f : Int) (s s' : State) : Prop :=
  ∀ g, s'.world (.slot "Faecher" g "belegt") = s.world (.slot "Faecher" g "belegt")

theorem gift2 (ρ : Env) (s : State) (f : Int) (hf : s.local' "f" = .int f)
    (hoffen : s.world (.slot "Faecher" f "belegt") = .bool true) :
    ∃ s', finalState (exec ρ raeumen_body s) = some s' ∧ falscher_rahmen f s s' := by
  gabbro_simp [raeumen_body, falscher_rahmen, hf, hoffen]

-- GIFT 3: die Spezifikation nennt ein Feld, das es nicht gibt.
def erfundenes_feld (f : Int) (s : State) : Prop :=
  s.world (.slot "Faecher" f "gewicht") = .int 0

theorem gift3 (ρ : Env) (s : State) (f : Int) (hf : s.local' "f" = .int f) :
    ∃ s', finalState (exec ρ raeumen_body s) = some s' ∧ erfundenes_feld f s' := by
  gabbro_simp [raeumen_body, erfundenes_feld, hf]

-- GIFT 4: **die Spezifikation RUNDET AB, wo C abschneidet.** `-7 / 2` ist in Lean `-4` und
-- in C `-3`; das Modell nimmt `Int.tdiv`, und darum faellt dieser Satz. Das ist die eine
-- Falle, die die alte Absage `division-or-bits` beim Namen nannte -- jetzt steht sie nicht
-- mehr als Absage da, sondern als Satz, den jemand hat fallen sehen.
def falsch_gerundet (f : Int) (s : State) : Prop :=
  s.world (.slot "Faecher" f "menge") = .int (-4)

theorem gift4 (ρ : Env) (s : State) (f : Int) (hf : s.local' "f" = .int f)
    (hroh : s.local' "roh" = .int 0)
    (hm : s.world (.slot "Faecher" f "menge") = .int (-7)) :
    ∃ s', finalState (exec ρ kennzeichnen_body s) = some s' ∧ falsch_gerundet f s' := by
  gabbro_simp [kennzeichnen_body, falsch_gerundet, hf, hroh, hm]

-- GIFT 5: **die Maske wird als Wahrheitswert gelesen.** `27 >> 4` ist `1` und `1 & 3` ist
-- `1` -- nicht `3`. Ein `&`, das man fuer ein logisches Und haelt, rechnet genau so daneben.
def falsche_maske (f : Int) (s : State) : Prop :=
  s.world (.slot "Faecher" f "marken") = .int 3

-- `hm` steht hier, obwohl die Maske die Menge nicht anfasst: **ohne sie faellt der Satz in
-- der falschen FARBE.** Der Rumpf teilt danach noch `menge / 2`, und ueber einer unbekannten
-- Menge bleibt `binop .div` stehen -- das Ziel stockt dann an der Division und sieht aus wie
-- ein Fehler im Programm, statt zu sagen: `1` ist nicht `3`.
theorem gift5 (ρ : Env) (s : State) (f : Int) (hf : s.local' "f" = .int f)
    (hroh : s.local' "roh" = .int 27)
    (hm : s.world (.slot "Faecher" f "menge") = .int 8) :
    ∃ s', finalState (exec ρ kennzeichnen_body s) = some s' ∧ falsche_maske f s' := by
  gabbro_simp [kennzeichnen_body, falsche_maske, hf, hroh, hm]
