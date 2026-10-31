/- Joint source fixtures for the actual forever lowering, including ABI and nested counters. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Proben

namespace Gabbro.Stage0.Senke.ForeverHookProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def u : UProg := {
  tabs := [], locks := [], axs := [], annahmen := ["tick"]
  fns := [
    { name := "main", params := [], kinds := [], res := some (0, 100), held := [], puts := [], gives := [], body := [], ret := .val (.lit 0) },
    { name := "worker", params := [("parameter", .int 0 100)], kinds := [.int], res := some (0, 100), held := [], puts := [], gives := [], body := [], ret := .val (.lit 0) },
    { name := "callee", params := [("parameter", .int 0 100)], kinds := [.int], res := some (0, 100), held := [], puts := [], gives := [], body := [], ret := .val (.lit 0) }]
}
abbrev D := declOf u
abbrev mainFn : D.Fn := ⟨0, by decide⟩
abbrev worker : D.Fn := ⟨1, by decide⟩
abbrev callee : D.Fn := ⟨2, by decide⟩
abbrev progress : D.Annahme := some ⟨0, by decide⟩
abbrev locals : Ctx := [.int 73 73, .int 41 41, .int 0 100]

theorem fit (f g : D.Fn) : RufPasst D (vertragVon D f) (D.sigNr (D.sig g)) [] := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  have hf' : f = 0 ∨ f = 1 ∨ f = 2 := by change f < 3 at hf; omega
  have hg' : g = 0 ∨ g = 1 ∨ g = 2 := by change g < 3 at hg; omega
  rcases hf' with rfl | rfl | rfl <;> rcases hg' with rfl | rfl | rfl <;>
    exact {
      hw := fun t => Fin.elim0 t
      hg := fun g => Fin.elim0 g
      hk := ⟨[], List.Perm.nil, List.Sublist.refl []⟩
      hh := fun l => Fin.elim0 l }


def retN {Γ : Ctx} (n : Int) (hl : 0 ≤ n) (hh : n ≤ 100) :
    Endblock D (vertragVon D worker) true Γ [] :=
  .ret (.val (.widen hl hh (.lit n))) (.refl [])

/-- The callee result, both lexical sentinels and the parameter are checked together. -/
def inner : Block D (vertragVon D worker) true locals [] [] :=
  .bindCall callee (.cons (.var (.there (.there .here))) .nil) rfl (fit worker callee) rfl
    (.check (.and (.eq (.var .here) (.lit 17))
      (.and (.eq (.var (.there .here)) (.lit 73))
        (.and (.eq (.var (.there (.there .here))) (.lit 41))
          (.eq (.var (.there (.there (.there .here)))) (.lit 17)))))
      (retN 97 (by decide) (by decide)) (.cons (.leave rfl) .nil))

def outer (mode : Nat) : Block D (vertragVon D worker) true locals [] [] :=
  .cons (.forever progress .tru inner)
    (.check (.and (.eq (.var .here) (.lit 73))
      (.and (.eq (.var (.there .here)) (.lit 41))
        (.eq (.var (.there (.there .here))) (.lit 17))))
      (retN 98 (by decide) (by decide))
      (.cons (if mode = 1 then .next rfl else if mode = 2 then .leave rfl
        else if mode = 3 then .ret (.val (.widen (by decide) (by decide) (.lit 43))) (.refl [])
        else .ite .tru .nil .nil) .nil))

def workerBody (mode : Nat) : Endblock D (vertragVon D worker) false [.int 0 100] [] :=
  .bind (.lit 41) (.bind (.lit 73)
    (.cons (.forever progress (if mode = 4 then .fls else .tru) (outer mode))
      (.ret (.val (.var (.there (.there .here)))) (.refl []))))

def mainBody : Endblock D (vertragVon D mainFn) false [] [] :=
  .bindCall worker (.cons (.widen (by decide) (by decide) (.lit 17)) .nil)
    rfl (fit mainFn worker) rfl (.ret (.val (.var .here)) (.refl []))

def program (mode : Nat) : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures := Fin.cases .tru
    (Fin.cases (.eq (.var (.there .here)) (.lit 17))
      (Fin.cases (.eq (.var (.there .here)) (.lit 17)) (fun i => Fin.elim0 i)))
  rumpf := Fin.cases mainBody
    (Fin.cases (workerBody mode)
      (Fin.cases (.ret (.val (.var .here)) (.refl [])) (fun i => Fin.elim0 i)))

def image (budget mode : Nat) : Except String (List Runner.B) := do
  let b ← bild budget (program mode) (layU u (fun _ => none))
    [mainFn, worker, callee] Fin.val (fun f => if f.val = 0 then "main" else if f.val = 1 then "worker" else "callee") mainFn [] 512
  pure b.bytes

def expected (budget mode : Nat) : Int :=
  if budget = 0 then 111 else if mode = 4 then 104
  else if mode = 2 then 17 else if mode = 3 then 43 else 111

def world : World D where
  slots t := Fin.elim0 t
  globs g := Fin.elim0 g
  spur := []

def oracle : Orakel D where
  wirkt a := Fin.elim0 a
  regLies r := Fin.elim0 r
  regSchreib r := Fin.elim0 r
  sichtbar _ _ := true

/-- Evaluate the same complete source program, retaining the canonical call and loop semantics. -/
def sourceOutcome (budget mode : Nat) : Int :=
  match rufAt (program mode) oracle budget 5 mainFn world Env.nil with
  | .ok _ v => v.n
  | .hardware (.fortschritt _) => 111
  | .logik .schleife => 104
  | _ => -1

/-- The source outcomes distinguish exhausted fuel, invariant failure, leave and return. -/
theorem hook_outcomes_zeuge :
    (List.range 3).all (fun budget => (List.range 5).all
      (fun mode => decide (sourceOutcome budget mode = expected budget mode))) = true := by
  decide +kernel

/-- All joint fixtures use the complete image producer and the actual source hook. -/
theorem hook_images_zeuge :
    (List.range 3).all (fun budget => (List.range 5).all (fun mode => (image budget mode).isOk)) = true := by
  decide +kernel

end Gabbro.Stage0.Senke.ForeverHookProbe
