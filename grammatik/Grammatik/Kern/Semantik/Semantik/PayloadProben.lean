module

public import Grammatik.Kern.Syntax.Extensions.Geist.T2
public import Grammatik.Kern.Syntax.Typen.Transport
public import Grammatik.Logik.Vertraege.EinpassenVoll

@[expose] public section

namespace Gabbro.Grammatik.TypedPayload

/-- A heterogeneous, record-free schema, including a recursively tagged value. -/
def schema : List (Option Ty) :=
  [some .bool, some (.int 2 5), some (.arr (.int 0 255) 2), some (.str 8),
    some (.sum [none, some .bool])]

/-- One ordinary/ghost table pair and an identity function on the complete sum.
    The existing fixture supplies no marks, axioms, registers or invariants. -/
def D : Deklaration :=
  { Geist.Zeuge.GD with
    sigNr := fun _ =>
      { params := [.sum schema], erg := some (.sum schema), gruende := 0,
        haelt := [], schreibt := fun _ => false, gschreibt := (fun g => nomatch g),
        konsumiert := [], produziert := [] }
    passt := fun _ _ => false
    passt_ok := fun _ _ h => by cases h
    rzusage := fun r => nomatch r
    invarianten_gehalten := fun _ i => nomatch i }

def V : Vertrag D := vertragVon D ()

def world : World D :=
  { slots := fun _ _ _ => false, globs := (fun g => nomatch g), spur := [] }

def oracle : Orakel D :=
  { wirkt := (fun a => nomatch a), regLies := (fun r => nomatch r),
    regSchreib := (fun r => nomatch r), sichtbar := fun g => nomatch g }

/-- An arm returns its complete payload under the same tag, including arrays,
    strings and the nested sum; no projection or default value is substituted. -/
def arm : (i : Fin schema.length) → Block D V false (ArmCtx [.sum schema] (schema.get i)) [] []
  | ⟨0, _⟩ => .cons (.ret (.val (.case schema ⟨0, by decide⟩ (.val (.var .here)))) (List.Perm.refl [])) .nil
  | ⟨1, _⟩ => .cons (.ret (.val (.case schema ⟨1, by decide⟩ (.val (.var .here)))) (List.Perm.refl [])) .nil
  | ⟨2, _⟩ => .cons (.ret (.val (.case schema ⟨2, by decide⟩ (.val (.var .here)))) (List.Perm.refl [])) .nil
  | ⟨3, _⟩ => .cons (.ret (.val (.case schema ⟨3, by decide⟩ (.val (.var .here)))) (List.Perm.refl [])) .nil
  | ⟨4, _⟩ => .cons (.ret (.val (.case schema ⟨4, by decide⟩ (.val (.var .here)))) (List.Perm.refl [])) .nil
  | ⟨n + 5, h⟩ => by simp only [schema, List.length_cons, List.length_nil] at h; omega

def arms : Arms D V false [.sum schema] [] [] schema :=
  .cons (arm ⟨0, by decide⟩) (.cons (arm ⟨1, by decide⟩)
    (.cons (arm ⟨2, by decide⟩) (.cons (arm ⟨3, by decide⟩)
      (.cons (arm ⟨4, by decide⟩) .nil))))

def program : Programm D :=
  { requires := fun _ => .tru, ensures := fun _ => .tru,
    invariante := (fun i => nomatch i),
    rumpf := fun _ => .cons (.onTag (.var .here) arms)
      (.ret (.val (.var .here)) (List.Perm.refl [])) }

def flag : Expr D [] [] (.sum schema) := .case schema ⟨0, by decide⟩ (.val .tru)
def scalar : Expr D [] [] (.sum schema) :=
  .case schema ⟨1, by decide⟩ (.val (.widen (by decide) (by decide) (.lit 3)))
def array : Expr D [] [] (.sum schema) :=
  .case schema ⟨2, by decide⟩ (.val (.arrCons
    (.widen (by decide) (by decide) (.lit 7))
    (.arrCons (.widen (by decide) (by decide) (.lit 9)) .arrNil)))
def text : Expr D [] [] (.sum schema) :=
  .case schema ⟨3, by decide⟩ (.val (.strLit [⟨65, by decide, by decide⟩] (by decide)))
def nested : Expr D [] [] (.sum schema) :=
  .case schema ⟨4, by decide⟩ (.val (.case [none, some .bool] ⟨1, by decide⟩ (.val .fls)))

/-- These are ordinary source-language calls: `rufAt` runs the requires, match,
    payload binder, reconstructed return, ensures and invariant gates. -/
theorem flag_call_zeuge :
    rufAt program oracle 0 1 () world (.cons (eval world flag world .nil) .nil) =
      .ok world (eval world flag world .nil) := rfl

theorem scalar_call_zeuge :
    rufAt program oracle 0 1 () world (.cons (eval world scalar world .nil) .nil) =
      .ok world (eval world scalar world .nil) := rfl

theorem array_call_zeuge :
    rufAt program oracle 0 1 () world (.cons (eval world array world .nil) .nil) =
      .ok world (eval world array world .nil) := rfl

theorem text_call_zeuge :
    rufAt program oracle 0 1 () world (.cons (eval world text world .nil) .nil) =
      .ok world (eval world text world .nil) := rfl

theorem nested_call_zeuge :
    rufAt program oracle 0 1 () world (.cons (eval world nested world .nil) .nil) =
      .ok world (eval world nested world .nil) := rfl

/-- The scalar raw boundary refuses a schema that needs structured answers,
    including one with a bare case; it cannot silently drop a typed payload. -/
theorem foreign_typed_payload_refused_zeuge :
    antwortTyB (D := D) [()] (.sum [none, some .bool]) = false := rfl

theorem nested_schema_equality_zeuge :
    decide (Ty.sum [some (.arr (.sum [some .bool]) 2)] =
      Ty.sum [some (.arr (.sum [some .bool]) 2)]) = true := by decide +kernel

end Gabbro.Grammatik.TypedPayload
