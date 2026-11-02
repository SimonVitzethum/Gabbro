module

public import Grammatik.Kern.Syntax.Typen.Produkt

@[expose] public section

/-
  File:       Grammatik/Kern/Syntax/Typen/ProduktZeuge.lean
  Subject:    WITNESSES of `Typen/Produkt.lean` on a non-degenerate fixture: a product of three fields of three
              different types (a range, a bool, a wider range), a value of it, and the laws of get/replace on it.
-/

namespace Gabbro.Grammatik

/-- The field types of the fixture: a range, a bool, a wider range. -/
def zeugeFelder : List Ty := [.int 0 9, .bool, .int 0 255]

/-- The fixture product: declaration number 7. -/
def zeugeProd : Ty := Ty.prodOf 7 zeugeFelder

/-- A value of the fixture's field list. -/
def zeugeV (a : Zahl 0 9) (b : Bool) (c : Zahl 0 255) :
    ProdVal Unit (fun _ _ => true) zeugeFelder :=
  ProdVal.pcons a (ProdVal.pcons b (ProdVal.pcons c ()))

/-- The first, second and third field of the fixture. -/
def zeugeFeld0 : FieldAt zeugeFelder (.int 0 9) := .head

def zeugeFeld1 : FieldAt zeugeFelder .bool := .tail .head

def zeugeFeld2 : FieldAt zeugeFelder (.int 0 255) := .tail (.tail .head)

/-- Get after set, on the fixture. -/
theorem prodZeuge_lesen (a : Zahl 0 9) (b : Bool) (c : Zahl 0 255) (x : Zahl 0 9) :
    prodGetW zeugeFeld0 (prodSetW zeugeFeld0 (zeugeV a b c) x) = x :=
  prodGetW_prodSetW zeugeFeld0 (zeugeV a b c) x

/-- The siblings of the replaced field keep their values: the bool and the wide range. -/
theorem prodZeuge_geschwister (a : Zahl 0 9) (b : Bool) (c : Zahl 0 255) (x : Zahl 0 9) :
    prodGetW zeugeFeld1 (prodSetW zeugeFeld0 (zeugeV a b c) x) = b ∧
    prodGetW zeugeFeld2 (prodSetW zeugeFeld0 (zeugeV a b c) x) = c := ⟨rfl, rfl⟩

/-- The same through the general frame lemma, with the disjointness derivation. -/
theorem prodZeuge_geschwister_allgemein (a : Zahl 0 9) (b : Bool) (c : Zahl 0 255) (x : Zahl 0 9) :
    prodGetW zeugeFeld2 (prodSetW zeugeFeld0 (zeugeV a b c) x) =
      prodGetW zeugeFeld2 (zeugeV a b c) :=
  prodGetW_prodSetW_of_disj (FieldAt.Disj.headTail (FieldAt.tail FieldAt.head)) (zeugeV a b c) x

/-- Non-degenerate: replacing a field with a different value changes the product. -/
theorem prodZeuge_setzt_um :
    prodSetW zeugeFeld0 (zeugeV ⟨1, by decide, by decide⟩ true ⟨2, by decide, by decide⟩)
        (⟨5, by decide, by decide⟩ : Zahl 0 9) ≠
      zeugeV ⟨1, by decide, by decide⟩ true ⟨2, by decide, by decide⟩ := by
  intro h
  have h5 : (5 : Int) = 1 :=
    congrArg (fun v : ProdVal Unit (fun _ _ => true) zeugeFelder =>
      (prodGetW zeugeFeld0 v).n) h
  omega

/-- Extensionality on the fixture: agreeing at the three fields makes two values equal. -/
theorem prodZeuge_ext (v w : ProdVal Unit (fun _ _ => true) zeugeFelder)
    (h : ∀ {σ : Ty} (i : FieldAt zeugeFelder σ), prodGetW i v = prodGetW i w) : v = w :=
  ProdVal.prod_ext v w h

end Gabbro.Grammatik
