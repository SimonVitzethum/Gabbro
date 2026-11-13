/-
  Witnesses of the call rewrite: a call in an operand, a call as an argument of a call, a call in a
  condition and in an assigned value are bound in front; a call behind a read of a static, in the
  right operand of `&&`, and a call that already stands alone are left where they are.
-/
module
public import Grammatik.Parser.Elab.Modules.CallHoist
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section

namespace Gabbro.Grammatik.Parser.CallHoist

def zeugeK : Kontext := { fns := Tafel.von _ ["f", "g"], statics := Tafel.von _ ["s"] }

/-- `return f(3) + 1;` binds the call first. -/
theorem operand_zeuge :
    hebeKoerper zeugeK (.block [] (some (.ret (some (.bin "+" (.call "f" [.lit 3]) (.lit 1)))))) =
      .block [.bind false "#r0" none (.call "f" [.lit 3])]
        (some (.ret (some (.bin "+" (.variable "#r0") (.lit 1))))) := by kernel_rfl

/-- `let a = f(g(3));` binds the inner call; the outer one already stands alone. -/
theorem argument_zeuge :
    hebeKoerper zeugeK (.block [.bind false "a" none (.call "f" [.call "g" [.lit 3]])] none) =
      .block [.bind false "#r0" none (.call "g" [.lit 3]),
        .bind false "a" none (.call "f" [.variable "#r0"])] none := by kernel_rfl

/-- `if g(7) { }` binds the condition's call in front of the `if`; `x = f(1) + f(2);` binds both in order. -/
theorem bedingung_zeuge :
    hebeKoerper zeugeK (.block [.cond (.call "g" [.lit 7]) (.block [] none) [] none,
        .set (.variable "x") "=" (.bin "+" (.call "f" [.lit 1]) (.call "f" [.lit 2]))] none) =
      .block [.bind false "#r0" none (.call "g" [.lit 7]),
        .cond (.variable "#r0") (.block [] none) [] none,
        .bind false "#r1" none (.call "f" [.lit 1]),
        .bind false "#r2" none (.call "f" [.lit 2]),
        .set (.variable "x") "=" (.bin "+" (.variable "#r1") (.variable "#r2"))] none := by kernel_rfl

/-- A call behind a read of the static `s` stays, also as the right operand of `&&`. -/
theorem bleibt_zeuge :
    hebeKoerper zeugeK (.block [.bind false "a" none (.bin "+" (.variable "s") (.call "f" [.lit 1])),
        .bind false "b" none (.bin "&&" (.variable "s") (.call "g" [.lit 1]))] none) =
      .block [.bind false "a" none (.bin "+" (.variable "s") (.call "f" [.lit 1])),
        .bind false "b" none (.bin "&&" (.variable "s") (.call "g" [.lit 1]))] none := by kernel_rfl

/-- A call through a local pointer is bound as well: `let p = &f; return p() + 1;`. -/
theorem zeiger_zeuge :
    hebeKoerper zeugeK (.block [.bind false "p" none (.fnref "f")]
        (some (.ret (some (.bin "+" (.call "p" []) (.lit 1)))))) =
      .block [.bind false "p" none (.fnref "f"), .bind false "#r0" none (.call "p" [])]
        (some (.ret (some (.bin "+" (.variable "#r0") (.lit 1))))) := by kernel_rfl

/-- A constructed value as an argument and as a stored value is bound first; assigned to a variable
    or returned it stays: `f(Num(7));  t.slots[i].k = Num(9);  x = Num(5);`. -/
theorem fall_zeuge :
    hebeKoerper { zeugeK with faelle := Tafel.von _ ["Num"] } (.block [.call "f" [.call "Num" [.lit 7]],
        .set (.field (.index (.field (.variable "t") "slots") (.variable "i")) "k") "=" (.call "Num" [.lit 9]),
        .set (.variable "x") "=" (.call "Num" [.lit 5])] none) =
      .block [.bind false "#r0" none (.call "Num" [.lit 7]), .call "f" [.variable "#r0"],
        .bind false "#r1" none (.call "Num" [.lit 9]),
        .set (.field (.index (.field (.variable "t") "slots") (.variable "i")) "k") "=" (.variable "#r1"),
        .set (.variable "x") "=" (.call "Num" [.lit 5])] none := by kernel_rfl

/-- A case without a payload as an argument is bound as well: `return f(End);`. -/
theorem fall_ohne_nutzlast_zeuge :
    hebeKoerper { zeugeK with faelle := Tafel.von _ ["End"] }
        (.block [] (some (.ret (some (.call "f" [.variable "End"]))))) =
      .block [.bind false "#r0" none (.variable "End")]
        (some (.ret (some (.call "f" [.variable "#r0"])))) := by kernel_rfl

/-- An untyped `let` of an aggregate table field gets the field's declared type. -/
theorem feld_zeuge :
    hebeKoerper { zeugeK with felder := [("T", "s", .str (.lit 16))] }
        (.block [.bind false "a" none (.field (.index (.field (.variable "T") "slots") (.lit 1)) "s")] none) =
      .block [.bind false "a" (some (.str (.lit 16)))
        (.field (.index (.field (.variable "T") "slots") (.lit 1)) "s")] none := by kernel_rfl

/-- A call in the right operand runs only when the left operand admits it: `if c && g(1) { }` and
    `let b = c || g(2);` carry the result in a fresh mutable `bool`. -/
theorem bedingt_zeuge :
    hebeKoerper zeugeK (.block [.cond (.bin "&&" (.variable "c") (.call "g" [.lit 1])) (.block [] none) [] none,
        .bind false "b" none (.bin "||" (.variable "c") (.call "g" [.lit 2]))] none) =
      .block [.bind true "#r0" (some (.atom "bool")) .fls,
        .cond (.variable "c") (.block [.bind false "#r1" none (.call "g" [.lit 1]),
          .set (.variable "#r0") "=" (.variable "#r1")] none) [] none,
        .cond (.variable "#r0") (.block [] none) [] none,
        .bind true "#r2" (some (.atom "bool")) .tru,
        .cond (.un "!" (.variable "c")) (.block [.bind false "#r3" none (.call "g" [.lit 2]),
          .set (.variable "#r2") "=" (.variable "#r3")] none) [] none,
        .bind false "b" none (.variable "#r2")] none := by kernel_rfl

/-- An `else if` with a call becomes an `if` inside an `else`; the arms in front of it and behind it
    keep their place: `if a { } else if b { } else if g(1) { } else if d { } else { }`. -/
theorem elsif_zeuge :
    hebeKoerper zeugeK (.block [.cond (.variable "a") (.block [] none)
        [.elsif (.variable "b") (.block [] none), .elsif (.call "g" [.lit 1]) (.block [] none),
          .elsif (.variable "d") (.block [] none)] (some (.block [] none))] none) =
      .block [.cond (.variable "a") (.block [] none) [.elsif (.variable "b") (.block [] none)]
        (some (.block [.bind false "#r0" none (.call "g" [.lit 1]),
          .cond (.variable "#r0") (.block [] none) [.elsif (.variable "d") (.block [] none)]
            (some (.block [] none))] none))] none := by kernel_rfl

/-- An untyped `let` of an option static gets its declared type, and a constructed value assigned to
    a static is bound first; a local of the same name is left alone. -/
theorem statik_zeuge :
    hebeKoerper { zeugeK with faelle := Tafel.von _ ["Num"], statikTyp := [("s", .index true "T")] }
        (.block [.bind false "a" none (.variable "s"), .set (.variable "s") "=" (.call "Num" [.lit 5]),
          .bind false "s" none (.lit 1), .bind false "b" none (.variable "s")] none) =
      .block [.bind false "a" (some (.index true "T")) (.variable "s"),
        .bind false "#r0" none (.call "Num" [.lit 5]), .set (.variable "s") "=" (.variable "#r0"),
        .bind false "s" none (.lit 1), .bind false "b" none (.variable "s")] none := by kernel_rfl

/-- The context of a unit with one tagged static `cur : Tok`, `Tok` with the cases `Num(..)` and `End`. -/
def zeugeS : Kontext :=
  { fns := Tafel.von _ ["f", "g"], statics := Tafel.von _ ["s", "cur"],
    statikTyp := [("cur", STyp.atom "Tok")],
    statikFaelle := [("cur", [("Num", true), ("End", false)])] }

/-- `let t = cur;` for a tagged static `cur` is read case by case into a fresh local; a local named
    `cur` is read as it stands. -/
theorem statik_fall_zeuge :
    hebeKoerper zeugeS
        (.block [.bind false "t" none (.variable "cur"), .bind false "cur" none (.lit 1),
          .bind false "u" none (.variable "cur")] none) =
      .block [.bind true "#r0" (some (.atom "Tok")) (.variable "End"),
        .cases (.variable "cur")
          [.arm "Num" (some "#r1") (.block [.set (.variable "#r0") "=" (.call "Num" [.variable "#r1"])] none),
           .arm "End" none (.block [.set (.variable "#r0") "=" (.variable "End")] none)],
        .bind false "t" (some (.atom "Tok")) (.variable "#r0"),
        .bind false "cur" none (.lit 1), .bind false "u" none (.variable "cur")] none := by kernel_rfl

/-- `cur = End;` for the tagged static `cur`: the case without a payload is bound first. -/
theorem statik_fall_ohne_nutzlast_zeuge :
    hebeKoerper { zeugeS with faelle := Tafel.von _ ["Num", "End"] }
        (.block [.set (.variable "cur") "=" (.variable "End")] none) =
      .block [.bind false "#r0" none (.variable "End"),
        .set (.variable "cur") "=" (.variable "#r0")] none := by kernel_rfl

/-- A compound assignment reads its target first: `s += f(1);` on the static `s` keeps the call where
    it is (the elaborator refuses it), `x += f(1);` on a local binds it, and a slot target keeps it too. -/
theorem verbund_zeuge :
    hebeKoerper zeugeK (.block [.set (.variable "s") "+=" (.call "f" [.lit 1]),
        .set (.variable "x") "+=" (.call "f" [.lit 1]),
        .set (.field (.index (.field (.variable "t") "slots") (.lit 0)) "k") "+=" (.call "f" [.lit 1])] none) =
      .block [.set (.variable "s") "+=" (.call "f" [.lit 1]),
        .bind false "#r0" none (.call "f" [.lit 1]), .set (.variable "x") "+=" (.variable "#r0"),
        .set (.field (.index (.field (.variable "t") "slots") (.lit 0)) "k") "+=" (.call "f" [.lit 1])] none := by
  kernel_rfl

/-- The reason binder of an `else` body is a local there: `f(1) else (cur) { let t = cur; }` reads the
    reason, not the tagged static `cur`. -/
theorem grund_binder_zeuge :
    hebeKoerper zeugeS (.block [.callElse "f" [.lit 1] "cur"
        (.block [.bind false "t" none (.variable "cur")] none)] none) =
      .block [.callElse "f" [.lit 1] "cur" (.block [.bind false "t" none (.variable "cur")] none)] none := by
  kernel_rfl

/-- A call returned inside a branch is bound first; the one at the end of the function body stays:
    `if c { return f(1); } return f(2);`. A constructed value returned in a branch stays as well. -/
theorem zweig_rueckgabe_zeuge :
    hebeKoerper { zeugeK with faelle := Tafel.von _ ["Num"] }
        (.block [.cond (.variable "c") (.block [] (some (.ret (some (.call "f" [.lit 1]))))) [] none,
          .cond (.variable "d") (.block [] (some (.ret (some (.call "Num" [.lit 3]))))) [] none]
          (some (.ret (some (.call "f" [.lit 2]))))) =
      .block [.cond (.variable "c") (.block [.bind false "#r0" none (.call "f" [.lit 1])]
          (some (.ret (some (.variable "#r0"))))) [] none,
        .cond (.variable "d") (.block [] (some (.ret (some (.call "Num" [.lit 3]))))) [] none]
        (some (.ret (some (.call "f" [.lit 2])))) := by kernel_rfl

/-- A case without a payload stored into a slot is bound first: `t.slots[i].k = End;`. -/
theorem fall_in_slot_zeuge :
    hebeKoerper { zeugeK with faelle := Tafel.von _ ["End"] }
        (.block [.set (.field (.index (.field (.variable "t") "slots") (.variable "i")) "k") "="
          (.variable "End")] none) =
      .block [.bind false "#r0" none (.variable "End"),
        .set (.field (.index (.field (.variable "t") "slots") (.variable "i")) "k") "=" (.variable "#r0")] none := by
  kernel_rfl

/-- A direct array read stored into a slot uses the same binding as its explicit source form. -/
theorem slot_array_read_zeuge :
    hebeKoerper zeugeK (.block
        [.set (.field (.index (.field (.variable "src") "slots") (.variable "i")) "b") "="
          (.index (.variable "TEXT") (.variable "i"))] none) =
      .block [.bind false "#r0" none (.index (.variable "TEXT") (.variable "i")),
        .set (.field (.index (.field (.variable "src") "slots") (.variable "i")) "b") "="
          (.variable "#r0")] none := by kernel_rfl

/-- Calls needed for the target index stay before the stored read. -/
theorem slot_array_read_order_zeuge :
    hebeKoerper zeugeK (.block
        [.set (.field (.index (.field (.variable "src") "slots") (.call "f" [])) "b") "="
          (.index (.variable "TEXT") (.variable "i"))] none) =
      .block [.bind false "#r0" none (.call "f" []),
        .bind false "#r1" none (.index (.variable "TEXT") (.variable "i")),
        .set (.field (.index (.field (.variable "src") "slots") (.variable "#r0")) "b") "="
          (.variable "#r1")] none := by kernel_rfl

/-- A stateful target index and a compound target read prevent moving the indexed value. -/
theorem slot_array_read_stays_zeuge :
    hebeKoerper zeugeK (.block
        [.set (.field (.index (.field (.variable "src") "slots") (.variable "s")) "b") "="
          (.index (.variable "TEXT") (.variable "i")),
         .set (.field (.index (.field (.variable "src") "slots") (.variable "i")) "b") "+="
          (.index (.variable "TEXT") (.variable "i"))] none) =
      .block
        [.set (.field (.index (.field (.variable "src") "slots") (.variable "s")) "b") "="
          (.index (.variable "TEXT") (.variable "i")),
         .set (.field (.index (.field (.variable "src") "slots") (.variable "i")) "b") "+="
          (.index (.variable "TEXT") (.variable "i"))] none := by kernel_rfl

/-- A string literal reads no mutable state: its call is bound just like a numeric call. -/
theorem string_argument_operand_zeuge :
    hebeKoerper zeugeK (.block [] (some (.ret (some
        (.bin "+" (.bin "-" (.variable "v") (.variable "local"))
          (.call "f" [.ext .text ["Z"] []])))))) =
      .block [.bind false "#r0" none (.call "f" [.ext .text ["Z"] []])]
        (some (.ret (some (.bin "+" (.bin "-" (.variable "v") (.variable "local"))
          (.variable "#r0"))))) := by kernel_rfl

/-- A string argument does not permit a call to cross an earlier mutable read. -/
theorem string_argument_order_zeuge :
    hebeKoerper zeugeK (.block [.bind false "a" none
        (.bin "+" (.variable "s") (.call "f" [.ext .text ["Z"] []]))] none) =
      .block [.bind false "a" none
        (.bin "+" (.variable "s") (.call "f" [.ext .text ["Z"] []]))] none := by kernel_rfl

/-- The already accepted statement spelling keeps its original tree. -/
theorem string_argument_statement_zeuge :
    hebeKoerper zeugeK (.block [.bind false "a" none (.call "f" [.ext .text ["Z"] []])] none) =
      .block [.bind false "a" none (.call "f" [.ext .text ["Z"] []])] none := by kernel_rfl

/-- A table field's tagged type supplies the same cases as the static-read expansion. -/
def zeugeF : Kontext :=
  { zeugeK with
    felder := [("T", "k", .atom "Kind")],
    typFaelle := [("Kind", [("Leaf", false), ("Node", true)])] }

/-- Both typed and inferred bindings use one slot match; mutability and annotations survive. -/
theorem tagged_slot_read_zeuge :
    hebeKoerper zeugeF (.block
        [.bind false "a" (some (.atom "Kind"))
          (.field (.index (.field (.variable "T") "slots") (.lit 1)) "k"),
         .bind true "b" none
          (.field (.index (.field (.variable "T") "slots") (.variable "i")) "k")] none) =
      .block
        [.bind true "#r0" (some (.atom "Kind")) (.variable "Leaf"),
         .cases (.field (.index (.field (.variable "T") "slots") (.lit 1)) "k")
          [.arm "Leaf" none (.block [.set (.variable "#r0") "=" (.variable "Leaf")] none),
           .arm "Node" (some "#r1")
            (.block [.set (.variable "#r0") "=" (.call "Node" [.variable "#r1"])] none)],
         .bind false "a" (some (.atom "Kind")) (.variable "#r0"),
         .bind true "#r2" (some (.atom "Kind")) (.variable "Leaf"),
         .cases (.field (.index (.field (.variable "T") "slots") (.variable "i")) "k")
          [.arm "Leaf" none (.block [.set (.variable "#r2") "=" (.variable "Leaf")] none),
           .arm "Node" (some "#r3")
            (.block [.set (.variable "#r2") "=" (.call "Node" [.variable "#r3"])] none)],
         .bind true "b" (some (.atom "Kind")) (.variable "#r2")] none := by kernel_rfl

/-- An index call is evaluated once, before the single match read; fresh names do not collide. -/
theorem tagged_slot_index_call_zeuge :
    leseFeld zeugeF 64 0 false "a" none
        (.field (.index (.field (.variable "T") "slots") (.call "f" [])) "k") =
      some
        ([.bind false "#r0" none (.call "f" []),
          .bind true "#r1" (some (.atom "Kind")) (.variable "Leaf"),
          .cases (.field (.index (.field (.variable "T") "slots") (.variable "#r0")) "k")
            [.arm "Leaf" none (.block [.set (.variable "#r1") "=" (.variable "Leaf")] none),
             .arm "Node" (some "#r2")
              (.block [.set (.variable "#r1") "=" (.call "Node" [.variable "#r2"])] none)],
          .bind false "a" (some (.atom "Kind")) (.variable "#r1")], 3) := by kernel_rfl

/-- No initial case is invented, and a local shadowing the table prevents this rewrite. -/
theorem tagged_slot_boundaries_zeuge :
    leseFeld { zeugeF with typFaelle := [("Kind", [("Node", true)])] } 64 0 false "a" none
        (.field (.index (.field (.variable "T") "slots") (.lit 1)) "k") = none ∧
    leseFeld { zeugeF with lokal := ["T"] } 64 0 false "a" none
        (.field (.index (.field (.variable "T") "slots") (.lit 1)) "k") = none :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- A written annotation is retained even when it disagrees with the field's declared type. -/
theorem tagged_slot_annotation_zeuge :
    (leseFeld zeugeF 64 0 false "a" (some (.atom "Other"))
        (.field (.index (.field (.variable "T") "slots") (.lit 1)) "k")).map
        (fun result => result.1.getLast?) =
      some (some (.bind false "a" (some (.atom "Other")) (.variable "#r0"))) := by kernel_rfl

end Gabbro.Grammatik.Parser.CallHoist
