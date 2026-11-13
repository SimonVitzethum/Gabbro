module
public import Bruecke.Kette.Quelle
public import Bruecke.Anweisung.Zweig.SchattenZeuge
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.String.Length
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.Repr
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
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
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
@[expose] public section

namespace Gabbro.Bruecke.StatischZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def writer : UFn :=
  { name := "write_counter", params := [], kinds := [], res := none, held := [], puts := [],
    gputs := ["counter"], gives := [], body := [.assignGlob "counter" (.lit 9)], ret := .empty }

def reader : UFn :=
  { name := "read_counter", params := [], kinds := [], res := none, held := [], puts := [],
    gives := [], body := [.bind "seen" none (.glob "counter")], ret := .empty }

def caller : UFn :=
  { name := "use_counter", params := [], kinds := [], res := none, held := [], puts := [],
    gputs := ["counter"], gives := [],
    body := [.call "write_counter" [], .call "read_counter" []], ret := .empty }

def unit : UProg :=
  { tabs := [], locks := [], fns := [writer, reader, caller],
    globs := [{ name := "counter", ty := .int 3 10, init := 7, var := true, breite := 8 }] }

def source : String :=
  "module statics { static mut counter : u8 in 3 .. 10 = 7; " ++
  "impl fn write_counter() effects { writes counter } { counter = 9; } " ++
  "impl fn read_counter() effects { reads counter } { let seen = counter; } " ++
  "impl fn use_counter() effects { writes counter } { write_counter(); read_counter(); } }"

def writerBody : List Gabbro.Body.Stmt := [.assignGlobal "counter" (.lit (.int 9))]
def readerBody : List Gabbro.Body.Stmt := [.bindName "seen" (.global "counter")]
def callerBody : List Gabbro.Body.Stmt :=
  [.call "write_counter" [] [] (.lit (.bool true)), .call "read_counter" [] [] (.lit (.bool true))]

theorem reader_forms :
    zuBodyZ unit writer = some writerBody ∧ zuBodyZ unit reader = some readerBody ∧
      zuBodyZ unit caller = some callerBody := by
  exact ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by decide +kernel

def program : Programm (declOf unit) := ((lowerAllg unit).toOption.get lowered_some).1
def functions : List (declOf unit).Fn := ((lowerAllg unit).toOption.get lowered_some).2

theorem lowered : lowerAllg unit = .ok (program, functions) := except_ok_get lowered_some

theorem translated : uebersetzeAllg source = .ok ⟨unit, program, functions⟩ := by kernel_rfl

/-- Initializer seven is retained even though the declared range excludes zero. -/
theorem initial_value_zeuge : nullB unit = true ∧
    ∀ hn : nullB unit = true,
      valOf ((declOf unit).gtyp ⟨0, by decide⟩) ((nullSp unit hn).globs ⟨0, by decide⟩) = .int 7 := by
  refine ⟨by decide +kernel, fun hn => ?_⟩
  kernel_rfl

/-- Unsupported static kinds and an out-of-range initializer keep explicit refusal gates. -/
theorem static_refusals_zeuge :
    staticsB { unit with globs := [{ name := "flag", ty := .bool, init := 0 }] } = false ∧
    staticsB { unit with globs := [{ name := "array", ty := .wert (.arr (.int 0 10) 1), init := 0 }] } = false ∧
    staticsB { unit with globs := [{ name := "atomic", ty := .int 0 10, init := 0, atomic := true }] } = false ∧
    nullB { unit with globs := [{ name := "outside", ty := .int 3 10, init := 0 }] } = false := by
  decide +kernel

/-- O43 is proved over every matching computed signature of all three lowered functions. -/
theorem interfaces : SchnittstellenPflicht unit := by
  intro P fs hlow c n hf
  have hp : program = P := congrArg Prod.fst (Except.ok.inj (lowered.symm.trans hlow))
  subst P
  have hn : n < 3 := by
    have hh := passtAt_lt unit c n hf
    have hl : (sigFns unit).length = 3 := by kernel_rfl
    rw [hl] at hh
    exact hh
  rcases c with ⟨_ | _ | _ | c, hc⟩
  all_goals try (have hh : c + 3 < 3 := hc; omega)
  all_goals rcases n with _ | _ | _ | n
  all_goals try omega
  all_goals refine ⟨fun s0 ρ _ => ?_, fun s0 s1 ρ v _ _ => ?_⟩
  all_goals (kernel_change (true = true); rfl)

theorem writer_meets : meetsU unit (wfU unit) writer writerBody := by
  intro ρB s hW _
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB writerBody s) = some s' ∧ wfU unit s'
  refine ⟨⟨Gabbro.Body.store s.world (.global "counter") (.int 9), s.local'⟩, rfl, ?_⟩
  apply Gabbro.Body.WF_store (shapeOfUG unit) s.world (.global "counter") (.int 9) hW
  intro sh hsh
  have hs : shapeOfUG unit (.global "counter") = some (.intIn 3 10) := by kernel_rfl
  rw [hs] at hsh
  cases hsh
  decide +kernel

theorem reader_meets : meetsU unit (wfU unit) reader readerBody := by
  intro ρB s hW _
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB readerBody s) = some s' ∧ wfU unit s'
  exact ⟨⟨s.world, Gabbro.Body.bindLocal s.local' "seen" (s.world (.global "counter"))⟩, rfl, hW⟩

theorem caller_meets : meetsU unit (wfU unit) caller callerBody := by
  intro ρB s hW _
  change Gabbro.Body.Contract ρB "read_counter" (preProp (wfU unit) reader)
      (fun s s' r => (postU unit (wfU unit) reader s s' r).getD False) →
    Gabbro.Body.Frame ρB "read_counter" [] →
    Gabbro.Body.Contract ρB "write_counter" (preProp (wfU unit) writer)
      (fun s s' r => (postU unit (wfU unit) writer s s' r).getD False) →
    Gabbro.Body.Frame ρB "write_counter" ["counter"] →
    ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB callerBody s) = some s' ∧ wfU unit s'
  intro hread _ hwrite _
  let t0 : Gabbro.Body.State := ⟨s.world, fun _ => .absent⟩
  let t1 := (ρB "write_counter" t0).1
  have hw1 : wfU unit t1 := hwrite t0 ⟨hW, rfl⟩
  let t2 : Gabbro.Body.State := ⟨t1.world, fun _ => .absent⟩
  let t3 := (ρB "read_counter" t2).1
  have hw3 : wfU unit t3 := hread t2 ⟨hw1, rfl⟩
  exact ⟨⟨t3.world, s.local'⟩, rfl, hw3⟩

theorem duties : ∀ c : Fin unit.fns.length, ∃ bs,
    zuBodyZ unit (fnAt unit c) = some bs ∧ meetsU unit (wfU unit) (fnAt unit c) bs := by
  intro ⟨c, hc⟩
  rcases c with _ | _ | _ | c
  · exact ⟨writerBody, reader_forms.1, writer_meets⟩
  · exact ⟨readerBody, reader_forms.2.1, reader_meets⟩
  · exact ⟨callerBody, reader_forms.2.2, caller_meets⟩
  · have hh : c + 3 < 3 := hc
    omega

theorem all_duties : PflichtenAlle source :=
  ⟨unit, uOf_eq translated, (by decide +kernel), (by decide +kernel),
    (by decide +kernel), (by decide +kernel), (by decide +kernel), interfaces, duties⟩

theorem carried_duties : PflichtenTeilG source (u := unit) (fun _ => True) := by
  refine ⟨uOf_eq translated, (by decide +kernel),
    getragenG_of_bools (by decide +kernel) (by decide +kernel) (by decide +kernel),
    (by decide +kernel), fun P fs hlow c _ => interfaces P fs hlow c,
    fun c _ => duties c, ?_⟩
  intro c hc
  exact (hc True.intro).elim

/-- The source anchor, computed contracts, carried duties and final theorem hold together. -/
theorem nutzer_aus_quelleG_statisch_zeuge :
    PflichtenTeilG source (u := unit) (fun _ => True) ∧
      (∀ hn : nullB unit = true, OffeneStartPflicht unit (fun _ => True) program hn) ∧
      uebersetzeAllg source = .ok ⟨unit, program, functions⟩ ∧
      ∃ hn : nullB unit = true, Zielsatz.NutzerPflicht (einheitAllg unit program hn) := by
  have hStart : ∀ hn : nullB unit = true,
      OffeneStartPflicht unit (fun _ => True) program hn := fun _ _ _ hc => (hc True.intro).elim
  exact ⟨carried_duties, hStart, translated, nutzer_aus_quelleG carried_duties hStart translated⟩

/-- Nonempty ordinary statics also use the unchanged atomic-rely source endpoint. -/
theorem atomic_rely_zeuge :
    ∃ hn : nullB unit = true, Zielsatz.NutzerPflichtA (einheitAllg unit program hn) :=
  nutzerA_aus_quelleG carried_duties (fun _ _ _ hc => (hc True.intro).elim) translated

#print axioms nutzer_aus_quelleG_statisch_zeuge
#print axioms atomic_rely_zeuge


end Gabbro.Bruecke.StatischZeuge
