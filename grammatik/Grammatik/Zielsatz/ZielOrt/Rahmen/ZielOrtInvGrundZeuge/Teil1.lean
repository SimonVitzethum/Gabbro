module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInvGrund
public import Grammatik.Proben.InvZeuge
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



namespace Gabbro.Grammatik

/-! ## 1. The declaration -/

inductive IgFn where
  | haupt
  | setze
  | nichts
  deriving DecidableEq

def igSig (e : Option Ty) (n : Nat) (h : List Unit) (w : Bool) :
    Signatur Unit Empty Unit Empty where
  params := []
  erg := e
  gruende := n
  haelt := h
  schreibt := fun _ => w
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def igSigNr : Nat → Signatur Unit Empty Unit Empty
  | 0 => igSig none 0 [()] true
  | 1 => igSig (some .bool) 1 [()] true
  | _ => igSig none 0 [] false

/-- As `ivD`, with `setze` answering a `bool` and declaring one reason. -/
def igD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := IgFn
  sig := fun | .haupt => 0 | .setze => 1 | .nichts => 2
  sigNr := igSigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Unit
  traeger := fun _ => [.inl ()]
  invs := [()]
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun n _ h _ _ L _ => by
    cases L
    match n, h with
    | 0, _ => exact List.mem_singleton.mpr rfl
    | 1, _ => exact List.mem_singleton.mpr rfl
    | n + 2, h => simp only [igSigNr, igSig, List.any_cons, List.any_nil, Sum.elim_inl, Bool.or_self, Bool.false_eq_true] at h
  ggeteilt_bewacht := fun e => nomatch e

def igHaupt : igD.Fn := IgFn.haupt
def igSetze : igD.Fn := IgFn.setze
def igNichts : igD.Fn := IgFn.nichts

abbrev igL : List (Res igD) := [Res.held (D := igD) ()]

theorem igDarf : darf igD () igL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  rw [e]
  exact List.mem_singleton.mpr rfl

/-! ## 2. The invariant and the bodies -/

def igIdx {Γ : Ctx} {Λ : List (Res igD)} (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 1) :
    Expr igD Γ Λ (.index (igD.count ())) :=
  .widen (lo := k) (hi := k) h0 h1 (.lit k)

def igWert {Γ : Ctx} {Λ : List (Res igD)} (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 10) :
    Expr igD Γ Λ (igD.typ () ()) :=
  .widen (lo := k) (hi := k) h0 h1 (.lit k)

/-- `invariant gleich: konto[0] == konto[1]`. -/
def igInv : Expr igD [] (invSicht igD ()) .bool :=
  .eq (show Expr igD [] (invSicht igD ()) (.int 0 10) from
        .slot () () (igIdx 0 (by decide) (by decide)) igDarf)
      (show Expr igD [] (invSicht igD ()) (.int 0 10) from
        .slot () () (igIdx 1 (by decide) (by decide)) igDarf)

/-- `konto[k] := v` in a function that writes `konto`. -/
def igSchreib (f : igD.Fn) (hw : (vertragVon igD f).schreibt () = true) {Γ : Ctx} (k v : Int)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 10) :
    Stmt igD (vertragVon igD f) false Γ igL igL :=
  .assignSlot () () (igIdx k hk0 hk1) (igWert v hv0 hv1) hw igDarf

def igS0 : Stmt igD (vertragVon igD igSetze) false [] igL igL :=
  igSchreib igSetze rfl 0 5 (by decide) (by decide) (by decide) (by decide)
def igS1 : Stmt igD (vertragVon igD igSetze) false [] igL igL :=
  igSchreib igSetze rfl 1 5 (by decide) (by decide) (by decide) (by decide)

/-- `return R` from `setze`. -/
def igGrund : Endblock igD (vertragVon igD igSetze) false [] igL :=
  .retWhy ⟨0, by decide⟩ (List.Perm.refl _)

/-- `setze` (correct): both slots `5`, then the reason. -/
def igRumpfGut : Endblock igD (vertragVon igD igSetze) false [] igL :=
  .cons igS0 (.cons igS1 igGrund)

/-- `setze` (broken): only slot `0`, then the reason. -/
def igRumpfSchlecht : Endblock igD (vertragVon igD igSetze) false [] igL :=
  .cons igS0 igGrund

/-- The call of `setze` from `haupt`: both hold `L` by signature. -/
theorem igHp : RufPasst igD (vertragVon igD igHaupt) (igD.signatur igSetze) igL where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := fun L _ => by cases L; exact List.mem_singleton.mpr rfl
  hx := fun L _ hn => absurd (by cases L; exact List.mem_singleton.mpr rfl) hn

/-- `konto[k] := 1` in `haupt`, at any context. -/
def igH (Γ : Ctx) (k : Int) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    Stmt igD (vertragVon igD igHaupt) false Γ igL igL :=
  igSchreib igHaupt rfl (Γ := Γ) k 1 hk0 hk1 (by decide) (by decide)

/-- The reason branch of `haupt`: re-establish, return. -/
def igErr : Endblock igD (vertragVon igD igHaupt) false (.why (igD.gruende igSetze) :: [])
    (nach igD igSetze igL) :=
  .cons (igH _ 0 (by decide) (by decide)) (.cons (igH _ 1 (by decide) (by decide))
    (.ret .empty (List.Perm.refl _)))

/-- `let x = setze() else { r => … }`, the value branch empty. -/
def igB : Block igD (vertragVon igD igHaupt) false [] igL igL :=
  .bindCallElse igSetze .nil rfl igHp (by decide) igErr .nil

/-- The tail of `haupt`: re-establish, return. -/
def igTail : Endblock igD (vertragVon igD igHaupt) false [] igL :=
  .cons (igH [] 0 (by decide) (by decide)) (.cons (igH [] 1 (by decide) (by decide))
    (.ret .empty (List.Perm.refl _)))

def igRumpfHaupt : Endblock igD (vertragVon igD igHaupt) false [] igL :=
  .cons (.breaking () igB) igTail

def igRumpfNichts : Endblock igD (vertragVon igD igNichts) false [] [] :=
  .ret .empty List.Perm.nil

def igP (setze : Endblock igD (vertragVon igD igSetze) false [] igL) : Programm igD where
  invariante := fun _ => igInv
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .haupt => igRumpfHaupt
    | .setze => setze
    | .nichts => igRumpfNichts

def igPgut : Programm igD := igP igRumpfGut
def igPschlecht : Programm igD := igP igRumpfSchlecht

/-! ## 3. The fixed premises -/

def igFs : List igD.Fn := [igHaupt, igSetze, igNichts]

theorem igFs_voll : ∀ g : igD.Fn, g ∈ igFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

def igO : Orakel igD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem igO_gut : GutO igO := fun a => nomatch a

theorem igO_lokal : RegLokal igO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

def igSp : Speicher igD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

end Gabbro.Grammatik
