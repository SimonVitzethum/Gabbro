module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInv
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge
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

inductive IvFn where
  | haupt
  | setze
  | nichts
  deriving DecidableEq

def ivSigL : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def ivSigFrei : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- One table `konto` (two slots, `0 .. 10`) guarded by the lock `()`, one
    invariant over it; `haupt` and `setze` hold the lock by signature and
    write `konto`, `nichts` neither. -/
def ivD : Deklaration where
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
  Fn := IvFn
  sig := fun | .haupt => 0 | .setze => 0 | .nichts => 1
  sigNr := fun | 0 => ivSigL | _ => ivSigFrei
  eigner_nie_erzeugt := fun n _ _ _ h => by
    cases n with
    | zero => simp only [List.not_mem_nil] at h
    | succ n => simp only [List.not_mem_nil] at h
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
    cases n with
    | zero => cases L; exact List.mem_singleton.mpr rfl
    | succ n => simp only [ivSigFrei, List.any_cons, List.any_nil, Sum.elim_inl, Bool.or_self, Bool.false_eq_true] at h
  ggeteilt_bewacht := fun e => nomatch e

def ivHaupt : ivD.Fn := IvFn.haupt
def ivSetze : ivD.Fn := IvFn.setze
def ivNichts : ivD.Fn := IvFn.nichts

abbrev ivL : List (Res ivD) := [Res.held (D := ivD) ()]

theorem ivDarf : darf ivD () ivL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  rw [e]
  exact List.mem_singleton.mpr rfl

/-! ## 2. The invariant and the bodies -/

def ivIdx {Λ : List (Res ivD)} (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 1) :
    Expr ivD [] Λ (.index (ivD.count ())) :=
  .widen (lo := k) (hi := k) h0 h1 (.lit k)

def ivWert {Λ : List (Res ivD)} (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 10) :
    Expr ivD [] Λ (ivD.typ () ()) :=
  .widen (lo := k) (hi := k) h0 h1 (.lit k)

theorem ivInvSicht : invSicht ivD () = ivL := by rfl

/-- `invariant gleich: konto[0] == konto[1]`. -/
def ivInv : Expr ivD [] (invSicht ivD ()) .bool :=
  .eq (show Expr ivD [] (invSicht ivD ()) (.int 0 10) from
        .slot () () (ivIdx 0 (by decide) (by decide)) ivDarf)
      (show Expr ivD [] (invSicht ivD ()) (.int 0 10) from
        .slot () () (ivIdx 1 (by decide) (by decide)) ivDarf)

/-- `konto[k] := v` in a function that writes `konto`. -/
def ivSchreib (f : ivD.Fn) (hw : (vertragVon ivD f).schreibt () = true) (k v : Int)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 10) :
    Stmt ivD (vertragVon ivD f) false [] ivL ivL :=
  .assignSlot () () (ivIdx k hk0 hk1) (ivWert v hv0 hv1) hw ivDarf

def ivRetS : Endblock ivD (vertragVon ivD ivSetze) false [] ivL := .ret .empty (List.Perm.refl _)
def ivRetH : Endblock ivD (vertragVon ivD ivHaupt) false [] ivL := .ret .empty (List.Perm.refl _)

def ivS0 : Stmt ivD (vertragVon ivD ivSetze) false [] ivL ivL :=
  ivSchreib ivSetze rfl 0 5 (by decide) (by decide) (by decide) (by decide)
def ivS1 : Stmt ivD (vertragVon ivD ivSetze) false [] ivL ivL :=
  ivSchreib ivSetze rfl 1 5 (by decide) (by decide) (by decide) (by decide)

/-- `setze` (correct): both slots `5`. -/
def ivRumpfGut : Endblock ivD (vertragVon ivD ivSetze) false [] ivL :=
  .cons ivS0 (.cons ivS1 ivRetS)

/-- `setze` (broken): only slot `0`. -/
def ivRumpfSchlecht : Endblock ivD (vertragVon ivD ivSetze) false [] ivL :=
  .cons ivS0 ivRetS

/-- The call of `setze` from `haupt`: both hold `L` by signature. -/
theorem ivHp : RufPasst ivD (vertragVon ivD ivHaupt) (ivD.signatur ivSetze) ivL where
  ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _
    (OwnerFlow.empty_of_empty (ivD.signatur ivSetze).owner)
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := fun L _ => by cases L; exact List.mem_singleton.mpr rfl
  hx := fun L _ hn => absurd (by cases L; exact List.mem_singleton.mpr rfl) hn

def ivRuf : Stmt ivD (vertragVon ivD ivHaupt) false [] ivL ivL :=
  .call ivSetze .nil ivHp rfl

def ivH0 : Stmt ivD (vertragVon ivD ivHaupt) false [] ivL ivL :=
  ivSchreib ivHaupt rfl 0 1 (by decide) (by decide) (by decide) (by decide)
def ivH1 : Stmt ivD (vertragVon ivD ivHaupt) false [] ivL ivL :=
  ivSchreib ivHaupt rfl 1 1 (by decide) (by decide) (by decide) (by decide)

def ivHauptRest : Endblock ivD (vertragVon ivD ivHaupt) false [] ivL :=
  .cons ivH0 (.cons ivH1 ivRetH)

/-- `haupt`: call `setze`, then re-establish the invariant itself. -/
def ivRumpfHaupt : Endblock ivD (vertragVon ivD ivHaupt) false [] ivL :=
  .cons ivRuf ivHauptRest

def ivRumpfNichts : Endblock ivD (vertragVon ivD ivNichts) false [] [] :=
  .ret .empty List.Perm.nil

def ivP (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) : Programm ivD where
  invariante := fun _ => ivInv
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .haupt => ivRumpfHaupt
    | .setze => setze
    | .nichts => ivRumpfNichts

def ivPgut : Programm ivD := ivP ivRumpfGut
def ivPschlecht : Programm ivD := ivP ivRumpfSchlecht

/-! ## 3. The fixed premises -/

def ivFs : List ivD.Fn := [ivHaupt, ivSetze, ivNichts]

theorem ivFs_voll : ∀ g : ivD.Fn, g ∈ ivFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

def ivO : Orakel ivD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem ivO_gut : GutO ivO := fun a => nomatch a

theorem ivO_lokal : RegLokal ivO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

def ivSp : Speicher ivD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩


end Gabbro.Grammatik
