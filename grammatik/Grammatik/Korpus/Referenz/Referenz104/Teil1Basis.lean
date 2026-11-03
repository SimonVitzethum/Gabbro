module

public import Grammatik.Logik.Fortschritt.KostenGZeuge
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 1. The declaration -/

inductive R4Fn where
  | einzahlen
  | lies
  | treiber
  | ruhe
  deriving DecidableEq

def r4SigEin : Signatur Unit Empty Unit Empty where
  params := [.ptr (.table 0 (true, true)), .index 2, .int 0 10]
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def r4SigLies : Signatur Unit Empty Unit Empty where
  params := [.ptr (.table 0 (true, false)), .index 2]
  erg := some (.int 0 100)
  gruende := 0
  haelt := [()]
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def r4SigTreiber : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def r4SigRuhe : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- `0104-referenz.gab`'s declarations: table `Konto` (2 slots, field
    `stand : 0 .. 100`), lock `M` (rank 0) protecting it; functions
    `einzahlen`, `lies`, and the flagged additions `treiber`, `ruhe`. -/
def r4D : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
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
  Fn := R4Fn
  sig := fun | .einzahlen => 0 | .lies => 1 | .treiber => 2 | .ruhe => 3
  sigNr := fun n => match n with
    | 0 => r4SigEin | 1 => r4SigLies | 2 => r4SigTreiber | _ => r4SigRuhe
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
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
  geteilt_bewacht := fun _ _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def r4Ein : r4D.Fn := R4Fn.einzahlen
def r4Lies : r4D.Fn := R4Fn.lies
def r4Treiber : r4D.Fn := R4Fn.treiber
def r4Ruhe : r4D.Fn := R4Fn.ruhe

abbrev r4M : List (Res r4D) := [Res.held (D := r4D) ()]

theorem r4Darf : darf r4D () r4M := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-! ## 2. The bodies and contracts -/

/-- `einzahlen`'s parameters: `k` (`.here`), `i`, `b`. -/
abbrev r4GEin : Ctx := [.ptr (.table 0 (true, true)), .index 2, .int 0 10]

/-- `k.slots[i].stand = 100;` -/
def r4Schreib : Stmt r4D (vertragVon r4D r4Ein) false r4GEin r4M r4M :=
  .assignThru (.var .here) () rfl () (.var (.there .here)) (.widen (by decide) (by decide) (.lit 100))
    rfl r4Darf

/-- `einzahlen` calls `lies`: same lock, `lies` writes nothing. -/
theorem r4HpLies : RufPasst r4D (vertragVon r4D r4Ein) (r4D.signatur r4Lies) r4M where
  ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _
    (OwnerFlow.empty_of_empty (r4D.signatur r4Lies).owner)
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := RufPasst.hh_von (fun L => by
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)
  hx := RufPasst.hx_von (fun L => by
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)

/-- `lies(k, i);` -- `k` (rw) passed as `r`: the pointer to the same table. -/
def r4RufLies : Stmt r4D (vertragVon r4D r4Ein) false r4GEin r4M (nach r4D r4Lies r4M) :=
  .call r4Lies (.cons (.ptrOf () 0 rfl (true, false)) (.cons (.var (.there .here)) .nil)) r4HpLies rfl

def r4RetEin : Endblock r4D (vertragVon r4D r4Ein) false r4GEin r4M :=
  .ret .empty (List.Perm.refl _)

def r4RestEin : Endblock r4D (vertragVon r4D r4Ein) false r4GEin r4M := .cons r4RufLies r4RetEin

/-- `einzahlen`: `k.slots[i].stand = 100; lies(k, i);` -/
def r4RumpfEin : Endblock r4D (vertragVon r4D r4Ein) false r4GEin r4M := .cons r4Schreib r4RestEin

/-- `ensures old(k.slots[i].stand) <= k.slots[i].stand` -/
def r4EnsEin : Expr r4D (ErgCtx (r4D.params r4Ein) (r4D.erg r4Ein)) (vertragVon r4D r4Ein).ende
    .bool :=
  .le (.oldS () () (.var (.there .here)) r4Darf)
    (.thru (.var .here) () rfl () (.var (.there .here)) r4Darf)

/-- `lies`'s parameters: `k` (`.here`), `i`. -/
abbrev r4GLies : Ctx := [.ptr (.table 0 (true, false)), .index 2]

/-- `return k.slots[i].stand;` -/
def r4RumpfLies : Endblock r4D (vertragVon r4D r4Lies) false r4GLies r4M :=
  .ret (.val (.thru (.var .here) () rfl () (.var (.there .here)) r4Darf)) (List.Perm.refl _)

/-- `ensures result == k.slots[i].stand` -/
def r4EnsLies : Expr r4D (ErgCtx (r4D.params r4Lies) (r4D.erg r4Lies)) (vertragVon r4D r4Lies).ende
    .bool :=
  .eq (.var .here) (.thru (.var (.there .here)) () rfl () (.var (.there (.there .here))) r4Darf)

/-- The driver (flagged addition): `einzahlen(&Konto, 0, 7); lies(&Konto, 0); return`. -/
theorem r4HpEinT : RufPasst r4D (vertragVon r4D r4Treiber) (r4D.signatur r4Ein) r4M where
  ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _
    (OwnerFlow.empty_of_empty (r4D.signatur r4Ein).owner)
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := RufPasst.hh_von (fun L => by
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)
  hx := RufPasst.hx_von (fun L => by
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)

theorem r4HpLiesT : RufPasst r4D (vertragVon r4D r4Treiber) (r4D.signatur r4Lies) r4M where
  ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _
    (OwnerFlow.empty_of_empty (r4D.signatur r4Lies).owner)
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := RufPasst.hh_von (fun L => by
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)
  hx := RufPasst.hx_von (fun L => by
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)

def r4Idx0 {Γ : Ctx} : Expr r4D Γ r4M (.index 2) := .widen (by decide) (by decide) (.lit 0)
def r4Sieben {Γ : Ctx} : Expr r4D Γ r4M (.int 0 10) := .widen (by decide) (by decide) (.lit 7)

def r4RufEinT : Stmt r4D (vertragVon r4D r4Treiber) false [] r4M (nach r4D r4Ein r4M) :=
  .call r4Ein (.cons (.ptrOf () 0 rfl (true, true)) (.cons r4Idx0 (.cons r4Sieben .nil))) r4HpEinT rfl

def r4RufLiesT : Stmt r4D (vertragVon r4D r4Treiber) false [] r4M (nach r4D r4Lies r4M) :=
  .call r4Lies (.cons (.ptrOf () 0 rfl (true, false)) (.cons r4Idx0 .nil)) r4HpLiesT rfl

def r4RetT : Endblock r4D (vertragVon r4D r4Treiber) false [] r4M := .ret .empty (List.Perm.refl _)

def r4RestT : Endblock r4D (vertragVon r4D r4Treiber) false [] r4M := .cons r4RufLiesT r4RetT

def r4RumpfTreiber : Endblock r4D (vertragVon r4D r4Treiber) false [] r4M := .cons r4RufEinT r4RestT

def r4RumpfRuhe : Endblock r4D (vertragVon r4D r4Ruhe) false [] [] := .ret .empty List.Perm.nil


end Gabbro.Grammatik
