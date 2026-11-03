module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil1

@[expose] public section

namespace Gabbro.Code.Lower.WitC11
open Gabbro.Grammatik

/-- A writable global and table, with the fixture's real lock held across calls. -/
def guardedSig : Signatur Unit Unit Unit Empty :=
  { sigRuheM Unit Unit Unit Empty with
    schreibt := fun _ => true
    gschreibt := fun _ => true
    haelt := [()]
    boden := some 0 }

/-- The four-slot fixture extended with one lock-guarded global cell. -/
def guardedD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .int 0 100
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => false
  ggeteilt := fun _ => true
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun _ => [.inl ()]
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => guardedSig
  eigner_nie_erzeugt := fun _ _ _ _ h => nomatch h
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
  geteilt_bewacht := fun t h => absurd h (by decide)
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ _ => Or.inl (by decide)


/-- The guarded global is accessible with its lock in the holdings. -/
theorem guardedAccess : gdarf guardedD () [.held ()] := by
  intro w hw
  have h : w ∈ [(Sum.inl () : Unit ⊕ (Empty × Nat))] := hw
  rcases List.mem_singleton.mp h with rfl
  exact List.mem_singleton_self _

/-- The idle-root transport preserves access to a real guarded global. -/
theorem gdarfR_zeuge :
    gdarf guardedD.mitRuhe () (([.held ()] : List (Res guardedD)).map resR) :=
  gdarfR guardedAccess

/-- A concrete call retains write permissions, its lock and its floor. -/
def guardedContract : Vertrag guardedD := vertragVon guardedD ()

theorem guardedCall : RufPasst guardedD guardedContract guardedSig [.held ()] where
  hw := fun _ h => h
  hg := fun _ h => h
  hk := ⟨[], List.Perm.refl [], List.nil_sublist _⟩
  hh := fun L _ => by cases L; exact List.mem_singleton_self _
  hx := fun L _ hn => absurd (by cases L; exact List.mem_singleton_self _) hn
  hb := fun c hc => ⟨c, hc, Int.le_refl c⟩
  ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _ rfl

/-- The compatible call survives the idle-root transport. -/
theorem rufPasstR_zeuge :
    RufPasst guardedD.mitRuhe (vertragR guardedContract) (sigR guardedSig)
      (([.held ()] : List (Res guardedD)).map resR) :=
  rufPasstR guardedCall

end Gabbro.Code.Lower.WitC11
