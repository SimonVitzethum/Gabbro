import Grammatik.Bausteine.Arena.Ownership.Body.Check.Program
import Grammatik.Kern.Syntax.Zucker

/-! Witness of the ownership rule for references (PLAN-DYNAMIC 14). The declaration has two tables: the
four-slot arena `true` the ledger tracks (`A`, with its free list) and the OPEN region `false` with its provider
`()` (`table R from neu`). The one body is `let r = alloc R; r->x = 7; return;`: the executable checker admits it
(`checked`), so every reachable machine keeps the ownership invariant (`ownInv_reach` applies). A write through a
reference into the tracked arena itself is refused, for every program (`chkS_ref_arena`): the rule never lets a
reference bypass the ledger. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body.RefWitness

open Source

/-- The arena `true` (count 4, payload field 0, link field 1) and the open region `false`; the statics are the
    arena's words; the provider `()` answers a reference into the region. -/
@[reducible] def D : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun t => if t then 4 else 0
  offen := fun t => !t
  Feld := fun _ => Fin 4
  decFeld := fun _ => inferInstance
  typ := fun _ f => if f = 0 then .int 0 255 else .int 0 4
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some true | 1 => some false | _ => none
  Glob := Fin 4
  decGlob := inferInstance
  gtyp := fun _ => .int 0 4
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun _ => true
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => some (.ref 1)
  aschreibt := fun _ _ => false
  agschreibt := fun _ _ => false
  anbieter := fun t => if t then none else some ()
  anbieter_passt := fun t a h => by
    cases t
    · exact ⟨rfl, rfl, 1, rfl, rfl⟩
    · cases h
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => by simp at h

/-- The tracked arena: payload `0`, free link `1`; words `0` (counter), `1` (committed), `2` (free head). -/
def A : FreiForm D where
  tab := true
  feld := 0
  zaehl := 0
  hz := rfl
  hpos := by decide
  komm := 1
  hk := rfl
  hzwei := by decide
  kopf := 2
  hkopf := rfl
  nxt := 1
  hnxt := rfl
  hk1 := by decide
  hk2 := by decide
  hf := by decide

abbrev V : Vertrag D := vertragVon D ()

theorem region_right : darf D false [] := fun _ h => by cases h

/-- `r->x = 7; return;` behind the provider's answer. -/
def weiter : Endblock D V false [.ref 1] [] :=
  .cons (.assignSlotRef (.var .here) false rfl rfl 0 (.widen (by decide) (by decide) (.lit 7)) rfl region_right)
    (.ret .empty (List.Perm.refl _))

/-- `let r = alloc R; r->x = 7; return;` -/
def rumpf : Endblock D V false [] [] :=
  .alloc false () rfl rfl (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
    (fun _ h => by cases h) weiter

def P : Programm D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => rumpf

/-- The one function takes nothing and returns nothing. -/
def I : Interfaces A := fun _ => ⟨.nil, rfl, .plain⟩

/-- **The executable ownership checker admits the program with the reference write.** -/
theorem admitted : checkProgram P A I [()] = true := by decide +kernel

/-- **The body derives in the ownership judgment.** -/
theorem checked : Checked P A I := checkProgram_sound (fun f => by cases f; simp) admitted

/-- The checked program's interfaces hold at every actual call, under a good oracle. -/
theorem calls {O : Orakel D} (hO : GutO O) (passes : Nat) : ∀ n, Respects A I.contracts (rufAt P O passes n) :=
  checkProgram_calls (fun f => by cases f; simp) admitted hO passes

/-- **A reference never bypasses the ledger**: a write through a reference into the tracked arena is refused by
    the checker, in every declaration, for every program. -/
theorem chkS_ref_arena {D : Deklaration} (A : FreiForm D) (I : Interfaces A) (fs : List D.Fn) {V : Vertrag D}
    (out : Flow.Output A V.erg) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.ref n))
    (ht : D.tabNr n = some A.tab) (ho : D.offen A.tab = true) (f : D.Feld A.tab) (e : Expr D Γ Λ (D.typ A.tab f))
    (hw : V.schreibt A.tab = true) (hL : darf D A.tab Λ) (k c : Context) :
    chkS A I fs out (l := l) (.assignSlotRef r A.tab ht ho f e hw hL) k c = none := by
  simp [chkS]

#print axioms checked
#print axioms chkS_ref_arena

end Gabbro.Grammatik.ArenaOwnership.Body.RefWitness
