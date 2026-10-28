import Grammatik.Berechenbarkeit.BrainfuckG.Schritt
import Grammatik.Berechenbarkeit.Storage.GStack.MultiWitnesses

/-! Witnesses of `befehl_schritt` and `befehl_voll` over a concrete declaration with the four Brainfuck stacks in
one arena of four cells: `BD` is `MultiWitnesses.MD` with seven words, so words 3 to 6 head the left tape, the
right tape, the input and the output. In `w0` every stack and the free list are empty and the counter is 0; the
G block of `.` on the state with head 7 runs normally to the state whose output is `[7]`. In `wv` (counter 4 of
4) the same block runs the failure block. -/

namespace Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.SchrittWitnesses

open Brainfuck ArenaKette InvDynZeuge Storage.GStack

@[reducible] def BD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Fin 4
  decFeld := fun _ => inferInstance
  typ := fun _ f => if f = 0 then .int 0 255 else .int 0 4
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Fin 7
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
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => by simp only [Bool.false_eq_true] at h

/-- The arena: payload `0`, free link `1`; words `0` (counter), `1` (committed), `2` (free head). -/
def BA : FreiForm BD where
  tab := ()
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

/-- The stack link (field `2`). -/
def BL : LinkFeld BA where
  f := 2
  hf := rfl
  h1 := by decide
  h2 := by decide

/-- Stack `k` is headed by word `k + 3`. -/
def BG (k : Fin 4) : LinkKopf BA where
  g := ⟨k.val + 3, by omega⟩
  hg := rfl
  h1 := fun h => by have := congrArg Fin.val h; simp only [BA, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, Fin.isValue,
  reduceCtorEq, and_false] at this
  h2 := fun h => by have := congrArg Fin.val h; simp only [BA, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff] at this
  h3 := fun h => by have := congrArg Fin.val h; simp only [BA, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.reduceEqDiff] at this

theorem BG_inj : Function.Injective fun k => (BG k).g := by
  intro a b h
  have := congrArg Fin.val h
  simp only [BG, Nat.add_right_cancel_iff] at this
  exact Fin.ext this

def BV : Vertrag BD where
  schreibt := fun _ => true
  gschreibt := fun _ => true
  erg := none
  gruende := 0
  haelt := []
  produziert := []

theorem hp : BD.typ BA.tab BA.feld = ByteTy := rfl

theorem rechte : Rechte BA BG BV [] where
  wT := rfl
  lT := by intro w hw; cases hw
  wF := rfl
  lF := by intro w hw; cases hw
  wU := rfl
  lU := by intro w hw; cases hw
  wH := fun _ => rfl
  lH := fun _ => by intro w hw; cases hw

def failure : Endblock BD BV true (BCtx 1 []) [] := .ret .empty (List.Perm.refl [])

/-- A world with counter `c`, empty free list, every stack empty. -/
def welt (c : Zahl 0 4) : World BD where
  slots := fun _ k f =>
    if h0 : f = 0 then (by subst h0; exact (⟨0, by decide, by decide⟩ : Zahl 0 255))
    else (by
      have : BD.typ () f = .int 0 4 := by simp only [Fin.isValue, h0, ↓reduceIte]
      rw [this]; exact zc 4)
  globs := fun g => if g = 0 then c else if g = 1 then c else zc 4
  spur := []

def w0 : World BD := welt (zc 0)
def wv : World BD := welt (zc 4)

theorem frei_w0 : BA.FreiOk w0 :=
  ⟨[], FreiForm.Kette.nil, .nil, by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]⟩

theorem multi_w0 : MultiRep BL BG w0 (fun _ => []) := by
  refine ⟨fun _ => [], fun k => ⟨?_, .nil, by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true], rfl⟩, by simp only [ne_eq, List.not_mem_nil, not_false_eq_true, implies_true]⟩
  have : (BG k).st w0 = 4 := by
    rcases k with ⟨_ | _ | _ | _ | k, hk⟩ <;> rfl
  rw [this]
  exact KetteF.nil

/-- The state at counter 0 of a one-instruction program, head 7, all lists empty. -/
def s0 : State 1 := ⟨0, 7, [], [], [], []⟩

theorem stapel_s0 : stapel hp s0 = fun _ => [] := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | k, hk⟩ <;> rfl

def ρs : Env BD (BCtx 1 []) := .cons (kodiere 7) (.cons (pcWert 0) .nil)

/-- **Step witness**: the G block of `.` runs normally and the represented state has output `[7]`. -/
theorem befehl_schritt_zeuge (O : Orakel BD) (passes : Nat)
    (R : ∀ f : BD.Fn, World BD → Env BD (BD.params f) → RufAusgang f) :
    ∃ σ' ρ', execBlock O passes R (befehl BL BG hp rechte failure .output 1) w0 ρs = .ok σ' ρ' ∧
      Darstellt BL BG hp .nil (⟨1, 7, [], [], [], [7]⟩ : State 1) σ' ρ' :=
  befehl_schritt O passes R BL BG BG_inj hp rechte failure .nil .output 1 s0 w0 ρs
    ⟨rfl, stapel_s0 ▸ multi_w0, frei_w0⟩ (fun _ => .inr (by decide))

/-- **Out-of-memory witness**: in the full arena the G block of `.` runs the failure block. -/
theorem befehl_voll_zeuge (O : Orakel BD) (passes : Nat)
    (R : ∀ f : BD.Fn, World BD → Env BD (BD.params f) → RufAusgang f) :
    ∃ σf, execBlock O passes R (befehl BL BG hp rechte failure .output 1) wv ρs =
      (execEnd O passes R failure σf ρs).zuAusgang :=
  befehl_voll O passes R BL BG hp rechte failure .output (.inr (.inr rfl)) 1 wv ρs rfl rfl

end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.SchrittWitnesses
