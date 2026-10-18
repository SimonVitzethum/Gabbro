/-
  File:      Grammatik/ArenaSperreWelt.lean
  Subject:   THE WITNESS DECLARATION OF A SHARED ARENA (PLAN-DYNAMISCH.md section 8a.2): the four-slot arena of
             `ArenaDynZeuge.lean` again, now SHARED -- one lock `()` guards the table and all four words
             (`braucht`/`gbraucht` name `Held(())`), so every access needs the lock in the hand and the arena
             is the invariant of that lock.

  Only the lock-related fields of `InvDynZeuge.FD` change (`Lock := Unit`, `geteilt`, `braucht`, `gbraucht`). The types of
  the memory (`Tab`, `Feld`, `typ`, `Glob`, `gtyp`, `Fn`, `sig`) are the same terms, so a world of the old declaration is a
  world of the new one by re-packing its three fields (`uebertr`), and every number of `w0` carries over by `rfl`.
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreInv
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkennerZeuge

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace SperreZeuge

open InvDynZeuge

/-- The declaration of the shared arena: `FD` with one lock that guards every carrier. -/
@[reducible] def FDL : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Fin 4
  decFeld := fun _ => inferInstance
  typ := fun _ f => if f = 0 then .int 0 255 else .int 0 4
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Fin 4
  decGlob := inferInstance
  gtyp := fun _ => .int 0 4
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => true
  ggeteilt := fun _ => true
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [Sum.inl ()]
  gbraucht := fun _ => [Sum.inl ()]
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
  geteilt_bewacht := fun t _ => by simp
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g _ => Or.inl (by simp)

/-- The arena with slot release, over the shared declaration. -/
def FAL : FreiForm FDL where
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

def LLL : LinkFeld FAL where
  f := 2
  hf := rfl
  h1 := by decide
  h2 := by decide

def LGL : LinkKopf FAL where
  g := 3
  hg := rfl
  h1 := by decide
  h2 := by decide
  h3 := by decide

/-- **The arena of the witnesses carries a list and no tree.** -/
def KLL : Dekl FAL where
  liste := some ⟨LLL, LGL⟩
  baum := none
  getrennt := fun _ _ _ h => by cases h

/-- A world of the old declaration, as a world of the shared one. -/
def uebertr (σ : World FD) : World FDL := ⟨σ.slots, σ.globs, []⟩

/-- The scenario world: slot `1` on the free list, list `2 -> 0`. -/
def w0L : World FDL := uebertr w0

theorem stand_w0L : FAL.stand w0L = 4 := rfl
theorem kopf_w0L : FAL.kopfSt w0L = 1 := rfl
theorem naechst_w0L (j : Int) : FAL.naechst w0L j = 4 := rfl
theorem lg_w0L : LGL.st w0L = 2 := rfl
theorem ll_w0L (j : Int) : LLL.wert w0L j = ln0 j := ll_w0 j

theorem kette_w0L : FAL.Kette w0L 1 [1] :=
  FreiForm.Kette.cons 1 (by decide) (by decide) [] (by rw [naechst_w0L]; exact FreiForm.Kette.nil)

theorem freiOk_w0L : FAL.FreiOk w0L := by
  refine ⟨[1], by rw [kopf_w0L]; exact kette_w0L, by decide, ?_⟩
  intro i hi; simp at hi; subst hi; rw [stand_w0L]; omega

theorem aufListe_w0L (i : Int) : FAL.AufListe w0L i ↔ i = 1 := by
  constructor
  · rintro ⟨L, hL, hm⟩
    rw [kopf_w0L] at hL
    have := FreiForm.Kette.eindeutig hL kette_w0L
    subst this; simpa using hm
  · rintro rfl
    exact ⟨[1], by rw [kopf_w0L]; exact kette_w0L, by simp⟩

theorem lebt_w0L (i : Int) : FAL.Lebt w0L i ↔ (0 ≤ i ∧ i < 4 ∧ i ≠ 1) := by
  unfold FreiForm.Lebt
  rw [aufListe_w0L, stand_w0L]

theorem listeKette_w0L : KetteF 4 (LLL.wert w0L) 2 [2, 0] := by
  refine KetteF.cons 2 (by decide) (by decide) [0] ?_
  rw [ll_w0L]
  refine KetteF.cons 0 (by decide) (by decide) [] ?_
  rw [ll_w0L]
  exact KetteF.nil

theorem listOk_w0L : ListOk FAL LLL LGL w0L := by
  unfold ListOk
  rw [lg_w0L]
  refine ⟨[2, 0], listeKette_w0L, by decide, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact (lebt_w0L _).mpr (by decide)
  · exact (lebt_w0L _).mpr (by decide)

/-- **The scenario world meets the arena invariant of the shared arena.** -/
theorem ok_w0L : KLL.Ok w0L :=
  ⟨freiOk_w0L, (Dekl.LOk_some (K := KLL) (d := ⟨LLL, LGL⟩) rfl w0L).mpr listOk_w0L,
    Dekl.BOk_none (K := KLL) rfl w0L, fun j hj => Dekl.InB_none (K := KLL) rfl w0L j hj.2⟩

/-- Every carrier of the declaration is a carrier of the arena: the arena IS the shared state. -/
theorem alle_orte (c : FDL.Tab ⊕ FDL.Glob) : c ∈ KLL.orte := by
  rcases c with t | g
  · cases t; exact Dekl.tab_mem_orte
  · match g with
    | 0 => exact Dekl.glob_mem_orte (K := KLL) (g := 0) (Dekl.mem_lesGlobs.mpr (Or.inl rfl))
    | 1 => exact Dekl.komm_mem_orte
    | 2 => exact Dekl.glob_mem_orte (K := KLL) (g := 2) (Dekl.mem_lesGlobs.mpr (Or.inr (Or.inl rfl)))
    | 3 =>
      exact Dekl.glob_mem_orte (K := KLL) (g := 3)
        (Dekl.mem_lesGlobs.mpr (Or.inr (Or.inr (Or.inl ⟨⟨LLL, LGL⟩, rfl, rfl⟩))))

/-- **The lock family of the witness is well formed:** every carrier is guarded by `()` and the invariant reads only
    the carriers (`SperrInvOk`, the premise `sperrOrte` of the checker's acceptance). -/
theorem sperr_ok_zeuge : SperrInvOk (KLL.sperr ()) :=
  Dekl.sperr_ok (fun c _ => by
    rcases c with t | g <;> simp [Bewacht, FDL])

end SperreZeuge

end Gabbro.Grammatik
