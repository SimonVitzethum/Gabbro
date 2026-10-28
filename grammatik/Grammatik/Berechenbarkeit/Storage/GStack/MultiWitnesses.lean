import Grammatik.Berechenbarkeit.Storage.GStack.Multi
import Grammatik.Bausteine.Arena.Struktur.ArenaDynZeuge

/-! Witnesses of `push_multi` and `pop_multi` over a concrete declaration with TWO stacks in one arena: `MD` is the
arena declaration of `InvDynZeuge.FD` with a fifth word, so word 3 heads stack 0 and word 4 heads stack 1. In the
world `w1` each stack holds one cell (cell 0 on stack 0, cell 1 on stack 1). An executed push on stack 0 and an
executed pop on stack 1 each change their own stack and leave the other one, which is NOT empty, as it was. -/

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.MultiWitnesses

open ArenaKette InvDynZeuge

@[reducible] def MD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Fin 4
  decFeld := fun _ => inferInstance
  typ := fun _ f => if f = 0 then .int 0 255 else .int 0 4
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Fin 5
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
def MA : FreiForm MD where
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

/-- The stack link (field `2`) and the two heads (words `3` and `4`). -/
def ML : LinkFeld MA where
  f := 2
  hf := rfl
  h1 := by decide
  h2 := by decide

def MG0 : LinkKopf MA where
  g := 3
  hg := rfl
  h1 := by decide
  h2 := by decide
  h3 := by decide

def MG1 : LinkKopf MA where
  g := 4
  hg := rfl
  h1 := by decide
  h2 := by decide
  h3 := by decide

/-- The two heads, by stack index. -/
def heads : Fin 2 → LinkKopf MA := fun k => if k = 0 then MG0 else MG1

/-- Two stacks' contents, by stack index. -/
def zwei {α : Type} (a b : α) : Fin 2 → α := fun k => if k = 0 then a else b

theorem heads_inj : Function.Injective fun k => (heads k).g := by
  intro a b h
  rcases a with ⟨_ | _ | a, ha⟩ <;> rcases b with ⟨_ | _ | b, hb⟩ <;> first | rfl | omega | (simp only [heads, Fin.zero_eta, Fin.isValue, ↓reduceIte, MG0, Nat.zero_add, Fin.mk_one, Fin.one_eq_zero_iff, Nat.succ_ne_self, MG1, Fin.reduceEq] at h)

def MV : Vertrag MD where
  schreibt := fun _ => true
  gschreibt := fun _ => true
  erg := none
  gruende := 0
  haelt := []
  produziert := []

theorem mdarf : darf MD () ([] : List (Res MD)) := by
  intro w hw; cases hw

theorem mgdarf (g : MD.Glob) : gdarf MD g ([] : List (Res MD)) := by
  intro w hw; cases hw

abbrev Payload := MD.typ MA.tab MA.feld

def zero : Wert MD Payload := ⟨0, by decide, by decide⟩
def seven : Wert MD Payload := ⟨7, by decide, by decide⟩

/-- Counter 2, empty free list, stack 0 = cell 0, stack 1 = cell 1, every link 4 (the end), payload 0. -/
def w1 : World MD where
  slots := fun _ k f =>
    if h0 : f = 0 then (by subst h0; exact (⟨0, by decide, by decide⟩ : Zahl 0 255))
    else (by
      have : MD.typ () f = .int 0 4 := by simp only [Fin.isValue, h0, ↓reduceIte]
      rw [this]; exact zc 4)
  globs := fun g => if g = 0 then zc 2 else if g = 1 then zc 2 else if g = 2 then zc 4 else if g = 3 then zc 0
    else zc 1
  spur := []

theorem stand_w1 : MA.stand w1 = 2 := rfl
theorem kopf_w1 : MA.kopfSt w1 = 4 := rfl
theorem link_w1 (j : Int) : ML.wert w1 j = 4 := rfl

theorem aufListe_w1 (i : Int) : ¬ MA.AufListe w1 i := by
  rintro ⟨L, hL, hm⟩
  rw [kopf_w1] at hL
  cases hL with
  | nil => simp only [List.not_mem_nil] at hm
  | cons _ _ hk _ _ => exact absurd hk (by decide)

theorem lebt_w1 (i : Int) : MA.Lebt w1 i ↔ 0 ≤ i ∧ i < 2 := by
  unfold FreiForm.Lebt
  rw [stand_w1]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, aufListe_w1 i⟩⟩

theorem frei_w1 : MA.FreiOk w1 :=
  ⟨[], by rw [kopf_w1]; exact FreiForm.Kette.nil, .nil, by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]⟩

/-- Both stacks hold one cell with payload 0. -/
theorem multi_w1 : MultiRep ML heads w1 (fun _ => [zero]) := by
  refine ⟨zwei [0] [1], fun k => ?_, ?_⟩
  · rcases k with ⟨_ | _ | k, hk⟩
    · refine ⟨KetteF.cons 0 (by decide) (by decide) [] (by rw [link_w1]; exact KetteF.nil), by simp only [zwei, Fin.zero_eta, Fin.isValue, ↓reduceIte, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
  List.nodup_nil, and_self], ?_, rfl⟩
      intro i hi; simp only [zwei, Fin.zero_eta, Fin.isValue, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi; exact (lebt_w1 0).mpr (by decide)
    · refine ⟨KetteF.cons 1 (by decide) (by decide) [] (by rw [link_w1]; exact KetteF.nil), by simp only [zwei, Nat.zero_add, Fin.mk_one, Fin.isValue, Fin.one_eq_zero_iff, Nat.succ_ne_self, ↓reduceIte,
  List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self], ?_, rfl⟩
      intro i hi; simp only [zwei, Nat.zero_add, Fin.mk_one, Fin.isValue, Fin.one_eq_zero_iff, Nat.succ_ne_self, ↓reduceIte,
  List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi; exact (lebt_w1 1).mpr (by decide)
    · omega
  · intro a b hab i hi hi'
    rcases a with ⟨_ | _ | a, ha⟩ <;> rcases b with ⟨_ | _ | b, hb⟩ <;>
      first | omega | (simp only [zwei, Fin.zero_eta, Fin.isValue, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false, Nat.zero_add, Fin.mk_one, Fin.one_eq_zero_iff, Nat.succ_ne_self] at hi hi'; omega)

def failure {Γ : Ctx} : Endblock MD MV false Γ [] := .ret .empty (List.Perm.refl [])

/-- The fresh allocator storing the local `7`. -/
def fresh : Allocator MA MV false [Payload] [] :=
  Gabbro.Grammatik.Block.arenaAlloc MA.toArenaForm (.var .here) rfl mdarf rfl (mgdarf _) failure

/-- **Push witness**: pushing `7` on stack 0 gives stack 0 = `[7, 0]` and leaves stack 1 = `[0]`. -/
theorem push_multi_zeuge (O : Orakel MD) (passes : Nat)
    (R : ∀ f : MD.Fn, World MD → Env MD (MD.params f) → RufAusgang f) :
    ∃ σ' kk,
      (∀ {Λ'} (rest : Gabbro.Grammatik.Block MD MV false [Ty.index 4, Payload] [] Λ'),
        execBlock O passes R (Block.pushAllocated fresh ML (heads 0) rfl mdarf rfl (mgdarf _) rest) w1
          (.cons seven .nil) = (execBlock O passes R rest σ' (.cons kk (.cons seven .nil))).schrumpf) ∧
      kk.n = 2 ∧ MultiRep ML heads σ' (zwei [seven, zero] [zero]) ∧ MA.FreiOk σ' := by
  obtain ⟨σ', kk, hexec, hkn, hm, hf⟩ := push_multi O passes R fresh ML heads heads_inj 0 rfl mdarf rfl
    (mgdarf _) w1 (.cons seven .nil) seven (fun _ => [zero]) 2 multi_w1
    (fresh_allocated O passes R MA .here rfl mdarf rfl (mgdarf _) failure w1 (.cons seven .nil) frei_w1
      (by decide))
  refine ⟨σ', kk, hexec, hkn, ?_, hf⟩
  have he : Function.update (fun _ : Fin 2 => [zero]) 0 [seven, zero] = zwei [seven, zero] [zero] := by
    funext k
    rcases k with ⟨_ | _ | k, hk⟩
    · rfl
    · rfl
    · omega
  rw [← he]
  exact hm

/-- **Pop witness**: popping stack 1 hands its payload `0` to the continuation, empties stack 1 and leaves
stack 0 = `[0]`. -/
theorem pop_multi_zeuge (O : Orakel MD) (passes : Nat)
    (R : ∀ f : MD.Fn, World MD → Env MD (MD.params f) → RufAusgang f) :
    ∃ (σ' : World MD) (kk : Wert MD (Ty.index 4)),
      execBlock O passes R (Block.popAndRelease ML (heads 1) rfl (mgdarf _) rfl mdarf rfl (mgdarf _)
        (failure (Γ := [Payload])) (.nil : Gabbro.Grammatik.Block MD MV false [Payload, Ty.index 4, Payload] [] []))
        w1 (.cons seven .nil) =
        ((execBlock O passes R (.nil : Gabbro.Grammatik.Block MD MV false [Payload, Ty.index 4, Payload] [] [])
          σ' (.cons zero (.cons kk (.cons seven .nil)))).schrumpf).schrumpf ∧
      MultiRep ML heads σ' (zwei [zero] []) ∧ MA.FreiOk σ' := by
  obtain ⟨σ', kk, hexec, hm, hf⟩ := pop_multi O passes R ML heads heads_inj 1 rfl (mgdarf _) rfl mdarf rfl
    (mgdarf _) failure .nil w1 (.cons seven .nil) zero [] (fun _ => [zero]) rfl multi_w1 frei_w1
  refine ⟨σ', kk, hexec, ?_, hf⟩
  have he : Function.update (fun _ : Fin 2 => [zero]) 1 [] = zwei [zero] [] := by
    funext k
    rcases k with ⟨_ | _ | k, hk⟩
    · rfl
    · rfl
    · omega
  rw [← he]
  exact hm

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.MultiWitnesses
