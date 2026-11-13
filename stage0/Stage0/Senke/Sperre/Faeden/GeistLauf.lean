/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/GeistLauf.lean
  Subject:   RUNS OF THE ABSTRACT TICKET LOCK CARRY THE MODEL'S GHOST. `AbsLauf akt a` is a run of the abstract lock
             at the granularity of machine G: at each scheduler step the scheduled thread does what one G step can do
             to one lock (`Weg`: give, draw, enter, each optional, in this order), and a stutter changes nothing.
             Along such a run
             * the queue facts of the model's `FifoLauf` hold for the abstract queue (`AbsLauf.eindeutig`,
               `AbsLauf.kopf`, `AbsLauf.ordnung`); and
             * there is a ghost run of the model's ticket lock `Tkt` (Code/Conc/LockRel.lean) that shows the abstract
               lock at every step (`Passt`, with `Tkt.Ok`) and moves at each step by the scheduled thread's own
               `take`/`enter`/`leave` (`TWeg`), or not at all on a stutter (`AbsLauf.tkt`), provided fewer than
               `2 ^ wbits - 2` threads wait at any step. The ghost at the first step is read off the abstract lock
               (`tAnfang`: holder first, then the queue, as tickets `0, 1, …`).
-/
module
public import Stage0.Senke.Sperre.Faeden.Geist
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Code (Conf)
open Gabbro.Code.Lower (Tkt)

/-! ## 1. The ghost read off an abstract lock -/

/-- The holder, then the waiting threads. -/
def tListe (a : Abs Nat) : List Nat := a.holder.toList ++ a.queue

/-- **The ghost of an abstract lock**: ticket `i` belongs to the `i`-th thread of `tListe a`; none is served yet. -/
def tAnfang (a : Abs Nat) : Tkt := ⟨0, (tListe a).length, fun (i : Nat) => (tListe a)[i]?, a.holder.isSome⟩

/-- The owners of the tickets of a list after a prefix are the rest of the list. -/
theorem fm_liste : ∀ (q p : List Nat),
    (List.range' p.length q.length).filterMap (fun (i : Nat) => (p ++ q)[i]?) = q
  | [], _ => rfl
  | x :: q, p => by
    have hx : (p ++ x :: q)[p.length]? = some x := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    have e : p ++ x :: q = (p ++ [x]) ++ q := by simp
    have hl : (p ++ [x]).length = p.length + 1 := by simp
    rw [List.length_cons, List.range'_succ, List.filterMap_cons_some (f := fun (i : Nat) => (p ++ x :: q)[i]?) hx, e,
      ← hl, fm_liste q (p ++ [x])]

theorem liste_nodup {a : Abs Nat} (ha : AbsOK a) : (tListe a).Nodup := by
  unfold tListe
  cases hh : a.holder with
  | none => exact ha.nodup
  | some x => exact List.nodup_cons.2 ⟨ha.frei x hh, ha.nodup⟩

theorem erst_anfang (a : Abs Nat) : tErst (tAnfang a) = a.holder.toList.length := by
  cases hh : a.holder <;> simp [tErst, tAnfang, hh]

section

variable [Conf]

/-- **The ghost read off a well-formed abstract lock shows it.** -/
theorem passt_anfang (a : Abs Nat) (ha : AbsOK a) (hb : a.queue.length + 1 < 2 ^ Conf.wbits) :
    Passt (tAnfang a) a := by
  have hlen : (tListe a).length = a.holder.toList.length + a.queue.length := by simp [tListe]
  have h1 := Option.length_toList_le (o := a.holder)
  have hnd := liste_nodup ha
  have h2 : (tAnfang a).n - tErst (tAnfang a) = a.queue.length := by
    rw [erst_anfang]
    show (tListe a).length - _ = _
    omega
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show (tListe a).length - 0 < 2 ^ Conf.wbits
    omega
  · intro i _ h
    exact ⟨(tListe a)[i]'h, List.getElem?_eq_getElem h⟩
  · intro i j u _ hi _ _ e1 e2
    exact (hnd.getElem?_inj hi).1 (e1.trans e2.symm)
  · intro h
    show 0 < (tListe a).length
    cases hh : a.holder with
    | none => simp [tAnfang, hh] at h
    | some x => simp [tListe, hh]
  · cases hh : a.holder <;> simp [tHalter, tAnfang, tListe, hh]
  · unfold tWarte
    rw [h2, erst_anfang]
    exact (fm_liste a.queue a.holder.toList).symm
  · rw [erst_anfang]
    exact hlen

end

/-! ## 2. Runs of the abstract lock at the granularity of machine G -/

/-- **A run of the abstract lock, scheduled by `akt`**: each step of thread `u` is what one step of machine G can
    do to one lock, a stutter changes nothing. -/
structure AbsLauf (akt : Nat → Option Nat) (a : Nat → Abs Nat) : Prop where
  ok0 : AbsOK (a 0)
  schritt : ∀ n u, akt n = some u → Weg u (a n) (a (n + 1))
  stotter : ∀ n, akt n = none → a (n + 1) = a n

variable {akt : Nat → Option Nat} {a : Nat → Abs Nat}

theorem AbsLauf.ok (H : AbsLauf akt a) : ∀ n, AbsOK (a n)
  | 0 => H.ok0
  | n + 1 => by
    cases hk : akt n with
    | none => rw [H.stotter n hk]; exact H.ok n
    | some u => exact (H.schritt n u hk).ok (H.ok n)

/-- Each waiting thread once (`FifoLauf.eindeutig`). -/
theorem AbsLauf.eindeutig (H : AbsLauf akt a) (n : Nat) : (a n).queue.Nodup := (H.ok n).nodup

/-- **Only the head takes the lock** (`FifoLauf.kopf`): a waiting thread whose step makes it the holder headed
    the queue. -/
theorem AbsLauf.kopf (H : AbsLauf akt a) {n : Nat} {u : Nat} (hk : akt n = some u) (hu : u ∈ (a n).queue)
    (hh : (a (n + 1)).holder = some u) : (a n).queue.head? = some u :=
  Weg.kopf (H.schritt n u hk) (H.ok n) hu hh

/-- **First come, first served** (`FifoLauf.ordnung`). -/
theorem AbsLauf.ordnung (H : AbsLauf akt a) (n : Nat) :
    (a n).queue.filter (fun u => decide (u ∈ (a (n + 1)).queue)) <+: (a (n + 1)).queue := by
  cases hk : akt n with
  | none =>
    rw [H.stotter n hk]
    have hf : (a n).queue.filter (fun u => decide (u ∈ (a n).queue)) = (a n).queue :=
      List.filter_eq_self.2 (fun x hx => decide_eq_true hx)
    exact (congrArg (fun l => l <+: (a n).queue) hf).mpr (List.prefix_refl _)
  | some u => exact Weg.ordnung (H.schritt n u hk) (H.ok n) _ (fun x => decide_eq_true_iff)

/-! ## 3. Every such run carries a ghost run of the model's lock -/

/-- The ghost move at one scheduler step: none on a stutter, the scheduled thread's `TWeg` otherwise. -/
def Nach (o : Option Nat) (t t' : Tkt) : Prop :=
  match o with
  | none => t' = t
  | some u => TWeg u t t'

section

variable [Conf]

/-- **One G step of the abstract lock is one ghost move of the same thread.** -/
theorem passt_weg {t : Tkt} {b d : Abs Nat} {u : Nat} (P : Passt t b) (h : Weg u b d)
    (hd : d.queue.length + 2 < 2 ^ Conf.wbits) : ∃ t', Passt t' d ∧ TWeg u t t' := by
  obtain ⟨b1, c, h1, h2, h3⟩ := h
  obtain ⟨tb, Pb, Gb⟩ : ∃ tb, Passt tb b1 ∧ OptT (TGibt u) t tb := by
    rcases h1 with e | h1
    · exact ⟨t, e ▸ P, Or.inl rfl⟩
    · obtain ⟨Q, G⟩ := passt_gibt P h1
      exact ⟨_, Q, Or.inr G⟩
  have key : c.queue.length + 1 ≤ d.queue.length + 2 := by
    rcases h3 with e | ⟨_, hq, he⟩
    · subst e; omega
    · obtain ⟨r, hr⟩ := List.head?_eq_some_iff.1 hq
      have hdq : d.queue = c.queue.tail := congrArg Abs.queue he
      have h1 : c.queue.length = r.length + 1 := by rw [hr, List.length_cons]
      have h2 : d.queue.length = r.length := by rw [hdq, hr, List.tail_cons]
      omega
  obtain ⟨tc, Pc, Zc⟩ : ∃ tc, Passt tc c ∧ OptT (TZieht u) tb tc := by
    rcases h2 with e | h2
    · exact ⟨tb, e ▸ Pb, Or.inl rfl⟩
    · obtain ⟨Q, G⟩ := passt_zieht Pb h2 (Nat.lt_of_le_of_lt key hd)
      exact ⟨_, Q, Or.inr G⟩
  obtain ⟨td, Pd, Td⟩ : ∃ td, Passt td d ∧ OptT (TTritt u) tc td := by
    rcases h3 with e | h3
    · exact ⟨tc, e ▸ Pc, Or.inl rfl⟩
    · obtain ⟨Q, G⟩ := passt_tritt Pc h3
      exact ⟨_, Q, Or.inr G⟩
  exact ⟨td, Pd, tb, tc, Gb, Zc, Td⟩

theorem geist_ex (H : AbsLauf akt a) (hB : ∀ n, (a n).queue.length + 2 < 2 ^ Conf.wbits) {n : Nat} {t : Tkt}
    (P : Passt t (a n)) : ∃ t', Passt t' (a (n + 1)) ∧ Nach (akt n) t t' := by
  cases hk : akt n with
  | none => exact ⟨t, by rw [H.stotter n hk]; exact P, rfl⟩
  | some u => exact passt_weg P (H.schritt n u hk) (hB (n + 1))

open Classical in
/-- The ghost run: read off the first abstract state, then one ghost move per scheduler step. -/
noncomputable def geist (akt : Nat → Option Nat) (a : Nat → Abs Nat) : Nat → Tkt
  | 0 => tAnfang (a 0)
  | n + 1 => if h : ∃ t', Passt t' (a (n + 1)) ∧ Nach (akt n) (geist akt a n) t' then Classical.choose h
      else geist akt a n

open Classical in
theorem geist_succ (n : Nat) : geist akt a (n + 1) =
    if h : ∃ t', Passt t' (a (n + 1)) ∧ Nach (akt n) (geist akt a n) t' then Classical.choose h
      else geist akt a n := rfl

theorem geist_passt (H : AbsLauf akt a) (hB : ∀ n, (a n).queue.length + 2 < 2 ^ Conf.wbits) :
    ∀ n, Passt (geist akt a n) (a n)
  | 0 => passt_anfang (a 0) H.ok0 (by have := hB 0; omega)
  | n + 1 => by
    have hex := geist_ex H hB (geist_passt H hB n)
    rw [geist_succ, dif_pos hex]
    exact (Classical.choose_spec hex).1

theorem geist_nach (H : AbsLauf akt a) (hB : ∀ n, (a n).queue.length + 2 < 2 ^ Conf.wbits) (n : Nat) :
    Nach (akt n) (geist akt a n) (geist akt a (n + 1)) := by
  have hex := geist_ex H hB (geist_passt H hB n)
  rw [geist_succ, dif_pos hex]
  exact (Classical.choose_spec hex).2

/-- **THE ABSTRACT LOCK SIMULATES THE MODEL'S LOCK**: every run of the abstract lock at G granularity, with fewer
    than `2 ^ wbits - 2` waiting threads at every step, carries a ghost run of `Tkt` that shows it at every step
    and moves only by the scheduled thread's own `take`/`enter`/`leave`. -/
theorem AbsLauf.tkt (H : AbsLauf akt a) (hB : ∀ n, (a n).queue.length + 2 < 2 ^ Conf.wbits) :
    ∃ gh : Nat → Tkt, (∀ n, Passt (gh n) (a n)) ∧ ∀ n, Nach (akt n) (gh n) (gh (n + 1)) :=
  ⟨geist akt a, geist_passt H hB, geist_nach H hB⟩

end

end Gabbro.Stage0.Senke.Faeden
