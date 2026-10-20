/-
  File:      Grammatik/ArenaSperreMaschine.lean
  Subject:   WHAT THE GOAL STATEMENT GIVES FOR A SHARED ARENA (PLAN-DYNAMIC.md section 8a.2): `Ziel P S O passes M0 M`
             quantifies over the lock family `S`. For `S := K.sperr L` -- the lock whose invariant is the arena's structure
             invariant -- the existing legs say, without any change of `Spec.lean`:

    * `arena_ruhe`      -- (`sperrInv`) wherever no thread holds `L`, the arena invariant holds in shared memory;
    * `arena_wechsel`   -- (`sperrWechsel`) every step that acquires `L` starts from and ends in an arena-consistent
                           memory, and every step that releases `L` leaves one: a reader that acquires sees a WHOLE
                           arena, and a thread that releases hands over a whole arena;
    * `arena_sicht`     -- (`sperrSicht`) every access of an arena carrier -- the table, the counter, the free head, the
                           list head, the tree root and the COMMITTED WORD `komm` -- is made by a holder of `L`, and while
                           `L` is held no other thread's step moves one of them.

  Together: a `grow` (a store to `komm`, written only through `dynGrowB`) is made under `L` (`komm_nur_halter`); no other
  thread sees the committed word, the counter or a link between the acquire and the release of the grower; and the arena
  the next acquirer sees is one the grower released consistent. The theorems below are the unfoldings of the three legs on
  the arena family; the content is in `Dekl.sperr` (the invariant IS `Dekl.Ok`) and in `abschnitt_erk`/`abschnitt_rufe`
  (a recognized section restores it).
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreAbschnitt

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

section Maschine
variable {A : FreiForm D} (K : Dekl A) (L : D.Lock) (P : Programm D) (O : Orakel D) (passes : Nat)
  (M : RufMaschineG D)

/-- **No thread holds `L`: the arena is whole.** -/
theorem arena_ruhe (h : SperrInvG (K.sperr L) M) (hfrei : ∀ t : Faden, L ∉ offen (M.faeden t).spur) :
    K.Ok (M.speicher.welt []) :=
  (Dekl.sperr_inv_iff M.speicher).mp (h L hfrei)

/-- **Acquire and release of the arena lock move whole arenas.** -/
theorem arena_wechsel (h : SperrWechselG P O passes (K.sperr L) M) {u : Faden} {M' : RufMaschineG D}
    (hs : RufSchrittG P O passes M u M') :
    (L ∉ offen (M.faeden u).spur → L ∈ offen (M'.faeden u).spur →
      K.Ok (M.speicher.welt []) ∧ K.Ok (M'.speicher.welt [])) ∧
    (L ∈ offen (M.faeden u).spur → L ∉ offen (M'.faeden u).spur → K.Ok (M'.speicher.welt [])) := by
  obtain ⟨h1, h2⟩ := h u M' L hs
  exact ⟨fun a b => let r := h1 a b; ⟨(Dekl.sperr_inv_iff _).mp r.1, (Dekl.sperr_inv_iff _).mp r.2⟩,
    fun a b => (Dekl.sperr_inv_iff _).mp (h2 a b)⟩

/-- **The arena's carriers are touched by the holder alone.** -/
theorem arena_sicht (h : SperrSichtG P O passes (K.sperr L) M) {u : Faden} {M' : RufMaschineG D}
    (hs : RufSchrittG P O passes M u M') {c : D.Tab ⊕ D.Glob} (hc : c ∈ K.orte) :
    (ZugriffG M M' u c → L ∈ offen (M.faeden u).spur) ∧
    (∀ t, t ≠ u → L ∈ offen (M.faeden t).spur → TraegerGleich M'.speicher M.speicher c) := by
  refine h u M' hs L c ?_
  rw [Dekl.sperr_orte_self]
  exact hc

/-- **The committed word is written, and read, under the lock only** -- the model of "`grow` is a locked commit": the one
    store of `grow` is a store to `komm`, a carrier of the arena, so it is made by a holder of `L`, and while `L` is held
    no other thread's step changes it. -/
theorem komm_nur_halter (h : SperrSichtG P O passes (K.sperr L) M) {u : Faden} {M' : RufMaschineG D}
    (hs : RufSchrittG P O passes M u M') :
    (ZugriffG M M' u (Sum.inr A.komm) → L ∈ offen (M.faeden u).spur) ∧
    (∀ t, t ≠ u → L ∈ offen (M.faeden t).spur → TraegerGleich M'.speicher M.speicher (Sum.inr A.komm)) :=
  arena_sicht K L P O passes M h hs Dekl.komm_mem_orte

/-- **The three legs of the goal, read on the arena family.** From `Ziel` for `S := K.sperr L` the three statements
    above hold at every machine `M` reached. -/
theorem arena_ziel {M0 : RufMaschineG D} (h : Ziel P (K.sperr L) O passes M0 M) :
    (∀ _ : ∀ t : Faden, L ∉ offen (M.faeden t).spur, K.Ok (M.speicher.welt [])) ∧
    (∀ {u : Faden} {M' : RufMaschineG D}, RufSchrittG P O passes M u M' →
      (L ∉ offen (M.faeden u).spur → L ∈ offen (M'.faeden u).spur →
        K.Ok (M.speicher.welt []) ∧ K.Ok (M'.speicher.welt [])) ∧
      (L ∈ offen (M.faeden u).spur → L ∉ offen (M'.faeden u).spur → K.Ok (M'.speicher.welt []))) ∧
    (∀ {u : Faden} {M' : RufMaschineG D}, RufSchrittG P O passes M u M' → ∀ c ∈ K.orte,
      (ZugriffG M M' u c → L ∈ offen (M.faeden u).spur) ∧
      (∀ t, t ≠ u → L ∈ offen (M.faeden t).spur → TraegerGleich M'.speicher M.speicher c)) :=
  ⟨fun hf => arena_ruhe K L M h.sperrInv hf,
   fun hs => arena_wechsel K L P O passes M h.sperrWechsel hs,
   fun hs _ hc => arena_sicht K L P O passes M h.sperrSicht hs hc⟩

end Maschine

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.arena_ziel
