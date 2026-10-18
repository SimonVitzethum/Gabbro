/-
  File:      Grammatik/Zielsatz/Eigenschaften/RwRang.lean
  Subject:   THE READER/WRITER LOCK, STEP TWO: lock RANKS and DEADLOCK FREEDOM over the layer
             (`RwSchritt.lean`), and the progress of a reader.

  The rank order is machine G's: `Stmt.locks L hr` carries the premise that every lock held ranks
  below `L`, and the acquisition of the layer is machine G's own `dannLocks` step, so a shared
  acquisition obeys it exactly as an exclusive one does. What changes with a shared lock is the
  WAIT relation: a reader at `locks L` is not held back by readers, only by a writer; a writer is
  held back by every holder.

  * `rangInvG_rw` -- the per-thread rank invariant of G (`RangInvG`) along every layer run: the
    acting thread's record moves by a G step (`rwSchritt_akteur`), the others do not move.
  * `kein_warteZyklus_rw` -- NO WAIT CYCLE on every layer run, whatever the other threads do: the
    ranks along a chain of `WartetAuf` links rise strictly, the chain cannot close
    (`kein_warteZyklusG` over the layer; the argument is the same, the invariant is `rangInvG_rw`).
    The statement is about the plain `WartetAuf` (every holder blocks); the mode-aware relation
    `WartetAufRw` (a reader waits only for a writer, a writer for every holder) is a SUBRELATION,
    so `keinWarteZyklusRw_aus` is the statement for it.
  * `rw_leser_geht` -- PROGRESS FOR A READER: a thread at `locks L` that is a reader of `L`, with
    every other holder of `L` a reader, has a layer step (a shared acquisition). Machine G alone
    would hold it back (`RufFreiG` fails when another reader holds `L`); the layer admits it.
-/
import Grammatik.Zielsatz.Eigenschaften.RwSchritt
import Grammatik.Zielsatz.Kern.Beweis

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat} {lese : Lese D}

/-! ## 1. The rank invariant along a layer run -/

theorem rangInvG_rw (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup)
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : RwLauf P O passes lese (RufStartG P sp init) ms fs n) :
    ∀ k, k ≤ n → ∀ t, RangInvG (init t).1 ((ms k).faeden t)
  | 0, _ => by
      rw [hl.1]
      exact rangInvG_erreichbar (passes := passes) hO hSt sp init hND RufErreichbarG.start
  | k + 1, hk => by
      have ih := rangInvG_rw hO hSt sp init hND hl k (by omega)
      have hs := hl.2 k (by omega)
      intro t
      by_cases ht : t = fs k
      · subst ht
        obtain ⟨Mh, Mh', hg, h1, _, h3, _⟩ := rwSchritt_akteur hs
        have := rangInvG_schritt hO hSt hg (by rw [h1]; exact ih _)
        rw [h3] at this
        exact this
      · rw [rwSchritt_fremd hs t ht]
        exact ih t

/-! ## 2. No wait cycle -/

/-- **The wait relation of a shared lock**: `t` stands at `locks L`, `u` holds `L`, and the two are not
    both readers of `L` (a reader waits only for a writer; a writer waits for every holder). -/
def WartetAufRw (lese : Lese D) (M : RufMaschineG D) (t u : Faden) (L : D.Lock) : Prop :=
  AnSperre M t L ∧ L ∈ offen (M.faeden u).spur ∧ (¬ lese t L ∨ ¬ lese u L)

def KeinWarteZyklusRw (lese : Lese D) (M : RufMaschineG D) : Prop :=
  ∀ (n : Nat) (ts : Nat → Faden) (Ls : Nat → D.Lock),
    (∀ i, i ≤ n → WartetAufRw lese M (ts i) (ts (i + 1)) (Ls i)) → ts (n + 1) ≠ ts 0

/-- The mode-aware wait relation is a subrelation of the plain one, so the plain statement carries. -/
theorem keinWarteZyklusRw_aus {M : RufMaschineG D} (h : KeinWarteZyklus M) :
    KeinWarteZyklusRw lese M :=
  fun n ts Ls hW => h n ts Ls fun i hi => ⟨(hW i hi).1, (hW i hi).2.1⟩

/-- **No wait cycle on every layer run**: with the rank invariant of every thread, along a chain
    `t₀ … tₙ₊₁` of `WartetAuf` links the ranks of the locks rise strictly, so the chain cannot close.
    Shared holders do not weaken this: the invariant is about the ranks of what a thread holds. -/
theorem kein_warteZyklus_rw (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hLeer : ∀ t, D.haelt (init t).1 = [])
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : RwLauf P O passes lese (RufStartG P sp init) ms fs n) (k : Nat) (hk : k ≤ n) :
    KeinWarteZyklus (ms k) := by
  have hI := rangInvG_rw hO hSt sp init (startSpur_nodup_leer init hLeer) hl k hk
  intro m ts Ls hW he
  have hlt : ∀ i, i < m → D.rang (Ls i) < D.rang (Ls (i + 1)) := fun i hi =>
    (sperre_rang (hI (ts (i + 1))) (hW (i + 1) hi).1).2 (Ls i) (hW i (Nat.le_of_lt hi)).2
  have hle : ∀ i, i ≤ m → D.rang (Ls 0) ≤ D.rang (Ls i) := by
    intro i
    induction i with
    | zero => intro _; exact Int.le_refl _
    | succ i ih =>
        intro hi
        have h1 := hlt i hi
        have h2 := ih (Nat.le_of_succ_le hi)
        omega
  have h1 := (hW m (Nat.le_refl m)).2
  rw [he] at h1
  have hlast := (sperre_rang (hI (ts 0)) (hW 0 (Nat.zero_le m)).1).2 (Ls m) h1
  have := hle m (Nat.le_refl m)
  omega

/-! ## 3. Progress for a reader -/

theorem anSperre_ohneFremde {M : RufMaschineG D} {f : Faden} {L : D.Lock} :
    AnSperre (ohneFremde M f) f L ↔ AnSperre M f L := by
  unfold AnSperre
  rw [ohneFremde_self]

/-- **A reader that stands at `locks L` while only readers hold `L` can step.** The step is a shared
    acquisition; in machine G alone it would be blocked by `RufFreiG`. -/
theorem rw_leser_geht {w : D.Fn} {M : RufMaschineG D} {f : Faden} {L : D.Lock}
    (hI : RangInvG w (M.faeden f)) (hA : AnSperre M f L) (hl : lese f L)
    (hr : ∀ g, g ≠ f → L ∈ offen (M.faeden g).spur → lese g L) :
    ∃ M', RwAcq P O passes lese M f L M' := by
  have hA' : AnSperre (ohneFremde M f) f L := anSperre_ohneFremde.mpr hA
  have hI' : RangInvG w ((ohneFremde M f).faeden f) := by rw [ohneFremde_self]; exact hI
  obtain ⟨Mh, hs⟩ := schritt_an_sperre (P := P) (O := O) (passes := passes) hI' hA'
    (ohneFremde_frei M f L)
  obtain ⟨hself, _⟩ := sperre_rang hI hA
  have e := (sperre_schritt hA' hs).2
  refine ⟨{ Mh with faeden := rufUpdateG M.faeden f (Mh.faeden f) }, hl, hr, ⟨hself, ?_⟩, Mh, hs, rfl⟩
  show L ∈ offen (rufUpdateG M.faeden f (Mh.faeden f) f).spur
  rw [rufUpdateG_self, e]
  simp [offen]

end Gabbro.Grammatik.Zielsatz

#print axioms Gabbro.Grammatik.Zielsatz.kein_warteZyklus_rw
#print axioms Gabbro.Grammatik.Zielsatz.rw_leser_geht
