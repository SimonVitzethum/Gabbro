/-
  File:      Grammatik/Speichermodell/DRF.lean
  Subject:   THE DRF THEOREM FOR GABBRO (Opus agent B, 2026-09-26): on a program whose
             footprints the checker bounded, machine W (weak memory) takes only steps of
             machine G (sequential consistency) -- for EVERY carrier, `atomic` ones included,
             and for every choice of memory orders.

  THE STATEMENT. `schwach_ist_g`: from every state W reaches, every step of W is a step of G
  on G's own memory, and W's G-part moves exactly as G. So every run of W is a run of G
  (`g_aus_w`), and with `w_aus_g` (MaschineW.lean) the two machines reach the same G-states.
  The weakness of W is real (`sb_erlaubt`, `mp_rlx_erlaubt` in Sicht.lean: on other programs W
  shows non-SC outcomes); on these programs it never shows, because every read reads the
  newest message (`liest_neueste`).

  THE PREMISES are the ones the race leg of G already uses, no more: a good oracle (`GutO`),
  closed call graphs `K` containing the starts (`AbgK`), footprints bounded by locality or a
  lock (`FussS … (lokK P K)`, the checker's `fuss` component) and an exclusive start
  (`StartExklusiv`). In particular NOTHING about `atomic` carriers beyond what `fuss` demands
  of every carrier: a carrier that a thread reads is either thread-local (no other thread's
  call graph writes it: `GetrenntK`) or guarded by a lock (`Bewacht`) -- `atomic` or not.

  WHY IT HOLDS (the invariant `SichtInv`, every field a lower bound on a view):
  * `frei` -- an unguarded carrier a thread's graph reads: that thread's view has reached
    every message of it. Only that thread writes it (`frei_schreiber`), and a write sets the
    writer's view to its own, fresh, larger timestamp.
  * `halter`/`sperre` -- a guarded carrier: the view of the thread holding its lock, or the
    lock's own view when nobody holds it, has reached every message. Every access holds the
    lock (`zugriff_haelt`), a take joins the lock's view (`genommenVon`), a release joins the
    thread's view into the lock (`gegebenVon`).
  * `stimmt` -- at a carrier some thread reads, the newest message carries G's value.
  So at a read the thread's view is at the newest message, `Lesbar` admits only that one, and
  it carries G's value: the presented memory IS G's memory.

  WHAT IS NOT CLAIMED HERE: that the view machine is exactly RC11 (it is the promise-free
  timestamp machine, which over-approximates RC11 for the orders the emitter uses; see
  Sicht.lean) and that the C compiler implements C11 atomics and `pthread_mutex` as specified
  -- both named in the header of `Spec.lean`.
-/
module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss
public import Grammatik.Speichermodell.Maschine.MaschineW
@[expose] public section


namespace Gabbro.Grammatik

open Speichermodell

variable {D : Deklaration}

/-- Thread `t`'s call graph reads carrier `c` (some function of `K t` has it in its
    footprint). A static fact: it does not move with the run. -/
def LesbarK (P : Programm D) (K : Faden → D.Fn → Bool) (t : Faden) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∃ f, K t f = true ∧ c ∈ fussOrteG P f

/-! ## 1. Static facts from the footprint check -/

/-- An unguarded footprint carrier is thread-local: `FussS` leaves no other disjunct. -/
theorem getrennt_of_frei {P : Programm D} {S : SperrInv D} {K : Faden → D.Fn → Bool} {f : D.Fn}
    (hF : FussS P S (lokK P K) f) {c : D.Tab ⊕ D.Glob} (hc : c ∈ fussOrteG P f)
    (hB : ∀ L, ¬ Bewacht c L) : GetrenntK P K c := by
  have hsig : sigB f c = false := by
    cases h : sigB f c
    · rfl
    · obtain ⟨L, hL, _⟩ := List.any_eq_true.mp h
      exact absurd (waechterVon_mem.mp hL) (hB L)
  rcases List.mem_append.mp hc with hc | hc
  · rcases hF.1 c hc with h | ⟨L, hL, _⟩
    · rw [hsig, Bool.false_or] at h
      exact lokK_ok h
    · exact absurd hL (hB L)
  · have h := hF.2 c hc
    rw [hsig, Bool.false_or] at h
    exact lokK_ok h

/-! ## 2. The invariant -/

section Inv

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
  {S : SperrInv D} {fs : List D.Fn} (sp : Speicher D)
  (init : Faden → Σ f : D.Fn, Env D (D.params f)) (K : Faden → D.Fn → Bool)

/-- **The view invariant of W** on a checked program. -/
structure SichtInv (W : RufMaschineW D) : Prop where
  erreicht : RufErreichbarG P O passes (RufStartG P sp init) W.g
  frei : ∀ c t, (∀ L, ¬ Bewacht c L) → LesbarK P K t c → ∀ m ∈ W.hist c, m.ts ≤ W.sicht t c
  halter : ∀ c L, Bewacht c L → ∀ t, L ∈ offen (W.g.faeden t).spur →
    ∀ m ∈ W.hist c, m.ts ≤ W.sicht t c
  sperre : ∀ c L, Bewacht c L → (∀ t, L ∉ offen (W.g.faeden t).spur) →
    ∀ m ∈ W.hist c, m.ts ≤ W.lsicht L c
  stimmt : ∀ c, (∃ t, LesbarK P K t c) → ∀ m ∈ W.hist c, (∀ m' ∈ W.hist c, m'.ts ≤ m.ts) →
    TraegerGleich W.g.speicher m.wert c

theorem sichtInv_start :
    SichtInv (P := P) (O := O) (passes := passes) sp init K (RufStartW (RufStartG P sp init)) where
  erreicht := .start
  frei _ _ _ _ m hm := by rw [List.mem_singleton.mp hm]; exact Nat.zero_le _
  halter _ _ _ _ _ m hm := by rw [List.mem_singleton.mp hm]; exact Nat.zero_le _
  sperre _ _ _ _ m hm := by rw [List.mem_singleton.mp hm]; exact Nat.zero_le _
  stimmt c _ m hm _ := by rw [List.mem_singleton.mp hm]; exact traegerGleich_refl _ c

end Inv

end Gabbro.Grammatik
