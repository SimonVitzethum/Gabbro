/-
  File:      Grammatik/RennfreiG.lean
  Subject:   DATA-RACE FREEDOM ON THE CALL MACHINE G, AS AN EXPLICIT THEOREM.

  Access set from the events the step records in the thread's trace
  (`zugriffe`, via `zugriffVon` over the trace delta); the race claim
  from the step's memory footprint (`TraegerGleich`), which is what the
  one-step rely `schritt_traeger` makes provable without a 70-case analysis.
-/
import Grammatik.ZielOrtZeuge

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The access set of one step, from the thread trace -/

/-- One event as a carrier access: table/global with its write flag. -/
def zugriffVon (e : Ereignis D) : Option ((D.Tab ⊕ D.Glob) × Bool) :=
  match e with
  | .zugriff t w _ _ => some (Sum.inl t, w)
  | .gzugriff g w _ _ => some (Sum.inr g, w)
  | _ => none

/-- The access set of one step: the carrier accesses among the events the
    step prepended to the thread's trace (newest first). -/
def zugriffe (M M' : RufMaschineG D) (f : Faden) : List ((D.Tab ⊕ D.Glob) × Bool) :=
  ((M'.faeden f).spur.take ((M'.faeden f).spur.length - (M.faeden f).spur.length)).filterMap
    zugriffVon

/-! ## 2. The race: two adjacent writes to one guarded carrier -/

/-- A step of `f` records nothing on any other thread's trace: the access
    set attributes events to the actor. Both premises are used: `hs` for the
    untouched thread state, `hg` to select it. -/
theorem zugriffe_anders {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (g : Faden) (hg : g ≠ f) : zugriffe M M' g = [] := by
  have e : M'.faeden g = M.faeden g := rufSchrittG_fremd hs g hg
  simp [zugriffe, e]

/-- An adjacent double write on a lock-guarded carrier: two steps back to
    back by different threads, each changing the same carrier `c`, where `c`
    has a guard lock and is neither an atomic global nor a published payload
    (the two lock-free disciplines, allowed races by design, excluded here by
    their declared discipline `D.atomar` / `D.nutzlast`). -/
def SchreibRasse (M M' M'' : RufMaschineG D) (f g : Faden) (c : D.Tab ⊕ D.Glob) : Prop :=
  f ≠ g ∧ ¬ TraegerGleich M'.speicher M.speicher c ∧
    ¬ TraegerGleich M''.speicher M'.speicher c ∧ (∃ L : D.Lock, Bewacht c L) ∧
    ¬ AtomarAusgenommen c ∧ ¬ PaarungAusgenommen c

/-! ## 3. Race freedom: the writer holds every guard, all others are out -/

/-- **Data-race freedom on the call machine G (`rennfrei_g`).** On every run
    reachable from `RufStartG P sp init`, a step that changes a guarded
    carrier `c` holds every guard of `c` before the step (from the one-step
    rely `schritt_traeger`, contrapositive: an unheld guard would leave `c`
    alone), and after the step no other thread holds that guard (lock
    exclusivity `exklusivG` over the untouched other threads). So two threads
    writing one guarded carrier are always ordered through the lock: the next
    writer can take the guard only after this writer released it. Every
    premise is used: `hO` for the rely, `hex`/`hr` for exclusivity, `hs` for
    both, `hB`/`hwr` for the held guard. -/
theorem rennfrei_g (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hO : GutO O)
    (hex : StartExklusiv init) (M M' : RufMaschineG D) (f : Faden)
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hs : RufSchrittG P O passes M f M') (c : D.Tab ⊕ D.Glob) (L : D.Lock)
    (hB : Bewacht c L) (hwr : ¬ TraegerGleich M'.speicher M.speicher c) :
    L ∈ offen (M.faeden f).spur ∧ ∀ g, g ≠ f → L ∉ offen (M'.faeden g).spur := by
  have hhaelt : L ∈ offen (M.faeden f).spur := by
    apply Classical.byContradiction
    intro hn
    exact hwr (schritt_traeger hO hs c (Or.inl ⟨L, hB, hn⟩))
  refine ⟨hhaelt, fun g hg => ?_⟩
  rw [rufSchrittG_fremd hs g hg]
  exact exklusivG hO sp init hex hr f g (fun e => hg e.symm) L hhaelt

/-- **No adjacent race on a guarded carrier.** Two steps back to back by
    different threads never both change one guarded carrier: the first writer
    holds the guard and excludes the second thread (`rennfrei_g`), while the
    second writer would have to hold it too -- impossible. The lock-free
    exclusions travel unused into the race hypothesis, which is exactly their
    job: `SchreibRasse` already says the carrier is not excepted. Every
    premise is used: `hO`/`hex`/`hr`/`hs1`/`hs2` through the two `rennfrei_g`
    applications. -/
theorem rennfrei_g_nah (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hO : GutO O)
    (hex : StartExklusiv init) (M M' M'' : RufMaschineG D) (f g : Faden)
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hs1 : RufSchrittG P O passes M f M') (hs2 : RufSchrittG P O passes M' g M'')
    (c : D.Tab ⊕ D.Glob) : ¬ SchreibRasse M M' M'' f g c := by
  intro hR
  obtain ⟨hne, hw1, hw2, ⟨L, hB⟩, _, _⟩ := hR
  have h1 := rennfrei_g P O passes sp init hO hex M M' f hr hs1 c L hB hw1
  have hr' : RufErreichbarG P O passes (RufStartG P sp init) M' :=
    RufErreichbarG.schritt M M' f hr hs1
  have h2 := rennfrei_g P O passes sp init hO hex M' M'' g hr' hs2 c L hB hw2
  exact h1.2 g (fun e => hne e.symm) h2.1

/-! ## 4. The witness: every premise jointly on the two-thread run -/

/-- The guard of the witness table: `konto` is watched by the one lock. -/
theorem hBz : Bewacht (D := zD) (Sum.inl ()) () :=
  List.mem_singleton.mpr rfl

/-- **`rennfrei_g_zeuge`.** Every premise of `rennfrei_g` holds jointly on
    the non-degenerate program `zP`: the good oracle, the exclusive start,
    a reached machine `M7` (seven steps of thread 1: lock taken, `wrap`
    entered, `lies` called, read, returned, `einzahlen` entered) and the
    writing step `s8` (thread 1's `konto[0] := 100` under its signature
    lock, moving memory `0 -> 100` on the table `konto` that `einzahlen`
    writes) -- plus the concluded holder facts. -/
theorem rennfrei_g_zeuge : ∃ (M M' : RufMaschineG zD) (f : Faden)
    (c : zD.Tab ⊕ zD.Glob) (L : zD.Lock),
    RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M ∧
    RufSchrittG zP zO 0 M f M' ∧ Bewacht c L ∧
    ¬ TraegerGleich M'.speicher M.speicher c ∧
    (M.speicher.slots () 0 ()).n = 0 ∧ (M'.speicher.slots () 0 ()).n = 100 ∧
    L ∈ offen (M.faeden f).spur ∧ ∀ g, g ≠ f → L ∉ offen (M'.faeden g).spur := by
  have h01 := zM0_faden (1 : Faden)
  have hoff0 : offen ((RufStartG zP zSp zInit).faeden 1).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := zP) (O := zO) (passes := 0) h01 zLocks zHauptRet
    .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := zP) (O := zO) (passes := 0) hZ1.1 ()
    _ _ _ _ .nil rfl (hg0 hoff0)
    (fun u hu h => by rw [rufSchrittG_fremd s1 u hu, zM0_faden] at h; exact List.not_mem_nil h)
  have hoff2 : offen (M2.faeden 1).spur = [()] := by
    rw [hZ2.spur]
    show offen (Ereignis.nimmt () (offen (M1.weltVon 1).spur) :: (M1.weltVon 1).spur) = [()]
    simp only [offen]
    rw [offen_weltVon, hZ1.spur]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_rufDann (P := zP) (O := zO) (passes := 0) hZ2.1 zWrap .nil zHpWrap
    rfl _ _ .nil rfl
    (hgL (hoff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 1).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hZ3.1 zLies .nil zHpLies
    rfl (.cons (.call zEin .nil zHpEin rfl) (.ret .keine (by rfl))) .nil rfl
    (hgL (hoff_z hZ3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 1).spur = [()] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff3
  obtain ⟨M5, s5, hZ5⟩ := w_endeBind (P := zP) (O := zO) (passes := 0) hZ4.1
    (.slot () () zIdx zDarf) (.ret (.wert (.var .hier)) (by rfl)) .nil rfl
    (hgL (hoff_z hZ4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden 1).spur = [()] := by
    rw [hZ5.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hZ5.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_z hZ5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden 1).spur = [()] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hG6.1 zEin .nil zHpEin rfl
    (.ret .keine (by rfl)) .nil rfl
    (hgL (hoff_g hG6 hoff6)).heldIn
  have hoff7 : offen (M7.faeden 1).spur = [()] := by
    rw [hZ7.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff6
  obtain ⟨M8, s8, hZ8⟩ := w_blatt (P := zP) (O := zO) (passes := 0) hZ7.1
    _ _ _ rfl rfl
    (hgL (hoff_z hZ7 hoff7)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hr7 : RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M7 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6) s7
  have e1 : M1.speicher = (RufStartG zP zSp zInit).speicher := by rw [hZ1.2]; rfl
  have e2 : M2.speicher = M1.speicher := by rw [hZ2.2]; rfl
  have e3 : M3.speicher = M2.speicher := by rw [hZ3.2]; rfl
  have e4 : M4.speicher = M3.speicher := by rw [hZ4.2]; rfl
  have e5 : M5.speicher = M4.speicher := by rw [hZ5.2]; rfl
  have e6 : M6.speicher = M5.speicher := by rw [hG6.2]; rfl
  have e7 : M7.speicher = M6.speicher := by rw [hZ7.2]; rfl
  have e7s : M7.speicher = (RufStartG zP zSp zInit).speicher := by
    rw [e7, e6, e5, e4, e3, e2, e1]
  have e0 : (M7.speicher.slots () 0 ()).n = 0 := by
    rw [e7s]
    rfl
  have e8 : (M8.speicher.slots () 0 ()).n = 100 := by
    rw [hZ8.2]
    rfl
  have hwr : ¬ TraegerGleich M8.speicher M7.speicher (Sum.inl ()) := by
    intro hC
    have hC' : M8.speicher.slots () = M7.speicher.slots () := hC
    have h01' := congrFun (congrFun hC' 0) ()
    have hn := congrArg Zahl.n h01'
    rw [e8, e0] at hn
    exact absurd hn (by decide)
  have hconc := rennfrei_g zP zO 0 zSp zInit zO_gut zInit_exklusiv M7 M8 1 hr7 s8
    (Sum.inl ()) () hBz hwr
  exact ⟨M7, M8, 1, Sum.inl (), (), hr7, s8, hBz, hwr, e0, e8, hconc.1, hconc.2⟩

/-! ## CUTS:

  What is proved: the access set of one step from the thread-trace delta
  (`zugriffe`, `zugriffVon`; actor attribution `zugriffe_anders`); the
  adjacent double-write race on a guarded carrier (`SchreibRasse`, with the
  atomic/published lock-free disciplines excluded by their declared
  discipline `D.atomar`/`D.nutzlast`); race freedom in holder form
  (`rennfrei_g`: a step changing a guarded carrier holds every guard before,
  and excludes every other thread after) and in adjacent form
  (`rennfrei_g_nah`: no `SchreibRasse` on reachable adjacent steps); the
  joint witness `rennfrei_g_zeuge` on the two-thread run of `zP`.

  What the theorem says about each carrier class (task item 4): guarded
  carriers (some `L` with `Bewacht c L`) are covered by `rennfrei_g` /
  `rennfrei_g_nah`. Atomic globals (`AtomarAusgenommen`) and published
  payloads (`PaarungAusgenommen`) are allowed races by design and excluded
  from `SchreibRasse` explicitly. Unshared carriers (`D.geteilt = false`,
  one thread's own state) are NOT covered here: their separation is the
  checker text-check duty (`PCUnsharedSep`, SATZKARTE D2) and the `W5`
  leg of `Gesittet`, not a lock argument.

  What is NOT proved: the actor-side characterization of `zugriffe` per
  rule (only `zugriffe_anders` -- other threads record nothing); a
  read/write formulation over `zugriffe` membership (the claims use the
  memory footprint `TraegerGleich`, which `schritt_traeger` decides);
  non-adjacent races with an explicit release event between the steps.
-/

#print axioms Gabbro.Grammatik.rennfrei_g
#print axioms Gabbro.Grammatik.rennfrei_g_nah
#print axioms Gabbro.Grammatik.rennfrei_g_zeuge

end Gabbro.Grammatik
