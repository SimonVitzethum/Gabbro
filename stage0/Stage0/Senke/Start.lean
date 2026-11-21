/-
  File:      stage0/Stage0/Senke/Start.lean
  Subject:   A thread's start (`start_ok`): from its start code (`startC`) in a frame of its own, the thread runs its
             root as G's `rufAt n` and ends with the system call `e` (`exit_group` with `main`'s result, `exit` for a
             root), or with the stop of G's outcome. The thread's parameter words are already in its frame (the
             image's bytes); the start's scratch lies above them (`startScratch`), so they survive the spawns and
             reach the call as `EnvAt`.
-/
module
public import Stage0.Senke.Images.BildLese
public import Stage0.Senke.Welt.StartEnv
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- The system call `nr` with the word of slot `r`. -/
theorem exitw_ok {m : Runner.Mem} {pc fp : Runner.W} {K nr s r : Nat} {w : Runner.W}
    (hc : CodeAt m pc [ci 1 s nr 0, ci 2 ((s + 1 : Nat) : Int) r 0, ci 23 ((s + 7 : Nat) : Int) s 0])
    (hf : CodeFar pc 3 fp K) (hF : FrameOK m fp K) (hs : s + 8 ≤ K) (hr : r < s) (hK : K < 2 ^ 31)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 r)) = some w) (hnr : nr < 2 ^ 31) :
    ∃ t' m' q, Star ⟨pc, fp⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = BitVec.ofNat 64 nr ∧ q.a1 = w := by
  have hroom := hF.room
  have s1 := const_step (k := (nr : Int)) (codeAt_left (a := [ci 1 s nr 0]) hc) hF (by omega) hK
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 (nr : Int)).toNat
  have a1 : Agree fp 0 K m m1 := agree_write hroom (Nat.zero_le _) (by omega) _
  have hc1 : CodeAt m1 (pc + 16) [ci 2 ((s + 1 : Nat) : Int) r 0, ci 23 ((s + 7 : Nat) : Int) s 0] := by
    have := (codeAt_right (a := [ci 1 s nr 0]) hc).agree a1 (codeFar_right (n := 1) (k := 2) hf)
    simpa using this
  have hF1 := hF.agree a1
  have hw1 : m1.rd64 (slot fp (BitVec.ofNat 64 r)) = some w := by
    simp only [m1]; rw [rd_other hroom (by omega) (by omega) (by omega)]; exact hw
  have s2 := mov_to (codeAt_left (a := [ci 2 ((s + 1 : Nat) : Int) r 0]) hc1) hF1 (j := s + 1) (s := r) (by omega)
    (by omega) hK hw1
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (s + 1))) 8 w.toNat
  have a2 : Agree fp 0 K m1 m2 := agree_write hroom (Nat.zero_le _) (by omega) _
  have hc2 : CodeAt m2 (pc + 16 + 16) [ci 23 ((s + 7 : Nat) : Int) s 0] := by
    have := (codeAt_right (a := [ci 2 ((s + 1 : Nat) : Int) r 0]) hc1).agree a2 (by
      have := codeFar_right (n := 2) (k := 1) hf
      simp only [List.length_singleton, Nat.mul_one]
      rw [BitVec.add_assoc, show (16 : Runner.W) + BitVec.ofNat 64 16 = BitVec.ofNat 64 (16 * 2) by decide]
      exact this)
    simpa using this
  have hF2 := hF1.agree a2
  have hi := hc2 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have hsx : sx (II.f (s : Int)) = BitVec.ofNat 64 s := sx_nat (by omega)
  have r0 : m2.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofInt 64 (nr : Int)) := by
    simp only [m2]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
    exact rd64_wr64 (wr64_some (hF.wr s (by omega))) (hF.rd s (by omega))
  have r1 : m2.rd64 (slot fp (BitVec.ofNat 64 (s + 1))) = some w :=
    rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))
  have rd : ∀ i, i < 7 → ∃ v, m2.rd64 (slot fp (BitVec.ofNat 64 (s + i))) = some v := fun i hi =>
    ⟨_, by simp only [Runner.Mem.rd64, hF2.rd (s + i) (by omega), ↓reduceIte]; rfl⟩
  obtain ⟨v2, r2⟩ := rd 2 (by decide)
  obtain ⟨v3, r3⟩ := rd 3 (by decide)
  obtain ⟨v4, r4⟩ := rd 4 (by decide)
  obtain ⟨v5, r5⟩ := rd 5 (by decide)
  obtain ⟨v6, r6⟩ := rd 6 (by decide)
  refine ⟨_, m2, ⟨BitVec.ofInt 64 (nr : Int), w, v2, v3, v4, v5, v6⟩, s1.trans s2,
    runTo_sys (t := ⟨pc + 16 + 16, fp⟩) hi (by rw [hsx]; exact r0) ?_ ?_ ?_ ?_ ?_ ?_, by rw [BitVec.ofInt_natCast], rfl⟩
  · rw [hsx, show (8 : Runner.W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus]; exact r1
  · rw [hsx, show (16 : Runner.W) = BitVec.ofNat 64 (8 * 2) by rfl, slot_plus]; exact r2
  · rw [hsx, show (24 : Runner.W) = BitVec.ofNat 64 (8 * 3) by rfl, slot_plus]; exact r3
  · rw [hsx, show (32 : Runner.W) = BitVec.ofNat 64 (8 * 4) by rfl, slot_plus]; exact r4
  · rw [hsx, show (40 : Runner.W) = BitVec.ofNat 64 (8 * 5) by rfl, slot_plus]; exact r5
  · rw [hsx, show (48 : Runner.W) = BitVec.ofNat 64 (8 * 6) by rfl, slot_plus]; exact r6

/-- The scratch of a start lies above the callee header, the complete parameter span, one result word and the status
    word: neither the spawns nor the exit code write a parameter word. -/
theorem startScratch_ge (f : D.Fn) : FB + FB + contextWords (D.params f) + 1 ≤ startScratch f := by
  have positive : 1 ≤ returnWords (D.erg f) (D.gruende f) :=
    Nat.le_trans (resultWords_pos _) (resultWords_le_returnWords _ _)
  rw [startScratch_eq]
  omega

theorem exitErg_none' {e : Option Ty} (h : e = none) (v : ErgVal D e) (w : Runner.W) : ExitErg Y e v w := by
  subst h; trivial

/-- A returned result is read at its first canonical word, which is the exit status. -/
theorem resultAt_exit {m : Runner.Mem} {fp : Runner.W} {base : Nat} :
    (e : Option Ty) → (v : ErgVal D e) → ResultAt Y m fp base e v → e.isSome = true →
    ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 base)) = some w ∧ ExitErg Y e v w
  | none, _, _, h => by simp at h
  | some τ, v, r, _ => by
    have r' : ValueAt Y m fp base τ (show Wert D τ from v) := r
    have length : 0 < (encodeWords Y τ (show Wert D τ from v)).length := by
      rw [encodeWords_length]; exact valueWords_pos τ
    have read := r'.2 0 length
    simp only [Nat.add_zero] at read
    refine ⟨(encodeWords Y τ (show Wert D τ from v))[0]'length, read, ?_, fun compatible => ?_⟩
    · have head : ∀ (l : List Runner.W) (h : 0 < l.length), l[0]'h = l.headD 0 := fun l h => by
        cases l with
        | nil => simp at h
        | cons a t => rfl
      exact head _ length
    · obtain ⟨w', read', encoded⟩ := ValueAt.word τ (show Wert D τ from v) compatible r'
      rw [read'] at read
      cases read
      exact encoded

theorem codeFar_nat' {a k f K : Nat} (ha : a + 16 * k ≤ f) (hf : f + 8 * K < 2 ^ 64) :
    CodeFar (BitVec.ofNat 64 a) k (BitVec.ofNat 64 f) K := by
  simp only [CodeFar, BitVec.toNat_ofNat]
  omega

/-- **A thread's start**: from its start code at `pc` in its frame at `fpI` (`Ks` slots, the world above), the thread
    runs `f` as G's `rufAt n f` and ends with the system call `e` -- with `f`'s result when `keep` -- or with the stop
    of G's outcome. -/
theorem start_ok {P : Programm D} {O : Orakel D} {passes : Nat} {Y : Lay D} [hT : TorOK Y O] [hV : SichtOK O] {A : D.Fn → Nat}
    {C : D.Fn → List II} {L Ks n : Nat} {f : D.Fn} {e : Nat} {keep : Bool}
    (hLA : Y.fa = A) (hC : ∀ g, ∃ top, lowFun passes P A Y g = some (C g, top) ∧ top ≤ L) (hAlt : ∀ g, A g < 2 ^ 31)
    (hlen : ∀ g, 16 * (C g).length < 2 ^ 31) (hwhy : D.gruende f = 0)
    (hroomK : FB + 2 * L ≤ Ks) (hexK : startScratch f + 8 ≤ Ks) (hL1 : 1 ≤ L) (hn : n = depthOf Ks L) (he : e < 2 ^ 31)
    {pc fpI : Nat} {m : Runner.Mem} (hfit : fpI + 8 * Ks < 2 ^ 31)
    (hc : CodeAt m (BitVec.ofNat 64 pc) (startC A f n e keep)) (hpc : pc + 16 * startLen ≤ fpI)
    (hF : FrameOK m (BitVec.ofNat 64 fpI) Ks) (hP : PCode m A C (BitVec.ofNat 64 fpI) Ks)
    (hW : WIn Y (BitVec.ofNat 64 fpI) Ks Ks) (σ : World D) (ρ : Env D (D.params f))
    (hval : ∀ τ (x : Var (D.params f) τ), ValueValid Y τ (ρ.get x))
    (hρ : WordsAt m (slot (BitVec.ofNat 64 fpI) (BitVec.ofNat 64 FB)) FB (encodeEnv Y ρ)) (hWa : WeltAt m Y σ)
    (hy : TicketSync m Y (BitVec.ofNat 64 fpI) Ks []) :
    match rufAt P O passes n f σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 pc, BitVec.ofNat 64 fpI⟩ m t' m' ∧ StopAt t' m' q ∧
        q.nr = BitVec.ofNat 64 e ∧ (keep = true → ExitErg Y (D.erg f) v q.a1) ∧
        (D.erg f = none → q.a1 = 0)
    | .logik l => Stops ⟨BitVec.ofNat 64 pc, BitVec.ofNat 64 fpI⟩ m (logikCode l)
    | .hardware h => Stops ⟨BitVec.ofNat 64 pc, BitVec.ofNat 64 fpI⟩ m (hwCode h)
    | _ => False := by
  have hFB3 : FB = 4 := rfl
  have hex := startScratch_ge f
  have hsl : startLen = 8 := rfl
  have hK : Ks < 2 ^ 31 := by omega
  have hroom := hF.room
  -- the depth
  have hq : 2 ≤ (Ks - FB) / L := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hn1 : n + 1 = (Ks - FB) / L := by rw [hn, depthOf]; omega
  have hdm := Nat.div_mul_le_self (Ks - FB) L
  have hnK : n + 1 ≤ Ks := by have := Nat.div_le_self (Ks - FB) L; omega
  have hS := lowFun_spec (Y := Y) (P := P) (O := O) (passes := passes) hLA hC hAlt hlen n (by omega)
  have hS0' : CodeAt m (BitVec.ofNat 64 pc) ([ci 1 2 ((n + 1 : Nat) : Int) 0] ++ (callTail A f FB ++
      [ci 1 (startScratch f) e 0,
       if keep && (D.erg f).isSome then ci 2 ((startScratch f + 1 : Nat) : Int) ((FB + 2 : Nat) : Int) 0
       else ci 1 ((startScratch f + 1 : Nat) : Int) 0 0,
       ci 23 ((startScratch f + 7 : Nat) : Int) (startScratch f) 0])) := by
    simpa [startC, List.append_assoc] using hc
  have s1 := const_step (j := 2) (k := ((n + 1 : Nat) : Int)) (codeAt_left hS0') hF (by omega) hK
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot (BitVec.ofNat 64 fpI) (BitVec.ofNat 64 2)) 8 (BitVec.ofInt 64 ((n + 1 : Nat) : Int)).toNat
  have a1 : Agree (BitVec.ofNat 64 fpI) 2 Ks m m1 := agree_write hroom (Nat.le_refl _) (by omega) _
  have hF1 := hF.agree a1
  have hfp0 : (BitVec.ofNat 64 fpI).toNat = fpI := by simp only [BitVec.toNat_ofNat]; omega
  have hWa1 : WeltAt m1 Y σ := weltAt_stab hW.lay hW.top m m1 hWa (a1.mono (Nat.zero_le _))
  have hfC : CodeFar (BitVec.ofNat 64 pc + BitVec.ofNat 64 (16 * [ci 1 2 ((n + 1 : Nat) : Int) 0].length))
      (callTail A f FB ++ [ci 1 (startScratch f) e 0,
       if keep && (D.erg f).isSome then ci 2 ((startScratch f + 1 : Nat) : Int) ((FB + 2 : Nat) : Int) 0
       else ci 1 ((startScratch f + 1 : Nat) : Int) 0 0,
       ci 23 ((startScratch f + 7 : Nat) : Int) (startScratch f) 0]).length (BitVec.ofNat 64 fpI) Ks := by
    rw [ofNat_add64]; exact codeFar_nat' (by simp [callTail, callTailN]; omega) (by omega)
  have hc1 := (codeAt_right hS0').agree a1 hfC
  have hdv : m1.rd64 (slot (BitVec.ofNat 64 fpI) (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 n + 1) := by
    have hconv : BitVec.ofInt 64 ((n + 1 : Nat) : Int) = BitVec.ofNat 64 n + 1 := by
      rw [BitVec.ofInt_natCast]; exact ofNat_succ n
    simp only [m1]
    rw [rd_same hF (by omega), hconv]
  have hρ1 : WordsAt m1 (slot (BitVec.ofNat 64 fpI) (BitVec.ofNat 64 FB)) (FB + 0) (encodeEnv Y ρ) :=
    startEnvWords_depth (frameOffset := FB) (reserved := 0) (words := encodeEnv Y ρ)
      (BitVec.ofInt 64 ((n + 1 : Nat) : Int)).toNat hF (by rw [encodeEnv_length]; omega) (by omega) hρ
  have hE : EnvAt Y m1 (slot (BitVec.ofNat 64 fpI) (BitVec.ofNat 64 FB)) ρ :=
    (envAt_encoding (reserved := 0) ρ).mpr ⟨hval, hρ1⟩
  have hcall := call_ok (σ := σ) hS (codeAt_left hc1) (codeFar_left (k := 3) (by
      have h4 : (callTail A f FB).length = 4 := rfl; simpa [h4] using hfC)) hF1 hK (Nat.le_refl _)
    (by omega) (by rw [hn1]; omega) (hAlt f) (pcode_agree hP a1) hdv hE hW hWa1
    (hy.agree a1 (by have := hW.top; have := hW.ord; omega)) HeldIn.nil
  generalize rufAt P O passes n f σ ρ = o at hcall ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m2, s2, a2, ⟨hres, hmirror, _⟩, _⟩ := hcall
    have hfE := codeFar_tail (a := callTail A f FB) hfC
    have hexC := codeAt_agreeWIn hW (a2.mono (Nat.zero_le _)) (codeAt_right (a := callTail A f FB) hc1) hfE
    have hF2 := frameOK_agreeW hF1 a2
    by_cases hs : (keep && (D.erg f).isSome) = true
    · simp only [hs, ite_true] at hexC hfE
      obtain ⟨w, hread, hexit⟩ := resultAt_exit (D.erg f) v hres (by simp only [Bool.and_eq_true] at hs; exact hs.2)
      have hw : m2.rd64 (slot (BitVec.ofNat 64 fpI) (BitVec.ofNat 64 (FB + 2))) = some w := by
        have mirrored := hmirror.trans hread
        rwa [slot_slot] at mirrored
      obtain ⟨t', m', q, sx, hq, hnr, ha⟩ := exitw_ok hexC hfE hF2 (by omega) (by omega) hK hw he
      refine ⟨t', m', q, s1.trans (s2.trans sx), hq, hnr, (fun _ => ha.symm ▸ hexit), ?_⟩
      intro void
      simp only [void, Option.isSome_none, Bool.and_false, Bool.false_eq_true] at hs
    · simp only [hs, Bool.false_eq_true, ite_false] at hexC hfE
      obtain ⟨t', m', q, sx, hq, hnr, zero⟩ := sys_ok (nr := e) (c := 0) (s := startScratch f) hexC hfE hF2 (by omega) hK
        (by decide) he
      refine ⟨t', m', q, s1.trans (s2.trans sx), hq, hnr, (fun hk => ?_), fun _ => zero⟩
      simp only [hk, Bool.true_and, Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at hs
      exact exitErg_none' hs v _
  | logik l => exact Stops.prefix s1 hcall
  | why _ r => exact (keinGrund hwhy r : False).elim
  | hardware h => exact Stops.prefix s1 hcall

/-! ## `main` starts the roots -/

/-- **The named environment assumption at `clone`**: the kernel answers the call that asks for
    a new thread (`cloneReq`: the fixed thread flags, no tid pointers, no new stack, so the memory stays as it is)
    with a word `r` that is not 0 and leaves the memory as it is. 0 is the answer of the new thread, which only the
    machine gives (`Runner.Mach`); every other word reaches the asking thread. `r` is a thread id (the kernel created
    the thread) or an error number (it refused): which of the two is NOT assumed. The emitted startup code checks the
    answer and stops with `cloneCode` on a refusal (`spawn1_ok`), so a refused thread creation is a declared stop of
    the image, never a silently missing thread. What remains assumed is only that the kernel relation answers this
    one call at all, in the shape the machine interprets (`Runner.Mach.Tr.clone`, `.cloneNo`). -/
class CloneAnswers : Prop where
  ans : ∀ m : Runner.Mem, ∃ r x : Runner.W, r ≠ 0 ∧ Kern.ans Runner.cloneReq m (some (r, x)) m

/-- One root's spawn site: both constants, the `spawn`, the check of the answer. -/
def spawnOne (s a f : Nat) : List II :=
  [ci 1 s a 0, ci 1 ((s + 1 : Nat) : Int) f 0, ci 24 ((s + 2 : Nat) : Int) s 0,
    ci 1 ((s + 3 : Nat) : Int) 0 0, ci 13 ((s + 4 : Nat) : Int) ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int)] ++
    guardC (s + 4) cloneCode s

theorem spawnOne_len (s a f : Nat) : (spawnOne s a f).length = 10 := by
  simp only [spawnOne, guardC, stopC, sysC, List.length_append, List.length_cons, List.length_nil]

theorem spawnC_cons (s a f : Nat) (r : List (Nat × Nat)) :
    spawnC s ((a, f) :: r) = spawnOne s a f ++ spawnC s r := rfl

/-- The word the check computes from the answer: `0 <s answer`, as 1 or 0. -/
def spawnFlag (r : Runner.W) : Runner.W := bool ((BitVec.ofInt 64 (0 : Int)).slt r)

theorem ofInt_zero_toInt : (BitVec.ofInt 64 (0 : Int)).toInt = 0 :=
  BitVec.toInt_ofInt_eq_self (by decide) (by decide) (by decide)

theorem spawnFlag_pos {r : Runner.W} (h : 0 < r.toInt) : spawnFlag r = 1 := by
  have hs : (BitVec.ofInt 64 (0 : Int)).slt r = true := by
    rw [BitVec.slt_eq_decide, ofInt_zero_toInt]; exact decide_eq_true h
  unfold spawnFlag Runner.IR.bool
  rw [hs]; rfl

theorem spawnFlag_nonpos {r : Runner.W} (h : r.toInt ≤ 0) : spawnFlag r = 0 := by
  have h' : ¬ (0 < r.toInt) := by omega
  have hs : (BitVec.ofInt 64 (0 : Int)).slt r = false := by
    rw [BitVec.slt_eq_decide, ofInt_zero_toInt]; exact decide_eq_false h'
  unfold spawnFlag Runner.IR.bool
  rw [hs]; rfl

/-- A position `a` instructions behind `pc`, then `b` more. -/
theorem pcN (pc : Runner.W) (a b c : Nat) (h : a + b = c) :
    pc + BitVec.ofNat 64 (16 * a) + BitVec.ofNat 64 (16 * b) = pc + BitVec.ofNat 64 (16 * c) := by
  subst h; exact pc_add pc a b

theorem const_step16 {m : Runner.Mem} {pc fp : Runner.W} {K j : Nat} {k : Int}
    (hc : CodeAt m pc [ci 1 j k 0]) (hF : FrameOK m fp K) (hj : j < K) (hK : K < 2 ^ 31) (hk : lit32 k = true) :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩
      (write m (slot fp (BitVec.ofNat 64 j)) 8 (BitVec.ofInt 64 k).toNat) :=
  star_cast (const_step hc hF hj hK hk) rfl rfl

/-- The first three instructions of a spawn site: the start code's address and the frame's address into the scratch
    slots `s`, `s + 1`, and the `spawn`. Whatever the kernel answers (a word that is not 0, memory untouched), the
    asking thread goes on after the `spawn` with the answer in slot `s + 2`; every slot below `s` is unchanged. -/
theorem spawn3_ok {m : Runner.Mem} {pc fp : Runner.W} {K s a f : Nat}
    (hc : CodeAt m pc [ci 1 s a 0, ci 1 ((s + 1 : Nat) : Int) f 0, ci 24 ((s + 2 : Nat) : Int) s 0])
    (hF : FrameOK m fp K) (hK : s + 3 ≤ K) (hK2 : K < 2 ^ 31) (ha : a < 2 ^ 31) (hf : f < 2 ^ 31)
    (hcf : CodeFar pc 3 fp K) :
    ∃ m2, Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m2 ∧ Agree fp s K m m2 ∧
      ∀ r x : Runner.W, r ≠ 0 → Kern.ans Runner.cloneReq m2 (some (r, x)) m2 →
        Star ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m2 ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩
          (write m2 (slot fp (BitVec.ofNat 64 (s + 2))) 8 r.toNat) := by
  have hroom := hF.room
  have hc' : CodeAt m pc ([ci 1 s a 0] ++ ([ci 1 ((s + 1 : Nat) : Int) f 0] ++
      [ci 24 ((s + 2 : Nat) : Int) s 0])) := hc
  have s1 := const_step16 (k := (a : Int)) (codeAt_left hc') hF (by omega) hK2
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 (a : Int)).toNat
  have a1 : Agree fp s K m m1 := agree_write hroom (Nat.le_refl _) (by omega) _
  have hF1 := hF.agree a1
  have hc1 : CodeAt m1 (pc + BitVec.ofNat 64 (16 * 1)) ([ci 1 ((s + 1 : Nat) : Int) f 0] ++
      [ci 24 ((s + 2 : Nat) : Int) s 0]) :=
    (codeAt_right (a := [ci 1 s a 0]) hc').agree a1 (codeFar_right (n := 1) (k := 2) hcf)
  have s2 := const_step16 (j := s + 1) (k := (f : Int)) (codeAt_left hc1) hF1 (by omega) hK2
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (s + 1))) 8 (BitVec.ofInt 64 (f : Int)).toNat
  have a2 : Agree fp s K m1 m2 := agree_write hroom (by omega) (by omega) _
  have hF2 := hF1.agree a2
  have hc2 : CodeAt m2 (pc + BitVec.ofNat 64 (16 * 2)) [ci 24 ((s + 2 : Nat) : Int) s 0] :=
    (codeAt_right (a := [ci 1 s a 0, ci 1 ((s + 1 : Nat) : Int) f 0])
      (b := [ci 24 ((s + 2 : Nat) : Int) s 0]) hc).agree (a1.trans a2) (codeFar_right (n := 2) (k := 1) hcf)
  refine ⟨m2, star_cast (s1.trans s2) rfl (by simp only [T.mk.injEq, and_true]; exact pcN pc 1 1 2 rfl),
    a1.trans a2, ?_⟩
  intro r x hr0 hk
  have hi := hc2 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have h0 : m2.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofInt 64 (a : Int)) := by
    simp only [m2]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
    exact rd64_wr64 (wr64_some (hF.wr _ (by omega))) (hF.rd _ (by omega))
  have h1 : m2.rd64 (slot fp (BitVec.ofNat 64 s) + 8) = some (BitVec.ofInt 64 (f : Int)) := by
    rw [show (8 : Runner.W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus]
    exact rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))
  have s3 : Star ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m2 ⟨pc + BitVec.ofNat 64 (16 * 2) + 16, fp⟩
      (write m2 (slot fp (BitVec.ofNat 64 (s + 2))) 8 r.toNat) := by
    refine Star.one (run_step (t := ⟨_, fp⟩) hi (by decide) ?_)
    simp only [op]
    refine f2_run (t := ⟨_, fp⟩) hi ?_
    rw [sx_nat (by omega)]
    simp only [ld]
    refine run_rd64 h0 (run_rd64 h1 ?_)
    refine Run.sys (a := some (r, x)) (m' := m2) hk ?_
    simp only [Runner.opt, hr0, ↓reduceIte, ret1]
    refine f1_run (t := ⟨_, fp⟩) hi ?_
    rw [sx_nat (by omega)]
    exact run_wr64 (wr64_some (hF2.wr _ (by omega)))
  exact star_cast s3 rfl (by simp only [T.mk.injEq, and_true]; exact pcN pc 2 1 3 rfl)

/-- The check of a spawn's answer `r` (in slot `s + 2`): slot `s + 4` becomes `0 <s r`; the guard stops with
    `cloneCode` when it is zero (a refusal: `r` is not positive) and goes on otherwise (`r` is a thread id). -/
theorem spawnCheck_ok {m : Runner.Mem} {pc fp : Runner.W} {K s : Nat} {r : Runner.W}
    (hc : CodeAt m pc ([ci 1 ((s + 3 : Nat) : Int) 0 0] ++ ([ci 13 ((s + 4 : Nat) : Int) ((s + 3 : Nat) : Int)
      ((s + 2 : Nat) : Int)] ++ guardC (s + 4) cloneCode s)))
    (hF : FrameOK m fp K) (hK : s + 8 ≤ K) (hK2 : K < 2 ^ 31) (hcf : CodeFar pc 7 fp K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 (s + 2))) = some r) :
    (0 < r.toInt → ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 7), fp⟩ m' ∧ Agree fp (s + 3) K m m') ∧
    (r.toInt ≤ 0 → Stops ⟨pc, fp⟩ m cloneCode) := by
  have hroom := hF.room
  have s1 := const_step16 (j := s + 3) (k := (0 : Int)) (codeAt_left hc) hF (by omega) hK2
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot fp (BitVec.ofNat 64 (s + 3))) 8 (BitVec.ofInt 64 (0 : Int)).toNat
  have a1 : Agree fp (s + 3) K m m1 := agree_write hroom (Nat.le_refl _) (by omega) _
  have hF1 := hF.agree a1
  have hc1 : CodeAt m1 (pc + BitVec.ofNat 64 (16 * 1)) ([ci 13 ((s + 4 : Nat) : Int) ((s + 3 : Nat) : Int)
      ((s + 2 : Nat) : Int)] ++ guardC (s + 4) cloneCode s) :=
    (codeAt_right (a := [ci 1 ((s + 3 : Nat) : Int) 0 0]) hc).agree a1 (codeFar_right (n := 1) (k := 6) hcf)
  have hra : m1.rd64 (slot fp (BitVec.ofNat 64 (s + 3))) = some (BitVec.ofInt 64 (0 : Int)) :=
    rd64_wr64 (wr64_some (hF.wr _ (by omega))) (hF.rd _ (by omega))
  have hrb : m1.rd64 (slot fp (BitVec.ofNat 64 (s + 2))) = some r := by
    simp only [m1]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
    exact hr
  have s2 := bin_star (o := 13) (d := s + 4) (a := s + 3) (b := s + 2)
    (g := fun a b => some (bool (a.slt b))) (K := K) (va := BitVec.ofInt 64 (0 : Int)) (vb := r)
    (r := spawnFlag r)
    (codeAt_left (a := [ci 13 ((s + 4 : Nat) : Int) ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int)]) hc1)
    rfl (by decide) hF1 (by omega) (by omega) (by omega) hK2 hra hrb rfl
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (s + 4))) 8 (spawnFlag r).toNat
  have a2 : Agree fp (s + 3) K m1 m2 := agree_write hroom (by omega) (by omega) _
  have hF2 := hF1.agree a2
  have hglen : (guardC (s + 4) cloneCode s).length = 5 := by
    simp only [guardC, stopC, sysC, List.length_append, List.length_cons, List.length_nil]
  have hc2 : CodeAt m2 (pc + BitVec.ofNat 64 (16 * 1) + BitVec.ofNat 64 (16 * 1)) (guardC (s + 4) cloneCode s) :=
    (codeAt_right (a := [ci 13 ((s + 4 : Nat) : Int) ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int)]) hc1).agree a2
      (by
        have := codeFar_right (n := 1) (k := 5) (codeFar_right (n := 1) (k := 6) hcf)
        rwa [BitVec.add_assoc, ← BitVec.ofNat_add] at this ⊢)
  have hs12 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 1) + BitVec.ofNat 64 (16 * 1), fp⟩ m2 :=
    s1.trans s2
  have hread : m2.rd64 (slot fp (BitVec.ofNat 64 (s + 4))) = some (spawnFlag r) :=
    rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))
  have hcf5 : CodeFar (pc + BitVec.ofNat 64 (16 * 1) + BitVec.ofNat 64 (16 * 1)) 5 fp K := by
    have := codeFar_right (n := 1) (k := 5) (codeFar_right (n := 1) (k := 6) hcf)
    exact this
  refine ⟨fun hpos => ?_, fun hneg => ?_⟩
  · have hne : spawnFlag r ≠ 0 := by rw [spawnFlag_pos hpos]; decide
    have pass := guard_pass (fp := fp) hc2 (by omega) hread hne
    refine ⟨m2, star_cast (hs12.trans pass) rfl ?_, a1.trans a2⟩
    simp only [T.mk.injEq, and_true, hglen]
    rw [pcN pc 1 1 2 rfl]
    exact pcN pc 2 5 7 rfl
  · have h0 : spawnFlag r = 0 := spawnFlag_nonpos hneg
    rw [h0] at hread
    exact Stops.prefix hs12 (guard_stop hc2 hcf5 hF2 (by omega) (by omega) hK2 (by decide) hread)

/-- **One spawn site, for every answer the kernel may give** (a word that is not 0, memory untouched): a positive
    answer (a thread id) lets the asking thread run through the site; a negative one (a refusal) stops the process
    with `cloneCode`. The first component is the state before the kernel is asked. -/
theorem spawn1_cases {m : Runner.Mem} {pc fp : Runner.W} {K s a f : Nat}
    (hc : CodeAt m pc (spawnOne s a f)) (hF : FrameOK m fp K) (hK : s + 8 ≤ K) (hK2 : K < 2 ^ 31)
    (ha : a < 2 ^ 31) (hf : f < 2 ^ 31) (hcf : CodeFar pc 10 fp K) :
    ∃ m2, Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m2 ∧ Agree fp s K m m2 ∧
      ∀ r x : Runner.W, r ≠ 0 → Kern.ans Runner.cloneReq m2 (some (r, x)) m2 →
        (0 < r.toInt → ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 10), fp⟩ m' ∧ Agree fp s K m m') ∧
        (r.toInt ≤ 0 → Stops ⟨pc, fp⟩ m cloneCode) := by
  have hroom := hF.room
  have hc' : CodeAt m pc ([ci 1 s a 0, ci 1 ((s + 1 : Nat) : Int) f 0, ci 24 ((s + 2 : Nat) : Int) s 0] ++
      ([ci 1 ((s + 3 : Nat) : Int) 0 0] ++ ([ci 13 ((s + 4 : Nat) : Int) ((s + 3 : Nat) : Int)
        ((s + 2 : Nat) : Int)] ++ guardC (s + 4) cloneCode s))) := hc
  obtain ⟨m2, s12, a12, hs3⟩ := spawn3_ok (codeAt_left hc') hF (by omega) hK2 ha hf
    (codeFar_left (k := 7) hcf)
  refine ⟨m2, s12, a12, fun r x hr0 hk => ?_⟩
  have s3 := hs3 r x hr0 hk
  let m3 := write m2 (slot fp (BitVec.ofNat 64 (s + 2))) 8 r.toNat
  have a3 : Agree fp s K m2 m3 := agree_write hroom (by omega) (by omega) _
  have hF2 := hF.agree a12
  have hF3 := hF2.agree a3
  have hc3 : CodeAt m3 (pc + BitVec.ofNat 64 (16 * 3)) ([ci 1 ((s + 3 : Nat) : Int) 0 0] ++
      ([ci 13 ((s + 4 : Nat) : Int) ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int)] ++ guardC (s + 4) cloneCode s)) :=
    (codeAt_right (a := [ci 1 s a 0, ci 1 ((s + 1 : Nat) : Int) f 0, ci 24 ((s + 2 : Nat) : Int) s 0]) hc').agree
      (a12.trans a3) (codeFar_right (n := 3) (k := 7) hcf)
  have hr3 : m3.rd64 (slot fp (BitVec.ofNat 64 (s + 2))) = some r :=
    rd64_wr64 (wr64_some (hF2.wr _ (by omega))) (hF2.rd _ (by omega))
  obtain ⟨pos, neg⟩ := spawnCheck_ok (s := s) hc3 hF3 hK hK2 (codeFar_right (n := 3) (k := 7) hcf) hr3
  have s123 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩ m3 := s12.trans s3
  refine ⟨fun hp => ?_, fun hn => ?_⟩
  · obtain ⟨m', s4, a4⟩ := pos hp
    exact ⟨m', star_cast (s123.trans s4) rfl (by simp only [T.mk.injEq, and_true]; exact pcN pc 3 7 10 rfl),
      a12.trans (a3.trans (a4.mono (Nat.le_add_right s 3)))⟩
  · exact Stops.prefix s123 (neg hn)

/-- **One spawn site**: under the kernel's answer (`CloneAnswers`) the asking thread runs through the site, or the
    process stops with the declared `cloneCode` -- a refused clone is never a silent absence of the thread. -/
theorem spawn1_ok [CloneAnswers] {m : Runner.Mem} {pc fp : Runner.W} {K s a f : Nat}
    (hc : CodeAt m pc (spawnOne s a f)) (hF : FrameOK m fp K) (hK : s + 8 ≤ K) (hK2 : K < 2 ^ 31)
    (ha : a < 2 ^ 31) (hf : f < 2 ^ 31) (hcf : CodeFar pc 10 fp K) :
    (∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 10), fp⟩ m' ∧ Agree fp s K m m') ∨
      Stops ⟨pc, fp⟩ m cloneCode := by
  obtain ⟨m2, _, _, hcases⟩ := spawn1_cases hc hF hK hK2 ha hf hcf
  obtain ⟨r, x, hr0, hk⟩ := CloneAnswers.ans m2
  obtain ⟨pos, neg⟩ := hcases r x hr0 hk
  rcases Int.lt_or_le 0 r.toInt with h | h
  · exact Or.inl (pos h)
  · exact Or.inr (neg h)

/-- The spawns of all roots: every site is run through, or the process stops with `cloneCode`. -/
theorem spawnC_ok [CloneAnswers] {fp : Runner.W} {K s : Nat} (hK : s + 8 ≤ K) (hK2 : K < 2 ^ 31) :
    (l : List (Nat × Nat)) → (∀ x ∈ l, x.1 < 2 ^ 31 ∧ x.2 < 2 ^ 31) → (m : Runner.Mem) → (pc : Runner.W) →
    CodeAt m pc (spawnC s l) → FrameOK m fp K → CodeFar pc (spawnC s l).length fp K →
    (∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (spawnC s l).length), fp⟩ m' ∧ Agree fp s K m m') ∨
      Stops ⟨pc, fp⟩ m cloneCode
  | [], _, m, pc, _, _, _ => Or.inl ⟨m, by simpa [spawnC] using Star.refl _ m, Agree.refl _ _ _ _⟩
  | (a, f) :: r, hl, m, pc, hc, hF, hcf => by
    have h0 := hl (a, f) (by simp)
    have hc' : CodeAt m pc (spawnOne s a f ++ spawnC s r) := hc
    have hcf' : CodeFar pc ((spawnOne s a f).length + (spawnC s r).length) fp K := by
      have h := hcf
      rw [spawnC_cons, List.length_append] at h
      exact h
    rw [spawnOne_len] at hcf'
    rcases spawn1_ok (codeAt_left hc') hF hK hK2 h0.1 h0.2 (codeFar_left hcf') with ⟨m1, s1, a1⟩ | hstop
    · have hc1 : CodeAt m1 (pc + BitVec.ofNat 64 (16 * 10)) (spawnC s r) := by
        have := (codeAt_right hc').agree a1 (codeFar_right (n := 10) (k := (spawnC s r).length) hcf')
        rwa [spawnOne_len] at this
      rcases spawnC_ok hK hK2 r (fun x hx => hl x (by simp [hx])) m1 _ hc1 (hF.agree a1)
        (codeFar_right hcf') with ⟨m2, s2, a2⟩ | hstop
      · refine Or.inl ⟨m2, s1.trans (star_cast s2 rfl ?_), a1.trans a2⟩
        simp only [T.mk.injEq, and_true, spawnC_cons, List.length_append, spawnOne_len, addr_norm]
        congr 2
        omega
      · exact Or.inr (Stops.prefix s1 hstop)
    · exact Or.inr hstop

end Gabbro.Stage0.Senke
