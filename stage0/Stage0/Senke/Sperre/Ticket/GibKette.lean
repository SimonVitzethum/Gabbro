/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/GibKette.lean
  Subject:   The release chain of a scoped return (lock stage 3, `gibTs` in `Ticket/Code.lean`). From a memory in
              which every lock of `Ls` (none twice) is mine without waiters, the chain runs to its end (`gibTs_run`),
              leaves each of those locks free with both tickets one higher, and changes nothing but its scratch slots
              and the words of those locks (`AgreeKL`). What survives such a change: the slots below the scratch, the
              code, the environment, the frame header (`AgreeKL.kopf`), the world, a result below the scratch, the
              words and the class of every other lock; the ticket state then holds against the held set without
              `Ls` (`TicketSync.nachKette`).
-/
module
public import Stage0.Senke.Sperre.Ticket.Lauf
public import Stage0.Senke.Sperre.Ticket.Paar
public import Stage0.Senke.Sperre.Paar
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- Where the chain may run with scratch from slot `s`: the scratch ends below the world's end, the world ends below
    `2 ^ 31`, every lock's three words lie above the world, apart from each other, below `L.sye < 2 ^ 31`. -/
structure KetteOK (L : Lay D) (fp : W) (s : Nat) : Prop where
  far : fp.toNat + 8 * (s + 18) ≤ L.hi
  hi : L.hi < 2 ^ 31
  lay : ∀ Lk, L.hi ≤ L.lk Lk ∧ L.lk Lk + 24 ≤ L.sye
  sye : L.sye < 2 ^ 31
  dis : ∀ Lk Lk', Lk ≠ Lk' → L.lk Lk + 24 ≤ L.lk Lk' ∨ L.lk Lk' + 24 ≤ L.lk Lk

theorem KetteOK.lk {L : Lay D} {fp : W} {s : Nat} (h : KetteOK L fp s) (Lk : D.Lock) :
    fp.toNat + 8 * (s + 18) ≤ L.lk Lk ∧ L.lk Lk + 24 < 2 ^ 31 := by
  have hf := h.far
  have hs := h.sye
  obtain ⟨h1, h2⟩ := h.lay Lk
  exact ⟨by omega, by omega⟩

/-- Apart from the scratch slots `s .. s+17` and the words of the locks of `Ls`, `m'` is `m`. -/
structure AgreeKL (L : Lay D) (fp : W) (s : Nat) (Ls : List D.Lock) (m m' : Mem) : Prop where
  rd : m'.rd = m.rd
  wr : m'.wr = m.wr
  b : ∀ x, ¬ inSlots fp s (s + 18) x → (∀ Lk, Lk ∈ Ls → ¬ InLk (L.lk Lk) x) → m'.b x = m.b x

theorem AgreeKL.refl (L : Lay D) (fp : W) (s : Nat) (Ls : List D.Lock) (m : Mem) : AgreeKL L fp s Ls m m :=
  ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem AgreeKL.trans {L : Lay D} {fp : W} {s : Nat} {Ls : List D.Lock} {m1 m2 m3 : Mem}
    (h1 : AgreeKL L fp s Ls m1 m2) (h2 : AgreeKL L fp s Ls m2 m3) : AgreeKL L fp s Ls m1 m3 :=
  ⟨h2.rd.trans h1.rd, h2.wr.trans h1.wr, fun x hx hl => (h2.b x hx hl).trans (h1.b x hx hl)⟩

theorem AgreeKL.cons {L : Lay D} {fp : W} {s : Nat} {Ls : List D.Lock} {m m' : Mem}
    (h : AgreeKL L fp s Ls m m') (Lk : D.Lock) : AgreeKL L fp s (Lk :: Ls) m m' :=
  ⟨h.rd, h.wr, fun x hx hl => h.b x hx fun M hM => hl M (List.mem_cons.mpr (Or.inr hM))⟩

/-- One give is a change of the chain of every list headed by its lock. -/
theorem AgreeK.kl {L : Lay D} {fp : W} {s : Nat} {Lk : D.Lock} {m m' : Mem}
    (h : AgreeK fp s (L.lk Lk) m m') (Ls : List D.Lock) : AgreeKL L fp s (Lk :: Ls) m m' :=
  ⟨h.rd, h.wr, fun x hx hl => h.b x hx (hl Lk (List.mem_cons.mpr (Or.inl rfl)))⟩

/-- A word of another lock (at `b`, apart from the lock at `a`, above the scratch) survives one give or take. -/
theorem AgreeK.lk_other {m m1 : Mem} {fp : W} {s a b y : Nat} (h : AgreeK fp s a m m1)
    (hb31 : b + 24 < 2 ^ 31) (hf : fp.toNat + 8 * (s + 18) ≤ b) (hd : b + 24 ≤ a ∨ a + 24 ≤ b)
    (h1 : b ≤ y) (h2 : y ≤ b + 16) :
    m1.rd64 (BitVec.ofNat 64 y) = m.rd64 (BitVec.ofNat 64 y) :=
  rd64_keep h.rd fun j hj => h.b _
    (fun ⟨_, h3⟩ => by rw [lk_byte (by omega) hj] at h3; omega)
    (fun ⟨h3, h4⟩ => by rw [lk_byte (by omega) hj] at h3 h4; omega)

/-- A word of a lock outside `Ls` survives the chain's change. -/
theorem AgreeKL.lk_other {L : Lay D} {fp : W} {s : Nat} {Ls : List D.Lock} {m m' : Mem}
    (h : AgreeKL L fp s Ls m m') (hK : KetteOK L fp s) {Lb : D.Lock} (hb : Lb ∉ Ls) {y : Nat}
    (h1 : L.lk Lb ≤ y) (h2 : y ≤ L.lk Lb + 16) :
    m'.rd64 (BitVec.ofNat 64 y) = m.rd64 (BitVec.ofNat 64 y) := by
  obtain ⟨hf, hb31⟩ := hK.lk Lb
  refine rd64_keep h.rd fun j hj => h.b _ (fun ⟨_, h3⟩ => ?_) (fun M hM ⟨h3, h4⟩ => ?_)
  · rw [lk_byte (by omega) hj] at h3
    omega
  · have hne : M ≠ Lb := fun e => hb (e ▸ hM)
    have hd := hK.dis M Lb hne
    rw [lk_byte (by omega) hj] at h3 h4
    omega

/-- Every other lock keeps its class (`TicketKlasse`) through the chain. -/
theorem AgreeKL.ticketKlasse {L : Lay D} {fp : W} {s : Nat} {Ls : List D.Lock} {m m' : Mem}
    (h : AgreeKL L fp s Ls m m') (hK : KetteOK L fp s) {Lb : D.Lock} (hb : Lb ∉ Ls) :
    TicketKlasse m m' (L.lk Lb) :=
  TicketKlasse.ofWords fun k hk => h.lk_other hK hb (y := L.lk Lb + 8 * k) (by omega) (by omega)

theorem AgreeKL.big {L : Lay D} {fp : W} {s : Nat} {Ls : List D.Lock} {m m' : Mem}
    (h : AgreeKL L fp s Ls m m') (hK : KetteOK L fp s) : Agree fp s ((2 ^ 64 - fp.toNat) / 8) m m' := by
  have hf := hK.far
  have hhi := hK.hi
  refine ⟨h.rd, h.wr, fun x hx => h.b x (fun ⟨h1, h2⟩ => hx ⟨h1, ?_⟩) (fun M _ ⟨h1, h2⟩ => hx ⟨?_, ?_⟩)⟩
  · have := x.isLt; have := fp.isLt; omega
  · obtain ⟨l1, l2⟩ := hK.lk M
    omega
  · obtain ⟨l1, l2⟩ := hK.lk M
    have := x.isLt; have := fp.isLt; omega

theorem AgreeKL.rd_low {L : Lay D} {fp : W} {s i : Nat} {Ls : List D.Lock} {m m' : Mem}
    (h : AgreeKL L fp s Ls m m') (hK : KetteOK L fp s) (hi : i < s) :
    m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i)) := by
  have hf := hK.far
  have hhi := hK.hi
  have hs := slot_toNat (fp := fp) (K := s + 18) (i := i) (by omega) (by omega)
  refine rd64_keep h.rd fun j hj => h.b _ (fun ⟨h1, _⟩ => ?_) (fun M _ ⟨h1, _⟩ => ?_)
  · have := fp.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs] at h1
    omega
  · have := fp.isLt
    obtain ⟨l1, l2⟩ := hK.lk M
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs] at h1
    omega

theorem AgreeKL.valueAt {L : Lay D} {fp : W} {base s : Nat} {Ls : List D.Lock} {m m' : Mem} {τ : Ty}
    {v : Wert D τ} (h : AgreeKL L fp s Ls m m') (hK : KetteOK L fp s) (value : ValueAt L m fp base τ v)
    (below : base + valueWords τ ≤ s) : ValueAt L m' fp base τ v := by
  refine ⟨value.1, ?_⟩
  intro i hi
  have width := encodeWords_length L τ v
  rw [h.rd_low hK (i := base + i) (by omega)]
  exact value.2 i hi

theorem AgreeKL.resultAt {L : Lay D} {fp : W} {base s : Nat} {Ls : List D.Lock} {m m' : Mem}
    {e : Option Ty} {v : ErgVal D e} (h : AgreeKL L fp s Ls m m') (hK : KetteOK L fp s)
    (value : ResultAt L m fp base e v) (below : base + resultWords e ≤ s) : ResultAt L m' fp base e v := by
  cases e with
  | some τ => exact h.valueAt hK value below
  | none =>
    intro i hi
    have zero : i = 0 := by simpa using hi
    subst i
    rw [h.rd_low hK (i := base + 0) (by change base + 1 ≤ s at below; omega)]
    exact value 0 (by simp)

theorem AgreeKL.envAt {reserved : Nat} {L : Lay D} {fp : W} {s : Nat} {Ls : List D.Lock} {m m' : Mem}
    {Γ : Ctx} {ρ : Env D Γ} (h : AgreeKL L fp s Ls m m') (hK : KetteOK L fp s)
    (he : EnvAt L m fp ρ reserved) (hs : frei Γ reserved ≤ s) : EnvAt L m' fp ρ reserved := fun τ x => by
  have bound := variableOffset_bound x
  exact h.valueAt hK (he τ x) (by unfold vslot frei at *; omega)

theorem AgreeKL.codeAt {L : Lay D} {fp : W} {s : Nat} {Ls : List D.Lock} {m m' : Mem}
    (h : AgreeKL L fp s Ls m m') (hK : KetteOK L fp s) {pc : W} {is : List II} (hc : CodeAt m pc is) {K : Nat}
    (hcf : CodeFar pc is.length fp K) : CodeAt m' pc is :=
  hc.agree (h.big hK) (by obtain ⟨h1, h2, h3⟩ := hcf; have := fp.isLt; exact ⟨h1, by omega, h3⟩)

theorem AgreeKL.pcode {L : Lay D} {fp : W} {s K : Nat} {Ls : List D.Lock} {m m1 : Mem} {A : D.Fn → Nat}
    {C : D.Fn → List II} (h : AgreeKL L fp s Ls m m1) (hK : KetteOK L fp s) (hp : PCode m A C fp K) :
    PCode m1 A C fp K := fun g => ⟨h.codeAt hK (hp g).1 (hp g).2, (hp g).2⟩

theorem AgreeKL.weltAt {L : Lay D} {fp : W} {s : Nat} {Ls : List D.Lock} {m m1 : Mem} {σ : World D}
    (h : AgreeKL L fp s Ls m m1) (hK : KetteOK L fp s) (hw : WeltAt m L σ) (hl : LayIn L)
    (hlo : fp.toNat + 8 * (s + 18) ≤ L.lo) : WeltAt m1 L σ :=
  weltAt_keep hw hl h.rd h.wr fun x h1 h2 => h.b x (fun ⟨_, h3⟩ => by omega)
    (fun M _ ⟨h3, _⟩ => by have := (hK.lay M).1; omega)

theorem AgreeKL.kopf {L : Lay D} {P : Programm D} {σ0 : World D} {m m1 : Mem} {fp : W} {K s : Nat} {f : D.Fn}
    {rp cfp : W} {ρ0 : Env D (D.params f)} {Ls : List D.Lock}
    (h : Kopf L f m fp K rp cfp ρ0 P σ0) (ha : AgreeKL L fp s Ls m m1) (hK : KetteOK L fp s)
    (hs : (functionFrame P f).internalResult ≤ s) : Kopf L f m1 fp K rp cfp ρ0 P σ0 := by
  have hFB3 : FB = 4 := rfl
  have original := functionFrame_prefix P f
  have parameterEnd : frei (D.params f) (functionFrame P f).ensReserved =
      (functionFrame P f).internalResult := rfl
  have snapshotEnd : FB + EntrySnapshots.words (oldCells (P.ensures f)) ≤
      (functionFrame P f).internalResult := (functionFrame P f).protected_prefix.1
  refine ⟨by rw [ha.rd_low hK (i := 0) (by omega)]; exact h.r0,
    by rw [ha.rd_low hK (i := 1) (by omega)]; exact h.r1,
    ha.envAt hK h.env (by rw [parameterEnd]; exact hs), h.big, ?_⟩
  have saved := (EntrySnapshots.values_at σ0 (oldCells (P.ensures f)) (reserved := 0)).mpr h.entry
  have kept := ha.envAt hK saved (by
    simp only [frei, Nat.add_zero, EntrySnapshots.types_words]
    omega)
  exact (EntrySnapshots.values_at σ0 (oldCells (P.ensures f)) (reserved := 0)).mp kept

/-- A lock of the held set is mine without waiters: next = serving + 1. -/
theorem TicketSync.mine {m : Mem} {L : Lay D} {fp : W} {Ks : Nat} {H : List D.Lock} (hy : TicketSync m L fp Ks H)
    {Lk : D.Lock} (h : Lk ∈ H) : ∃ u : W, m.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some (u + 1) ∧
      m.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some u ∧ m.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0 := by
  obtain ⟨n, u, hn, hu, hw, hmine, -⟩ := hy.zust Lk
  refine ⟨u, ?_, hu, hw⟩
  rw [← hmine h]
  exact hn

/-- **The chain runs**: from a memory in which every lock of `Ls` (none twice) is mine without waiters, the chain at
    instruction `p` of `code` runs to its end; every lock of `Ls` then reads free with both tickets one higher (from
    the serving ticket `u` it read: `u + 1`, `u + 1`, no waiters), and only the scratch slots and those locks' words
    changed. -/
theorem gibTs_run {L : Lay D} {fp pc : W} {s : Nat} {code : List II} (hK : KetteOK L fp s) (hs : s + 18 < 2 ^ 31)
    (hcf : CodeFar pc code.length fp (s + 18)) :
    ∀ (Ls : List D.Lock) (m : Mem) (p : Nat), Ls.Nodup → FrameOK m fp (s + 18) →
      (∀ Lk k, k ≤ 2 → all m.wr (BitVec.ofNat 64 (L.lk Lk + 8 * k)) 8 = true) → CodeAt m pc code →
      At code p (gibTs L s Ls) →
      (∀ Lk, Lk ∈ Ls → ∃ u : W, m.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some (u + 1) ∧
        m.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some u ∧ m.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0) →
      ∃ m', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 16 * Ls.length)), fp⟩ m' ∧
        AgreeKL L fp s Ls m m' ∧
        ∀ Lk, Lk ∈ Ls → ∀ u : W, m.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some u →
          m'.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some (u + 1) ∧
          m'.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some (u + 1) ∧
          m'.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0
  | [], m, p, _, _, _, _, _, _ =>
    ⟨m, by simpa using Star.refl ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m, AgreeKL.refl L fp s [] m,
      fun _ h => (List.not_mem_nil h).elim⟩
  | Lk :: rest, m, p, hnd, hF, hwr, hc, hAt, hmine => by
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hfa, ha31⟩ := hK.lk Lk
    obtain ⟨u0, ho, hcu, hw⟩ := hmine Lk (List.mem_cons.mpr (Or.inl rfl))
    have E : LE m pc fp s (L.lk Lk) code :=
      ⟨hF, hs, hfa, ha31, by simpa using hwr Lk 0 (by omega), by simpa using hwr Lk 1 (by omega),
        by simpa using hwr Lk 2 (by omega), hc, hcf⟩
    have hAt' : At code p (gibT L (L.lk Lk) s ++ gibTs L s rest) := by simpa only [gibTs] using hAt
    have hAt1 : At code p (gibT L (L.lk Lk) s) := At.left hAt'
    have hAt2 : At code (p + 16) (gibTs L s rest) := by
      have h := At.right hAt'
      rw [gibT_len] at h
      exact h
    obtain ⟨f0, hL0⟩ := ls_init E ho hcu hw
    obtain ⟨m1, f1, s1, hL1⟩ := gibT_paar E hL0 hAt1
    have hag : AgreeK fp s (L.lk Lk) m m1 := hL1.ag
    have hF1 : FrameOK m1 fp (s + 18) := E.frameK hag
    have hwr1 : ∀ Lk' k, k ≤ 2 → all m1.wr (BitVec.ofNat 64 (L.lk Lk' + 8 * k)) 8 = true :=
      fun Lk' k hk => by rw [hag.wr]; exact hwr Lk' k hk
    have hc1 : CodeAt m1 pc code := hag.codeAt hfa ha31 hc hcf
    have hmine1 : ∀ Lk', Lk' ∈ rest → ∃ u' : W, m1.rd64 (BitVec.ofNat 64 (L.lk Lk')) = some (u' + 1) ∧
        m1.rd64 (BitVec.ofNat 64 (L.lk Lk' + 8)) = some u' ∧
        m1.rd64 (BitVec.ofNat 64 (L.lk Lk' + 16)) = some 0 := by
      intro Lk' hm
      have hne : Lk' ≠ Lk := fun e => hnot (e ▸ hm)
      obtain ⟨hfb, hb31⟩ := hK.lk Lk'
      have hd := hK.dis Lk' Lk hne
      obtain ⟨u', h1, h2, h3⟩ := hmine Lk' (List.mem_cons.mpr (Or.inr hm))
      refine ⟨u', ?_, ?_, ?_⟩
      · rw [hag.lk_other (y := L.lk Lk') hb31 hfb hd (Nat.le_refl _) (by omega)]; exact h1
      · rw [hag.lk_other (y := L.lk Lk' + 8) hb31 hfb hd (by omega) (by omega)]; exact h2
      · rw [hag.lk_other (y := L.lk Lk' + 16) hb31 hfb hd (by omega) (Nat.le_refl _)]; exact h3
    obtain ⟨m2, s2, a2, hfin⟩ := gibTs_run hK hs hcf rest m1 (p + 16) hnd' hF1 hwr1 hc1 hAt2 hmine1
    have e : p + 16 + 16 * rest.length = p + 16 * (Lk :: rest).length := by
      simp only [List.length_cons]
      omega
    refine ⟨m2, star_cast (s1.trans s2) rfl (by rw [e]), (hag.kl (L := L) rest).trans (a2.cons Lk), ?_⟩
    intro Lb hm u hu
    rcases List.mem_cons.mp hm with e' | hm'
    · rw [e'] at hu ⊢
      have hq : u = u0 := Option.some_inj.mp (hu.symm.trans hcu)
      rw [hq]
      refine ⟨?_, ?_, ?_⟩
      · rw [a2.lk_other hK hnot (y := L.lk Lk) (Nat.le_refl _) (by omega)]; exact hL1.o
      · rw [a2.lk_other hK hnot (y := L.lk Lk + 8) (by omega) (by omega)]; exact hL1.c
      · rw [a2.lk_other hK hnot (y := L.lk Lk + 16) (by omega) (Nat.le_refl _)]; exact hL1.w
    · have hne : Lb ≠ Lk := fun e'' => hnot (e'' ▸ hm')
      obtain ⟨hfb, hb31⟩ := hK.lk Lb
      have hd := hK.dis Lb Lk hne
      exact hfin Lb hm' u (by rw [hag.lk_other (y := L.lk Lb + 8) hb31 hfb hd (by omega) (by omega)]; exact hu)

/-- The chain at the start of a code: from the code's start to the chain's end. -/
theorem gibTs_run0 {L : Lay D} {fp pc : W} {s : Nat} {Ls : List D.Lock} {rest : List II} {m : Mem}
    (hK : KetteOK L fp s) (hs : s + 18 < 2 ^ 31) (hcf : CodeFar pc (gibTs L s Ls ++ rest).length fp (s + 18))
    (hnd : Ls.Nodup) (hF : FrameOK m fp (s + 18))
    (hwr : ∀ Lk k, k ≤ 2 → all m.wr (BitVec.ofNat 64 (L.lk Lk + 8 * k)) 8 = true)
    (hc : CodeAt m pc (gibTs L s Ls ++ rest))
    (hmine : ∀ Lk, Lk ∈ Ls → ∃ u : W, m.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some (u + 1) ∧
      m.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some u ∧ m.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (gibTs L s Ls).length), fp⟩ m' ∧
      AgreeKL L fp s Ls m m' ∧
      ∀ Lk, Lk ∈ Ls → ∀ u : W, m.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some u →
        m'.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some (u + 1) ∧
        m'.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some (u + 1) ∧
        m'.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0 := by
  obtain ⟨m', s1, a1, hf⟩ := gibTs_run hK hs hcf Ls m 0 hnd hF hwr hc (At.left (At.whole _)) hmine
  exact ⟨m', star_cast s1 (by simp) (by rw [gibTs_len, Nat.zero_add]), a1, hf⟩

/-- **The chain, in the invariant**: after it the ticket state holds against every `H'` that holds exactly the locks
    of `H` outside `Ls`. -/
theorem TicketSync.nachKette {m m' : Mem} {L : Lay D} {fp : W} {Ks s : Nat} {H H' Ls : List D.Lock}
    (hy : TicketSync m L fp Ks H) (hK : KetteOK L fp s) (ha : AgreeKL L fp s Ls m m')
    (hfin : ∀ Lk, Lk ∈ Ls → ∀ u : W, m.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some u →
      m'.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some (u + 1) ∧
      m'.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some (u + 1) ∧ m'.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0)
    (hH' : ∀ M, M ∈ H' ↔ M ∈ H ∧ M ∉ Ls) : TicketSync m' L fp Ks H' := by
  refine ⟨hy.sb31, hy.st, hy.st31, hy.lo, hy.room, hy.band, hy.lay, hy.sye, hy.dis,
    fun Lk k hk => by rw [ha.wr]; exact hy.wr Lk k hk, fun Lk => ?_⟩
  obtain ⟨n, u, hn, hu, hw, hmine, hfree⟩ := hy.zust Lk
  by_cases hm : Lk ∈ Ls
  · obtain ⟨e1, e2, e3⟩ := hfin Lk hm u hu
    exact ⟨u + 1, u + 1, e1, e2, e3, fun h => (((hH' Lk).mp h).2 hm).elim, fun _ => rfl⟩
  · have k0 := ha.lk_other hK hm (y := L.lk Lk) (Nat.le_refl _) (by omega)
    have k1 := ha.lk_other hK hm (y := L.lk Lk + 8) (by omega) (by omega)
    have k2 := ha.lk_other hK hm (y := L.lk Lk + 16) (by omega) (Nat.le_refl _)
    exact ⟨n, u, by rw [k0]; exact hn, by rw [k1]; exact hu, by rw [k2]; exact hw,
      fun h => hmine ((hH' Lk).mp h).1, fun h => hfree fun h' => h ((hH' Lk).mpr ⟨h', hm⟩)⟩

end Gabbro.Stage0.Senke
