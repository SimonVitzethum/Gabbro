/-
  File:      stage0/Stage0/Senke/Anweisung/Puffer.lean
  Subject:   A gate's buffer: packing the byte field of a table into words of the frame (`pack1_ok`, `packJ_ok`,
             `packI_ok`: word `i` is `packV` of the cells' words) and unpacking it into the cells after the call
             (`unpackK_ok`: cell `k` gets `byteOf` the buffer).
-/
import Stage0.Senke.Anweisung.Tor

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {reserved : Nat}

variable {D : Deklaration} {L : Lay D}

/-- `d := g a b` in one step. -/
theorem bin_star {m : Runner.Mem} {pc fp : Runner.W} {K o d a b : Nat} {g : Runner.W → Runner.W → Option Runner.W}
    {va vb r : Runner.W} (hc : CodeAt m pc [ci o d a b]) (hop : op o = bin g) (ho : o < 256) (hF : FrameOK m fp K)
    (hd : d < K) (ha : a < K) (hb : b < K) (hK : K < 2 ^ 31)
    (hra : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some va) (hrb : m.rd64 (slot fp (BitVec.ofNat 64 b)) = some vb)
    (hg : g va vb = some r) :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [ci o d a b].length), fp⟩
      (write m (slot fp (BitVec.ofNat 64 d)) 8 r.toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  refine star_ins hc (by simpa [ci] using ho) ?_
  simp only [ci]
  rw [hop]
  rw [← sx_nat (d := a) (by omega)] at hra
  rw [← sx_nat (d := b) (by omega)] at hrb
  have hw := wr64_some (v := r) (hF.wr d hd)
  rw [← sx_nat (d := d) (by omega)] at hw
  have := run_bin (t := ⟨pc, fp⟩) hi hra hrb hg hw
  rwa [sx_nat (d := d) (by omega)] at this

theorem shl_amt {j : Nat} (hj : j < 8) : (BitVec.ofInt 64 (8 * (j : Int))).toNat % 64 = 8 * j := by
  rw [show (8 * (j : Int)) = ((8 * j : Nat) : Int) by push_cast; rfl, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  omega

/-- One byte: `u := cell`, `u := u << 8 j`, `acc := acc + u`. -/
theorem pack1_ok {m : Runner.Mem} {pc fp : Runner.W} {K acc u adr j : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {A w : Runner.W}
    (hp : Pre L m pc fp K u (pack1 acc u adr j) ρ W reserved) (hacc : acc < u) (hu : u + 2 ≤ K) (hadr : adr < 2 ^ 31)
    (hj : j < 8) (hA : m.rd64 (slot fp (BitVec.ofNat 64 acc)) = some A)
    (hw : ∀ m', W m' → m'.rd64 (BitVec.ofNat 64 adr) = some w) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 5), fp⟩ m' ∧ Agree fp acc K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 acc)) = some (A + (w <<< (8 * j))) := by
  have hsmall := hp.small
  have hp' : Pre L m pc fp K u (([ci 1 u adr 0] ++ [ci 15 u u 0]) ++
      ([ci 1 ((u : Int) + 1) (8 * j) 0, ci 11 u u ((u : Int) + 1)] ++ [ci 3 acc acc u])) ρ W reserved := hp
  have hX : Ok m pc fp K u ([ci 1 u adr 0] ++ [ci 15 u u 0]) (· = w) :=
    ok_seq hp'.left (const_ok hp'.left.left (lit_ok (by omega) (by omega)) (by omega))
      (fun m' w' hp'' hr he => by
        rw [he, BitVec.ofInt_natCast] at hr
        exact ld_ok hp'' (by omega) hr (hw m' hp''.welt)) (by omega)
  have hp3 : Pre L m pc fp K u ((([ci 1 u adr 0] ++ [ci 15 u u 0]) ++
      [ci 1 ((u : Int) + 1) (8 * j) 0, ci 11 u u ((u : Int) + 1)]) ++ [ci 3 acc acc u]) ρ W reserved := hp
  have hq := hp3.left
  obtain ⟨m1, s1, a1, v, hv, rfl⟩ := ok_seq hq hX (Pb := (· = w <<< (8 * j)))
    (fun m' w' hp'' hr he => (binK_ok (o := 11) (g := fun a b => some (a <<< (b.toNat % 64)))
      (r := w' <<< (8 * j)) hp'' hr (lit_ok (by omega) (by omega)) rfl (by decide)
      (by simp only [shl_amt hj]) (by omega)).mono fun x hx => by rw [hx, he]) (by omega)
  have hn := hp3.next a1 (Nat.le_refl _) (by omega)
  simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at s1 hn
  have hA1 : m1.rd64 (slot fp (BitVec.ofNat 64 acc)) = some A := by
    rw [agree_rd_low a1 hp.frame.room hacc (by omega)]; exact hA
  have s2 := bin_star (o := 3) (K := K) (d := acc) (a := acc) (b := u) (g := fun a b => some (a + b)) hn.code rfl (by decide) hn.frame (by omega) (by omega)
    (by omega) hsmall hA1 hv rfl
  refine ⟨_, s1.trans (star_cast s2 rfl ?_), (a1.mono (Nat.le_of_lt hacc)).trans
    (agree_write hp.frame.room (Nat.le_refl _) (by omega) _), rd64_write_same (hn.frame.rd acc (by omega))⟩
  simp only [List.length_singleton, addr_norm]

/-- `Pre.next` after code that changed the slots from `lo` on, below `d`. -/
theorem Pre.next' {m m' : Runner.Mem} {pc fp : Runner.W} {K d lo : Nat} {a b : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (h : Pre L m pc fp K d (a ++ b) ρ W reserved) (ha : Agree fp lo K m m') (hlo : frei Γ reserved ≤ lo)
    (hd : lo ≤ d) (hK : d ≤ K) : Pre L m' (pc + BitVec.ofNat 64 (16 * a.length)) fp K d b ρ W reserved :=
  have hf := codeFar_right (n := a.length) (k := b.length) (by simpa using h.far)
  ⟨h.ctx, h.small, h.frame.agree ha, (codeAt_right h.code).agree ha hf, hf,
   envAt_agree h.env ha h.frame hlo (by omega), h.wstab m m' h.welt (ha.mono (Nat.zero_le _)), h.wstab⟩

/-- The bytes `j < J` of word `i` into the accumulator. -/
theorem packJ_ok {L : Lay D} {t : D.Tab} {f : D.Feld t} {c i acc u : Nat} {fp : Runner.W} {K : Nat} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {ws : Nat → Runner.W} (hacc : acc < u) (hu : u + 2 ≤ K)
    (hctx : frei Γ reserved ≤ acc) (hadr : ∀ k, k < c → L.elem t f k < 2 ^ 31)
    (hw : ∀ k, k < c → ∀ m', W m' → m'.rd64 (BitVec.ofNat 64 (L.elem t f k)) = some (ws k)) :
    (J : Nat) → J ≤ 8 → (m : Runner.Mem) → (pc : Runner.W) → Pre L m pc fp K u (packJ L t f c i acc u J) ρ W reserved →
    m.rd64 (slot fp (BitVec.ofNat 64 acc)) = some 0 →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (packJ L t f c i acc u J).length), fp⟩ m' ∧
      Agree fp acc K m m' ∧ m'.rd64 (slot fp (BitVec.ofNat 64 acc)) = some (packV ws c i J)
  | 0, _, m, pc, _, h0 => ⟨m, by simpa [packJ] using Star.refl _ m, Agree.refl _ _ _ _, h0⟩
  | J + 1, hJ, m, pc, hp, h0 => by
    have hp' : Pre L m pc fp K u (packJ L t f c i acc u J ++
        (if 8 * i + J < c then pack1 acc u (L.elem t f (8 * i + J)) J else [])) ρ W reserved := hp
    obtain ⟨m1, s1, a1, hr1⟩ := packJ_ok hacc hu hctx hadr hw J (by omega) m pc hp'.left h0
    have hn := hp'.next' a1 hctx (Nat.le_of_lt hacc) (by omega)
    by_cases hc : 8 * i + J < c
    · simp only [hc, ↓reduceIte] at hn
      obtain ⟨m2, s2, a2, hr2⟩ := pack1_ok hn hacc hu (hadr _ hc) (by omega) hr1 (hw _ hc)
      refine ⟨m2, s1.trans (star_cast s2 rfl ?_), a1.trans a2, ?_⟩
      · simp only [T.mk.injEq, and_true]
        rw [addr_norm]
        congr 2
        simp only [packJ, hc, ↓reduceIte, List.length_append, pack1, List.length_cons, List.length_nil]
        omega
      · rw [hr2]; simp only [packV, hc, ↓reduceIte]
    · refine ⟨m1, star_cast s1 rfl ?_, a1, ?_⟩
      · simp only [packJ, hc, ↓reduceIte, List.append_nil]
      · rw [hr1]; simp only [packV, hc, ↓reduceIte]

/-- The words `i < I` of the buffer from slot `B`; the accumulator in `B + Wn`, scratch above. -/
theorem packI_ok {L : Lay D} {t : D.Tab} {f : D.Feld t} {c B Wn : Nat} {fp : Runner.W} {K : Nat} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {ws : Nat → Runner.W} (hu : B + Wn + 3 ≤ K) (hctx : frei Γ reserved ≤ B)
    (hadr : ∀ k, k < c → L.elem t f k < 2 ^ 31)
    (hw : ∀ k, k < c → ∀ m', W m' → m'.rd64 (BitVec.ofNat 64 (L.elem t f k)) = some (ws k)) :
    (I : Nat) → I ≤ Wn → (m : Runner.Mem) → (pc : Runner.W) →
    Pre L m pc fp K (B + Wn + 1) (packI L t f c B (B + Wn) (B + Wn + 1) I) ρ W reserved →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (packI L t f c B (B + Wn) (B + Wn + 1) I).length), fp⟩ m' ∧
      Agree fp B K m m' ∧ ∀ i, i < I → m'.rd64 (slot fp (BitVec.ofNat 64 (B + i))) = some (packV ws c i 8)
  | 0, _, m, pc, _ => ⟨m, by simpa [packI] using Star.refl _ m, Agree.refl _ _ _ _, fun _ h => absurd h (by omega)⟩
  | I + 1, hI, m, pc, hp => by
    have hsmall := hp.small
    have hroom := hp.frame.room
    have hp' : Pre L m pc fp K (B + Wn + 1) (packI L t f c B (B + Wn) (B + Wn + 1) I ++
        ([ci 1 ((B + Wn : Nat) : Int) 0 0] ++ packJ L t f c I (B + Wn) (B + Wn + 1) 8 ++
          [ci 2 ((B + I : Nat) : Int) ((B + Wn : Nat) : Int) 0])) ρ W reserved := hp
    obtain ⟨m1, s1, a1, hr1⟩ := packI_ok hu hctx hadr hw I (by omega) m pc hp'.left
    have hn := hp'.next' a1 hctx (by omega) (by omega)
    have s2 := const_step (k := 0) hn.left.left.code hn.frame (by omega) hsmall (by decide)
    let m2 := write m1 (slot fp (BitVec.ofNat 64 (B + Wn))) 8 (BitVec.ofInt 64 0).toNat
    have a2 : Agree fp (B + Wn) K m1 m2 := agree_write hroom (Nat.le_refl _) (by omega) _
    have hz : m2.rd64 (slot fp (BitVec.ofNat 64 (B + Wn))) = some 0 :=
      rd64_write_same (w := BitVec.ofInt 64 0) (hn.frame.rd _ (by omega))
    have hJ := hn.left.next' a2 (by omega) (by omega) (by omega)
    obtain ⟨m3, s3, a3, hr3⟩ := packJ_ok (by omega) (by omega) (by omega) hadr hw 8 (Nat.le_refl _) m2 _ hJ hz
    have hm := hn.next' (a2.trans a3) (by omega) (by omega) (by omega)
    have s4 := mov_to hm.code hm.frame (j := B + I) (s := B + Wn) (by omega) (by omega) hsmall hr3
    have s34 := s3.trans (star_cast s4 (by simp only [List.length_append, addr_norm, Nat.mul_add, Nat.add_assoc]) rfl)
    refine ⟨_, s1.trans (s2.trans (star_cast s34 ?_ ?_)), a1.trans ((((a2.trans a3).mono (by omega))).trans
      (agree_write hroom (by omega) (by omega) _)), fun i hi => ?_⟩
    · simp only [T.mk.injEq, and_true, List.length_singleton]
      rfl
    · simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, addr_norm, packI]
      congr 2
      omega
    · by_cases hiI : i = I
      · subst hiI
        exact rd64_write_same (hm.frame.rd _ (by omega))
      · have h1 := hr1 i (by omega)
        rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega)),
          agree_rd_low (a2.trans a3) hroom (by omega) (by omega), h1]

/-! ## Unpacking -/

theorem shr_amt {k : Nat} : (BitVec.ofInt 64 ((8 * (k % 8) : Nat) : Int)).toNat % 64 = 8 * (k % 8) := by
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega

/-- One element back: `u := buffer word`, `u := u >> 8 (k % 8)`, `u := u & 255`, the cell's address into `u + 1`,
    the store. The frame below `u` and every word of the world apart from the cell keep their contents. -/
theorem unpack1_ok {m : Runner.Mem} {pc fp : Runner.W} {Ks B u adr k : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {bw : Runner.W}
    {L : Lay D} (hp : Pre L m pc fp Ks u (unpack1 B u adr k) ρ W reserved) (hB : B + k / 8 < u)
    (hu : u + 2 ≤ Ks) (hadr : adr < 2 ^ 31) (hrd : Runner.Mem.all m.rd (BitVec.ofNat 64 adr) 8 = true)
    (hwr0 : Runner.Mem.all m.wr (BitVec.ofNat 64 adr) 8 = true) (ha1 : L.lo ≤ adr) (ha2 : adr + 8 ≤ L.hi)
    (hl3 : L.hi < 2 ^ 31) (htop : fp.toNat + 8 * Ks ≤ L.lo)
    (hbw : m.rd64 (slot fp (BitVec.ofNat 64 (B + k / 8))) = some bw) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 7), fp⟩ m' ∧ AgreeW L fp u Ks m m' ∧
      m'.rd64 (BitVec.ofNat 64 adr) = some ((bw >>> (8 * (k % 8))) &&& 255) ∧
      ∀ a : Nat, a + 8 ≤ 2 ^ 64 → fp.toNat + 8 * Ks ≤ a → Far (BitVec.ofNat 64 a) 8 (BitVec.ofNat 64 adr) 8 →
        m'.rd64 (BitVec.ofNat 64 a) = m.rd64 (BitVec.ofNat 64 a) := by
  have hsmall := hp.small
  have hroom := hp.frame.room
  have hp3 : Pre L m pc fp Ks u ((([ci 2 u ((B + k / 8 : Nat) : Int) 0] ++
      [ci 1 ((u : Int) + 1) ((8 * (k % 8) : Nat) : Int) 0, ci 12 u u ((u : Int) + 1)]) ++
      [ci 1 ((u : Int) + 1) 255 0, ci 8 u u ((u : Int) + 1)]) ++
      ([ci 1 ((u + 1 : Nat) : Int) adr 0] ++ [ci 16 ((u + 1 : Nat) : Int) u 0])) ρ W reserved := hp
  have hA := ok_seq hp3.left.left (mov_ok hp3.left.left.left (by omega) (by omega) hbw)
    (Pb := (· = bw >>> (8 * (k % 8))))
    (fun m' w' hp'' hr he => (binK_ok (o := 12) (g := fun a b => some (a >>> (b.toNat % 64)))
      (r := w' >>> (8 * (k % 8))) hp'' hr (lit_ok (by omega) (by omega)) rfl (by decide)
      (by simp only [shr_amt]) (by omega)).mono fun x hx => by rw [hx, he]) (by omega)
  obtain ⟨m1, s1, a1, v, hv, rfl⟩ := ok_seq hp3.left hA (Pb := (· = (bw >>> (8 * (k % 8))) &&& 255))
    (fun m' w' hp'' hr he => (binK_ok (o := 8) (g := fun a b => some (a &&& b))
      (r := w' &&& 255) hp'' hr (by decide) rfl (by decide) rfl (by omega)).mono fun x hx => by rw [hx, he])
    (by omega)
  have hn := hp3.next a1 (Nat.le_refl _) (by omega)
  have s2 := const_step (k := (adr : Int)) hn.left.code hn.frame (by omega) hsmall (lit_ok (by omega) (by omega))
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (u + 1))) 8 (BitVec.ofInt 64 (adr : Int)).toNat
  have a2 : Agree fp u Ks m1 m2 := agree_write hroom (by omega) (by omega) _
  have hc3 : CodeAt m2 (pc + BitVec.ofNat 64 (16 * 5) + 16) [ci 16 ((u + 1 : Nat) : Int) u 0] := by
    have := (codeAt_right hn.code).agree a2 (by simpa using codeFar_right (n := 1) (k := 1) hn.far)
    simpa [List.length_append] using this
  have hi := hc3 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have hra : m2.rd64 (slot fp (BitVec.ofNat 64 (u + 1))) = some (BitVec.ofNat 64 adr) := by
    rw [← BitVec.ofInt_natCast]; exact rd64_write_same (hn.frame.rd _ (by omega))
  have hrb : m2.rd64 (slot fp (BitVec.ofNat 64 u)) = some ((bw >>> (8 * (k % 8))) &&& 255) := by
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]; exact hv
  have a12 : Agree fp u Ks m m2 := a1.trans a2
  have hwr : all m2.wr (BitVec.ofNat 64 adr) 8 = true := by
    rw [a12.wr]; exact hwr0
  have s3 := star_ins (fp := fp) (m' := write m2 (BitVec.ofNat 64 adr) 8 ((bw >>> (8 * (k % 8))) &&& 255).toNat) hc3
    (by simp [ci]) (by
      simp only [ci, op]
      refine f1_run (t := ⟨_, fp⟩) hi ?_
      rw [sx_nat (by omega)]
      refine run_rd64 hra ?_
      refine f2_run (t := ⟨_, fp⟩) hi ?_
      rw [sx_nat (by omega)]
      exact run_rd64 hrb (run_wr64 (wr64_some hwr)))
  refine ⟨_, s1.trans (s2.trans (star_cast s3 rfl ?_)), (agreeW_of a12).trans
    (agreeW_write_welt ha1 ha2 hl3 _), ?_, fun a h1 h2 h3 => ?_⟩
  · simp only [T.mk.injEq, and_true, List.length_singleton]
    rw [show (16 : Runner.W) = BitVec.ofNat 64 16 from rfl, addr_norm, addr_norm]
  · exact rd64_write_same (by rw [a12.rd]; exact hrd)
  · rw [rd64_write_far (by exact ⟨h3.2.1, h3.1, h3.2.2.symm⟩), rd64_agree_out a12 h1 (.inr h2)]

theorem unpackK_len (L : Lay D) (t : D.Tab) (f : D.Feld t) (B u : Nat) :
    (K' : Nat) → (unpackK L t f B u K').length = 7 * K'
  | 0 => rfl
  | K' + 1 => by simp only [unpackK, List.length_append, unpackK_len L t f B u K', unpack1, List.length_cons,
      List.length_nil]; omega

/-- **The elements `k < K'` back from the buffer at slot `B`**: each cell holds `byteOf` the buffer; every other word
    of the world above the frame keeps its contents, and so does the frame below `u`. -/
theorem unpackK_ok {L : Lay D} {t : D.Tab} {f : D.Feld t} {B u : Nat} {fp : Runner.W} {Ks : Nat} {Γ : Ctx}
    {ρ : Env D Γ} (hl : LayIn L) (hd : LayDis L) (hu : u + 2 ≤ Ks) (hwlo : fp.toNat + 8 * Ks ≤ L.lo)
    (hord : L.lo ≤ L.hi) :
    (K' : Nat) → (K' : Int) ≤ D.count t → (∀ k, k < K' → B + k / 8 < u) → (m : Runner.Mem) → (pc : Runner.W) →
    PreS L m pc fp Ks u (unpackK L t f B u K') ρ reserved → WeltWr m L →
    (∀ k : Nat, (k : Int) < D.count t → Runner.Mem.all m.rd (BitVec.ofNat 64 (L.elem t f k)) 8 = true) →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (unpackK L t f B u K').length), fp⟩ m' ∧ AgreeW L fp u Ks m m' ∧
      (∀ k, k < K' → m'.rd64 (BitVec.ofNat 64 (L.elem t f k)) = some (byteOf m (slot fp (BitVec.ofNat 64 B)) k)) ∧
      ∀ a : Nat, a + 8 ≤ 2 ^ 64 → fp.toNat + 8 * Ks ≤ a →
        (∀ k, k < K' → Far (BitVec.ofNat 64 a) 8 (BitVec.ofNat 64 (L.elem t f k)) 8) →
        m'.rd64 (BitVec.ofNat 64 a) = m.rd64 (BitVec.ofNat 64 a)
  | 0, _, _, m, pc, _, _, _ => ⟨m, by simpa [unpackK] using Star.refl _ m, AgreeW.refl _ _ _ _ _,
      fun _ h => absurd h (by omega), fun _ _ _ _ => rfl⟩
  | K' + 1, hK', hB, m, pc, hp, hwr, hrdc => by
    have hroom := hp.frame.room
    have hsmall := hp.small
    have hl3 := hl.2.2
    have hp' : PreS L m pc fp Ks u (unpackK L t f B u K' ++ unpack1 B u (L.elem t f K') K') ρ reserved := hp
    obtain ⟨m1, s1, a1, hc1, ho1⟩ := unpackK_ok hl hd hu hwlo hord K' (by omega)
      (fun k hk => hB k (by omega)) m pc hp'.left hwr hrdc
    have hfr := codeFar_right (by simpa using hp'.far)
    have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * (unpackK L t f B u K').length)) fp Ks u
        (unpack1 B u (L.elem t f K') K') ρ reserved :=
      ⟨hp.ctx, hsmall, ⟨hp.frame.lt, fun i hi => by rw [a1.rd]; exact hp.frame.rd i hi,
        fun i hi => by rw [a1.wr]; exact hp.frame.wr i hi⟩,
       codeAt_agreeW a1 hwlo hl3 hord (codeAt_right hp'.code) hfr, hfr,
       envAt_agreeW hp.env a1 hwlo hroom hp.ctx (by omega), trivial, wstab_true _ _⟩
    have hcell := hl.1 t f K' (L.bounded (by omega))
    have hbw : m1.rd64 (slot fp (BitVec.ofNat 64 (B + K' / 8))) =
        some ((m.rd64 (slot fp (BitVec.ofNat 64 B) + BitVec.ofNat 64 (8 * (K' / 8)))).getD 0) := by
      rw [agreeW_rd_low a1 hwlo hroom (hB K' (by omega)) (by omega), slot_succ]
      exact rd64_rdW hp.frame (by have := hB K' (by omega); omega)
    obtain ⟨m2, s2, a2, hc2, ho2⟩ := unpack1_ok hp1 (hB K' (by omega)) hu (by omega)
      (by rw [a1.rd]; exact hrdc K' (by omega)) (by rw [a1.wr]; exact hwr.word hcell.1 hcell.2 hl3)
      hcell.1 hcell.2 hl3 hwlo hbw
    refine ⟨m2, s1.trans (star_cast s2 rfl ?_), a1.trans a2, fun k hk => ?_, fun a h1 h2 h3 => ?_⟩
    · simp only [T.mk.injEq, and_true, unpackK, List.length_append, unpack1, List.length_cons, List.length_nil,
        addr_norm]
      congr 2
    · by_cases hkK : k = K'
      · subst hkK; rw [hc2]; rfl
      · obtain ⟨hck1, hck2⟩ := hl.1 t f k (L.bounded (by omega))
        obtain ⟨hcl1, hcl2⟩ := hcell
        have hfar := cell_far (c := .elem t f k) (c' := .elem t f K') hl hd (by simp only [Zelle.da]; apply L.bounded; omega)
          (by simp only [Zelle.da]; apply L.bounded; omega) (by simpa [Zelle.adr] using hck2) (by simpa [Zelle.adr] using hcl2)
          (by simp; omega)
        simp only [Zelle.adr] at hfar
        rw [ho2 _ (by omega) (by omega) hfar]
        exact hc1 k (by omega)
    · rw [ho2 a h1 h2 (h3 K' (by omega)), ho1 a h1 h2 (fun k hk => h3 k (by omega))]

end Gabbro.Stage0.Senke
