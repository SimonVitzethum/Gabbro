/-
  File:      Grammatik/X86/HwForwardingGeneric.lean
  Subject:   Generic word-forwarding theorem on the coherent machine
             (lane 1185, follow-up of lane 1139 `HwStackCalls`).

  Lifts the accepted `hwWortAusgabe` word stores and the accepted
  `stapelLadeWort` forwarding loads to a generic word family on
  `HwMaschine`: under the `WortGruppe` guard the owner core forwards
  the stored word, a foreign core reads canonical memory until drain,
  and partial overlaps follow the accepted byte rules (`loadByte`,
  `neuestens`). Misaligned loads, torn buffers and overlapping older
  or younger entries never group. No model is redefined here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwStackCalls

namespace Gabbro.Grammatik.X86

/-! ## 1. Family events and the adapter.

  A word store buffers eight bytes through the accepted
  `hwWortAusgabe`; a word observation reads through the accepted
  `stapelLadeWort` without moving state. -/

/-- Generic word family events on the coherent machine. -/
inductive FwdEreignis where
  | speichere : Adresse → Wort → FwdEreignis
  | beobachte : Adresse → FwdEreignis
  deriving DecidableEq, Repr

/-- The family adapter: stores buffer a word, observations read one
    (state unchanged). -/
def fwdAdapter : HwAdapter FwdEreignis :=
  ⟨fun m c ev => match ev with
    | .speichere a v => hwWortAusgabe m c a v
    | .beobachte a =>
      match stapelLadeWort (tsoAnsicht m) c a with
      | some _ => some m
      | none => none⟩

/-! ## 2. Buffer resolution helpers.

  Both lemmas are induction principles over `neuestens` used by every
  forwarding leg below: a buffer with no entry for `x` misses, and a
  match in the young part survives any older prefix. -/

/-- No entry for `x` anywhere means no match: induction over the
    buffer; the head match decides, the tail carries the hypothesis. -/
theorem fwd_neuestens_miss (l : List TSOEintrag) (x : Adresse)
    (h : ∀ e ∈ l, e.addr ≠ x) :
    neuestens l x = none := by
  induction l with
  | nil => rfl
  | cons f rest ih =>
    simp only [neuestens]
    have hf : f.addr ≠ x := h f (by simp)
    have hrest : ∀ e ∈ rest, e.addr ≠ x := by
      intro e hm
      exact h e (by simp only [List.mem_cons]; exact Or.inr hm)
    rw [ih hrest]
    simp [hf]

/-- A young-part match survives any older prefix: induction over the
    prefix; the tail match wins at every head. -/
theorem fwd_neuestens_angehaengt_list (l1 l2 : List TSOEintrag)
    (x : Adresse) (w : Byte)
    (h : neuestens l2 x = some w) :
    neuestens (l1 ++ l2) x = some w := by
  induction l1 with
  | nil =>
    simp only [List.nil_append]
    exact h
  | cons f rest ih =>
    simp only [List.cons_append, neuestens]
    rw [ih]

/-- Every footprint byte of the canonical eight-entry list resolves
    to its little-endian word byte: younger same-address shadows are
    impossible by `addrOff_ne8`. The proof shape follows the accepted
    `neuestens_entriesOf` 64-bit case; the model is reused, not copied. -/
theorem fwd_neuestens_wort (a : Adresse) (v : Wort)
    (k : Nat) (hk : k < 8) :
    neuestens (wortEintraege a v) (addrOff a k) = some (wortByte v k) := by
  have hkk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
      k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  have g : ∀ i j : Nat, i < 8 → j < 8 → i ≠ j →
      addrOff a i ≠ addrOff a j :=
    fun i j hi hj hij => addrOff_ne8 hi hj hij
  rcases hkk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wortEintraege, neuestens]
    rw [if_neg (g 7 0 (by decide) (by decide) (by decide)),
      if_neg (g 6 0 (by decide) (by decide) (by decide)),
      if_neg (g 5 0 (by decide) (by decide) (by decide)),
      if_neg (g 4 0 (by decide) (by decide) (by decide)),
      if_neg (g 3 0 (by decide) (by decide) (by decide)),
      if_neg (g 2 0 (by decide) (by decide) (by decide)),
      if_neg (g 1 0 (by decide) (by decide) (by decide))]
    rfl
  · simp only [wortEintraege, neuestens]
    rw [if_neg (g 7 1 (by decide) (by decide) (by decide)),
      if_neg (g 6 1 (by decide) (by decide) (by decide)),
      if_neg (g 5 1 (by decide) (by decide) (by decide)),
      if_neg (g 4 1 (by decide) (by decide) (by decide)),
      if_neg (g 3 1 (by decide) (by decide) (by decide)),
      if_neg (g 2 1 (by decide) (by decide) (by decide)),
      if_neg (g 0 1 (by decide) (by decide) (by decide))]
    rfl
  · simp only [wortEintraege, neuestens]
    rw [if_neg (g 7 2 (by decide) (by decide) (by decide)),
      if_neg (g 6 2 (by decide) (by decide) (by decide)),
      if_neg (g 5 2 (by decide) (by decide) (by decide)),
      if_neg (g 4 2 (by decide) (by decide) (by decide)),
      if_neg (g 3 2 (by decide) (by decide) (by decide)),
      if_neg (g 1 2 (by decide) (by decide) (by decide)),
      if_neg (g 0 2 (by decide) (by decide) (by decide))]
    rfl
  · simp only [wortEintraege, neuestens]
    rw [if_neg (g 7 3 (by decide) (by decide) (by decide)),
      if_neg (g 6 3 (by decide) (by decide) (by decide)),
      if_neg (g 5 3 (by decide) (by decide) (by decide)),
      if_neg (g 4 3 (by decide) (by decide) (by decide)),
      if_neg (g 2 3 (by decide) (by decide) (by decide)),
      if_neg (g 1 3 (by decide) (by decide) (by decide)),
      if_neg (g 0 3 (by decide) (by decide) (by decide))]
    rfl
  · simp only [wortEintraege, neuestens]
    rw [if_neg (g 7 4 (by decide) (by decide) (by decide)),
      if_neg (g 6 4 (by decide) (by decide) (by decide)),
      if_neg (g 5 4 (by decide) (by decide) (by decide)),
      if_neg (g 3 4 (by decide) (by decide) (by decide)),
      if_neg (g 2 4 (by decide) (by decide) (by decide)),
      if_neg (g 1 4 (by decide) (by decide) (by decide)),
      if_neg (g 0 4 (by decide) (by decide) (by decide))]
    rfl
  · simp only [wortEintraege, neuestens]
    rw [if_neg (g 7 5 (by decide) (by decide) (by decide)),
      if_neg (g 6 5 (by decide) (by decide) (by decide)),
      if_neg (g 4 5 (by decide) (by decide) (by decide)),
      if_neg (g 3 5 (by decide) (by decide) (by decide)),
      if_neg (g 2 5 (by decide) (by decide) (by decide)),
      if_neg (g 1 5 (by decide) (by decide) (by decide)),
      if_neg (g 0 5 (by decide) (by decide) (by decide))]
    rfl
  · simp only [wortEintraege, neuestens]
    rw [if_neg (g 7 6 (by decide) (by decide) (by decide)),
      if_neg (g 5 6 (by decide) (by decide) (by decide)),
      if_neg (g 4 6 (by decide) (by decide) (by decide)),
      if_neg (g 3 6 (by decide) (by decide) (by decide)),
      if_neg (g 2 6 (by decide) (by decide) (by decide)),
      if_neg (g 1 6 (by decide) (by decide) (by decide)),
      if_neg (g 0 6 (by decide) (by decide) (by decide))]
    rfl
  · simp only [wortEintraege, neuestens]
    rw [if_neg (g 6 7 (by decide) (by decide) (by decide)),
      if_neg (g 5 7 (by decide) (by decide) (by decide)),
      if_neg (g 4 7 (by decide) (by decide) (by decide)),
      if_neg (g 3 7 (by decide) (by decide) (by decide)),
      if_neg (g 2 7 (by decide) (by decide) (by decide)),
      if_neg (g 1 7 (by decide) (by decide) (by decide)),
      if_neg (g 0 7 (by decide) (by decide) (by decide))]
    rfl

/-! ## 3. Generic word forwarding.

  Under the `WortGruppe` guard every footprint byte resolves to its
  word byte (`fwd_neuestens_wort`), so the accepted forwarding word
  load returns exactly the stored word -- for every core, every word
  address and every buffer content carrying the group. The old
  evaluator is lifted, never redefined. -/

/-- GENERIC WORD FORWARDING: under the group guard a word load after
    the word store by the same core returns the stored word. The
    group pins the buffer shape, readability feeds every byte load. -/
theorem fwdWeiterleitung_generisch (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort)
    (hgrp : WortGruppe s c a v)
    (hles : ∀ k, k < 8 → s.mem.lesbar (addrOff a k) = true) :
    stapelLadeWort s c a = some v := by
  obtain ⟨hbuf, _⟩ := hgrp
  have l0 : loadByte s c (addrOff a 0) = some (wortByte v 0) := by
    unfold loadByte
    rw [if_pos (hles 0 (by decide)), hbuf,
      fwd_neuestens_wort a v 0 (by decide)]
  have l1 : loadByte s c (addrOff a 1) = some (wortByte v 1) := by
    unfold loadByte
    rw [if_pos (hles 1 (by decide)), hbuf,
      fwd_neuestens_wort a v 1 (by decide)]
  have l2 : loadByte s c (addrOff a 2) = some (wortByte v 2) := by
    unfold loadByte
    rw [if_pos (hles 2 (by decide)), hbuf,
      fwd_neuestens_wort a v 2 (by decide)]
  have l3 : loadByte s c (addrOff a 3) = some (wortByte v 3) := by
    unfold loadByte
    rw [if_pos (hles 3 (by decide)), hbuf,
      fwd_neuestens_wort a v 3 (by decide)]
  have l4 : loadByte s c (addrOff a 4) = some (wortByte v 4) := by
    unfold loadByte
    rw [if_pos (hles 4 (by decide)), hbuf,
      fwd_neuestens_wort a v 4 (by decide)]
  have l5 : loadByte s c (addrOff a 5) = some (wortByte v 5) := by
    unfold loadByte
    rw [if_pos (hles 5 (by decide)), hbuf,
      fwd_neuestens_wort a v 5 (by decide)]
  have l6 : loadByte s c (addrOff a 6) = some (wortByte v 6) := by
    unfold loadByte
    rw [if_pos (hles 6 (by decide)), hbuf,
      fwd_neuestens_wort a v 6 (by decide)]
  have l7 : loadByte s c (addrOff a 7) = some (wortByte v 7) := by
    unfold loadByte
    rw [if_pos (hles 7 (by decide)), hbuf,
      fwd_neuestens_wort a v 7 (by decide)]
  have hfun : (fun i : Fin 8 => if i.val = 0 then wortByte v 0
      else if i.val = 1 then wortByte v 1
      else if i.val = 2 then wortByte v 2
      else if i.val = 3 then wortByte v 3
      else if i.val = 4 then wortByte v 4
      else if i.val = 5 then wortByte v 5
      else if i.val = 6 then wortByte v 6
      else wortByte v 7) = (fun i => wortByte v i.val) := by
    funext i
    have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
        i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 := by
      have h8 : i.val < 8 := i.isLt
      omega
    rcases hc with h | h | h | h | h | h | h | h <;> simp [h]
  unfold stapelLadeWort
  rw [l0, l1, l2, l3, l4, l5, l6, l7]
  show some (bytesWort (fun i : Fin 8 => if i.val = 0 then wortByte v 0
    else if i.val = 1 then wortByte v 1
    else if i.val = 2 then wortByte v 2
    else if i.val = 3 then wortByte v 3
    else if i.val = 4 then wortByte v 4
    else if i.val = 5 then wortByte v 5
    else if i.val = 6 then wortByte v 6
    else wortByte v 7)) = some v
  rw [hfun, bytesWort_wortByte]

/-! ## 4. Foreign cores read canonical memory until drain.

  `FremdFrei` keeps every foreign buffer off the footprint, so each
  footprint byte misses (`fwd_neuestens_miss`) and the accepted
  unbuffered word agreement (`stapelLadeWort_still`) applies. -/

/-- FOREIGN CORE SEES CANONICAL MEMORY: with no foreign entry in the
    footprint, a foreign word load is the accepted `read64`. The
    exclusion premise feeds every byte miss, readability the memory
    bytes, inequality the foreign core. -/
theorem fwdFremd_liest_speicher (s : TSOZustand) (c d : Nat)
    (a : Adresse)
    (hff : FremdFrei s c a) (hd : d ≠ c)
    (hles : ∀ k, k < 8 → s.mem.lesbar (addrOff a k) = true) :
    stapelLadeWort s d a = read64 s.mem a := by
  have miss : ∀ k, k < 8 →
      neuestens (s.puffer d) (addrOff a k) = none := by
    intro k hk
    apply fwd_neuestens_miss
    intro e hm
    have hni : e.addr ∉ Fuss a := hff d hd e hm
    intro heq
    exact hni (heq ▸ fuss_mem_offset a k hk)
  exact stapelLadeWort_still s d a
    (miss 0 (by decide)) (miss 1 (by decide)) (miss 2 (by decide))
    (miss 3 (by decide)) (miss 4 (by decide)) (miss 5 (by decide))
    (miss 6 (by decide)) (miss 7 (by decide)) hles

/-- JOINT GUARD THEOREM: under one `WortGruppe` guard the owner
    core forwards the stored word while a foreign core reads canonical
    memory. The shape half feeds the owner leg, the exclusion half the
    foreign leg, readability both, inequality the foreign core. -/
theorem fwdWeiterleitung_und_fremd (s : TSOZustand) (c d : Nat)
    (a : Adresse) (v : Wort)
    (hgrp : WortGruppe s c a v)
    (hles : ∀ k, k < 8 → s.mem.lesbar (addrOff a k) = true)
    (hd : d ≠ c) :
    stapelLadeWort s c a = some v ∧
      stapelLadeWort s d a = read64 s.mem a := by
  obtain ⟨hbuf, hff⟩ := hgrp
  exact ⟨fwdWeiterleitung_generisch s c a v ⟨hbuf, hff⟩ hles,
    fwdFremd_liest_speicher s c d a hff hd hles⟩

/-! ## 5. Partial overlaps follow the byte rules.

  An older differing entry inside the footprint is shadowed by the
  young word bytes; a younger differing entry wins and mixes the
  word. Both are accepted `neuestens`/`loadByte` consequences. -/

/-- An older differing entry is shadowed: the young word byte wins. -/
theorem fwd_aelterer_beschattet (a : Adresse) (v : Wort)
    (bAlt : Byte) :
    neuestens ([⟨addrOff a 3, bAlt⟩] ++ wortEintraege a v)
      (addrOff a 3) = some (wortByte v 3) :=
  fwd_neuestens_angehaengt_list _ _ _ _
    (fwd_neuestens_wort a v 3 (by decide))

/-- A younger differing entry wins over the word byte. -/
theorem fwd_juengerer_gewinnt (a : Adresse) (v : Wort)
    (bNeu : Byte) :
    neuestens (wortEintraege a v ++ [⟨addrOff a 3, bNeu⟩])
      (addrOff a 3) = some bNeu :=
  neuestens_angehaengt _ _ _

/-- At load level: the shadowed older entry still forwards the young
    word byte. The buffer shape feeds the resolution, readability the
    load equation. -/
theorem fwd_aelterer_last_weiter (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort) (bAlt : Byte)
    (hbuf : s.puffer c =
      [⟨addrOff a 3, bAlt⟩] ++ wortEintraege a v)
    (hrd : s.mem.lesbar (addrOff a 3) = true) :
    loadByte s c (addrOff a 3) = some (wortByte v 3) := by
  unfold loadByte
  rw [if_pos hrd, hbuf, fwd_aelterer_beschattet a v bAlt]

/-- At load level: the younger differing entry wins the byte. The
    buffer shape feeds the resolution, readability the load. -/
theorem fwd_juengerer_last_neu (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort) (bNeu : Byte)
    (hbuf : s.puffer c =
      wortEintraege a v ++ [⟨addrOff a 3, bNeu⟩])
    (hrd : s.mem.lesbar (addrOff a 3) = true) :
    loadByte s c (addrOff a 3) = some bNeu := by
  unfold loadByte
  rw [if_pos hrd, hbuf, fwd_juengerer_gewinnt a v bNeu]

/-- Byte three survives reassembly: splitting then reassembling
    is the identity at every byte position, shown here for the
    overlap position. Bounds feed the arithmetic. -/
theorem fwd_wortByte_bytesWort3 (f : Fin 8 → Byte) :
    wortByte (bytesWort f) 3 = f 3 := by
  apply BitVec.eq_of_toNat_eq
  unfold wortByte bytesWort
  simp only [BitVec.toNat_ofNat]
  have e3 : (256 : Nat) ^ 3 = 16777216 := by decide
  rw [e3]
  have b0 : (f 0).toNat < 256 := (f 0).isLt
  have b1 : (f 1).toNat < 256 := (f 1).isLt
  have b2 : (f 2).toNat < 256 := (f 2).isLt
  have b3 : (f 3).toNat < 256 := (f 3).isLt
  have b4 : (f 4).toNat < 256 := (f 4).isLt
  have b5 : (f 5).toNat < 256 := (f 5).isLt
  have b6 : (f 6).toNat < 256 := (f 6).isLt
  have b7 : (f 7).toNat < 256 := (f 7).isLt
  omega

/-- A successful word load pins every observed byte: byte three
    of the loaded word is the loaded third byte. Each refusal branch
    fails the word match, so the hypothesis feeds every case. -/
theorem fwd_ladeWort_byte3 (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort)
    (h : stapelLadeWort s c a = some v) :
    loadByte s c (addrOff a 3) = some (wortByte v 3) := by
  unfold stapelLadeWort at h
  cases h0 : loadByte s c (addrOff a 0) with
  | none => rw [h0] at h; cases h
  | some b0 =>
    cases h1 : loadByte s c (addrOff a 1) with
    | none => rw [h0, h1] at h; cases h
    | some b1 =>
      cases h2 : loadByte s c (addrOff a 2) with
      | none => rw [h0, h1, h2] at h; cases h
      | some b2 =>
        cases h3 : loadByte s c (addrOff a 3) with
        | none => rw [h0, h1, h2, h3] at h; cases h
        | some b3 =>
          cases h4 : loadByte s c (addrOff a 4) with
          | none => rw [h0, h1, h2, h3, h4] at h; cases h
          | some b4 =>
            cases h5 : loadByte s c (addrOff a 5) with
            | none => rw [h0, h1, h2, h3, h4, h5] at h; cases h
            | some b5 =>
              cases h6 : loadByte s c (addrOff a 6) with
              | none => rw [h0, h1, h2, h3, h4, h5, h6] at h; cases h
              | some b6 =>
                cases h7 : loadByte s c (addrOff a 7) with
                | none => rw [h0, h1, h2, h3, h4, h5, h6, h7] at h; cases h
                | some b7 =>
                  rw [h0, h1, h2, h3, h4, h5, h6, h7] at h
                  simp only [Option.some.injEq] at h
                  have hc := congrArg (fun w => wortByte w 3) h
                  rw [fwd_wortByte_bytesWort3] at hc
                  have e3 : b3 = wortByte v 3 := hc
                  rw [e3]

/-- A younger differing entry mixes the word: the load is observably
    not the stored word. The equation feeds the byte extraction, the
    shape the winning byte, readability the load, inequality the
    observable difference. -/
theorem fwd_juengerer_mischt (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort) (bNeu : Byte)
    (hbuf : s.puffer c =
      wortEintraege a v ++ [⟨addrOff a 3, bNeu⟩])
    (hne : bNeu ≠ wortByte v 3)
    (hles : ∀ k, k < 8 → s.mem.lesbar (addrOff a k) = true) :
    stapelLadeWort s c a ≠ some v := by
  intro heq
  have lb := fwd_ladeWort_byte3 s c a v heq
  have lneu := fwd_juengerer_last_neu s c a v bNeu hbuf
    (hles 3 (by decide))
  rw [lb] at lneu
  simp only [Option.some.injEq] at lneu
  exact hne lneu.symm

/- CUTS:
    Skeleton only: events and the adapter are stated, nothing proved.
-/

#print axioms FwdEreignis
#print axioms fwdAdapter

end Gabbro.Grammatik.X86
