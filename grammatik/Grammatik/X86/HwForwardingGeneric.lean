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

/-! ## 6. Negative cases: misalignment and overlap never group.

  A word load one byte beside the stored word, a torn buffer and an
  overlapping older or younger entry all fail the `WortGruppe` guard
  structurally. Partial-shape refusals reuse the accepted
  `hwTeilwort_keine_gruppe` and
  `hwGruppe_verweigert_bei_fremdeintrag`; the misaligned and
  extra-entry shapes are proved here. -/

/-- Byte offsets compose (same two-rewrite proof as the accepted
    `Pipeline.addrOff_addrOff`; local so this leaf stays light). -/
theorem fwd_addrOff_add (a : Adresse) (i j : Nat) :
    addrOff (addrOff a i) j = addrOff a (i + j) := by
  unfold addrOff
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- Offset eight lies outside every eight-footprint. -/
theorem fwd_addrOff_acht_ne (a : Adresse) (k : Nat)
    (hk : k < 8) : addrOff a 8 ≠ addrOff a k := by
  intro heq
  have h2 := congrArg BitVec.toNat heq
  unfold addrOff at h2
  rw [BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
  have ha := a.isLt
  omega

/-- MISALIGNED LOAD NEVER GROUPS: the exact eight entries of a word
    at `a` are no group at `a + 1`. The hypothesis feeds the shape,
    the group the competing shape; the heads disagree by
    `addrOff_inj8`. -/
theorem fwd_fehlalign_keine_gruppe (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort)
    (hbuf : s.puffer c = wortEintraege a v) :
    ¬ WortGruppe s c (addrOff a 1) v := by
  intro hgrp
  obtain ⟨hbuf2, _⟩ := hgrp
  have heq : wortEintraege a v = wortEintraege (addrOff a 1) v := by
    rw [← hbuf, hbuf2]
  have hhead : addrOff a 0 = addrOff (addrOff a 1) 0 := by
    have hh := congrArg (fun l => l.head?) heq
    simpa [wortEintraege] using hh
  rw [addrOff_null (addrOff a 1)] at hhead
  have h01 : (0 : Nat) = 1 :=
    addrOff_inj8 (by decide) (by decide) hhead
  exact absurd h01 (by decide)

/-- An overlapping older entry breaks the group: nine entries are no
    exact eight. Lengths feed the contradiction. -/
theorem fwd_aelterer_keine_gruppe (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort) (bAlt : Byte)
    (hbuf : s.puffer c =
      [⟨addrOff a 3, bAlt⟩] ++ wortEintraege a v) :
    ¬ WortGruppe s c a v := by
  intro hgrp
  obtain ⟨hbuf2, _⟩ := hgrp
  rw [hbuf] at hbuf2
  have hlen := congrArg List.length hbuf2
  rw [List.length_append, wortEintraege_laenge] at hlen
  simp at hlen

/-- An overlapping younger entry breaks the group the same way. -/
theorem fwd_juengerer_keine_gruppe (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort) (bNeu : Byte)
    (hbuf : s.puffer c =
      wortEintraege a v ++ [⟨addrOff a 3, bNeu⟩]) :
    ¬ WortGruppe s c a v := by
  intro hgrp
  obtain ⟨hbuf2, _⟩ := hgrp
  rw [hbuf] at hbuf2
  have hlen := congrArg List.length hbuf2
  rw [List.length_append, wortEintraege_laenge] at hlen
  simp at hlen

/-- MISALIGNED LOAD MIXES, byte zero: the first byte of the
    shifted load forwards word byte one. The offset equation feeds
    the address, the shape the resolution, readability the load. -/
theorem fwd_fehlalign_byte0_weiter (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort)
    (hbuf : s.puffer c = wortEintraege a v)
    (hrd : s.mem.lesbar (addrOff (addrOff a 1) 0) = true) :
    loadByte s c (addrOff (addrOff a 1) 0) =
      some (wortByte v 1) := by
  have e0 : addrOff (addrOff a 1) 0 = addrOff a 1 := addrOff_null _
  rw [e0] at hrd ⊢
  unfold loadByte
  rw [if_pos hrd, hbuf, fwd_neuestens_wort a v 1 (by decide)]

/-- MISALIGNED LOAD MIXES, byte seven: the last byte of the shifted
    load falls outside the stored footprint and reads memory. The
    composition feeds the outside address, membership plus
    `fwd_addrOff_acht_ne` the miss, readability the memory byte. -/
theorem fwd_fehlalign_byte7_speicher (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort)
    (hbuf : s.puffer c = wortEintraege a v)
    (hrd : s.mem.lesbar (addrOff (addrOff a 1) 7) = true) :
    loadByte s c (addrOff (addrOff a 1) 7) =
      some (s.mem.bytes (addrOff (addrOff a 1) 7)) := by
  have e7 : addrOff (addrOff a 1) 7 = addrOff a 8 := by
    simp only [fwd_addrOff_add]
  have miss : neuestens (wortEintraege a v) (addrOff a 8) = none := by
    apply fwd_neuestens_miss
    intro e hm
    obtain ⟨j, hj8, he⟩ := wortEintraege_mem a v e hm
    subst he
    show addrOff a j ≠ addrOff a 8
    exact Ne.symm (fwd_addrOff_acht_ne a j hj8)
  unfold loadByte
  rw [if_pos hrd, hbuf, e7, miss]

/-! ## 7. Adapter duties: well-formedness, agreement, embedding.

  Stores are the accepted `hwWortAusgabe` (buffer agreement and
  memory silence reused); observations move no state; every buffered
  byte is one `HwSchritt.gibAus` event and every observed byte one
  `lade` event through the accepted byte embeddings. -/

/-- Every adapter step preserves well-formedness: stores ride
    `setTso`, observations are silent. -/
theorem fwdAdapter_wf (m : HwMaschine) (c : Nat) (ev : FwdEreignis)
    (m' : HwMaschine) (h : fwdAdapter.schritt m c ev = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases ev with
  | speichere a v =>
    have had : fwdAdapter.schritt m c (.speichere a v) =
        hwWortAusgabe m c a v := rfl
    rw [had] at h
    unfold hwWortAusgabe at h
    cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
    | none => rw [h1] at h; cases h
    | some s' =>
      rw [h1] at h
      cases h
      exact setTso_wf _ s' hwf
  | beobachte a =>
    cases hl : stapelLadeWort (tsoAnsicht m) c a with
    | none =>
      have hh : fwdAdapter.schritt m c (.beobachte a) = none := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = none
        rw [hl]
      rw [hh] at h
      cases h
    | some w =>
      have hh : fwdAdapter.schritt m c (.beobachte a) = some m := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = some m
        rw [hl]
      rw [hh] at h
      cases h
      exact hwf

/-- A buffered word store appends exactly the canonical eight
    entries: the accepted `hwWortAusgabe_puffer`, lifted. -/
theorem fwdSpeichere_puffer (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : fwdAdapter.schritt m c (.speichere a v) = some m') :
    m'.puffer c = m.puffer c ++ wortEintraege a v :=
  hwWortAusgabe_puffer m c a v m' h

/-- A buffered word store changes no shared-memory byte: the accepted
    `hwWortAusgabe_kein_speicher`, lifted. -/
theorem fwdSpeichere_kein_speicher (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : fwdAdapter.schritt m c (.speichere a v) = some m')
    (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x :=
  hwWortAusgabe_kein_speicher m c a v m' h x

/-- A successful observation moves no state. -/
theorem fwdBeobachte_still (m : HwMaschine) (c : Nat) (a : Adresse)
    (w : Wort) (h : stapelLadeWort (tsoAnsicht m) c a = some w) :
    fwdAdapter.schritt m c (.beobachte a) = some m := by
  show (match stapelLadeWort (tsoAnsicht m) c a with
    | some _ => some m | none => none) = _
  rw [h]

/-- A buffered word store reaches the machine in eight store-issue
    steps: the accepted `issueListe_stern` fold, lifted. -/
theorem fwdSpeichere_stern (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : fwdAdapter.schritt m c (.speichere a v) = some m') :
    HwStern m m' := by
  have had : fwdAdapter.schritt m c (.speichere a v) =
      hwWortAusgabe m c a v := rfl
  rw [had] at h
  unfold hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
  | none =>
    rw [h1] at h
    cases h
  | some s' =>
    rw [h1] at h
    cases h
    have hs := issueListe_stern m c (wortEintraege a v)
      (tsoAnsicht m) s' h1
    have hrefl : setTso m (tsoAnsicht m) = m := by
      cases m with
      | mk mem kerne puffer hw bereit => rfl
    rw [hrefl] at hs
    exact hs

/-- An observed word byte IS a machine load event: the accepted
    `stapelByte_beob`, lifted. The observation feeds the event. -/
theorem fwdByte_beob (m : HwMaschine) (c : Nat) (a : Adresse)
    (b : Byte) (h : loadByte (tsoAnsicht m) c a = some b) :
    HwSchritt m m (.leseBeob c a b) :=
  stapelByte_beob m c a b h

/-! ## 8. Planted refusals.

  A word store at an address whose first byte is not writable admits
  no issue; a word observation at an address whose first byte is not
  readable admits no load. Both fail loudly (`none`) through the
  accepted byte refusals. -/

/-- GUARD STORE REFUSES: without write permission at the first byte
    the whole word fold refuses. The denial fails the first byte
    issue, the fold shape carries it. -/
theorem fwdSpeichere_wache (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort)
    (hguard : m.mem.schreibbar (addrOff a 0) = false) :
    fwdAdapter.schritt m c (.speichere a v) = none := by
  have had : fwdAdapter.schritt m c (.speichere a v) =
      hwWortAusgabe m c a v := rfl
  rw [had]
  unfold hwWortAusgabe
  have hfirst : issueByte (tsoAnsicht m) c (addrOff a 0)
      (wortByte v 0) = none :=
    issue_verweigert _ _ _ _
      (by simpa [addrOff_null, tsoAnsicht_speicher] using hguard)
  have hcons : wortEintraege a v =
      ⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩,
       ⟨addrOff a 4, wortByte v 4⟩,
       ⟨addrOff a 5, wortByte v 5⟩,
       ⟨addrOff a 6, wortByte v 6⟩,
       ⟨addrOff a 7, wortByte v 7⟩] := rfl
  have hfold : issueListe (tsoAnsicht m) c
      (⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩,
       ⟨addrOff a 4, wortByte v 4⟩,
       ⟨addrOff a 5, wortByte v 5⟩,
       ⟨addrOff a 6, wortByte v 6⟩,
       ⟨addrOff a 7, wortByte v 7⟩]) = none :=
    issueListe_cons_none _ _ _ _ hfirst
  rw [hcons, hfold]

/-- DARK OBSERVATION REFUSES: without read permission at the first
    byte the whole word observation refuses. The denial fails the
    first byte load. -/
theorem fwdBeobachte_dunkel (s : TSOZustand) (c : Nat) (a : Adresse)
    (hguard : s.mem.lesbar (addrOff a 0) = false) :
    stapelLadeWort s c a = none :=
  stapelPop_unlesbar s c a hguard

/-! ## 9. Joint witness: two cores, store, forward, drain.

  Core 0 buffers word 42 at address 8184 through the family adapter;
  core 0 forwards it while core 1 still reads zero; after core 0
  drains, shared memory holds 42 for both cores. The drain observably
  changes memory (0 becomes 42). Beside it stand the planted guard,
  dark-read, misaligned and overlap refusals. -/

/-- Witness bytes: zeroed everywhere. -/
def witFwdBytes (_ : Adresse) : Byte := BitVec.ofNat 8 0

/-- Witness data permission: sixteen bytes at 8176. -/
def witFwdDaten (a : Adresse) : Bool :=
  decide (8176 ≤ a.toNat ∧ a.toNat < 8192)

/-- Witness code permission: fifteen bytes at 4096. -/
def witFwdCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4111)

/-- Witness shared memory: zeroed bytes, data RW, code X-only. -/
def witFwdMem : Speicher :=
  { bytes := witFwdBytes, lesbar := witFwdDaten,
    schreibbar := witFwdDaten, ausfuehrbar := witFwdCode }

/-- Witness core-0 registers: top at 8192, `rax` holding 9. -/
def witFwdReg0 : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 8192
  else if q = Register.rax then BitVec.ofNat 64 9
  else BitVec.ofNat 64 0

/-- Witness core-1 registers: top at 8184. -/
def witFwdReg1 : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 8184
  else BitVec.ofNat 64 0

/-- Witness core data: core 0 runs at 4096, core 1 idles at 8192. -/
def witFwdKern : Nat → HwKern
  | 0 => ⟨witFwdReg0, zeugeFlags, BitVec.ofNat 64 4096,
      (fun _ => BitVec.ofNat 128 0), kontextReset⟩
  | _ => ⟨witFwdReg1, zeugeFlags, BitVec.ofNat 64 8192,
      (fun _ => BitVec.ofNat 128 0), kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state. -/
def witFwdM0 : HwMaschine :=
  ⟨witFwdMem, witFwdKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Witness word address. -/
def witFwdAdr : Adresse := BitVec.ofNat 64 8184

/-- Witness stored word. -/
def witFwdWort : Wort := BitVec.ofNat 64 42

/-- Witness zero word. -/
def witFwdNull : Wort := BitVec.ofNat 64 0

/-- Witness pushed machine: core 0 carries the exact eight entries,
    core 1 is empty. The adapter reaches exactly this state. -/
def witFwdM1 : HwMaschine :=
  setTso witFwdM0 ⟨witFwdMem, fun d =>
    if d = 0 then wortEintraege witFwdAdr witFwdWort else []⟩

/-- The witness machine is well-formed: full silicon admits all. -/
theorem witFwd_wf : HwWf witFwdM0 := by
  intro c f _
  cases f <;> rfl

/-- Core 0 stores word 42 at the witness address through the
    family adapter. -/
def witFwdPush : Option HwMaschine :=
  fwdAdapter.schritt witFwdM0 0 (.speichere witFwdAdr witFwdWort)

/-- Buffered entry count on core 0 after the store. -/
def witFwdBufLen : Option Nat :=
  match witFwdPush with
  | some m1 => some (m1.puffer 0).length
  | none => none

/-- Shared-memory byte at the address right after the store. -/
def witFwdMemStill : Option Byte :=
  match witFwdPush with
  | some m1 => some (m1.mem.bytes witFwdAdr)
  | none => none

/-- Core 0 observes its own buffered word (forwarding). -/
def witFwdLoadEigen : Option (Option Wort) :=
  match witFwdPush with
  | some m1 => some (stapelLadeWort (tsoAnsicht m1) 0 witFwdAdr)
  | none => none

/-- Core 1 observes the old word (no foreign forwarding). -/
def witFwdLoadFremd : Option (Option Wort) :=
  match witFwdPush with
  | some m1 => some (stapelLadeWort (tsoAnsicht m1) 1 witFwdAdr)
  | none => none

/-- Core 0 drains its oldest entry, eight times chained. -/
def witFwdD1 : Option TSOZustand :=
  match witFwdPush with
  | some m1 => flushKern (tsoAnsicht m1) 0
  | none => none

def witFwdD2 : Option TSOZustand :=
  match witFwdD1 with
  | some s => flushKern s 0
  | none => none

def witFwdD3 : Option TSOZustand :=
  match witFwdD2 with
  | some s => flushKern s 0
  | none => none

def witFwdD4 : Option TSOZustand :=
  match witFwdD3 with
  | some s => flushKern s 0
  | none => none

def witFwdD5 : Option TSOZustand :=
  match witFwdD4 with
  | some s => flushKern s 0
  | none => none

def witFwdD6 : Option TSOZustand :=
  match witFwdD5 with
  | some s => flushKern s 0
  | none => none

def witFwdD7 : Option TSOZustand :=
  match witFwdD6 with
  | some s => flushKern s 0
  | none => none

def witFwdD8 : Option TSOZustand :=
  match witFwdD7 with
  | some s => flushKern s 0
  | none => none

/-- Shared memory after the full drain. -/
def witFwdNachFlush : Option Speicher :=
  match witFwdD8 with
  | some s => some s.mem
  | none => none

/-- The word read from shared memory after the drain. -/
def witFwdNachRead : Option (Option Wort) :=
  match witFwdNachFlush with
  | some mem => some (read64 mem witFwdAdr)
  | none => none

/-- Core 1 reads the drained word from shared memory. -/
def witFwdFremdNachFlush : Option (Option Wort) :=
  match witFwdD8 with
  | some s => some (stapelLadeWort s 1 witFwdAdr)
  | none => none

/-! ## 10. Witness facts: the reached run forwards, then drains.

  The adapter run exhibits exactly the generic behaviour: eight
  buffered entries, owner-only forwarding, foreign zero, and a drain
  changing shared memory 0 to 42 observed from both cores. The
  generic theorems fire on the pushed shape beside it. -/

/-- The store buffers exactly eight entries on core 0. -/
theorem witFwd_puffer8 : witFwdBufLen = some 8 := by
  decide

/-- The store leaves the shared address byte at zero. -/
theorem witFwd_mem_still :
    witFwdMemStill = some (BitVec.ofNat 8 0) := by
  decide

/-- Forwarding on the reached run: core 0 reads its own word 42. -/
theorem witFwd_weiterleitung :
    witFwdLoadEigen = some (some witFwdWort) := by
  decide

/-- No foreign forwarding on the reached run: core 1 reads zero. -/
theorem witFwd_fremd_alt :
    witFwdLoadFremd = some (some witFwdNull) := by
  decide

/-- The drain changes shared memory: the address reads 42. -/
theorem witFwd_spuelung_aendert_speicher :
    witFwdNachRead = some (some witFwdWort) := by
  decide

/-- After the drain core 1 observes the new word. -/
theorem witFwd_fremd_neu :
    witFwdFremdNachFlush = some (some witFwdWort) := by
  decide

/-- The address starts zeroed: the run really changes memory. -/
theorem witFwd_anfang_null :
    witFwdMem.bytes witFwdAdr = BitVec.ofNat 8 0 := by
  decide

/-- The pushed buffer carries exactly the word entries. -/
theorem witFwd_pufferform :
    (tsoAnsicht witFwdM1).puffer 0 =
      wortEintraege witFwdAdr witFwdWort := by
  decide

/-- No foreign entry touches the footprint on the witness. -/
theorem witFwd_fremdfrei :
    FremdFrei (tsoAnsicht witFwdM1) 0 witFwdAdr := by
  intro d hd e hm
  have hbuf : (tsoAnsicht witFwdM1).puffer d = [] := by
    simp only [tsoAnsicht, witFwdM1, setTso]
    rw [if_neg hd]
  rw [hbuf] at hm
  cases hm

/-- The pushed state satisfies the group guard. -/
theorem witFwd_gruppe :
    WortGruppe (tsoAnsicht witFwdM1) 0 witFwdAdr witFwdWort :=
  ⟨witFwd_pufferform, witFwd_fremdfrei⟩

/-- Every footprint byte is readable on the witness. -/
theorem witFwd_lesbar_all (k : Nat) (hk : k < 8) :
    (tsoAnsicht witFwdM1).mem.lesbar (addrOff witFwdAdr k) = true := by
  have haddr : (addrOff witFwdAdr k).toNat = 8184 + k := by
    unfold addrOff witFwdAdr
    rw [BitVec.toNat_add]
    have e1 : (BitVec.ofNat 64 8184).toNat = 8184 := by
      rw [BitVec.toNat_ofNat]
    have e2 : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2]
    exact Nat.mod_eq_of_lt (by omega)
  show witFwdDaten (addrOff witFwdAdr k) = true
  unfold witFwdDaten
  rw [decide_eq_true_eq]
  omega

/-- The generic owner-forwarding fires on the pushed shape. -/
theorem witFwd_generisch_eigen :
    stapelLadeWort (tsoAnsicht witFwdM1) 0 witFwdAdr =
      some witFwdWort :=
  fwdWeiterleitung_generisch _ _ _ _ witFwd_gruppe witFwd_lesbar_all

/-- The generic foreign leg fires on the pushed shape. -/
theorem witFwd_generisch_fremd :
    stapelLadeWort (tsoAnsicht witFwdM1) 1 witFwdAdr =
      read64 (tsoAnsicht witFwdM1).mem witFwdAdr :=
  (fwdWeiterleitung_und_fremd _ _ _ _ _ witFwd_gruppe
    witFwd_lesbar_all (by decide)).2

/-! ## 11. Refusal witnesses.

  Guard memory denies the store, dark memory denies the observation,
  and the shifted and overlapped buffers never group -- each through
  the generic refusal it plants. -/

/-- Guard witness memory: nothing is writable. -/
def witFwdGuardMem : Speicher :=
  { bytes := witFwdBytes, lesbar := witFwdDaten,
    schreibbar := fun _ => false, ausfuehrbar := witFwdCode }

/-- Guard witness machine: same cores, write-protected memory. -/
def witFwdGuardM0 : HwMaschine :=
  ⟨witFwdGuardMem, witFwdKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩

/-- Dark witness memory: nothing is readable. -/
def witFwdDarkMem : Speicher :=
  { bytes := witFwdBytes, lesbar := fun _ => false,
    schreibbar := witFwdDaten, ausfuehrbar := witFwdCode }

/-- Older-overlap witness state: a differing older byte before the
    word entries. -/
def witFwdAlt : TSOZustand :=
  ⟨witFwdMem, fun d => if d = 0
    then [⟨addrOff witFwdAdr 3, BitVec.ofNat 8 1⟩] ++
      wortEintraege witFwdAdr witFwdWort
    else []⟩

/-- Younger-overlap witness state: a differing younger byte after
    the word entries (word byte three of 42 is zero, the younger
    byte is one). -/
def witFwdJung : TSOZustand :=
  ⟨witFwdMem, fun d => if d = 0
    then wortEintraege witFwdAdr witFwdWort ++
      [⟨addrOff witFwdAdr 3, BitVec.ofNat 8 1⟩]
    else []⟩

/-- The guard denies the first footprint byte. -/
theorem witFwd_guard_dicht :
    witFwdGuardM0.mem.schreibbar (addrOff witFwdAdr 0) = false := by
  decide

/-- Guard store refuses on the witness, through the generic refusal. -/
theorem witFwd_guard_speichere_verweigert :
    fwdAdapter.schritt witFwdGuardM0 0
      (.speichere witFwdAdr witFwdWort) = none :=
  fwdSpeichere_wache _ _ _ _ witFwd_guard_dicht

/-- The dark page denies the first footprint byte. -/
theorem witFwd_dark_dicht :
    witFwdDarkMem.lesbar (addrOff witFwdAdr 0) = false := by
  decide

/-- Dark observation refuses on the witness. -/
theorem witFwd_dark_beob_verweigert :
    stapelLadeWort ⟨witFwdDarkMem, fun _ => []⟩ 0 witFwdAdr = none :=
  fwdBeobachte_dunkel _ _ _ witFwd_dark_dicht

/-- The shifted load address never groups on the pushed shape. -/
theorem witFwd_fehlalign_verweigert :
    ¬ WortGruppe (tsoAnsicht witFwdM1) 0 (addrOff witFwdAdr 1)
      witFwdWort :=
  fwd_fehlalign_keine_gruppe _ _ _ _ witFwd_pufferform

/-- The older-overlap buffer shape. -/
theorem witFwd_alt_form : witFwdAlt.puffer 0 =
    [⟨addrOff witFwdAdr 3, BitVec.ofNat 8 1⟩] ++
      wortEintraege witFwdAdr witFwdWort := by
  decide

/-- The older overlap never groups. -/
theorem witFwd_aelterer_verweigert :
    ¬ WortGruppe witFwdAlt 0 witFwdAdr witFwdWort :=
  fwd_aelterer_keine_gruppe _ _ _ _ _ witFwd_alt_form

/-- The younger-overlap buffer shape. -/
theorem witFwd_jung_form : witFwdJung.puffer 0 =
    wortEintraege witFwdAdr witFwdWort ++
      [⟨addrOff witFwdAdr 3, BitVec.ofNat 8 1⟩] := by
  decide

/-- The younger overlap never groups. -/
theorem witFwd_juengerer_verweigert :
    ¬ WortGruppe witFwdJung 0 witFwdAdr witFwdWort :=
  fwd_juengerer_keine_gruppe _ _ _ _ _ witFwd_jung_form

/-- Witness memory readability in `∀` form for the overlap state. -/
theorem witFwdMem_lesbar_all (k : Nat) (hk : k < 8) :
    witFwdMem.lesbar (addrOff witFwdAdr k) = true :=
  witFwd_lesbar_all k hk

/-- The younger byte mixes the word on the witness: the load is
    observably not 42. -/
theorem witFwd_juengerer_mischt_beispiel :
    stapelLadeWort witFwdJung 0 witFwdAdr ≠ some witFwdWort :=
  fwd_juengerer_mischt _ _ _ _ _ witFwd_jung_form (by decide)
    (fun k hk => witFwdMem_lesbar_all k hk)

/-! ## 12. Joint witness.

  Every duty premise holds jointly on a reached, non-degenerate
  two-core run: the group guard with readability, owner-only
  forwarding of 42, foreign zero, a drain changing shared memory 0
  to 42 observed from both cores -- beside the planted guard,
  dark-read, misaligned and overlap refusals and the mixed-word
  observation. -/

/-- JOINT WITNESS. -/
theorem fwdTso_zeuge :
    HwWf witFwdM0 ∧
      WortGruppe (tsoAnsicht witFwdM1) 0 witFwdAdr witFwdWort ∧
      (∀ k, k < 8 →
        (tsoAnsicht witFwdM1).mem.lesbar (addrOff witFwdAdr k) =
          true) ∧
      (1 : Nat) ≠ 0 ∧
      witFwdBufLen = some 8 ∧
      witFwdMemStill = some (BitVec.ofNat 8 0) ∧
      witFwdLoadEigen = some (some witFwdWort) ∧
      witFwdLoadFremd = some (some witFwdNull) ∧
      witFwdNachRead = some (some witFwdWort) ∧
      witFwdFremdNachFlush = some (some witFwdWort) ∧
      witFwdMem.bytes witFwdAdr = BitVec.ofNat 8 0 ∧
      stapelLadeWort (tsoAnsicht witFwdM1) 0 witFwdAdr =
        some witFwdWort ∧
      stapelLadeWort (tsoAnsicht witFwdM1) 1 witFwdAdr =
        read64 (tsoAnsicht witFwdM1).mem witFwdAdr ∧
      witFwdGuardM0.mem.schreibbar (addrOff witFwdAdr 0) = false ∧
      fwdAdapter.schritt witFwdGuardM0 0
        (.speichere witFwdAdr witFwdWort) = none ∧
      witFwdDarkMem.lesbar (addrOff witFwdAdr 0) = false ∧
      stapelLadeWort ⟨witFwdDarkMem, fun _ => []⟩ 0 witFwdAdr =
        none ∧
      ¬ WortGruppe (tsoAnsicht witFwdM1) 0 (addrOff witFwdAdr 1)
        witFwdWort ∧
      ¬ WortGruppe witFwdAlt 0 witFwdAdr witFwdWort ∧
      ¬ WortGruppe witFwdJung 0 witFwdAdr witFwdWort ∧
      stapelLadeWort witFwdJung 0 witFwdAdr ≠ some witFwdWort := by
  exact ⟨witFwd_wf, witFwd_gruppe, witFwd_lesbar_all, by decide,
    witFwd_puffer8, witFwd_mem_still, witFwd_weiterleitung,
    witFwd_fremd_alt, witFwd_spuelung_aendert_speicher,
    witFwd_fremd_neu, witFwd_anfang_null, witFwd_generisch_eigen,
    witFwd_generisch_fremd, witFwd_guard_dicht,
    witFwd_guard_speichere_verweigert, witFwd_dark_dicht,
    witFwd_dark_beob_verweigert, witFwd_fehlalign_verweigert,
    witFwd_aelterer_verweigert, witFwd_juengerer_verweigert,
    witFwd_juengerer_mischt_beispiel⟩

/- CUTS:
    Proved here (all over the REUSED canonical `Zustand`/`Speicher`
    vocabulary, the accepted `HwMaschine`/`HwSchritt`/`HwWf`,
    `issueByte`/`loadByte`/`flushKern`, `wortEintraege`,
    `WortGruppe`/`FremdFrei`, `hwWortAusgabe`, `stapelLadeWort`,
    `read64` and `Fuss` -- no new machine, no new decoder row, no
    new instruction, no source claim):
    - family events `FwdEreignis` and the adapter `fwdAdapter`
      (stores buffer a word, observations read one without moving
      state); every adapter step preserves `HwWf`
      (`fwdAdapter_wf`);
    - buffer agreement: stores append exactly the canonical eight
      entries (`fwdSpeichere_puffer`) and change no shared-memory
      byte (`fwdSpeichere_kein_speicher`); observations move no
      state (`fwdBeobachte_still`);
    - exact byte embedding: a folded word store is eight
      `HwSchritt.gibAus` events (`fwdSpeichere_stern` over the
      `HwStern` closure), every observed byte one `lade` event
      (`fwdByte_beob`);
    - GENERIC WORD FORWARDING (`fwdWeiterleitung_generisch`): under
      the `WortGruppe` guard a same-core word load returns the
      stored word, for every core, address and buffer content;
      per-byte resolution (`fwd_neuestens_wort` via `addrOff_ne8`),
      reassembly (`bytesWort_wortByte`);
    - foreign cores read canonical memory until drain
      (`fwdFremd_liest_speicher` via `fwd_neuestens_miss` and the
      accepted `stapelLadeWort_still`); joint guard theorem
      (`fwdWeiterleitung_und_fremd`) using both guard halves;
    - partial overlaps follow the byte rules: an older differing
      entry is shadowed (`fwd_aelterer_beschattet`,
      `fwd_aelterer_last_weiter`), a younger differing entry wins
      (`fwd_juengerer_gewinnt`, `fwd_juengerer_last_neu`) and mixes
      the word (`fwd_juengerer_mischt` via byte-three extraction
      `fwd_ladeWort_byte3` and `fwd_wortByte_bytesWort3`);
    - negative cases: misaligned loads never group
      (`fwd_fehlalign_keine_gruppe` via `addrOff_inj8`), older and
      younger overlaps never group (`fwd_aelterer_keine_gruppe`,
      `fwd_juengerer_keine_gruppe` by length); the shifted load
      mixes forwarded and memory bytes (`fwd_fehlalign_byte0_weiter`,
      `fwd_fehlalign_byte7_speicher` via `fwd_addrOff_add` and
      `fwd_addrOff_acht_ne`); partial-shape and foreign-footprint
      refusals reuse `hwTeilwort_keine_gruppe` and
      `hwGruppe_verweigert_bei_fremdeintrag` (cited);
    - planted refusals: guard stores (`fwdSpeichere_wache` via
      `issueListe_cons_none`) and dark observations
      (`fwdBeobachte_dunkel` via `stapelPop_unlesbar`);
    - joint non-degenerate two-core witness (`fwdTso_zeuge`):
      adapter store of 42 with owner-only forwarding, foreign
      zero, eight-drain changing shared memory 0 to 42 observed
      from both cores, the generic theorems firing on the pushed
      shape, beside guard, dark-read, misaligned and overlap
      refusals and the mixed-word observation.
    NOT proved here, and not claimed:
    - No silicon correspondence: encodings are the accepted
      canonical subsets with self-consistency only, not x86 truth.
      Alignment carries no gate in this model (the byte drain is
      alignment-agnostic by `WortGruppe` design); the misaligned
      case is proved as group refusal plus byte mixing, not as a
      hardware fault. The Intel SDM extracts supplied to the clone
      were consulted for ordering (TSO store-issue FIFO,
      youngest-own forwarding, no multi-byte atomicity); they are
      provenance, not proofs.
    - No drain-equals-`write64` theorem: the drained word is
      witnessed (`witFwd_spuelung_aendert_speicher`); the generic
      eight-flush induction stays with `wort_gruppe_liest_zurueck`
      (cited, `DrainSpur`-based).
    - No LOCK/RMW, fault, interrupt, addressed/SIB, FP-control or
      SIMD path; no source/IR/ABI/loader/entry/budget link; no
      target-to-W/GX simulation; no whole-word atomicity beyond
      `WortGruppe`-guarded byte drains.
    - `fwd_addrOff_add` mirrors the accepted
      `Pipeline.addrOff_addrOff` with the same two-rewrite proof,
      kept local so this leaf stays light; it states arithmetic
      only, no model.
-/

#print axioms FwdEreignis
#print axioms fwdAdapter
#print axioms fwd_neuestens_miss
#print axioms fwd_neuestens_angehaengt_list
#print axioms fwd_neuestens_wort
#print axioms fwdWeiterleitung_generisch
#print axioms fwdFremd_liest_speicher
#print axioms fwdWeiterleitung_und_fremd
#print axioms fwd_aelterer_beschattet
#print axioms fwd_juengerer_gewinnt
#print axioms fwd_aelterer_last_weiter
#print axioms fwd_juengerer_last_neu
#print axioms fwd_wortByte_bytesWort3
#print axioms fwd_ladeWort_byte3
#print axioms fwd_juengerer_mischt
#print axioms fwd_addrOff_add
#print axioms fwd_addrOff_acht_ne
#print axioms fwd_fehlalign_keine_gruppe
#print axioms fwd_aelterer_keine_gruppe
#print axioms fwd_juengerer_keine_gruppe
#print axioms fwd_fehlalign_byte0_weiter
#print axioms fwd_fehlalign_byte7_speicher
#print axioms fwdAdapter_wf
#print axioms fwdSpeichere_puffer
#print axioms fwdSpeichere_kein_speicher
#print axioms fwdBeobachte_still
#print axioms fwdSpeichere_stern
#print axioms fwdByte_beob
#print axioms fwdSpeichere_wache
#print axioms fwdBeobachte_dunkel
#print axioms witFwd_gruppe
#print axioms witFwd_lesbar_all
#print axioms witFwd_weiterleitung
#print axioms witFwd_generisch_eigen
#print axioms witFwd_generisch_fremd
#print axioms fwdTso_zeuge

end Gabbro.Grammatik.X86
