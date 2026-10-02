/-
  File:      Grammatik/X86/ISARelax.lean
  Subject:   Branch relaxation and cross-block selection over the unified
             instruction set: a program with SYMBOLIC branch targets (labels
             are instruction indices) is laid out from encoded lengths, every
             jump is resolved to rel32 or rel8 by the bounded DESIGN-§2B
             relaxation (start all wide, at most `N` compression rounds,
             narrow a branch only if the WHOLE resulting layout validates),
             and the resolved byte image, laid out in executable memory, is
             proved to run under `laufBytesI` exactly as the labelled
             program's semantics (every jump goes to the address of its
             label). This DERIVES the trace premise that `laufBytesI_spur`
             assumes for programs with control flow (loops, branches).

  Reused, not redefined: `Instr`/`stepI`/`canonI`/`encodeI`/`kanonischI`
  (`ISA.lean`), `byteschrittI`/`laufBytesI`/`byteschrittI_kanonisch`/
  `progBytes`/`CodeAt`/`WX`/`stepI_rahmen`/`faelltDurchI`/`geholt_codeAt`/
  `codeAt_links`/`codeAt_rechts`/`codeAt_schutz`/`wx_schutz`/`ausgangVon`
  (`ISAExecution.lean`), the jump step equations `schritt_jump32`,
  `schritt_jumpIf32_*` (`Ausfuehrung.lean`) and `schrittC_jump8`,
  `schrittC_jumpIf8_*`, `rel8FromWort`/`passtRel8Wort` (`CompactForms.lean`),
  and the decided selector `sel`/`Wahl`/`wahl_korrekt`/`Gl`/`EndGl`/`OptRel`
  (`ISASelect.lean`). The pilot `jump32`/`jumpIf32` and compact
  `jump8`/`jumpIf8` are the ONLY jump encodings; no new instruction, step or
  decoder exists here.

  Contents:
    §1 labelled programs `LInstr`, encoded lengths, the layout `off`/`adrL`,
       resolution `aufloesen`, the decided validator `layoutOk`, the image
       `bild`;
    §2 bounded relaxation `relax` and `relax_ok` (the answer validates);
    §3 the labelled semantics `stepL`/`laufL` (jumps go to label addresses);
    §4 THE LAYOUT THEOREM WITH CONTROL FLOW `laufBytesL`: the byte run of
       the image IS the labelled run, outcome for outcome;
    §5 basic blocks, block semantics `laufB`, the flattening `flach` and the
       simulation `laufB_flach`;
    §6 per-block selection `waehleB` (`sel` on each block body, labels kept)
       and its agreement theorem `waehleB_korrekt`;
    §7 the combined statement `waehleB_relax_bytes`: select per block,
       flatten, relax, lay out; the byte run agrees with the ORIGINAL
       block program outside the scratch list, at the same block label.
  Witnesses and poison probes: `ISARelaxWitnesses.lean`.
-/
import Grammatik.X86.ISASelect

namespace Gabbro.Grammatik.X86

/-! ## 1. Labelled programs, layout, resolution, validation. -/

/-- A labelled instruction: an ordinary unified instruction (must fall
    through), or a jump whose target is a LABEL (an instruction index;
    the index equal to the program length is the program end). -/
inductive LInstr where
  | op (i : Instr)
  | jmp (ziel : Nat)
  | jcc (c : Bedingung) (ziel : Nat)
  deriving DecidableEq, Repr

/-- A labelled program. -/
abbrev LProg := List LInstr

/-- Encoded length of a labelled instruction at a chosen width
    (`kurz = true`: rel8, 2 bytes; otherwise rel32, 5 or 6 bytes). -/
def lenL (kurz : Bool) : LInstr → Nat
  | .op i => (encodeI i).length
  | .jmp _ => if kurz then 2 else 5
  | .jcc _ _ => if kurz then 2 else 6

/-- Encoded length of instruction `k` under the width vector `ws`
    (0 past the end). -/
def lenAt (ws : List Bool) (p : LProg) (k : Nat) : Nat :=
  match p[k]? with
  | some li => lenL (ws.getD k false) li
  | none => 0

/-- Byte offset of instruction `k` (and of label `k`): the sum of the
    encoded lengths before it. -/
def off (ws : List Bool) (p : LProg) (k : Nat) : Nat :=
  ((List.range k).map (lenAt ws p)).sum

theorem off_null (ws : List Bool) (p : LProg) : off ws p 0 = 0 := rfl

theorem off_succ (ws : List Bool) (p : LProg) (k : Nat) :
    off ws p (k + 1) = off ws p k + lenAt ws p k := by
  simp [off, List.range_succ]

/-- The address of label `k` when the program starts at `base`. -/
def adrL (base : Adresse) (ws : List Bool) (p : LProg) (k : Nat) : Adresse :=
  ripNach base (off ws p k)

/-- The displacement WORD from the end of instruction `k` (length `l`) to
    label `z`: recomputed from the layout, never reused across widths. -/
def dispW (ws : List Bool) (p : LProg) (k z l : Nat) : Wort :=
  BitVec.ofNat 64 (off ws p z) - BitVec.ofNat 64 (off ws p k + l)

/-- rel32 admission: the word round-trips through a sign-extended 32-bit
    displacement (the rel32 analogue of `CompactForms.passtRel8Wort`). -/
def passtRel32Wort (w : Wort) : Bool :=
  decide (dispWort (BitVec.ofNat 32 w.toNat) = w)

/-- Resolution of instruction `k`: ordinary instructions unchanged, jumps
    to the existing pilot rel32 or compact rel8 forms at the displacement
    the layout computes. -/
def aufloesen (ws : List Bool) (p : LProg) (k : Nat) : LInstr → Instr
  | .op i => i
  | .jmp z =>
    if ws.getD k false then .compact (.jump8 (rel8FromWort (dispW ws p k z 2)))
    else .pilot (.jump32 (BitVec.ofNat 32 (dispW ws p k z 5).toNat))
  | .jcc c z =>
    if ws.getD k false then .compact (.jumpIf8 c (rel8FromWort (dispW ws p k z 2)))
    else .pilot (.jumpIf32 c (BitVec.ofNat 32 (dispW ws p k z 6).toNat))

/-- Resolution by index (a dummy past the end, never reached). -/
def aufloesenAt (ws : List Bool) (p : LProg) (k : Nat) : Instr :=
  match p[k]? with
  | some li => aufloesen ws p k li
  | none => .pilot .ret

/-- The decided row check: ordinary rows are canonical and fall through;
    a jump's label lies inside the program (or at its end) and its
    displacement fits the chosen width. -/
def zeileOk (ws : List Bool) (p : LProg) (k : Nat) : LInstr → Bool
  | .op i => kanonischI i && faelltDurchI i
  | .jmp z => decide (z ≤ p.length) &&
      (if ws.getD k false then passtRel8Wort (dispW ws p k z 2)
       else passtRel32Wort (dispW ws p k z 5))
  | .jcc _ z => decide (z ≤ p.length) &&
      (if ws.getD k false then passtRel8Wort (dispW ws p k z 2)
       else passtRel32Wort (dispW ws p k z 6))

/-- THE LAYOUT VALIDATOR: every row passes `zeileOk` under `ws`. -/
def layoutOk (ws : List Bool) (p : LProg) : Bool :=
  (List.range p.length).all (fun k =>
    match p[k]? with
    | some li => zeileOk ws p k li
    | none => true)

theorem layoutOk_zeile (ws : List Bool) (p : LProg) (h : layoutOk ws p = true)
    (k : Nat) (li : LInstr) (hk : p[k]? = some li) : zeileOk ws p k li = true := by
  have hlt : k < p.length := by
    rcases Nat.lt_or_ge k p.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at hk; cases hk
  simp only [layoutOk, List.all_eq_true, List.mem_range] at h
  have := h k hlt
  rw [hk] at this
  exact this

/-- The resolved instruction list. -/
def aufgeloest (ws : List Bool) (p : LProg) : List Instr :=
  (List.range p.length).map (aufloesenAt ws p)

/-- The byte image: the resolved instructions back to back. -/
def bild (ws : List Bool) (p : LProg) : List Byte :=
  progBytes (aufgeloest ws p)

/-- A forged-image check: the given bytes are exactly the image of a
    validated layout. -/
def bildOk (ws : List Bool) (p : LProg) (bs : List Byte) : Bool :=
  layoutOk ws p && (bs == bild ws p)

theorem progBytes_append (xs ys : List Instr) :
    progBytes (xs ++ ys) = progBytes xs ++ progBytes ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [progBytes, ih]

theorem jump32_laenge (d : BitVec 32) : (encodeI (.pilot (.jump32 d))).length = 5 := by
  simp [encodeI, encode, length_leBytes32]

theorem jumpIf32_laenge (c : Bedingung) (d : BitVec 32) :
    (encodeI (.pilot (.jumpIf32 c d))).length = 6 := by
  simp [encodeI, encode, length_leBytes32]

/-- The resolved instruction has exactly the length the layout assumed. -/
theorem aufloesen_laenge (ws : List Bool) (p : LProg) (k : Nat) (li : LInstr) :
    (encodeI (aufloesen ws p k li)).length = lenL (ws.getD k false) li := by
  cases li with
  | op i => rfl
  | jmp z =>
    simp only [aufloesen, lenL]
    split
    · rfl
    · exact jump32_laenge _
  | jcc c z =>
    simp only [aufloesen, lenL]
    split
    · rfl
    · exact jumpIf32_laenge _ _

theorem aufloesenAt_laenge (ws : List Bool) (p : LProg) (k : Nat) (hk : k < p.length) :
    (encodeI (aufloesenAt ws p k)).length = lenAt ws p k := by
  unfold aufloesenAt lenAt
  rw [List.getElem?_eq_getElem hk]
  exact aufloesen_laenge ws p k _

/-- The layout offset IS the byte length of the image prefix. -/
theorem off_bild (ws : List Bool) (p : LProg) (k : Nat) (hk : k ≤ p.length) :
    off ws p k = (progBytes ((List.range k).map (aufloesenAt ws p))).length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [off_succ, ih (by omega), List.range_succ, List.map_append, progBytes_append,
      List.length_append]
    simp only [List.map_cons, List.map_nil, progBytes, List.append_nil]
    rw [aufloesenAt_laenge ws p k (by omega)]

/-- PLACEMENT: if the image sits at `base`, the resolved instruction `k`
    sits at the address of label `k`. -/
theorem codeAt_zeile (m : Speicher) (base : Adresse) (ws : List Bool) (p : LProg)
    (h : CodeAt m base (bild ws p)) (k : Nat) (hk : k < p.length) :
    CodeAt m (adrL base ws p k) (encodeI (aufloesenAt ws p k)) := by
  have gen : ∀ n, k < n → n ≤ p.length →
      CodeAt m base (progBytes ((List.range n).map (aufloesenAt ws p))) →
      CodeAt m (adrL base ws p k) (encodeI (aufloesenAt ws p k)) := by
    intro n
    induction n with
    | zero => intro h0; omega
    | succ n ih =>
      intro hkn hn hc
      rw [List.range_succ, List.map_append, progBytes_append] at hc
      by_cases hkn' : k < n
      · exact ih hkn' (by omega) (codeAt_links _ _ _ _ hc)
      · have hke : k = n := by omega
        subst hke
        have hr := codeAt_rechts _ _ _ _ hc
        simp only [List.map_cons, List.map_nil, progBytes, List.append_nil] at hr
        unfold adrL
        rw [off_bild ws p k (by omega)]
        exact hr
  exact gen p.length hk (Nat.le_refl _) h

/-! ## 2. Bounded relaxation (DESIGN §2B). -/

/-- One compression attempt at index `k`: narrow it only if it is still
    wide AND the WHOLE layout with it narrowed validates. -/
def versuche (p : LProg) (ws : List Bool) (k : Nat) : List Bool :=
  if ws.getD k false = false ∧ layoutOk (ws.set k true) p = true then ws.set k true else ws

/-- One compression round over all indices, in order. -/
def runde (p : LProg) (ws : List Bool) : List Bool :=
  (List.range p.length).foldl (versuche p) ws

/-- At most `n` rounds; stops early at a fixpoint. -/
def relaxN (p : LProg) : Nat → List Bool → List Bool
  | 0, ws => ws
  | n + 1, ws =>
    let ws' := runde p ws
    if ws' = ws then ws else relaxN p n ws'

/-- The all-wide start. -/
def alleWeit (p : LProg) : List Bool := List.replicate p.length false

/-- BOUNDED RELAXATION: start all wide; refuse (`none`) if even the wide
    layout does not validate (a label outside the program, a rel32
    overflow, a non-canonical or control-flow `op` row); otherwise at most
    `fuel` compression rounds. -/
def relax (fuel : Nat) (p : LProg) : Option (List Bool) :=
  if layoutOk (alleWeit p) p = true then some (relaxN p fuel (alleWeit p)) else none

theorem versuche_ok (p : LProg) (ws : List Bool) (k : Nat) (h : layoutOk ws p = true) :
    layoutOk (versuche p ws k) p = true := by
  unfold versuche
  split
  · rename_i hc; exact hc.2
  · exact h

theorem runde_ok (p : LProg) (ws : List Bool) (h : layoutOk ws p = true) :
    layoutOk (runde p ws) p = true := by
  unfold runde
  generalize List.range p.length = ks
  induction ks generalizing ws with
  | nil => exact h
  | cons k ks ih => exact ih _ (versuche_ok p ws k h)

theorem relaxN_ok (p : LProg) (n : Nat) (ws : List Bool) (h : layoutOk ws p = true) :
    layoutOk (relaxN p n ws) p = true := by
  induction n generalizing ws with
  | zero => exact h
  | succ n ih =>
    simp only [relaxN]
    split
    · exact h
    · exact ih _ (runde_ok p ws h)

/-- RELAXATION SOUNDNESS: whatever the fuel, the answer validates. -/
theorem relax_ok (fuel : Nat) (p : LProg) (ws : List Bool)
    (h : relax fuel p = some ws) : layoutOk ws p = true := by
  unfold relax at h
  split at h
  · rename_i h0; cases h; exact relaxN_ok p fuel _ h0
  · cases h

/-- FUEL EXHAUSTED: with no rounds the answer is the validated all-wide
    layout. -/
theorem relax_null (p : LProg) (h : layoutOk (alleWeit p) p = true) :
    relax 0 p = some (alleWeit p) := by
  simp [relax, h, relaxN]

/-! ## 3. The labelled semantics: a jump goes to the address of its label. -/

/-- One labelled step at program counter `x.1` (a label), given the
    address map `adr` of labels. Ordinary rows run the unified `stepI`;
    a jump sets RIP to the address of its label; an untaken conditional
    jump continues at the next label. Past the end: no change. -/
def stepL (adr : Nat → Adresse) (p : LProg) (x : Nat × Zustand) : Option (Nat × Zustand) :=
  match p[x.1]? with
  | none => some x
  | some (.op i) => (stepI (canonI i) x.2).map (fun s' => (x.1 + 1, s'))
  | some (.jmp z) => some (z, { x.2 with rip := adr z })
  | some (.jcc c z) =>
    some (if bedingung c x.2.flags then (z, { x.2 with rip := adr z })
      else (x.1 + 1, { x.2 with rip := adr (x.1 + 1) }))

/-- Bounded labelled run: at most `n` steps; it STOPS at the program end
    (a label `≥ p.length`); `none` is a refusal. -/
def laufL (adr : Nat → Adresse) (p : LProg) : Nat → Nat × Zustand → Option (Nat × Zustand)
  | 0, x => some x
  | n + 1, x =>
    if x.1 < p.length then
      match stepL adr p x with
      | some y => laufL adr p n y
      | none => none
    else some x

/-- The number of machine steps the bounded labelled run executes
    (a refusing step counts). -/
def schritteL (adr : Nat → Adresse) (p : LProg) : Nat → Nat × Zustand → Nat
  | 0, _ => 0
  | n + 1, x =>
    if x.1 < p.length then
      match stepL adr p x with
      | some y => schritteL adr p n y + 1
      | none => 1
    else 0

/-- The resolved instructions the bounded labelled run executes, in order
    (the trace `laufBytesI_spur` speaks about). -/
def spurL (ws : List Bool) (adr : Nat → Adresse) (p : LProg) :
    Nat → Nat × Zustand → List Instr
  | 0, _ => []
  | n + 1, x =>
    if x.1 < p.length then
      aufloesenAt ws p x.1 ::
        (match stepL adr p x with
         | some y => spurL ws adr p n y
         | none => [])
    else []

/-- Runs compose (also across the program end, where the run stays). -/
theorem laufL_add (adr : Nat → Adresse) (p : LProg) (a b : Nat) (x : Nat × Zustand) :
    laufL adr p (a + b) x = (laufL adr p a x).bind (laufL adr p b) := by
  induction a generalizing x with
  | zero => simp [laufL]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [laufL]
    split
    · cases stepL adr p x with
      | none => rfl
      | some y => exact ih y
    · rename_i hx
      show some x = laufL adr p b x
      cases b with
      | zero => rfl
      | succ b => simp [laufL, hx]

/-! ## 4. The layout theorem with control flow. -/

theorem ripNach_ripNach (b : Adresse) (x y : Nat) :
    ripNach (ripNach b x) y = ripNach b (x + y) := by
  unfold ripNach
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem ripNach_null (a : Adresse) : ripNach a 0 = a := by
  unfold ripNach
  simp

/-- The one arithmetic fact of branch resolution: from the end of an
    instruction at offset `a` with length `l`, adding the displacement word
    to offset `c` lands at offset `c` (modular, no no-wrap premise). -/
theorem ziel_arith (base : Adresse) (a l c : Nat) :
    ripNach (ripNach base a) l + (BitVec.ofNat 64 c - BitVec.ofNat 64 (a + l)) =
      ripNach base c := by
  rw [ripNach_ripNach]
  unfold ripNach
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_sub]
  omega

theorem adrL_succ (base : Adresse) (ws : List Bool) (p : LProg) (k : Nat) :
    adrL base ws p (k + 1) = ripNach (adrL base ws p k) (lenAt ws p k) := by
  unfold adrL
  rw [off_succ, ripNach_ripNach]

/-- A rel8 jump resolved by the layout reaches the label address. -/
theorem ziel_kurz (base : Adresse) (ws : List Bool) (p : LProg) (k z : Nat)
    (h : passtRel8Wort (dispW ws p k z 2) = true) :
    ripNach (adrL base ws p k) 2 + dispWort8 (rel8FromWort (dispW ws p k z 2)) =
      adrL base ws p z := by
  rw [of_decide_eq_true h]
  exact ziel_arith base _ 2 _

/-- A rel32 jump resolved by the layout reaches the label address. -/
theorem ziel_weit (base : Adresse) (ws : List Bool) (p : LProg) (k z l : Nat)
    (h : passtRel32Wort (dispW ws p k z l) = true) :
    ripNach (adrL base ws p k) l + dispWort (BitVec.ofNat 32 (dispW ws p k z l).toNat) =
      adrL base ws p z := by
  rw [of_decide_eq_true h]
  exact ziel_arith base _ l _

/-- The layout invariant of a labelled state: RIP is the address of its
    label, memory is W^X, and the image still sits at `base`. -/
def InvL (base : Adresse) (ws : List Bool) (p : LProg) (x : Nat × Zustand) : Prop :=
  x.2.rip = adrL base ws p x.1 ∧ WX x.2.speicher ∧ CodeAt x.2.speicher base (bild ws p)

theorem invL_rip (base : Adresse) (ws : List Bool) (p : LProg) (s : Zustand) (pc z : Nat)
    (h : InvL base ws p (pc, s)) :
    InvL base ws p (z, { s with rip := adrL base ws p z }) :=
  ⟨rfl, h.2.1, h.2.2⟩

/-- ONE BYTE STEP OF A LAID-OUT LABELLED PROGRAM: at a label inside a
    validated program, under the layout invariant, the unified byte step
    from actual memory is the labelled step (successor or refusal), and the
    invariant is kept. -/
theorem byteschrittL (base : Adresse) (ws : List Bool) (p : LProg)
    (hok : layoutOk ws p = true) (pc : Nat) (s : Zustand) (hx : pc < p.length)
    (hinv : InvL base ws p (pc, s)) :
    byteschrittI s = ausgangVon ((stepL (adrL base ws p) p (pc, s)).map Prod.snd) ∧
      ∀ y, stepL (adrL base ws p) p (pc, s) = some y → InvL base ws p y := by
  have hli : p[pc]? = some p[pc] := List.getElem?_eq_getElem hx
  generalize hL : p[pc] = li at hli
  have hz := layoutOk_zeile ws p hok pc li hli
  have hcode := codeAt_zeile s.speicher base ws p hinv.2.2 pc hx
  rw [← hinv.1] at hcode
  have hJ : aufloesenAt ws p pc = aufloesen ws p pc li := by
    simp only [aufloesenAt, hli]
  rw [hJ] at hcode
  obtain ⟨suf, hw⟩ := geholt_codeAt s _ hcode (encodeI_len _).2
  have hlen : lenAt ws p pc = lenL (ws.getD pc false) li := by
    simp only [lenAt, hli]
  cases li with
  | op i =>
    simp only [zeileOk, Bool.and_eq_true] at hz
    have hb := (byteschrittI_kanonisch i hz.1 s suf hw).2
    simp only [stepL, hli]
    refine ⟨?_, ?_⟩
    · rw [hb]
      cases stepI (canonI i) s <;> rfl
    · intro y hy
      cases hs : stepI (canonI i) s with
      | none => rw [hs] at hy; cases hy
      | some s1 =>
        rw [hs] at hy
        cases hy
        obtain ⟨hschutz, hrip⟩ := stepI_rahmen i _ s s1 hs
        refine ⟨?_, wx_schutz _ _ hinv.2.1 hschutz,
          codeAt_schutz _ _ _ _ hinv.2.1 hschutz hinv.2.2⟩
        show s1.rip = adrL base ws p (pc + 1)
        rw [hrip hz.2, adrL_succ, hlen, ← hinv.1]
        rfl
  | jmp z =>
    simp only [zeileOk, Bool.and_eq_true] at hz
    refine ⟨?_, fun y hy => ?_⟩
    · simp only [stepL, hli, Option.map_some]
      cases hk : ws.getD pc false with
      | true =>
        simp only [hk, if_true] at hz
        have hJ' : aufloesen ws p pc (.jmp z) =
            .compact (.jump8 (rel8FromWort (dispW ws p pc z 2))) := by
          simp only [aufloesen, hk, if_true]
        rw [hJ'] at hw
        rw [(byteschrittI_kanonisch _ rfl s suf hw).2]
        show ausgangVon (schrittC ⟨.jump8 _, 2⟩ s) = _
        rw [schrittC_jump8 _ s _ rfl rfl]
        show ByteAusgang.weiter _ = ByteAusgang.weiter _
        rw [hinv.1, ziel_kurz base ws p pc z hz.2]
      | false =>
        simp only [hk] at hz
        have hJ' : aufloesen ws p pc (.jmp z) =
            .pilot (.jump32 (BitVec.ofNat 32 (dispW ws p pc z 5).toNat)) := by
          simp only [aufloesen, hk, Bool.false_eq_true, if_false]
        rw [hJ'] at hw
        rw [(byteschrittI_kanonisch _ rfl s suf hw).2]
        have hc : canonI (.pilot (.jump32 (BitVec.ofNat 32 (dispW ws p pc z 5).toNat))) =
            ⟨.pilot (.jump32 (BitVec.ofNat 32 (dispW ws p pc z 5).toNat)), 5⟩ := by
          simp only [canonI, jump32_laenge]
        rw [hc]
        show ausgangVon (schritt ⟨.jump32 _, 5⟩ s) = _
        rw [schritt_jump32 _ s _ rfl rfl]
        show ByteAusgang.weiter _ = ByteAusgang.weiter _
        rw [hinv.1, ziel_weit base ws p pc z 5 hz.2]
    · simp only [stepL, hli, Option.some.injEq] at hy
      subst hy
      exact invL_rip base ws p s pc z hinv
  | jcc c z =>
    simp only [zeileOk, Bool.and_eq_true] at hz
    refine ⟨?_, fun y hy => ?_⟩
    · simp only [stepL, hli, Option.map_some]
      cases hk : ws.getD pc false with
      | true =>
        simp only [hk, if_true] at hz
        have hJ' : aufloesen ws p pc (.jcc c z) =
            .compact (.jumpIf8 c (rel8FromWort (dispW ws p pc z 2))) := by
          simp only [aufloesen, hk, if_true]
        rw [hJ'] at hw
        rw [(byteschrittI_kanonisch _ rfl s suf hw).2]
        show ausgangVon (schrittC ⟨.jumpIf8 c _, 2⟩ s) = _
        cases hb : bedingung c s.flags with
        | true =>
          rw [schrittC_jumpIf8_genommen _ s c _ rfl rfl hb]
          simp only [if_true]
          show ByteAusgang.weiter _ = ByteAusgang.weiter _
          rw [hinv.1, ziel_kurz base ws p pc z hz.2]
        | false =>
          rw [schrittC_jumpIf8_nicht _ s c _ rfl rfl hb]
          simp only [Bool.false_eq_true, if_false]
          show ByteAusgang.weiter _ = ByteAusgang.weiter _
          rw [adrL_succ, hlen, ← hinv.1]
          simp only [lenL, hk, if_true]
      | false =>
        simp only [hk] at hz
        have hJ' : aufloesen ws p pc (.jcc c z) =
            .pilot (.jumpIf32 c (BitVec.ofNat 32 (dispW ws p pc z 6).toNat)) := by
          simp only [aufloesen, hk, Bool.false_eq_true, if_false]
        rw [hJ'] at hw
        rw [(byteschrittI_kanonisch _ rfl s suf hw).2]
        have hc : canonI (.pilot (.jumpIf32 c (BitVec.ofNat 32 (dispW ws p pc z 6).toNat))) =
            ⟨.pilot (.jumpIf32 c (BitVec.ofNat 32 (dispW ws p pc z 6).toNat)), 6⟩ := by
          simp only [canonI, jumpIf32_laenge]
        rw [hc]
        show ausgangVon (schritt ⟨.jumpIf32 c _, 6⟩ s) = _
        cases hb : bedingung c s.flags with
        | true =>
          rw [schritt_jumpIf32_genommen _ s c _ rfl rfl hb]
          simp only [if_true]
          show ByteAusgang.weiter _ = ByteAusgang.weiter _
          rw [hinv.1, ziel_weit base ws p pc z 6 hz.2]
        | false =>
          rw [schritt_jumpIf32_nicht _ s c _ rfl rfl hb]
          simp only [Bool.false_eq_true, if_false]
          show ByteAusgang.weiter _ = ByteAusgang.weiter _
          rw [adrL_succ, hlen, ← hinv.1]
          simp only [lenL, hk, Bool.false_eq_true, if_false]
    · simp only [stepL, hli, Option.some.injEq] at hy
      subst hy
      split
      · exact invL_rip base ws p s pc z hinv
      · exact invL_rip base ws p s pc (pc + 1) hinv

/-- THE LAYOUT THEOREM WITH CONTROL FLOW. A validated labelled program
    (loops and branches allowed), laid out by `bild` at `base` in W^X
    memory and entered at the address of a label: the unified byte run of
    exactly as many steps as the bounded labelled run executes produces the
    labelled run's outcome -- the same successor state, or a refusal
    exactly when the labelled run refuses -- and the layout invariant holds
    at the end (RIP is the address of the reached label). -/
theorem laufBytesL (base : Adresse) (ws : List Bool) (p : LProg)
    (hok : layoutOk ws p = true) :
    ∀ (n : Nat) (x : Nat × Zustand), InvL base ws p x →
      laufBytesI (schritteL (adrL base ws p) p n x) x.2 =
          ausgangVon ((laufL (adrL base ws p) p n x).map Prod.snd) ∧
        ∀ y, laufL (adrL base ws p) p n x = some y → InvL base ws p y := by
  intro n
  induction n with
  | zero => intro x hx; exact ⟨rfl, fun y hy => by cases hy; exact hx⟩
  | succ n ih =>
    intro x hinv
    obtain ⟨pc, s⟩ := x
    by_cases hx : pc < p.length
    · obtain ⟨hb, hinv'⟩ := byteschrittL base ws p hok pc s hx hinv
      simp only [schritteL, laufL, hx, if_true]
      cases hs : stepL (adrL base ws p) p (pc, s) with
      | none =>
        rw [hs] at hb
        simp only [laufBytesI, hb, ausgangVon, Option.map_none]
        exact ⟨trivial, fun y hy => by cases hy⟩
      | some y =>
        rw [hs] at hb
        simp only [laufBytesI, hb, ausgangVon, Option.map_some]
        exact ih y (hinv' y hs)
    · simp only [schritteL, laufL, hx, if_false]
      exact ⟨rfl, fun y hy => by cases hy; exact hinv⟩

/-- THE TRACE PREMISE, DERIVED. The resolved instructions the labelled run
    executes satisfy `SpurAn` from the layout alone -- the premise that
    `laufBytesI_spur` (ISAExecution) ASSUMED for control flow. -/
theorem spurAn_layoutL (base : Adresse) (ws : List Bool) (p : LProg)
    (hok : layoutOk ws p = true) :
    ∀ (n : Nat) (x : Nat × Zustand), InvL base ws p x →
      SpurAn (spurL ws (adrL base ws p) p n x) x.2 := by
  intro n
  induction n with
  | zero => intro x _; trivial
  | succ n ih =>
    intro x hinv
    obtain ⟨pc, s⟩ := x
    by_cases hx : pc < p.length
    · simp only [spurL, hx, if_true]
      obtain ⟨hb, hinv'⟩ := byteschrittL base ws p hok pc s hx hinv
      have hli : p[pc]? = some p[pc] := List.getElem?_eq_getElem hx
      have hcode := codeAt_zeile s.speicher base ws p hinv.2.2 pc hx
      rw [← hinv.1] at hcode
      obtain ⟨suf, hw⟩ := geholt_codeAt s _ hcode (encodeI_len _).2
      have hk : kanonischI (aufloesenAt ws p pc) = true := by
        have hz := layoutOk_zeile ws p hok pc _ hli
        simp only [aufloesenAt, hli]
        revert hz
        cases p[pc] with
        | op i =>
          intro hz
          simp only [zeileOk, Bool.and_eq_true] at hz
          exact hz.1
        | jmp z => intro _; simp only [aufloesen]; split <;> rfl
        | jcc c z => intro _; simp only [aufloesen]; split <;> rfl
      have hb2 := (byteschrittI_kanonisch _ hk s suf hw).2
      refine ⟨hk, ⟨suf, hw⟩, fun s1 hs1 => ?_⟩
      rw [hb2, hs1] at hb
      cases hs : stepL (adrL base ws p) p (pc, s) with
      | none => rw [hs] at hb; cases hb
      | some y =>
        rw [hs] at hb
        simp only [ausgangVon, Option.map_some, ByteAusgang.weiter.injEq] at hb
        subst hb
        exact ih y (hinv' y hs)
    · simp only [spurL, hx, if_false]
      trivial

/-- ENTRY FORM: a validated program whose image sits at the current RIP in
    W^X memory, entered at label 0. -/
theorem laufBytesL_start (ws : List Bool) (p : LProg) (hok : layoutOk ws p = true)
    (s : Zustand) (hwx : WX s.speicher) (hcode : CodeAt s.speicher s.rip (bild ws p))
    (n : Nat) :
    laufBytesI (schritteL (adrL s.rip ws p) p n (0, s)) s =
        ausgangVon ((laufL (adrL s.rip ws p) p n (0, s)).map Prod.snd) ∧
      ∀ y, laufL (adrL s.rip ws p) p n (0, s) = some y →
        y.2.rip = adrL s.rip ws p y.1 :=
  have h := laufBytesL s.rip ws p hok n (0, s)
    ⟨by simp [adrL, off_null, ripNach_null], hwx, hcode⟩
  ⟨h.1, fun y hy => (h.2 y hy).1⟩

/-- RELAXED FORM: whatever the fuel, the relaxed layout runs as the
    labelled program. -/
theorem relax_laufBytes (fuel : Nat) (p : LProg) (ws : List Bool)
    (hr : relax fuel p = some ws) (s : Zustand) (hwx : WX s.speicher)
    (hcode : CodeAt s.speicher s.rip (bild ws p)) (n : Nat) :
    laufBytesI (schritteL (adrL s.rip ws p) p n (0, s)) s =
        ausgangVon ((laufL (adrL s.rip ws p) p n (0, s)).map Prod.snd) ∧
      ∀ y, laufL (adrL s.rip ws p) p n (0, s) = some y →
        y.2.rip = adrL s.rip ws p y.1 :=
  laufBytesL_start ws p (relax_ok fuel p ws hr) s hwx hcode n

/-! ## 5. Basic blocks and their flattening. -/

/-- A block terminator: fall through to the next block, or a jump to a
    BLOCK label (the index equal to the block count is the program end). -/
inductive Term where
  | weiter
  | jmp (ziel : Nat)
  | jcc (c : Bedingung) (ziel : Nat)
  deriving DecidableEq, Repr

/-- A basic block: a straight-line body and one terminator. -/
structure Block where
  body : List Instr
  term : Term
  deriving DecidableEq, Repr

/-- A block program; labels are block indices. -/
abbrev BProg := List Block

def termLen : Term → Nat
  | .weiter => 0
  | _ => 1

def blockLen (B : Block) : Nat := B.body.length + termLen B.term

/-- The instruction index at which block `b` starts in the flattening. -/
def startB (bp : BProg) (b : Nat) : Nat := ((bp.take b).map blockLen).sum

def termFlach (bp : BProg) : Term → LProg
  | .weiter => []
  | .jmp z => [.jmp (startB bp z)]
  | .jcc c z => [.jcc c (startB bp z)]

def blockFlach (bp : BProg) (B : Block) : LProg :=
  B.body.map .op ++ termFlach bp B.term

/-- The flattening: blocks back to back, block labels turned into the
    instruction index of the block start. -/
def flach (bp : BProg) : LProg := (bp.map (blockFlach bp)).flatten

/-- Block-level semantics: one block body under `laufI`, then its
    terminator; jumps set RIP to the address `adr` of the target block. -/
def termSchritt (adr : Nat → Adresse) (b : Nat) (s : Zustand) : Term → Nat × Zustand
  | .weiter => (b + 1, s)
  | .jmp z => (z, { s with rip := adr z })
  | .jcc c z =>
    if bedingung c s.flags then (z, { s with rip := adr z })
    else (b + 1, { s with rip := adr (b + 1) })

def stepB (adr : Nat → Adresse) (bp : BProg) (x : Nat × Zustand) : Option (Nat × Zustand) :=
  match bp[x.1]? with
  | none => some x
  | some B => (laufI (B.body.map canonI) x.2).map (fun s1 => termSchritt adr x.1 s1 B.term)

/-- Bounded block run (fuel counts blocks); stops at the program end. -/
def laufB (adr : Nat → Adresse) (bp : BProg) : Nat → Nat × Zustand → Option (Nat × Zustand)
  | 0, x => some x
  | n + 1, x =>
    if x.1 < bp.length then
      match stepB adr bp x with
      | some y => laufB adr bp n y
      | none => none
    else some x

theorem blockFlach_laenge (bp : BProg) (B : Block) :
    (blockFlach bp B).length = blockLen B := by
  unfold blockFlach blockLen
  cases B.term <;> simp [termFlach, termLen]

theorem startB_null (bp : BProg) : startB bp 0 = 0 := by simp [startB]

theorem startB_succ (bp : BProg) (b : Nat) (hb : b < bp.length) :
    startB bp (b + 1) = startB bp b + blockLen bp[b] := by
  unfold startB
  rw [List.take_add_one, List.getElem?_eq_getElem hb, Option.toList_some, List.map_append,
    List.sum_append]
  simp

theorem laenge_flatten_map (bp : BProg) (xs : List Block) :
    ((xs.map (blockFlach bp)).flatten).length = (xs.map blockLen).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons, ih,
      blockFlach_laenge]

theorem flatten_map_mitte (f : α → List β) (l : List α) (b : Nat) (hb : b < l.length) :
    (l.map f).flatten =
      ((l.take b).map f).flatten ++ (f l[b] ++ ((l.drop (b + 1)).map f).flatten) := by
  have hl : l = l.take b ++ l[b] :: l.drop (b + 1) := by
    rw [← List.drop_eq_getElem_cons hb, List.take_append_drop]
  conv => lhs; rw [hl]
  simp only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]

/-- The flattening around block `b`: what lies before it is exactly
    `startB bp b` instructions long. -/
theorem flach_zerlegung (bp : BProg) (b : Nat) (hb : b < bp.length) :
    ∃ A R : LProg, flach bp = A ++ (blockFlach bp bp[b] ++ R) ∧ A.length = startB bp b := by
  refine ⟨((bp.take b).map (blockFlach bp)).flatten,
    ((bp.drop (b + 1)).map (blockFlach bp)).flatten, ?_, laenge_flatten_map bp _⟩
  unfold flach
  exact flatten_map_mitte (blockFlach bp) bp b hb

theorem getElem?_mitte (A X R : List α) (j : Nat) (hj : j < X.length) :
    (A ++ (X ++ R))[A.length + j]? = X[j]? := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

theorem flach_body (bp : BProg) (b : Nat) (hb : b < bp.length) (j : Nat)
    (hj : j < bp[b].body.length) :
    (flach bp)[startB bp b + j]? = some (.op bp[b].body[j]) := by
  obtain ⟨A, R, hf, hA⟩ := flach_zerlegung bp b hb
  rw [hf, ← hA, getElem?_mitte _ _ _ _ (by rw [blockFlach_laenge]; unfold blockLen; omega)]
  unfold blockFlach
  rw [List.getElem?_append_left (by simpa using hj)]
  simp [hj]

theorem flach_term (bp : BProg) (b : Nat) (hb : b < bp.length) (t : LInstr)
    (ht : termFlach bp bp[b].term = [t]) :
    (flach bp)[startB bp b + bp[b].body.length]? = some t := by
  obtain ⟨A, R, hf, hA⟩ := flach_zerlegung bp b hb
  rw [hf, ← hA, getElem?_mitte _ _ _ _ (by
    rw [blockFlach_laenge]; unfold blockLen; cases h : bp[b].term <;>
      simp_all [termFlach, termLen])]
  unfold blockFlach
  rw [ht, List.getElem?_append_right (by simp)]
  simp

/-- A straight-line body found in the labelled program runs as `laufI`. -/
theorem laufL_body (adr : Nat → Adresse) (p : LProg) (body : List Instr) :
    ∀ (pc : Nat) (s : Zustand), (∀ j (hj : j < body.length), p[pc + j]? = some (.op body[j])) →
      laufL adr p body.length (pc, s) =
        (laufI (body.map canonI) s).map (fun s' => (pc + body.length, s')) := by
  induction body with
  | nil => intro pc s _; simp [laufL, laufI]
  | cons i rest ih =>
    intro pc s h
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hlt : pc < p.length := by
      rcases Nat.lt_or_ge pc p.length with h1 | h1
      · exact h1
      · rw [List.getElem?_eq_none h1] at h0; cases h0
    simp only [List.length_cons, laufL, hlt, if_true, stepL, h0, List.map_cons, laufI_cons]
    cases hs : stepI (canonI i) s with
    | none => rfl
    | some s1 =>
      simp only [Option.map_some, Option.bind_some]
      rw [ih (pc + 1) s1 (fun j hj => by
        have := h (j + 1) (by simp; omega)
        rw [show pc + (j + 1) = pc + 1 + j by omega] at this
        simpa using this)]
      congr 1
      funext s'
      congr 1
      omega

/-- One labelled step at a terminator jump inside the program. -/
theorem laufL_eins (adr : Nat → Adresse) (p : LProg) (x : Nat × Zustand)
    (hx : x.1 < p.length) : laufL adr p 1 x = stepL adr p x := by
  simp only [laufL, hx, if_true]
  cases stepL adr p x <;> rfl

/-- BLOCK-TO-LABEL SIMULATION. Every bounded block run is matched by a
    bounded labelled run of the flattening (with the label map
    `b ↦ startB bp b` and the block addresses `adr ∘ startB bp`): the same
    states, refusals and reached labels. -/
theorem laufB_flach (adr : Nat → Adresse) (bp : BProg) :
    ∀ (n : Nat) (x : Nat × Zustand), ∃ k,
      laufL adr (flach bp) k (startB bp x.1, x.2) =
        (laufB (fun b => adr (startB bp b)) bp n x).map (fun y => (startB bp y.1, y.2)) := by
  intro n
  induction n with
  | zero => intro x; exact ⟨0, rfl⟩
  | succ n ih =>
    intro x
    obtain ⟨b, s⟩ := x
    by_cases hb : b < bp.length
    · have hli : bp[b]? = some bp[b] := List.getElem?_eq_getElem hb
      have hbody := laufL_body adr (flach bp) bp[b].body (startB bp b) s
        (fun j hj => flach_body bp b hb j hj)
      simp only [laufB, hb, if_true, stepB, hli]
      cases hl : laufI (bp[b].body.map canonI) s with
      | none =>
        rw [hl] at hbody
        exact ⟨bp[b].body.length, hbody⟩
      | some s1 =>
        rw [hl] at hbody
        simp only [Option.map_some] at hbody ⊢
        have hsucc := startB_succ bp b hb
        generalize ht : bp[b].term = t
        cases t with
        | weiter =>
          obtain ⟨k2, hk2⟩ := ih (b + 1, s1)
          refine ⟨bp[b].body.length + k2, ?_⟩
          rw [laufL_add, hbody, Option.bind_some]
          have : startB bp b + bp[b].body.length = startB bp (b + 1) := by
            rw [hsucc]; unfold blockLen; rw [ht]; rfl
          rw [this]
          exact hk2
        | jmp z =>
          have hterm := flach_term bp b hb (.jmp (startB bp z)) (by rw [ht]; rfl)
          have hlt : startB bp b + bp[b].body.length < (flach bp).length := by
            rcases Nat.lt_or_ge (startB bp b + bp[b].body.length) (flach bp).length with h1 | h1
            · exact h1
            · rw [List.getElem?_eq_none h1] at hterm; cases hterm
          obtain ⟨k2, hk2⟩ := ih (z, { s1 with rip := adr (startB bp z) })
          refine ⟨bp[b].body.length + 1 + k2, ?_⟩
          rw [laufL_add, laufL_add, hbody, Option.bind_some, laufL_eins _ _ _ hlt]
          simp only [stepL, hterm, Option.bind_some, termSchritt]
          exact hk2
        | jcc c z =>
          have hterm := flach_term bp b hb (.jcc c (startB bp z)) (by rw [ht]; rfl)
          have hlt : startB bp b + bp[b].body.length < (flach bp).length := by
            rcases Nat.lt_or_ge (startB bp b + bp[b].body.length) (flach bp).length with h1 | h1
            · exact h1
            · rw [List.getElem?_eq_none h1] at hterm; cases hterm
          have hnext : startB bp b + bp[b].body.length + 1 = startB bp (b + 1) := by
            rw [hsucc]; unfold blockLen; rw [ht]; rfl
          simp only [termSchritt]
          cases hbed : bedingung c s1.flags with
          | true =>
            obtain ⟨k2, hk2⟩ := ih (z, { s1 with rip := adr (startB bp z) })
            refine ⟨bp[b].body.length + 1 + k2, ?_⟩
            rw [laufL_add, laufL_add, hbody, Option.bind_some, laufL_eins _ _ _ hlt]
            simp only [stepL, hterm, Option.bind_some, hbed, if_true]
            exact hk2
          | false =>
            obtain ⟨k2, hk2⟩ := ih (b + 1, { s1 with rip := adr (startB bp (b + 1)) })
            refine ⟨bp[b].body.length + 1 + k2, ?_⟩
            rw [laufL_add, laufL_add, hbody, Option.bind_some, laufL_eins _ _ _ hlt]
            simp only [stepL, hterm, Option.bind_some, hbed, Bool.false_eq_true, if_false]
            rw [hnext]
            exact hk2
    · refine ⟨0, ?_⟩
      simp [laufB, hb, laufL]

/-! ## 6. Selection per basic block. -/

/-- Select one block body with the decided selector `sel`: the scratch
    registers may already differ at block entry (D = S), all flags agree at
    entry and must agree at exit (`fe = true`, so a terminating `jcc` reads
    agreeing flags). The terminator -- and with it every label -- is kept. -/
def waehleBlock (S : List Register) (B : Block) : Option Block :=
  (sel S true S true B.body).map (fun q => ⟨q, B.term⟩)

/-- Selection over a whole block program: every block must be selected
    (`none` otherwise, and the caller keeps the original program). -/
def waehleB (S : List Register) : BProg → Option BProg
  | [] => some []
  | B :: bs =>
    match waehleBlock S B, waehleB S bs with
    | some B', some bs' => some (B' :: bs')
    | _, _ => none

/-- LABELS PRESERVED: the selected program has the same blocks in the same
    order with the same terminators, and every body is a `Wahl`
    derivation of the original body. -/
theorem waehleB_bloecke (S : List Register) :
    ∀ (p q : BProg), waehleB S p = some q →
      q.length = p.length ∧
        ∀ (b : Nat) (B : Block), p[b]? = some B →
          ∃ B' : Block, q[b]? = some B' ∧ B'.term = B.term ∧ Wahl S true S true B.body B'.body := by
  intro p
  induction p with
  | nil => intro q h; cases h; exact ⟨rfl, fun b B hB => by simp at hB⟩
  | cons B bs ih =>
    intro q h
    simp only [waehleB] at h
    split at h
    · rename_i B' bs' hB hbs
      cases h
      obtain ⟨hl, hr⟩ := ih bs' hbs
      refine ⟨by simp [hl], fun b C hC => ?_⟩
      cases b with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
        subst hC
        unfold waehleBlock at hB
        cases hs : sel S true S true B.body with
        | none => rw [hs] at hB; cases hB
        | some qb =>
          rw [hs] at hB
          cases hB
          exact ⟨_, rfl, rfl, sel_wahl S true B.body S true qb hs⟩
      | succ b =>
        simp only [List.getElem?_cons_succ] at hC ⊢
        exact hr b C hC
    · cases h

theorem waehleB_labels (S : List Register) (p q : BProg) (h : waehleB S p = some q) :
    q.map Block.term = p.map Block.term := by
  obtain ⟨hl, hr⟩ := waehleB_bloecke S p q h
  apply List.ext_getElem (by simp [hl])
  intro b h1 h2
  simp only [List.length_map] at h1 h2
  obtain ⟨B', hB', ht, _⟩ := hr b p[b] (List.getElem?_eq_getElem h2)
  rw [List.getElem?_eq_getElem h1, Option.some.injEq] at hB'
  simp only [List.getElem_map, hB', ht]

/-- Lifting a relation to optional outcomes (refuse together, or both
    succeed related). -/
def OptRelP (R : α → α → Prop) : Option α → Option α → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

/-- Agreement of two block states: the same label, and agreement outside
    the scratch list on registers, on all memory and on all flags. RIP is
    not compared (each program has its own layout). -/
def GlB (S : List Register) (x y : Nat × Zustand) : Prop :=
  x.1 = y.1 ∧ Gl S true x.2 y.2

theorem gl_rip (S : List Register) (s1 s2 : Zustand) (a1 a2 : Adresse)
    (h : Gl S true s1 s2) : Gl S true { s1 with rip := a1 } { s2 with rip := a2 } :=
  ⟨h.1, h.2.1, h.2.2⟩

theorem termSchritt_gl (S : List Register) (adr1 adr2 : Nat → Adresse) (b : Nat)
    (s1 s2 : Zustand) (t : Term) (h : Gl S true s1 s2) :
    GlB S (termSchritt adr1 b s1 t) (termSchritt adr2 b s2 t) := by
  cases t with
  | weiter => exact ⟨rfl, h⟩
  | jmp z => exact ⟨rfl, gl_rip S s1 s2 _ _ h⟩
  | jcc c z =>
    have hc : bedingung c s2.flags = bedingung c s1.flags := by rw [h.2.2 rfl]
    simp only [termSchritt]
    rw [hc]
    split
    · exact ⟨rfl, gl_rip S s1 s2 _ _ h⟩
    · exact ⟨rfl, gl_rip S s1 s2 _ _ h⟩

/-- CROSS-BLOCK SELECTION CORRECTNESS. If the per-block selector accepts
    `p` with scratch list `S`, then for any two block-address maps and any
    two agreeing start states at the same label, the bounded block runs of
    the original and the selected program refuse together, or both succeed
    at the SAME label in states that agree outside `S`, on memory and on
    the flags. -/
theorem waehleB_korrekt (S : List Register) (p q : BProg) (h : waehleB S p = some q)
    (adrP adrQ : Nat → Adresse) :
    ∀ (n : Nat) (x y : Nat × Zustand), GlB S x y →
      OptRelP (GlB S) (laufB adrP p n x) (laufB adrQ q n y) := by
  obtain ⟨hl, hr⟩ := waehleB_bloecke S p q h
  intro n
  induction n with
  | zero => intro x y hg; exact hg
  | succ n ih =>
    intro x y hg
    obtain ⟨b, s1⟩ := x
    obtain ⟨b', s2⟩ := y
    obtain ⟨hbb, hg2⟩ := hg
    simp only at hbb
    subst hbb
    by_cases hb : b < p.length
    · have hbq : b < q.length := by rw [hl]; exact hb
      obtain ⟨B', hB', ht, hw⟩ := hr b p[b] (List.getElem?_eq_getElem hb)
      have hk := wahl_korrekt S true S true _ _ hw s1 s2 (fun _ h => h) hg2
      simp only [laufB, hb, hbq, if_true, stepB, List.getElem?_eq_getElem hb, hB']
      cases h1 : laufI (p[b].body.map canonI) s1 with
      | none =>
        cases h2 : laufI (B'.body.map canonI) s2 with
        | none => trivial
        | some t2 => rw [h1, h2] at hk; exact absurd hk id
      | some t1 =>
        cases h2 : laufI (B'.body.map canonI) s2 with
        | none => rw [h1, h2] at hk; exact absurd hk id
        | some t2 =>
          rw [h1, h2] at hk
          simp only [Option.map_some]
          rw [ht]
          exact ih _ _ (termSchritt_gl S adrP adrQ b t1 t2 _ ⟨hk.1, hk.2.1, hk.2.2⟩)
    · have hbq : ¬ b < q.length := by rw [hl]; exact hb
      simp only [laufB, hb, hbq, if_false]
      exact ⟨rfl, hg2⟩

/-! ## 7. Select, flatten, relax, lay out: the combined statement. -/

/-- The whole pass: per-block selection, flattening, bounded relaxation;
    the answer is the selected program, the widths and the byte image. -/
def uebersetze (S : List Register) (fuel : Nat) (p : BProg) :
    Option (BProg × List Bool × List Byte) :=
  match waehleB S p with
  | none => none
  | some q =>
    match relax fuel (flach q) with
    | none => none
    | some ws => some (q, ws, bild ws (flach q))

/-- SELECTION ACROSS A BRANCHY PROGRAM, DOWN TO BYTES. If the pass answers
    `(q, ws, img)` and `img` sits at RIP in W^X memory, then for every block
    fuel `n` there is a byte step count `k` such that the ORIGINAL block
    program `p` (under any address map) and the byte run of `img` from
    actual memory refuse together, or both succeed: the original reaches
    block label `b` in a state that agrees with the byte state outside the
    scratch list, on all memory and on all flags, and the byte state's RIP
    is the address of the SAME block label `b` in the relaxed layout. -/
theorem uebersetze_bytes (S : List Register) (fuel : Nat) (p q : BProg) (ws : List Bool)
    (img : List Byte) (hu : uebersetze S fuel p = some (q, ws, img)) (s : Zustand)
    (hwx : WX s.speicher) (hcode : CodeAt s.speicher s.rip img)
    (adrP : Nat → Adresse) (n : Nat) :
    ∃ k : Nat,
      (laufB adrP p n (0, s) = none ∧ laufBytesI k s = .verweigert) ∨
      ∃ (b : Nat) (s1 s2 : Zustand), laufB adrP p n (0, s) = some (b, s1) ∧
        laufBytesI k s = .weiter s2 ∧ EndGl S true s1 s2 ∧
        s2.rip = adrL s.rip ws (flach q) (startB q b) := by
  unfold uebersetze at hu
  split at hu
  · cases hu
  · rename_i q0 hq
    split at hu
    · cases hu
    · rename_i ws0 hr
      cases hu
      have hok := relax_ok fuel _ _ hr
      let adrF := adrL s.rip ws (flach q)
      obtain ⟨k, hk⟩ := laufB_flach adrF q n (0, s)
      rw [startB_null] at hk
      obtain ⟨hbytes, hrip⟩ := laufBytesL_start ws (flach q) hok s hwx hcode k
      have hsel := waehleB_korrekt S p q hq adrP (fun b => adrF (startB q b)) n (0, s) (0, s)
        ⟨rfl, fun _ _ => rfl, rfl, fun _ => rfl⟩
      refine ⟨schritteL adrF (flach q) k (0, s), ?_⟩
      rw [hbytes, hk]
      cases h1 : laufB adrP p n (0, s) with
      | none =>
        cases h2 : laufB (fun b => adrF (startB q b)) q n (0, s) with
        | none => exact Or.inl ⟨rfl, rfl⟩
        | some y => rw [h1, h2] at hsel; exact absurd hsel id
      | some x =>
        cases h2 : laufB (fun b => adrF (startB q b)) q n (0, s) with
        | none => rw [h1, h2] at hsel; exact absurd hsel id
        | some y =>
          rw [h1, h2] at hsel
          obtain ⟨hxy, hg⟩ := hsel
          refine Or.inr ⟨x.1, x.2, y.2, rfl, rfl, ⟨hg.1, hg.2.1, hg.2.2⟩, ?_⟩
          have := hrip (startB q y.1, y.2) (by rw [hk, h2]; rfl)
          rw [hxy]
          exact this

/- CUTS (what is NOT proved here):
   - The labelled semantics `stepL` sets RIP at a jump to `adr z`, the
     address of the label in the layout the theorem is about; it is a
     semantics PARAMETRISED by the label-address map, not a
     layout-independent one. The layout-independent content is stated in
     `waehleB_korrekt`/`uebersetze_bytes`, which compare runs modulo RIP
     (`Gl`), and in the reached LABEL, which is compared exactly.
   - Runs are BOUNDED (fuel `n`); `laufBytesL` is an equation for every
     fuel, not a termination, liveness or cost claim. The step count of the
     byte run is computed (`schritteL`), and `uebersetze_bytes` only says
     that SOME byte step count matches a given block fuel.
   - At the program end (label = length) the labelled run STOPS; the byte
     machine has no halt, so nothing is claimed about the bytes past the
     image (they are whatever memory holds; under the theorem the run is
     simply not continued).
   - Relaxation is the DESIGN-§2B bounded scheme: all wide first, rounds
     narrow one branch at a time and keep a narrowing only if the WHOLE
     layout still validates (`layoutOk`, decided). Soundness
     (`relax_ok`) holds for any fuel; NO optimality, convergence or
     fixpoint claim is made, and no theorem says narrowing is monotone
     (with only shrinking it is, but the validator re-checks every branch
     instead of relying on that).
   - rel32 range: the all-wide layout must validate, i.e. every rel32
     displacement must round-trip (`passtRel32Wort`); a program larger than
     2^31 bytes is refused, not split. Addresses are modular (`ripNach`),
     no no-wrap premise is needed and no physical placement is claimed.
   - Ordinary rows must fall through (`faelltDurchI`) and be canonical:
     raw pilot/compact jumps, calls and returns are not admitted as `op`
     rows (calls/returns are out of scope here: no stack-return labels).
   - Per-block selection keeps ALL flags live at every block boundary
     (`fe = true`) and lets the scratch registers `S` differ at every block
     entry (D = S); a block that reads a scratch register before writing it
     makes the whole selection refuse. No cross-block liveness analysis is
     done; the scratch list is the caller's declaration that `S` is dead
     everywhere outside the rewrites, exactly as in `waehle_korrekt`, and
     the final agreement is `EndGl S true`.
   - If any block fails selection, `waehleB` refuses the whole program; no
     per-block fallback (a kept block could read a scratch register that
     differs).
   - Self-modifying code is excluded by W^X at the start (`WX`) and the
     per-family frame `stepI_rahmen`, as in `laufBytesI_layout`.
   - No TSO, concurrency, timing, hardware or source-correspondence claim.
-/

#print axioms off_null
#print axioms off_succ
#print axioms layoutOk_zeile
#print axioms progBytes_append
#print axioms jump32_laenge
#print axioms jumpIf32_laenge
#print axioms aufloesen_laenge
#print axioms aufloesenAt_laenge
#print axioms off_bild
#print axioms codeAt_zeile
#print axioms versuche_ok
#print axioms runde_ok
#print axioms relaxN_ok
#print axioms relax_ok
#print axioms relax_null
#print axioms laufL_add
#print axioms ripNach_ripNach
#print axioms ripNach_null
#print axioms ziel_arith
#print axioms adrL_succ
#print axioms ziel_kurz
#print axioms ziel_weit
#print axioms invL_rip
#print axioms byteschrittL
#print axioms laufBytesL
#print axioms spurAn_layoutL
#print axioms laufBytesL_start
#print axioms relax_laufBytes
#print axioms blockFlach_laenge
#print axioms startB_null
#print axioms startB_succ
#print axioms laenge_flatten_map
#print axioms flatten_map_mitte
#print axioms flach_zerlegung
#print axioms getElem?_mitte
#print axioms flach_body
#print axioms flach_term
#print axioms laufL_body
#print axioms laufL_eins
#print axioms laufB_flach
#print axioms waehleB_bloecke
#print axioms waehleB_labels
#print axioms gl_rip
#print axioms termSchritt_gl
#print axioms waehleB_korrekt
#print axioms uebersetze_bytes

end Gabbro.Grammatik.X86
