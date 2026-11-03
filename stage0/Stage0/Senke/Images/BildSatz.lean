/- Generic program/image theorem for ordered typed starts, using the shared call ABI. -/
module
public import Stage0.Senke.Images.StartupExecution
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {passes : Nat}
/-- What `bild` lays out holds of its image. -/
theorem bild_lage {P : Programm D} {fs : List D.Fn} {pos : D.Fn → Nat} {name : D.Fn → String} {main : D.Fn}
    {ρ : Env D (D.params main)} {starts : List (Σ f : D.Fn, Env D (D.params f))} {Ks req : Nat} {Y : Nat → Lay D} {b : Bild D}
    (hb : bild passes P Y fs pos name main ρ starts Ks req = .ok b) (hfs : ∀ g, fs[pos g]? = some g)
    (hYin : ∀ x, (Y x).hi < 2 ^ 31 → LayIn (Y x)) (hYdis : ∀ x, LayDis (Y x)) (hYord : ∀ x, (Y x).lo ≤ (Y x).hi)
    (hYsync : ∀ x, LaySync (Y x)) :
    ∃ cs body sp, BildLage b.passes P fs pos main (starts.map (·.1)) b.K b.Ks b.Y b.A cs body
        b.depth b.fp0 sp ρ (starts.map (fun start => encodeEnv b.Y start.2)) ∧
      b.code = spawnC (startScratch main) sp ++ startC b.A main b.depth 231 true ++
        rootsC b.A b.depth (starts.map (·.1)) ++ body ∧
      b.roots = starts.map (·.1) ∧ b.args = encodeEnv b.Y ρ ∧
      b.rootArgs = starts.map (fun start => encodeEnv b.Y start.2) := by
  simp only [bild] at hb
  split at hb
  · cases hb
  · next cs0 h0 =>
    split at hb
    · cases hb
    · next cs h1 =>
      split at hb
      · next hg =>
        simp only [Except.ok.injEq] at hb
        subst hb
        obtain ⟨⟨hwhy, hrwhy, hlens, hfit, hroomK, hexK, hops, hYlo, hYhi, hYsye⟩, hfp⟩ := hg
        obtain ⟨hcl, hcs⟩ := lowAll_ok fs cs h1
        refine ⟨cs, cs.flatMap (·.1), _, ⟨rfl, rfl, rfl, rfl, hfp, fun g => by rw [hlens], hcl, hcs, hfs,
          by simp only [List.length_map], ?_, hwhy, hrwhy,
          hfit, hroomK, fun f hf => by simpa using List.all_eq_true.mp hexK f hf, hYlo, hYhi, hYord _, hYin _ (Nat.lt_of_le_of_lt hYhi hfit),
          ⟨(hYdis _).spans, (hYdis _).inj, (hYdis _).grid⟩, rfl, rfl, hYsync _, hYsye, hops⟩, rfl, rfl, rfl, rfl⟩
        intro words member
        obtain ⟨start, member, rfl⟩ := List.mem_map.mp member
        have fits : startScratch start.1 + 8 ≤ Ks := by
          simpa using List.all_eq_true.mp hexK start.1
            (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨start, member, rfl⟩))
        have above := startScratch_ge start.1
        rw [encodeEnv_length]
        dsimp only at fits above ⊢
        omega
      · exfalso
        revert hb
        repeat' split
        all_goals intro hb; cases hb

theorem bild_bytes {b : Bild D} {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) :
    BytesAt m codeBase (b.code.flatMap encII ++
      ((startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs)).getD [] ++
        List.replicate (8 * (b.K - b.Ks * (b.roots.length + 1))) 0)) := by
  have hm' := hm
  simp only [Bild.bytes, List.append_assoc] at hm'
  have hm2 := hm'.right.right
  simp only [leN_len] at hm2
  simpa [codeBase] using hm2

/-- Initialized root frames replace the reserved zero stack bytes without changing the
    total image length or any subsequent world/lock address. -/
theorem bild_length {P : Programm D} {fs : List D.Fn} {pos : D.Fn → Nat} {name : D.Fn → String} {main : D.Fn}
    {ρ : Env D (D.params main)} {starts : List (Σ f : D.Fn, Env D (D.params f))} {Ks req : Nat}
    {Y : Nat → Lay D} {b : Bild D}
    (hb : bild passes P Y fs pos name main ρ starts Ks req = .ok b) (hfs : ∀ g, fs[pos g]? = some g)
    (hYin : ∀ x, (Y x).hi < 2 ^ 31 → LayIn (Y x)) (hYdis : ∀ x, LayDis (Y x))
    (hYord : ∀ x, (Y x).lo ≤ (Y x).hi) (hYsync : ∀ x, LaySync (Y x)) :
    b.bytes.length = 16 + 16 * b.code.length + 8 * b.K := by
  obtain ⟨cs, body, sp, hl, hc, hr, ha, hra⟩ := bild_lage hb hfs hYin hYdis hYord hYsync
  obtain ⟨stacks, made, length⟩ := hl.stacks
  have fits : b.Ks * ((starts.map (·.1)).length + 1) ≤ b.K := by
    have := hl.hylo; have := hl.hyord; have := hl.hyhi
    omega
  simp only [Bild.bytes, hr, ha, hra, made, Option.getD_some, List.length_append,
    leN_len, flatMap_enc_len, List.length_replicate, length]
  omega

/-- **The program theorem**, `main`'s thread: from the loader's first instruction, the roots spawned, `main` as
    `rufAt b.depth main`, then `exit_group` of its result -- or the stop of G's outcome. -/
theorem bild_ok [CloneOK] {P : Programm D} {O : Orakel D} {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat}
    {name : D.Fn → String} {main : D.Fn} {starts : List (Σ f : D.Fn, Env D (D.params f))} {Ks req : Nat} {Y : Nat → Lay D} {b : Bild D}
    {ρ : Env D (D.params main)} (hb : bild passes P Y fs pos name main ρ starts Ks req = .ok b) (hfs : ∀ g, fs[pos g]? = some g)
    (hYin : ∀ x, (Y x).hi < 2 ^ 31 → LayIn (Y x)) (hYdis : ∀ x, LayDis (Y x)) (hYord : ∀ x, (Y x).lo ≤ (Y x).hi)
    (hYsync : ∀ x, LaySync (Y x)) {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (σ : World D)
    (hval : ∀ τ (x : Var (D.params main) τ), ValueValid b.Y τ (ρ.get x))
    (hWa : WeltAt m b.Y σ) (hT : TorOK b.Y O) (hV : SichtOK O) :
    match rufAt P O b.passes b.depth main σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m t' m' ∧ StopAt t' m' q ∧
        q.nr = 231 ∧ ExitErg b.Y (D.erg main) v q.a1
    | .logik e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (logikCode e)
    | .hardware h => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (hwCode h)
    | _ => False := by
  obtain ⟨cs, body, sp, hl, hc, hr, ha, hra⟩ := bild_lage hb hfs hYin hYdis hYord hYsync
  have hm2 := bild_bytes hm
  rw [hc, hr, ha, hra] at hm2
  obtain ⟨_, _, _, _, hz⟩ := hl.code hm2
  have locks : BytesAt m b.Y.hi (List.replicate (b.Y.sye - b.Y.hi) 0) :=
    zeroBytes_slice hz (by have := hl.hylo; have := hl.hyord; omega)
      (by have := hl.hysye; have := hl.hyhi; have := hl.hylo; have := hl.hyord; omega)
  exact bild_kern (hT := hT) (hV := hV) (passes := b.passes) hl hm2 hval σ hWa
    (by simpa using hl.sync locks (j := 0) (Nat.zero_le _))

/-- **The program theorem**, the thread of root `j`: from its start code on its stack, the root as
    `rufAt b.depth`, then `exit` -- or the stop of G's outcome. -/
theorem bild_wurzel_ok {P : Programm D} {O : Orakel D} {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat}
    {name : D.Fn → String} {main : D.Fn} {starts : List (Σ f : D.Fn, Env D (D.params f))} {Ks req : Nat} {Y : Nat → Lay D} {b : Bild D}
    {ρm : Env D (D.params main)} (hb : bild passes P Y fs pos name main ρm starts Ks req = .ok b) (hfs : ∀ g, fs[pos g]? = some g)
    (hYin : ∀ x, (Y x).hi < 2 ^ 31 → LayIn (Y x)) (hYdis : ∀ x, LayDis (Y x)) (hYord : ∀ x, (Y x).lo ≤ (Y x).hi)
    (hYsync : ∀ x, LaySync (Y x)) {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (j : Nat) (hj : j < starts.length) (σ : World D)
    (hval : ∀ τ (x : Var (D.params starts[j].1) τ), ValueValid b.Y τ (starts[j].2.get x))
    (hWa : WeltAt m b.Y σ) (hT : TorOK b.Y O) (hV : SichtOK O) :
    match rufAt P O b.passes b.depth starts[j].1 σ starts[j].2 with
    | .ok _ _ => ∃ t' m' q, Star ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = 60
    | .logik e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (hwCode e)
    | _ => False := by
  obtain ⟨cs, body, sp, hl, hc, hr, ha, hra⟩ := bild_lage hb hfs hYin hYdis hYord hYsync
  have hm2 := bild_bytes hm
  rw [hc, hr, ha, hra] at hm2
  obtain ⟨_, _, _, _, hz⟩ := hl.code hm2
  have locks : BytesAt m b.Y.hi (List.replicate (b.Y.sye - b.Y.hi) 0) :=
    zeroBytes_slice hz (by have := hl.hylo; have := hl.hyord; omega)
      (by have := hl.hysye; have := hl.hyhi; have := hl.hylo; have := hl.hyord; omega)
  have result := bild_wurzel (hT := hT) (hV := hV) (passes := b.passes) hl hm2 j
    (by simpa only [List.length_map] using hj) σ
    (by simpa only [List.getElem_map] using starts[j].2)
    (by simp only [List.getElem_map])
    (by simpa only [List.getElem_map] using hval) hWa (hl.sync locks (by simp only [List.length_map]; omega))
  simpa only [List.length_map, List.getElem_map] using result

end Gabbro.Stage0.Senke
