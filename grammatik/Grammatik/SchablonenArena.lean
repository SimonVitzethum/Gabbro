/-
  File:      Grammatik/SchablonenArena.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md): the runtime of a dynamic
             arena as a GENERATED template (C-free lane, 2026-09-30).

  Row `arena.dyn` of `crates/gabbro-check/src/schablonen.rs`.

  Until this template, `laufzeit/arena_dyn.c` was handwritten C: it reserved the address
  range of a dynamic arena's ceiling at load and made the committed prefix writable at every
  `grow`, through the binding's `gabbro_os_reserve`/`gabbro_os_commit` with addresses passed
  as NUMBERS. The generated driver now writes that runtime itself
  (`crates/gabbro-cli/src/treiber.rs`, `arena_laufzeit`), and the binding answers a REGION
  (`bibliothek/linux/linux.gab`: `gabbro_os_reserve(bytes) -> ptr<normal, rw> u8`, a gate
  over the kernel's mapping call, template `tor.region`) and takes one (`gabbro_os_commit(stelle, bytes)` with
  `requires bytes <= lenof(stelle)`). Everything that is arithmetic -- the span, the page
  rounding, the commit range -- is the template's, and this file proves it.

  An ABSTRACT CORE like `start.nolibc` (SchablonenOhneLibc.lean §2): machine G has the arena
  as a table of `max` slots (ArenaDyn.lean, `DynForm`); its storage is what the runtime
  premise (d) `Laufzeit.reserve`/`.commit` of the goal names (Zielsatz/Spec.lean). What is
  proved here is that the generated runtime keeps that premise's arithmetic half:

  * `arena_spanne_passt`: the span handed to the binding covers every slot below the ceiling
    and is a whole number of pages, and no 64-bit intermediate overflows (`max`, `elem` are
    32-bit fields, the page is at most `2^32` -- the template fail-stops otherwise);
  * `arena_commit_bereich`: the range a `grow` commits starts and ends on a page, covers
    every byte of the new slots, and lies inside the reserved span -- so the binding's
    `requires bytes <= lenof(stelle)` holds at the call the template makes, and the commit
    never touches memory the reservation did not hand over;
  * `arena_commit_monoton`: the committed prefix only grows, and a grow past the ceiling is
    refused before any commit (the fail-stop of the C).

  NOT proved: that the binding keeps its contract (a fresh region of `spanne` bytes; a commit
  answering 0 makes the range readable and writable) -- that is the binding's declared
  assumption, user logic in the program's source (`linux.gab`).

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness instantiating ALL
  its premises jointly.
-/

namespace Gabbro.Grammatik

namespace ArenaLaufzeit

/-- `(x + s - 1) / s * s` -- rounded UP to a multiple of `s` (the C's `ende`, `spanne`). -/
def aufrunden (x s : Nat) : Nat := (x + s - 1) / s * s

/-- `x / s * s` -- rounded DOWN to a multiple of `s` (the C's `start`). -/
def abrunden (x s : Nat) : Nat := x / s * s

/-- The span `gabbro_arena_reserve` hands to the binding: every slot, rounded up to pages. -/
def spanne (elem max seite : Nat) : Nat := aufrunden (max * elem) seite

/-- The range `gabbro_arena_grow` hands to the binding for `n` more slots above `committed`:
    from the page holding the first new byte to the page end past the last one. -/
def commitStart (elem committed seite : Nat) : Nat := abrunden (committed * elem) seite
def commitEnde (elem committed n seite : Nat) : Nat := aufrunden ((committed + n) * elem) seite

theorem abrunden_le (x s : Nat) : abrunden x s ≤ x := Nat.div_mul_le_self x s

theorem le_aufrunden (x s : Nat) (hs : 0 < s) : x ≤ aufrunden x s := by
  unfold aufrunden
  have h := Nat.div_add_mod (x + s - 1) s
  have hm := Nat.mod_lt (x + s - 1) hs
  rw [Nat.mul_comm] at h
  omega

theorem aufrunden_mono (x y s : Nat) (h : x ≤ y) : aufrunden x s ≤ aufrunden y s := by
  unfold aufrunden
  exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))

theorem aufrunden_teilbar (x s : Nat) : aufrunden x s % s = 0 := Nat.mul_mod_left _ _

theorem abrunden_teilbar (x s : Nat) : abrunden x s % s = 0 := Nat.mul_mod_left _ _

/-- A page multiple that bounds `x` from above bounds its rounding too. -/
theorem aufrunden_le_vielfach (x k s : Nat) (hs : 0 < s) (h : x ≤ k * s) :
    aufrunden x s ≤ k * s := by
  unfold aufrunden
  apply Nat.mul_le_mul_right
  have hlt : (x + s - 1) / s < k + 1 := by
    rw [Nat.div_lt_iff_lt_mul hs, Nat.succ_mul]
    omega
  omega

theorem aufrunden_idem (x s : Nat) (hs : 0 < s) : aufrunden (aufrunden x s) s = aufrunden x s := by
  apply Nat.le_antisymm
  · exact aufrunden_le_vielfach _ _ _ hs (Nat.le_refl _)
  · exact le_aufrunden _ _ hs

/-- **The reservation.** For 32-bit `max` and `elem` and a page `0 < seite <= 2^32` (the
    template fail-stops on any other page answer): the span covers every byte of every slot
    below the ceiling, is a whole number of pages, and the C's `max * elem + seite - 1` stays
    below `2^64` -- no wrap in the `uint64_t` the template computes in. -/
theorem arena_spanne_passt (elem max seite : Nat) (he : elem < 4294967296)
    (hm : max < 4294967296) (hs : 0 < seite) (hs2 : seite ≤ 4294967296) :
    max * elem ≤ spanne elem max seite ∧ spanne elem max seite % seite = 0 ∧
    max * elem + seite - 1 < 18446744073709551616 ∧
    spanne elem max seite < 18446744073709551616 := by
  have hp : max * elem ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h64 : max * elem + seite - 1 < 18446744073709551616 := by omega
  refine ⟨le_aufrunden _ _ hs, aufrunden_teilbar _ _, h64, ?_⟩
  unfold spanne aufrunden
  exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) h64

/-- **The commit of a `grow`.** For a grow that stays under the ceiling
    (`committed + n <= max` -- the template fail-stops before any commit otherwise, and `N426`
    holds it statically): the range starts and ends on a page, covers every byte of the new
    slots, and lies inside the reserved span. So `ende - start <= spanne - start`: the
    binding's `requires bytes <= lenof(stelle)` holds for `stelle = base + start`, whose
    extent under the reservation's contract is `spanne - start`. -/
theorem arena_commit_bereich (elem max committed n seite : Nat) (hs : 0 < seite)
    (hn : committed + n ≤ max) :
    commitStart elem committed seite ≤ committed * elem ∧
    (committed + n) * elem ≤ commitEnde elem committed n seite ∧
    commitEnde elem committed n seite ≤ spanne elem max seite ∧
    commitStart elem committed seite ≤ commitEnde elem committed n seite ∧
    commitStart elem committed seite % seite = 0 ∧
    commitEnde elem committed n seite % seite = 0 ∧
    commitEnde elem committed n seite - commitStart elem committed seite ≤
      spanne elem max seite - commitStart elem committed seite := by
  have h1 := abrunden_le (committed * elem) seite
  have h2 := le_aufrunden ((committed + n) * elem) seite hs
  have h3 : commitEnde elem committed n seite ≤ spanne elem max seite :=
    aufrunden_mono _ _ _ (Nat.mul_le_mul_right _ hn)
  have h4 : committed * elem ≤ (committed + n) * elem := Nat.mul_le_mul_right _ (by omega)
  refine ⟨h1, h2, h3, ?_, abrunden_teilbar _ _, aufrunden_teilbar _ _, ?_⟩
  · unfold commitStart commitEnde; omega
  · omega

/-- **The committed prefix only grows**, and every slot below the new prefix lies in the range
    committed so far or just now. -/
theorem arena_commit_monoton (elem committed n seite i : Nat) (hs : 0 < seite)
    (hi : i < committed + n) :
    committed ≤ committed + n ∧ (i + 1) * elem ≤ commitEnde elem committed n seite := by
  refine ⟨Nat.le_add_right _ _, ?_⟩
  exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) (le_aufrunden _ _ hs)

/-- The ceiling premise is not decoration: one slot past `max` needs a byte past the span
    when the span is exact (8 slots of 512 bytes on 4096-byte pages). -/
theorem arena_ueber_der_decke :
    commitEnde 512 8 1 4096 > spanne 512 8 4096 := by decide

/-- **Witness for `arena_spanne_passt`, `arena_commit_bereich` and `arena_commit_monoton`**,
    ALL premises jointly, on the os-probe's arena (`Puffer`: 8-byte slots, ceiling 65536,
    floor 8, grown by 1024) on 4096-byte pages. -/
theorem arena_zeuge :
    (65536 * 8 ≤ spanne 8 65536 4096 ∧ spanne 8 65536 4096 % 4096 = 0 ∧
      65536 * 8 + 4096 - 1 < 18446744073709551616 ∧
      spanne 8 65536 4096 < 18446744073709551616) ∧
    (commitStart 8 8 4096 ≤ 8 * 8 ∧ (8 + 1024) * 8 ≤ commitEnde 8 8 1024 4096 ∧
      commitEnde 8 8 1024 4096 ≤ spanne 8 65536 4096 ∧
      commitStart 8 8 4096 ≤ commitEnde 8 8 1024 4096 ∧
      commitStart 8 8 4096 % 4096 = 0 ∧ commitEnde 8 8 1024 4096 % 4096 = 0 ∧
      commitEnde 8 8 1024 4096 - commitStart 8 8 4096 ≤
        spanne 8 65536 4096 - commitStart 8 8 4096) ∧
    (8 ≤ 8 + 1024 ∧ (1031 + 1) * 8 ≤ commitEnde 8 8 1024 4096) :=
  ⟨arena_spanne_passt 8 65536 4096 (by decide) (by decide) (by decide) (by decide),
   arena_commit_bereich 8 65536 8 1024 4096 (by decide) (by decide),
   arena_commit_monoton 8 8 1024 4096 1031 (by decide) (by decide)⟩

/-! ## 2. `region.leeren` -- the page return of `reset X at i count n;`

  The emitted helper (`emit.rs`, `REGION_LEEREN`) clears a range of `bytes` at address `a`: the
  whole pages inside it go to the program's binding (`gabbro_os_seiten_zurueck(stelle, n)`, a
  Gabbro function under `requires n <= lenof(stelle)`), the edges it clears itself, and a
  refused page return is cleared by hand. The helper computes, over offsets from `a`,
  `von = aufrunden a s - a` and `bis = abrunden (a + bytes) s - a`, and hands over `[von, bis)`
  only when `von < bis`. `leeren_teilung` is what that needs: the three pieces cover the range
  exactly, the handed pages lie inside it -- so `bis - von <= bytes - von`, the binding's
  `requires` for `stelle = p + von`, whose extent is the rest of the range -- and they start and
  end on a page. -/

/-- Offsets of the whole pages inside `[a, a + bytes)`. -/
def leerenVon (a s : Nat) : Nat := aufrunden a s - a
def leerenBis (a bytes s : Nat) : Nat := abrunden (a + bytes) s - a

/-- **Soundness of `region.leeren`'s arithmetic.** For a page `s > 0` and a range whose whole
    pages are non-empty (`von < bis`, the helper's own test): `von <= bis <= bytes` (the edges
    and the pages cover `[0, bytes)` in three consecutive pieces), the handed pages fit the rest
    of the range (`bis - von <= bytes - von`), and `a + von`, `a + bis` are page boundaries. -/
theorem leeren_teilung (a bytes s : Nat) (hs : 0 < s)
    (hlt : leerenVon a s < leerenBis a bytes s) :
    leerenVon a s ≤ leerenBis a bytes s ∧ leerenBis a bytes s ≤ bytes ∧
    leerenBis a bytes s - leerenVon a s ≤ bytes - leerenVon a s ∧
    (a + leerenVon a s) % s = 0 ∧ (a + leerenBis a bytes s) % s = 0 := by
  have h1 := le_aufrunden a s hs
  have h2 := abrunden_le (a + bytes) s
  have h3 := aufrunden_teilbar a s
  have h4 := abrunden_teilbar (a + bytes) s
  unfold leerenVon leerenBis at *
  have e1 : a + (aufrunden a s - a) = aufrunden a s := by omega
  have hb : a ≤ abrunden (a + bytes) s := by omega
  have e2 : a + (abrunden (a + bytes) s - a) = abrunden (a + bytes) s := by omega
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · rw [e1]; exact h3
  · rw [e2]; exact h4

/-- **Witness** (all premises jointly): 10000 bytes from address 5000 on 4096-byte pages -- the
    edges are 3192 and 1808 bytes, one whole page (8192 .. 12288) goes back. -/
theorem leeren_zeuge :
    leerenVon 5000 4096 = 3192 ∧ leerenBis 5000 10000 4096 = 7288 ∧
    (leerenVon 5000 4096 ≤ leerenBis 5000 10000 4096 ∧ leerenBis 5000 10000 4096 ≤ 10000 ∧
      leerenBis 5000 10000 4096 - leerenVon 5000 4096 ≤ 10000 - leerenVon 5000 4096 ∧
      (5000 + leerenVon 5000 4096) % 4096 = 0 ∧ (5000 + leerenBis 5000 10000 4096) % 4096 = 0) :=
  ⟨by decide, by decide, leeren_teilung 5000 10000 4096 (by decide) (by decide)⟩

/-- The helper's test is not decoration: a range inside one page has no whole page
    (`von >= bis`), and handing `[von, bis)` over there would be a negative length. -/
theorem leeren_ohne_seite : ¬ leerenVon 5000 4096 < leerenBis 5000 100 4096 := by decide

end ArenaLaufzeit

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.ArenaLaufzeit.arena_spanne_passt
#print axioms Gabbro.Grammatik.ArenaLaufzeit.arena_commit_bereich
#print axioms Gabbro.Grammatik.ArenaLaufzeit.arena_commit_monoton
#print axioms Gabbro.Grammatik.ArenaLaufzeit.arena_zeuge
#print axioms Gabbro.Grammatik.ArenaLaufzeit.leeren_teilung
#print axioms Gabbro.Grammatik.ArenaLaufzeit.leeren_zeuge
