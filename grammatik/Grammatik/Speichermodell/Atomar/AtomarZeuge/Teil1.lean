module

public import Grammatik.Speichermodell.Atomar.Zulassung
public import Grammatik.Speichermodell.Maschine.WeakWitness
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



namespace Gabbro.Grammatik

open Speichermodell Zielsatz

/-! ## 3. Witnesses -/

namespace AtomarZeuge

open NIZeuge

local instance : DecidableEq nD.Ax := inferInstanceAs (DecidableEq Empty)

/-- **The flag is refused by the goal's checker** (configuration 1: `kern` writes the atomic
    `konfig`, `hauptA`/`hauptB` read it, no lock)... -/
theorem n1_abgelehnt : Akzeptiert nP SchwachZeuge.nS nFs [] nCs [NFn.hauptA, NFn.hauptB, NFn.kern] = false :=
  SchwachZeuge.akzeptiert_n1_abgelehnt

/-- **... and accepted with the atomic exemption.** -/
theorem n1_akzeptiertA : AkzeptiertA nP SchwachZeuge.nS nFs [] nCs [NFn.hauptA, NFn.hauptB, NFn.kern] = true := by
  decide

/-- Every thread of `init1` runs `hauptA`, `hauptB`, `kern` or the idle `ruhe`. -/
theorem init1_fall (t : Faden) : (init1 t).1 = NFn.hauptA ∧ t = 0 ∨ (init1 t).1 = NFn.hauptB ∧ t = 1 ∨
    (init1 t).1 = NFn.kern ∧ t = 2 ∨ (init1 t).1 = NFn.ruhe := by
  by_cases h0 : t = 0
  · subst h0; exact Or.inl ⟨rfl, rfl⟩
  · by_cases h1 : t = 1
    · subst h1; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · by_cases h2 : t = 2
      · subst h2; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · refine Or.inr (Or.inr (Or.inr ?_))
        unfold init1
        simp only [h0, h1, h2, if_false]
        rfl

/-- The idle routine is idle. -/
theorem ruhe_ruhig : Ruhig nP nFs NFn.ruhe :=
  (ruheB_iff nFs_voll nCs_voll).mp (by decide)

/-- **The start of configuration 1 is admissible** for its declared starts. -/
theorem n1_start (sp : Speicher nD) :
    StartZulaessig nP SchwachZeuge.nS nFs [NFn.hauptA, NFn.hauptB, NFn.kern] sp init1 where
  wurzel t := by
    rcases init1_fall t with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | h
    · exact Or.inl (by rw [h]; exact List.mem_cons_self)
    · exact Or.inl (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    · exact Or.inl (by rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact Or.inr (by rw [h]; exact ruhe_ruhig)
  einmal t u htu he := by
    refine Or.inl ?_
    rcases init1_fall t with ⟨h, ht⟩ | ⟨h, ht⟩ | ⟨h, ht⟩ | h
    · rcases init1_fall u with ⟨h', hu⟩ | ⟨h', _⟩ | ⟨h', _⟩ | h'
      · exact absurd (ht.trans hu.symm) htu
      · rw [h, h'] at he; cases he
      · rw [h, h'] at he; cases he
      · rw [h, h'] at he; cases he
    · rcases init1_fall u with ⟨h', _⟩ | ⟨h', hu⟩ | ⟨h', _⟩ | h'
      · rw [h, h'] at he; cases he
      · exact absurd (ht.trans hu.symm) htu
      · rw [h, h'] at he; cases he
      · rw [h, h'] at he; cases he
    · rcases init1_fall u with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', hu⟩ | h'
      · rw [h, h'] at he; cases he
      · rw [h, h'] at he; cases he
      · exact absurd (ht.trans hu.symm) htu
      · rw [h, h'] at he; cases he
    · rw [h]; exact ruhe_ruhig
  req _ := by rfl
  sperren L := (nomatch L)

/-- **THE FLAG, COVERED: on configuration 1 every W step is a GA step, and plain tables read
    the newest write** -- for every order assignment, every budget, every start memory. -/
theorem n1_ga (sp : Speicher nD) (ord : nD.Glob → Ordnung) (passes : Nat)
    {W W' : RufMaschineW nD}
    (hr : RufErreichbarW nP nO passes ord (RufStartW (RufStartG nP sp init1)) W) {u : Faden}
    {σ : Speicher nD} {M'' : RufMaschineG nD} {wahl : nD.Tab ⊕ nD.Glob → NachrichtW nD}
    {neu : nD.Tab ⊕ nD.Glob → Nat} (h : SchrittW nP nO passes ord W u W' σ M'' wahl neu) :
    RufSchrittGA nP nO passes W.g u W'.g ∧ ∀ t : NTab, σ.slots t = W.g.speicher.slots t := by
  obtain ⟨h1, h2⟩ := schwach_ist_gA_akzeptiert (ls := []) (cs := nCs) nFs_voll n1_akzeptiertA
    (n1_start sp) nO_gut hr h
  exact ⟨h1, fun t => h2 (.inl t) (fun ⟨_, e, _⟩ => by cases e)⟩

/-- **The language-carried legs on the flag program**, at every machine W reaches from
    configuration 1 (for every order assignment and budget). -/
theorem n1_sprache (sp : Speicher nD) (ord : nD.Glob → Ordnung) (passes : Nat)
    {W : RufMaschineW nD}
    (hr : RufErreichbarW nP nO passes ord (RufStartW (RufStartG nP sp init1)) W) :
    SpurInv W.g ∧ Exklusiv W.g ∧ KeinWarteZyklus W.g ∧ ZeitAb nP nO passes W.g := by
  obtain ⟨h1, h2, _, h4, h5, _⟩ := (w_sprache_akzeptiertA (ls := []) (cs := nCs) (ord := ord)
    (passes := passes) nFs_voll (fun L => nomatch L) nCs_voll n1_akzeptiertA (n1_start sp)
    nO_gut).1 W hr
  exact ⟨h1, h2, h4, h5⟩

/-- **NON-DEGENERATE: W's non-SC step really happens on this accepted program, and it is a GA
    step.** After `kern` wrote `konfig := 3`, W lets `hauptA` read the INITIAL `konfig` and
    store `0` into `tabA[0]`, where G on the same schedule stores `3` (`w_nicht_sc`): a stale
    atomic read. The theorem covers it -- the step is a GA step and the plain tables it was
    presented are G's. -/
theorem n1_nicht_sc_aber_ga (ord : nD.Glob → Ordnung) :
    ∃ W1 W2 : RufMaschineW nD,
      RufErreichbarW nP nO 0 ord (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      RufSchrittW nP nO 0 ord W1 0 W2 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (W2.g.speicher.slots NTab.tabA 0 ()).n = 0 ∧
      ((r1M2 sp0).speicher.slots NTab.tabA 0 ()).n = 3 ∧
      RufSchrittGA nP nO 0 W1.g 0 W2.g := by
  obtain ⟨W1, W2, hW1, hs, _, hk, hA, hG⟩ := SchwachZeuge.w_nicht_sc ord
  obtain ⟨σ, M'', wahl, neu, h⟩ := hs
  exact ⟨W1, W2, hW1, ⟨σ, M'', wahl, neu, h⟩, hk, hA, hG, (n1_ga sp0 ord 0 hW1 h).1⟩

/-- On this accepted program the SC leg is false: `SchwachSC` fails at the machine G reaches
    after `kern`'s write (`schwach_nicht_trivial`). A goal over `AkzeptiertA` cannot keep the
    leg `schwach` as it is; its GA form is `n1_ga`. -/
theorem n1_schwachSC_falsch :
    AkzeptiertA nP SchwachZeuge.nS nFs [] nCs [NFn.hauptA, NFn.hauptB, NFn.kern] = true ∧
      ¬ SchwachSC nP nO 0 (RufStartG nP sp0 init1) (r1M1 sp0) :=
  ⟨n1_akzeptiertA, SchwachZeuge.schwach_nicht_trivial⟩

/-- **THE PER-CORE FOLD (OFFEN O17, read half).** `zaehlA` on two threads (a pool, each
    instance writing the atomic accumulator `zaehler`) and `zaehlB` reading it (the fold): the
    goal's checker refuses at the footprint component ... -/
theorem faltung_abgelehnt :
    Akzeptiert nP SchwachZeuge.nS nFs [] nCs [NFn.zaehlA, NFn.zaehlA, NFn.zaehlB] = false ∧
      fussWB nP SchwachZeuge.nS nFs [NFn.zaehlA, NFn.zaehlA, NFn.zaehlB] = false := by
  decide

/-- ... and `AkzeptiertA` accepts. -/
theorem faltung_akzeptiertA :
    AkzeptiertA nP SchwachZeuge.nS nFs [] nCs [NFn.zaehlA, NFn.zaehlA, NFn.zaehlB] = true := by
  decide

/-- Non-degenerate: the fold reads the atomic the pool writes. -/
theorem faltung_echt :
    TraegerSchreibt (D := nD) NFn.zaehlA (.inr NGlob.zaehler) = true ∧
      (.inr NGlob.zaehler : nD.Tab ⊕ nD.Glob) ∈ fussOrteG nP NFn.zaehlB ∧
      nD.atomar NGlob.zaehler = true :=
  ⟨rfl, istIn_iff.mp (by decide), rfl⟩

end AtomarZeuge
end Gabbro.Grammatik
