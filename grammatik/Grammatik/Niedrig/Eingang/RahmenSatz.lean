/-
  File:      Grammatik/Niedrig/Eingang/RahmenSatz.lean
  Subject:   THEOREMS FOR THE ENTRY FRAME DESCRIPTORS (L5a): accepted
    frames keep preserved and clobbered disjoint, keep every list
    duplicate-free, clobber no pure input, name no two entries, carry the
    record's context fields, and refuse deterministically with the first
    failing check's message.

  Accepted means: (1) no record names both a vector and a `via` handler;
  preserved and clobbered are disjoint; every input clobbered is also an
  output; `erhaelt`, `kills`, `regIn` and `regOut` are duplicate-free; no
  output is clobbered without an input; the stack check holds. The refusal
  is deterministic: each lemma below says that when checks 1..k-1 pass and
  check k fails, the result is message k. Per-kind frame theorems are L5b,
  not here.
-/
module

public import Grammatik.Niedrig.Eingang.Rahmen

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Eingang

open Gabbro.Grammatik

/-! ## Accepted frames keep preserved and clobbered disjoint -/

/-- An empty overlap means disjoint, by induction over the first list. -/
theorem ueber_leer_getrennt (xs ys : List String)
    (h : ueberschneidung xs ys = []) : getrennt xs ys := by
  induction xs with
  | nil =>
    exact True.intro
  | cons x xs ih =>
    have hunfold : ueberschneidung (x :: xs) ys =
        match ys.contains x with
        | true => x :: ueberschneidung xs ys
        | false => ueberschneidung xs ys := rfl
    rw [hunfold] at h
    cases hc : ys.contains x with
    | true =>
      rw [hc] at h
      cases h
    | false =>
      rw [hc] at h
      show ys.contains x = false ∧ getrennt xs ys
      exact ⟨hc, ih h⟩

/-- `frameOf` accepts only when preserved and clobbered are disjoint. -/
theorem frameOf_akzeptiert_getrennt (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) : getrennt f.erhaelt f.kills := by
  unfold frameOf at h
  split at h
  · rename_i hok
    unfold alleOk at hok
    cases h
    obtain ⟨_, h2, _, _, _, _, _, _, _⟩ := hok
    exact ueber_leer_getrennt d.erhaelt d.kills h2
  · cases h

/-! ## Accepted frames are duplicate-free -/

/-- A `contains`-negative element is not a member. -/
theorem ohne_enthalten {xs : List String} {x : String}
    (hc : xs.contains x = false) : x ∉ xs := by
  intro hm
  have h1 : xs.contains x = true := List.contains_iff_mem.mpr hm
  rw [h1] at hc
  cases hc

/-- No duplicate flag means no duplicate element, by induction. -/
theorem doppelt_nodup (xs : List String) (h : hatDoppelt xs = false) :
    xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    have hunfold : hatDoppelt (x :: xs) =
        (xs.contains x || hatDoppelt xs) := rfl
    rw [hunfold] at h
    cases hc : xs.contains x with
    | true =>
      rw [hc] at h
      cases h
    | false =>
      cases hd : hatDoppelt xs with
      | true =>
        rw [hc, hd] at h
        cases h
      | false =>
        exact List.nodup_cons.mpr ⟨ohne_enthalten hc, ih hd⟩

/-- `frameOf` accepts only duplicate-free preserved sets. -/
theorem frameOf_akzeptiert_erhaeltNodup (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) : d.erhaelt.Nodup := by
  unfold frameOf at h
  split at h
  · rename_i hok
    unfold alleOk at hok
    cases h
    obtain ⟨_, _, _, hd, _, _, _, _, _⟩ := hok
    exact doppelt_nodup _ hd
  · cases h

/-- `frameOf` accepts only duplicate-free clobbered sets. -/
theorem frameOf_akzeptiert_killsNodup (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) : d.kills.Nodup := by
  unfold frameOf at h
  split at h
  · rename_i hok
    unfold alleOk at hok
    cases h
    obtain ⟨_, _, _, _, hd, _, _, _, _⟩ := hok
    exact doppelt_nodup _ hd
  · cases h

/-- `frameOf` accepts only duplicate-free input maps. -/
theorem frameOf_akzeptiert_regInNodup (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) : (regNamen d.regIn).Nodup := by
  unfold frameOf at h
  split at h
  · rename_i hok
    unfold alleOk at hok
    cases h
    obtain ⟨_, _, _, _, _, hd, _, _, _⟩ := hok
    exact doppelt_nodup _ hd
  · cases h

/-- `frameOf` accepts only duplicate-free output maps. -/
theorem frameOf_akzeptiert_regOutNodup (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) : (regNamen d.regOut).Nodup := by
  unfold frameOf at h
  split at h
  · rename_i hok
    unfold alleOk at hok
    cases h
    obtain ⟨_, _, _, _, _, _, hd, _, _⟩ := hok
    exact doppelt_nodup _ hd
  · cases h

/-! ## Accepted frames name no two entries and clobber no pure input -/

/-- `frameOf` accepts only records without both a vector and a `via`. -/
theorem frameOf_akzeptiert_keinVektorVia (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) :
    ¬ ∃ (v : Parser.SExpr) (w : String), d.vektor = some v ∧ d.via = some w := by
  unfold frameOf at h
  split at h
  · rename_i hok
    unfold alleOk at hok
    cases h
    obtain ⟨hb, _, _, _, _, _, _, _, _⟩ := hok
    intro hEx
    obtain ⟨v, w, hv, hw⟩ := hEx
    have ht : hatBeide d = true := by
      have e : hatBeide d =
          match d.vektor, d.via with
          | some _, some _ => true
          | _, _ => false := rfl
      rw [e, hv, hw]
    rw [ht] at hb
    cases hb
  · cases h

/-- `frameOf` accepts only when every clobbered input is also an output:
    the inputs outside the outputs are disjoint from the clobbered set. -/
theorem frameOf_akzeptiert_ein (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) :
    getrennt (ohneAus (regNamen d.regIn) (regNamen d.regOut)) d.kills := by
  unfold frameOf at h
  split at h
  · rename_i hok
    unfold alleOk at hok
    cases h
    obtain ⟨_, _, h3, _, _, _, _, _, _⟩ := hok
    exact ueber_leer_getrennt _ _ h3
  · cases h

/-- The frame's kind determines the privilege pair. -/
theorem frameOf_privPaar (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) :
    (f.privVor, f.privNach) = privPaar f.art := by
  unfold frameOf at h
  split at h
  · cases h
    rfl
  · cases h

/-! ## Accepted frames carry the record's context fields -/

/-- `frameOf` carries the architecture name. -/
theorem frameOf_traegtArch (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) : f.arch = d.arch := by
  unfold frameOf at h
  split at h
  · cases h
    rfl
  · cases h

/-- `frameOf` carries the per-cpu mark. -/
theorem frameOf_traegtPerCpu (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) : f.perCpu = d.perCpu := by
  unfold frameOf at h
  split at h
  · cases h
    rfl
  · cases h

/-- `frameOf` carries the `ist` expression. -/
theorem frameOf_traegtIst (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) : f.ist = d.ist := by
  unfold frameOf at h
  split at h
  · cases h
    rfl
  · cases h

/-- `frameOf` carries the nesting mark. -/
theorem frameOf_traegtNest (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) : f.nest = d.nest := by
  unfold frameOf at h
  split at h
  · cases h
    rfl
  · cases h

/-- `frameOf` carries the dispatch path. -/
theorem frameOf_traegtDispatch (d : Parser.SEingang) (f : EntryFrame)
    (h : frameOf d = Except.ok f) : f.dispatch = d.dispatch := by
  unfold frameOf at h
  split at h
  · cases h
    rfl
  · cases h

/-! ## The refusal is the first failing check -/

/-- Check 1 fails: both a vector and a `via` handler. -/
theorem frameOf_fehler_beide (d : Parser.SEingang) (v : Parser.SExpr) (w : String)
    (hv : d.vektor = some v) (hw : d.via = some w) :
    frameOf d = Except.error einVektorVia := by
  have ht : hatBeide d = true := by
    have e : hatBeide d =
        match d.vektor, d.via with
        | some _, some _ => true
        | _, _ => false := rfl
    rw [e, hv, hw]
  have hnc : ¬ alleOk d := by
    intro hc
    unfold alleOk at hc
    obtain ⟨h1, _, _, _, _, _, _, _, _⟩ := hc
    rw [ht] at h1
    cases h1
  unfold frameOf
  rw [if_neg hnc]
  have e1 : ersteFehler d = einVektorVia := by
    unfold ersteFehler
    rw [ht]
  rw [e1]

/-- Checks 1 passes and check 2 fails: the preserved/clobbered overlap. -/
theorem frameOf_fehler_erhaelt (d : Parser.SEingang) (z : String) (zs : List String)
    (hb : hatBeide d = false)
    (hov : ueberschneidung d.erhaelt d.kills = z :: zs) :
    frameOf d = Except.error einErhVerdeckt := by
  have hnc : ¬ alleOk d := by
    intro hc
    unfold alleOk at hc
    obtain ⟨_, h2, _, _, _, _, _, _, _⟩ := hc
    rw [hov] at h2
    cases h2
  unfold frameOf
  rw [if_neg hnc]
  have e1 : ersteFehler d = einErhVerdeckt := by
    unfold ersteFehler
    rw [hb, hov]
  rw [e1]

/-- Checks 1-2 pass and check 3 fails: an input clobbered without output. -/
theorem frameOf_fehler_eingabe (d : Parser.SEingang) (z : String) (zs : List String)
    (hb : hatBeide d = false)
    (hov : ueberschneidung d.erhaelt d.kills = [])
    (hin : ueberschneidung (ohneAus (regNamen d.regIn) (regNamen d.regOut)) d.kills = z :: zs) :
    frameOf d = Except.error einEinVerdeckt := by
  have hnc : ¬ alleOk d := by
    intro hc
    unfold alleOk at hc
    obtain ⟨_, _, h3, _, _, _, _, _, _⟩ := hc
    rw [hin] at h3
    cases h3
  unfold frameOf
  rw [if_neg hnc]
  have e1 : ersteFehler d = einEinVerdeckt := by
    unfold ersteFehler
    rw [hb, hov, hin]
  rw [e1]

/-- Checks 1-3 pass and check 4 fails: a duplicate in `erhaelt`. -/
theorem frameOf_fehler_doppeltErhaelt (d : Parser.SEingang)
    (hb : hatBeide d = false)
    (hov : ueberschneidung d.erhaelt d.kills = [])
    (hin : ueberschneidung (ohneAus (regNamen d.regIn) (regNamen d.regOut)) d.kills = [])
    (hdE : hatDoppelt d.erhaelt = true) :
    frameOf d = Except.error einDoppelt := by
  have hnc : ¬ alleOk d := by
    intro hc
    unfold alleOk at hc
    obtain ⟨_, _, _, h4, _, _, _, _, _⟩ := hc
    rw [hdE] at h4
    cases h4
  unfold frameOf
  rw [if_neg hnc]
  have e1 : ersteFehler d = einDoppelt := by
    unfold ersteFehler
    rw [hb, hov, hin, hdE]
  rw [e1]

/-- Checks 1-4 pass and check 5 fails: a duplicate in `kills`. -/
theorem frameOf_fehler_doppeltKills (d : Parser.SEingang)
    (hb : hatBeide d = false)
    (hov : ueberschneidung d.erhaelt d.kills = [])
    (hin : ueberschneidung (ohneAus (regNamen d.regIn) (regNamen d.regOut)) d.kills = [])
    (hdE : hatDoppelt d.erhaelt = false)
    (hdK : hatDoppelt d.kills = true) :
    frameOf d = Except.error einDoppelt := by
  have hnc : ¬ alleOk d := by
    intro hc
    unfold alleOk at hc
    obtain ⟨_, _, _, _, h5, _, _, _, _⟩ := hc
    rw [hdK] at h5
    cases h5
  unfold frameOf
  rw [if_neg hnc]
  have e1 : ersteFehler d = einDoppelt := by
    unfold ersteFehler
    rw [hb, hov, hin, hdE, hdK]
  rw [e1]

/-- Checks 1-5 pass and check 6 fails: a register bound twice in `regIn`. -/
theorem frameOf_fehler_doppeltRegIn (d : Parser.SEingang)
    (hb : hatBeide d = false)
    (hov : ueberschneidung d.erhaelt d.kills = [])
    (hin : ueberschneidung (ohneAus (regNamen d.regIn) (regNamen d.regOut)) d.kills = [])
    (hdE : hatDoppelt d.erhaelt = false)
    (hdK : hatDoppelt d.kills = false)
    (hdI : hatDoppelt (regNamen d.regIn) = true) :
    frameOf d = Except.error einDoppelt := by
  have hnc : ¬ alleOk d := by
    intro hc
    unfold alleOk at hc
    obtain ⟨_, _, _, _, _, h6, _, _, _⟩ := hc
    rw [hdI] at h6
    cases h6
  unfold frameOf
  rw [if_neg hnc]
  have e1 : ersteFehler d = einDoppelt := by
    unfold ersteFehler
    rw [hb, hov, hin, hdE, hdK, hdI]
  rw [e1]

/-- Checks 1-6 pass and check 7 fails: a register bound twice in `regOut`. -/
theorem frameOf_fehler_doppeltRegOut (d : Parser.SEingang)
    (hb : hatBeide d = false)
    (hov : ueberschneidung d.erhaelt d.kills = [])
    (hin : ueberschneidung (ohneAus (regNamen d.regIn) (regNamen d.regOut)) d.kills = [])
    (hdE : hatDoppelt d.erhaelt = false)
    (hdK : hatDoppelt d.kills = false)
    (hdI : hatDoppelt (regNamen d.regIn) = false)
    (hdO : hatDoppelt (regNamen d.regOut) = true) :
    frameOf d = Except.error einDoppelt := by
  have hnc : ¬ alleOk d := by
    intro hc
    unfold alleOk at hc
    obtain ⟨_, _, _, _, _, _, h7, _, _⟩ := hc
    rw [hdO] at h7
    cases h7
  unfold frameOf
  rw [if_neg hnc]
  have e1 : ersteFehler d = einDoppelt := by
    unfold ersteFehler
    rw [hb, hov, hin, hdE, hdK, hdI, hdO]
  rw [e1]

/-- Checks 1-7 pass and check 8 fails: an output clobbered without input. -/
theorem frameOf_fehler_ausgabe (d : Parser.SEingang) (z : String) (zs : List String)
    (hb : hatBeide d = false)
    (hov : ueberschneidung d.erhaelt d.kills = [])
    (hin : ueberschneidung (ohneAus (regNamen d.regIn) (regNamen d.regOut)) d.kills = [])
    (hdE : hatDoppelt d.erhaelt = false)
    (hdK : hatDoppelt d.kills = false)
    (hdI : hatDoppelt (regNamen d.regIn) = false)
    (hdO : hatDoppelt (regNamen d.regOut) = false)
    (hav : ausVerdeckt (regNamen d.regOut) (regNamen d.regIn) d.kills = z :: zs) :
    frameOf d = Except.error einAusVerdeckt := by
  have hnc : ¬ alleOk d := by
    intro hc
    unfold alleOk at hc
    obtain ⟨_, _, _, _, _, _, _, h8, _⟩ := hc
    rw [hav] at h8
    cases h8
  unfold frameOf
  rw [if_neg hnc]
  have e1 : ersteFehler d = einAusVerdeckt := by
    unfold ersteFehler
    rw [hb, hov, hin, hdE, hdK, hdI, hdO, hav]
  rw [e1]

/-- Checks 1-8 pass and check 9 fails: the missing stack. -/
theorem frameOf_fehler_stapel (d : Parser.SEingang)
    (hb : hatBeide d = false)
    (hov : ueberschneidung d.erhaelt d.kills = [])
    (hin : ueberschneidung (ohneAus (regNamen d.regIn) (regNamen d.regOut)) d.kills = [])
    (hdE : hatDoppelt d.erhaelt = false)
    (hdK : hatDoppelt d.kills = false)
    (hdI : hatDoppelt (regNamen d.regIn) = false)
    (hdO : hatDoppelt (regNamen d.regOut) = false)
    (hav : ausVerdeckt (regNamen d.regOut) (regNamen d.regIn) d.kills = [])
    (hst : stapelOk (artAus d) d.stapel = false) :
    frameOf d = Except.error einStapelFehlt := by
  have hnc : ¬ alleOk d := by
    intro hc
    unfold alleOk at hc
    obtain ⟨_, _, _, _, _, _, _, _, h9⟩ := hc
    rw [hst] at h9
    cases h9
  unfold frameOf
  rw [if_neg hnc]
  have e1 : ersteFehler d = einStapelFehlt := by
    unfold ersteFehler
    rw [hb, hov, hin, hdE, hdK, hdI, hdO, hav]
  rw [e1]

#print axioms Gabbro.Grammatik.Niedrig.Eingang.doppelt_nodup
#print axioms Gabbro.Grammatik.Niedrig.Eingang.frameOf_akzeptiert_getrennt
#print axioms Gabbro.Grammatik.Niedrig.Eingang.frameOf_akzeptiert_ein
#print axioms Gabbro.Grammatik.Niedrig.Eingang.frameOf_akzeptiert_keinVektorVia
#print axioms Gabbro.Grammatik.Niedrig.Eingang.frameOf_privPaar
#print axioms Gabbro.Grammatik.Niedrig.Eingang.frameOf_traegtArch
#print axioms Gabbro.Grammatik.Niedrig.Eingang.frameOf_fehler_eingabe

end Gabbro.Grammatik.Niedrig.Eingang
