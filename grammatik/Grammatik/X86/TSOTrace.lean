/-
  File:      Grammatik/X86/TSOTrace.lean
  Subject:   Append-only TSO trace history with increasing fresh timestamps.

  Lane 596: `TSOHistory.histVon` is a two-message snapshot (timestamps 0/1)
  and its `fresh2` lemma builds no preserved growing history. This module
  links canonical `TSOZustand`/`TSOSchritt` traces to an append-only
  history projection: issues keep the history, flushes append one release
  message (`Speichermodell.nachricht .freigabe`) at a strictly fresh
  timestamp, and the writer view joins it. No new TSO executor, no new
  source semantics. Byte granularity only: typed-carrier W/GX stays CUTS.
-/
import Grammatik.X86.TSOHistory

namespace Gabbro.Grammatik.X86

/-- A trace node: the canonical TSO state plus its grown history, the
    per-core views, and the next fresh timestamp. -/
structure SpurKnoten where
  tso : TSOZustand
  hist : Adresse → List (Speichermodell.Nachricht Adresse Byte)
  blick : Nat → Speichermodell.Sicht Adresse
  frisch : Nat

/-- Start node over a TSO state: only the initial message, empty views,
    timestamp 1 is the next fresh one. -/
def spurStart (s : TSOZustand) : SpurKnoten :=
  { tso := s
    hist := fun _ => [⟨0, 0, Speichermodell.Sicht.null⟩]
    blick := fun _ => Speichermodell.Sicht.null
    frisch := 1 }

/-- One trace step, projecting the canonical step: an issue keeps history,
    views and clock; a flush of the actual oldest entry `e` appends one
    release message at the old clock and advances it. The appended value
    comes from the flushed entry, never from a desired conclusion. -/
inductive SpurSchritt : SpurKnoten → SpurKnoten → Prop where
  | issue (n n' : SpurKnoten) (c : Nat) (a : Adresse) (v : Byte)
      (h : issueByte n.tso c a v = some n'.tso)
      (hh : n'.hist = n.hist)
      (hb : n'.blick = n.blick)
      (hf : n'.frisch = n.frisch) : SpurSchritt n n'
  | flush (n n' : SpurKnoten) (c : Nat) (e : TSOEintrag)
      (rest : List TSOEintrag)
      (h : flushKern n.tso c = some n'.tso)
      (he : n.tso.puffer c = e :: rest)
      (hh : n'.hist = fun x =>
        if x = e.addr then n.hist x ++
          [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
            (n.blick c) e.addr n.frisch e.wert]
        else n.hist x)
      (hb : n'.blick = fun d =>
        if d = c then (n.blick c).setze e.addr n.frisch else n.blick d)
      (hf : n'.frisch = n.frisch + 1) : SpurSchritt n n'

/-- Reached trace nodes from `n0`. -/
inductive SpurErreichbar (n0 : SpurKnoten) : SpurKnoten → Prop where
  | start : SpurErreichbar n0 n0
  | schritt {n n' : SpurKnoten} :
      SpurErreichbar n0 n → SpurSchritt n n' → SpurErreichbar n0 n'

/- CUTS:
    - So far only the node/step vocabulary; preservation, freshness,
      forwarding and the joint witness follow as increments.
    - Byte granularity only: no typed-carrier W/GX mapping, no aligned
      multi-byte atomicity, no LOCK RMW, no run induction to W runs.
-/

end Gabbro.Grammatik.X86
