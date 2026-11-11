module
public import Grammatik.Parser.Item.ElementTief
@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Bare `u32` as its full range (what the exporter computes with). -/
def u32Voll : STyp :=
  .range (.atom "u32") (.lit 0) (.lit 4294967295) false

/-- A type with bare `u32` normalised (lane 160 has no
    full-range rule by design; the normalisation lives here,
    never by editing `Uebersetze.lean`). -/
def normTypU32 : STyp → STyp
  | .atom a => if a == "u32" then u32Voll else .atom a
  | t => t

/-- A slot field with bare `u32` normalised. -/
def normFeldU32 (f : SFeld) : SFeld :=
  { f with ftyp := normTypU32 f.ftyp }

/-- A table part with bare `u32` normalised. -/
def normTabTeilU32 : STabTeil → STabTeil
  | .tSlot fds => .tSlot (fds.map normFeldU32)
  | t => t

/-- A function head with bare `u32` normalised (parameters and
    result). -/
def normSigU32 (s : FnSig) : FnSig :=
  { s with params := s.params.map (fun p => (p.1, normTypU32 p.2)), res := s.res.map normTypU32 }

/-- One item with bare `u32` normalised (no module recursion:
    `uMembers` unwraps the single module `elabU` supports). -/
def normU32Item : SItemTief → SItemTief
  | .tableT n v c a b g parts space =>
    .tableT n v c a b g (parts.map normTabTeilU32) space
  | .fnT s k => .fnT (normSigU32 s) k
  -- An adapter is an ordinary function after desugaring: its head is normalised like one.
  | .adaptT s ps a body => .adaptT (normSigU32 s)
      (ps.map fun | .neu n t => .neu n (normTypU32 t) | p => p) a body
  | .specGroupT n ts es fs => .specGroupT n ts es (fs.map normSigU32)
  | .implGroupT n ts es fs => .implGroupT n (ts.map normTypU32) es (fs.map fun
      | .fnT s b => .fnT (normSigU32 s) b
      | it => it)
  | it => it

/-- Bare `u32` normalised over a top-level list. -/
def normTopU32 : List SItemTief → List SItemTief
  | [] => []
  | it :: rest => normU32Item it :: normTopU32 rest

end Gabbro.Grammatik.Parser.UebersetzeAllg2
