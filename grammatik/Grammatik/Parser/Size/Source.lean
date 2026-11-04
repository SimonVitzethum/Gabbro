module

public import Grammatik.Parser.Item.ElementTief.Kopf.Teil2
public import Grammatik.Parser.Size.Basic
public meta import Grammatik.Parser.Size.Derive

public section
namespace Gabbro.Grammatik.Parser.Size

/- Exact native realization of every field of the original source tree. The
    exporter reads constructors; this list selects their existing type closure,
    including lossless library tokens and all metadata, without interpreting it. -/
derive_source_size source for SItemTief with [
  Token, XKind, SExpr, STyp, SEnde, SLibraryCall, SAnw,
  SEffekt, SKlausel, SGenericParam, SAdaptParam, SAdapt, FnSig,
  SFeld, SRegFeld, SReg, STrans, SGruppenInv, SKonstWert,
  STabTeil, SGerTeil, SAnKlasse, SProfEintrag, SRegBind, SBootSchritt,
  SWeg, SEingang, SCheck, SHerkunft, SBind, SGate, SWay, SSyscall, SItemTief]

end Gabbro.Grammatik.Parser.Size
