module

public import Grammatik.Parser.Stmt.LibraryCertificates

public section

namespace Gabbro.Grammatik.Uebersetzung

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The nonidentity two-row translator resolves its declared, nonempty library. -/
theorem translation_library_exists_zeuge :
    (libraryDecl (translationMembers true) translationCall).toOption.isSome = true :=
  translation_library_exists true

/-- The same reversing translator has an actual typed lowering. -/
theorem translation_lower_exists_zeuge :
    (lowerAllg (translationUnit true)).toOption.isSome = true :=
  translation_lower_exists true

/-- The translator itself is a real function, and is not its own direct callee. -/
theorem translation_no_direct_call_zeuge :
    direkt (translationDeclaration true).program (translationDeclaration true).translator
      (translationDeclaration true).translator = false :=
  translation_no_direct_call (translationDeclaration true)
    (translationDeclaration true).translator

/-- The certified reversal preserves the starting world for every execution environment. -/
theorem translationCertificate_weltTreu_zeuge
    (oracle : Orakel (declOf (translationUnit true))) (passes : Nat)
    (world : World (declOf (translationUnit true))) :
    (translationCertificate true).WorldPreserving oracle passes world :=
  translationCertificate_weltTreu (source := translationSource true)
    (u := translationUnit true) (decl := translationDeclaration true)
    (translationCertificate true) oracle passes world

end Gabbro.Grammatik.Uebersetzung
