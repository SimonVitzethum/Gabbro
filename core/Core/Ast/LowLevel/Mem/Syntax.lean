module

public import Core.Ast.LowLevel.Syntax
public import Core.Katalog.Seiten

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog

/-- Memory and address-space management forms (§4.2–4.3): region partition and
    merge, space creation, mapping, protection, revocation, shootdown and
    activation. A separate sub-category of the low-level tree so device and
    register forms can grow beside it without touching these constructors. -/
inductive MemForm where
  | splitAt
  | splitPages
  | merge
  | newSpace
  | mapSpace
  | protectSpace
  | unmapSpace
  | flushSpace
  | activateSpace
  deriving DecidableEq

/-- Low-level memory-management leaves of the reference AST. Region operands
    resolve through the region names of the arrival contract, spaces through a
    separate space scope, and the revocation token of `flush` through the
    token scope; the enclosing statement layer keeps the token scope and the
    frame's token bindings in the same order. -/
inductive MemTree : MemForm → Type where
  /-- `r.split_at(a)`: partition the held region `r` at the address `a`. -/
  | splitAt (region : Identifier) (point : Nat) : MemTree .splitAt
  /-- `r.split_pages(n)`: split the first `n` pages off the held region `r`. -/
  | splitPages (region : Identifier) (pages : Nat) : MemTree .splitPages
  /-- `merge(r1, r2)`: join two adjacent held regions into one. -/
  | merge (first second : Identifier) : MemTree .merge
  /-- `space.new(tables)`: create an address space from the owned table region. -/
  | newSpace (tables : Identifier) : MemTree .newSpace
  /-- `map(s, virt, frames, rights { … }) else full`: install the mapping. -/
  | mapSpace (space : Identifier) (virt : Nat) (frames : Identifier)
      (rights : List Speicherdienst) : MemTree .mapSpace
  /-- `protect(s, virt, n, rights { … })`: narrow the rights of mapped pages. -/
  | protectSpace (space : Identifier) (virt : Nat) (pages : Nat)
      (rights : List Speicherdienst) : MemTree .protectSpace
  /-- `unmap(s, virt, n)`: clear the entries and take the revocation token. -/
  | unmapSpace (space : Identifier) (virt : Nat) (pages : Nat) : MemTree .unmapSpace
  /-- `flush(name)`: invalidate stale translations and return the frames. -/
  | flushSpace (name : Identifier) : MemTree .flushSpace
  /-- `activate(s)`: install the well-formed space on this core. -/
  | activateSpace (space : Identifier) : MemTree .activateSpace

def rightsToken : Speicherdienst → Token
  | .read => keyword "read"
  | .write => keyword "write"
  | .execute => keyword "execute"

def rightsTokens (rights : List Speicherdienst) : List Token :=
  (rights.map rightsToken).intersperse comma

def rightsPrint : Speicherdienst → PrintedToken
  | .read => lowWord 'r' "ead"
  | .write => lowWord 'w' "rite"
  | .execute => lowWord 'e' "xecute"

def rightsPrints (rights : List Speicherdienst) : List PrintedToken :=
  ((rights.map rightsPrint).intersperse printComma)

def MemTree.printPieces : MemTree form → List PrintedToken
  | .splitAt region point =>
      [region.print, printDot, lowWord 's' "plit_at", printOpen, printInteger point, printClose]
  | .splitPages region pages =>
      [region.print, printDot, lowWord 's' "plit_pages", printOpen, printInteger pages, printClose]
  | .merge first second =>
      [lowWord 'm' "erge", printOpen, first.print, printComma, second.print, printClose]
  | .newSpace tables =>
      [lowWord 's' "pace", printDot, lowWord 'n' "ew", printOpen, tables.print, printClose]
  | .mapSpace space virt frames rights =>
      [lowWord 'm' "ap", printOpen, space.print, printComma, printInteger virt, printComma,
        frames.print, printComma, lowWord 'r' "ights", printOpenBrace] ++ rightsPrints rights ++
        [printCloseBrace, printClose, lowWord 'e' "lse", lowWord 'f' "ull"]
  | .protectSpace space virt pages rights =>
      [lowWord 'p' "rotect", printOpen, space.print, printComma, printInteger virt, printComma,
        printInteger pages, printComma, lowWord 'r' "ights", printOpenBrace] ++
        rightsPrints rights ++ [printCloseBrace, printClose]
  | .unmapSpace space virt pages =>
      [lowWord 'u' "nmap", printOpen, space.print, printComma, printInteger virt, printComma,
        printInteger pages, printClose]
  | .flushSpace name => [lowWord 'f' "lush", printOpen, name.print, printClose]
  | .activateSpace space => [lowWord 'a' "ctivate", printOpen, space.print, printClose]

/-- Exact productions over canonical tokens. Numbers use the decimal token and
    rights use the closed read/write/execute vocabulary. -/
def MemTree.production : MemTree form → List Token → Prop
  | .splitAt region point => fun tokens =>
      tokens = [.word region.val, dot, keyword "split_at", openParen, .natural point, closeParen]
  | .splitPages region pages => fun tokens =>
      tokens = [.word region.val, dot, keyword "split_pages", openParen, .natural pages, closeParen]
  | .merge first second => fun tokens =>
      tokens = [keyword "merge", openParen, .word first.val, comma, .word second.val, closeParen]
  | .newSpace tables => fun tokens =>
      tokens = [keyword "space", dot, keyword "new", openParen, .word tables.val, closeParen]
  | .mapSpace space virt frames rights => fun tokens =>
      tokens = [keyword "map", openParen, .word space.val, comma, .natural virt, comma,
        .word frames.val, comma, keyword "rights", openBrace] ++ rightsTokens rights ++
        [closeBrace, closeParen, keyword "else", keyword "full"]
  | .protectSpace space virt pages rights => fun tokens =>
      tokens = [keyword "protect", openParen, .word space.val, comma, .natural virt, comma,
        .natural pages, comma, keyword "rights", openBrace] ++ rightsTokens rights ++
        [closeBrace, closeParen]
  | .unmapSpace space virt pages => fun tokens =>
      tokens = [keyword "unmap", openParen, .word space.val, comma, .natural virt, comma,
        .natural pages, closeParen]
  | .flushSpace name => fun tokens =>
      tokens = [keyword "flush", openParen, .word name.val, closeParen]
  | .activateSpace space => fun tokens =>
      tokens = [keyword "activate", openParen, .word space.val, closeParen]

def MemParse (text : RawText) (tree : MemTree form) : Prop :=
  Text.Parse (tokenGrammar (fun tokens (tree : MemTree form) => tree.production tokens)) text tree

def MemTree.print (tree : MemTree form) : RawText := PrintedToken.render tree.printPieces

end Gabbro.Core.Ast.LowLevel
