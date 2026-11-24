module

public import Core.Ast.LowLevel.Exec.State

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog

/-- Execution-state and transfer forms (§4.1) with entry declarations (§4.4).
    State changes are named transitions between declared neutral states; no
    source names an instruction, a GIR cell, or a target row. -/
inductive ExecForm where
  | stateDecl
  | jump
  | jumpLong
  | waitInterrupt
  | stopCore
  | entryDecl
  deriving DecidableEq

/-- Low-level execution leaves of the reference AST. Code items, states,
    spaces and stacks resolve through the arrival-contract scope; the
    enclosing statement layer keeps the scope and the frame tables in the
    same order. -/
inductive ExecTree : ExecForm → Type where
  /-- `state S { width 64, privilege kernel, translation on, guards { … } }`. -/
  | stateDecl (name : Identifier) (decl : ExecStateDecl) : ExecTree .stateDecl
  /-- `jump f();`: tail transfer to a code item in the SAME state. -/
  | jump (target : Identifier) : ExecTree .jump
  /-- `jump long f() into S [with space s] [stack t];`: transfer to ANOTHER state. -/
  | jumpLong (target dest : Identifier) (space stack : Option Identifier) : ExecTree .jumpLong
  /-- `wait for interrupt;`. -/
  | waitInterrupt : ExecTree .waitInterrupt
  /-- `stop core;` (`never`). -/
  | stopCore : ExecTree .stopCore
  /-- `entry NAME KIND stack per core|own [priority N];`. -/
  | entryDecl (name : Identifier) (kind : EntryKind) (stack : EntryStack)
      (priority : Option Nat) : ExecTree .entryDecl

def privilegeKeyword : ExecPrivilege → Token
  | .machine => keyword "machine"
  | .hypervisor => keyword "hypervisor"
  | .kernel => keyword "kernel"
  | .user => keyword "user"

def translationKeyword : ExecTranslation → Token
  | .off => keyword "off"
  | .on => keyword "on"

def guardKeyword : ExecGuard → Token
  | .noExecute => keyword "no_execute"
  | .userAccessGate => keyword "user_access"
  | .noUserExec => keyword "no_user_exec"

def entryKindKeyword : EntryKind → Token
  | .interrupt => keyword "interrupt"
  | .exception => keyword "exception"
  | .nonmaskable => keyword "nonmaskable"
  | .machineCheck => keyword "machine_check"
  | .fatal => keyword "fatal"

def privilegePrint : ExecPrivilege → PrintedToken
  | .machine => lowWord 'm' "achine"
  | .hypervisor => lowWord 'h' "ypervisor"
  | .kernel => lowWord 'k' "ernel"
  | .user => lowWord 'u' "ser"

def translationPrint : ExecTranslation → PrintedToken
  | .off => lowWord 'o' "ff"
  | .on => lowWord 'o' "n"

def guardPrint : ExecGuard → PrintedToken
  | .noExecute => lowWord 'n' "o_execute"
  | .userAccessGate => lowWord 'u' "ser_access"
  | .noUserExec => lowWord 'n' "o_user_exec"

def entryKindPrint : EntryKind → PrintedToken
  | .interrupt => lowWord 'i' "nterrupt"
  | .exception => lowWord 'e' "xception"
  | .nonmaskable => lowWord 'n' "onmaskable"
  | .machineCheck => lowWord 'm' "achine_check"
  | .fatal => lowWord 'f' "atal"

def ExecTree.printPieces : ExecTree form → List PrintedToken
  | .stateDecl name decl =>
      [lowWord 's' "tate", name.print, printOpenBrace, lowWord 'w' "idth",
        printInteger decl.widthBits, printComma, lowWord 'p' "rivilege",
        privilegePrint decl.privilege, printComma, lowWord 't' "ranslation",
        translationPrint decl.translation, printComma, lowWord 'g' "uards",
        printOpenBrace] ++
        ((decl.guards.map guardPrint).intersperse printComma) ++
        [printCloseBrace, printCloseBrace, printSemicolon]
  | .jump target =>
      [lowWord 'j' "ump", target.print, printOpen, printClose, printSemicolon]
  | .jumpLong target dest space stack =>
      [lowWord 'j' "ump", lowWord 'l' "ong", target.print, printOpen, printClose,
        lowWord 'i' "nto", dest.print] ++
        (space.map (fun s => [lowWord 'w' "ith", lowWord 's' "pace", s.print])).getD [] ++
        (stack.map (fun s => [lowWord 's' "tack", s.print])).getD [] ++
        [printSemicolon]
  | .waitInterrupt =>
      [lowWord 'w' "ait", lowWord 'f' "or", lowWord 'i' "nterrupt", printSemicolon]
  | .stopCore =>
      [lowWord 's' "top", lowWord 'c' "ore", printSemicolon]
  | .entryDecl name kind stack priority =>
      [lowWord 'e' "ntry", name.print, entryKindPrint kind, lowWord 's' "tack"] ++
        (match stack with | .perCore => [lowWord 'p' "er", lowWord 'c' "ore"] | .own => [lowWord 'o' "wn"]) ++
        (priority.map (fun n => [lowWord 'p' "riority", printInteger n])).getD [] ++
        [printSemicolon]

def guardsTokens (guards : List ExecGuard) : List Token :=
  (guards.map guardKeyword).intersperse comma

/-- Exact productions over canonical tokens. Widths use the decimal token;
    privilege, translation, guards, entry kinds and stacks use closed
    vocabularies. -/
def ExecTree.production : ExecTree form → List Token → Prop
  | .stateDecl name decl => fun tokens =>
      tokens = [keyword "state", .word name.val, openBrace, keyword "width",
        .natural decl.widthBits, comma, keyword "privilege", privilegeKeyword decl.privilege,
        comma, keyword "translation", translationKeyword decl.translation, comma,
        keyword "guards", openBrace] ++ guardsTokens decl.guards ++
        [closeBrace, closeBrace, semicolon]
  | .jump target => fun tokens =>
      tokens = [keyword "jump", .word target.val, openParen, closeParen, semicolon]
  | .jumpLong target dest space stack => fun tokens =>
      (space.isNone ∧ stack.isNone ∧
        tokens = [keyword "jump", keyword "long", .word target.val, openParen, closeParen,
          keyword "into", .word dest.val, semicolon]) ∨
      (∃ sp, space = some sp ∧ stack.isNone ∧
        tokens = [keyword "jump", keyword "long", .word target.val, openParen, closeParen,
          keyword "into", .word dest.val, keyword "with", keyword "space",
          .word sp.val, semicolon]) ∨
      (∃ st, space.isNone ∧ stack = some st ∧
        tokens = [keyword "jump", keyword "long", .word target.val, openParen, closeParen,
          keyword "into", .word dest.val, keyword "stack", .word st.val, semicolon]) ∨
      (∃ sp st, space = some sp ∧ stack = some st ∧
        tokens = [keyword "jump", keyword "long", .word target.val, openParen, closeParen,
          keyword "into", .word dest.val, keyword "with", keyword "space",
          .word sp.val, keyword "stack", .word st.val, semicolon])
  | .waitInterrupt => fun tokens =>
      tokens = [keyword "wait", keyword "for", keyword "interrupt", semicolon]
  | .stopCore => fun tokens =>
      tokens = [keyword "stop", keyword "core", semicolon]
  | .entryDecl name kind stack priority => fun tokens =>
      (priority.isNone ∧
        tokens = [keyword "entry", .word name.val, entryKindKeyword kind, keyword "stack"] ++
          (match stack with | .perCore => [keyword "per", keyword "core"] | .own => [keyword "own"]) ++
          [semicolon]) ∨
      (∃ n, priority = some n ∧
        tokens = [keyword "entry", .word name.val, entryKindKeyword kind, keyword "stack"] ++
          (match stack with | .perCore => [keyword "per", keyword "core"] | .own => [keyword "own"]) ++
          [keyword "priority", .natural n, semicolon])

def ExecParse (text : RawText) (tree : ExecTree form) : Prop :=
  Text.Parse (tokenGrammar (fun tokens (tree : ExecTree form) => tree.production tokens)) text tree

def ExecTree.print (tree : ExecTree form) : RawText := PrintedToken.render tree.printPieces

end Gabbro.Core.Ast.LowLevel
