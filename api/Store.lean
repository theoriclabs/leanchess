/-
  What is stored. A person, and a game's agreement plus its log.
  The position, the clock, and the ending are not columns. They are the
  fold of the log, computed when a look asks.
-/

import LeanDb
import api.Wire

namespace LeanChess.Api

open LeanDb

structure User where
  name : String
  token : String
  autoClaim : Bool := false
  deriving Repr, LeanDb.Entity

/-- One account per name, and one per token: the database refuses a second. -/
instance : LeanDb.Indexes User :=
  ⟨#[{ unique := true, columns := #["name"] }, { unique := true, columns := #["token"] }]⟩

/-- One act, in the wire form the boundary reconstructs into a `GameEvent`. -/
structure Act where
  wire : String
  deriving Repr, LeanDb.Inline

/-- A game: the agreement, fixed when it opened, and its log. Each seat's
    choice to claim a threefold repetition is copied from the account when
    the game opens, so nothing outside this row changes how its log folds. -/
structure GameRow where
  white : Ref User
  black : Ref User
  rated : Bool
  initialMs : Nat
  incrementMs : Nat
  startMs : Nat
  whiteAutoClaim : Bool := false
  blackAutoClaim : Bool := false
  acts : List Act
  deriving Repr

/-- The agreement, read from the game row alone. A person is the account's
    id: a game against oneself is the same id in both seats. -/
def agreementOf (g : GameRow) : LeanChess.Agreement where
  white := ⟨toString g.white.toInt64, g.whiteAutoClaim⟩
  black := ⟨toString g.black.toInt64, g.blackAutoClaim⟩
  rated := g.rated
  time := .realtime g.initialMs g.incrementMs
  start := ⟨g.startMs⟩

/-- A stored game is an admitted history: every act decodes, and the
    sequence is one the admission would have written. LeanDB checks this on
    every read and before every write, so a row that fails is never folded. -/
@[leandb_invariant]
def GameRow.invariant (g : GameRow) : Bool :=
  match g.acts.mapM (parseAct ·.wire) with
  | .ok events => validLog (agreementOf g) events
  | .error _ => false

deriving instance LeanDb.Entity for GameRow

def schema : List TableSpec :=
  orderSpecs (Entity.specs User ++ Entity.specs GameRow)

def userByName (name : String) : DbM (Option (Stored User)) := do
  return (← select [User] (fun u => u.val.name == name))[0]?

def userByToken (token : String) : DbM (Option (Stored User)) := do
  return (← select [User] (fun u => u.val.token == token))[0]?

def gameById (id : Int64) : DbM (Option (Stored GameRow)) :=
  LeanDb.get (⟨id⟩ : LeanDb.Id GameRow)

end LeanChess.Api
