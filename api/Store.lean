/-
  What is stored. A person, and a game's agreement plus its log.
  The position, the clock, and the ending are not columns. They are the
  fold of the log, computed when a look asks.
-/

import LeanDb
import domain.Game

namespace LeanChess.Api

open LeanDb

structure User where
  name : String
  token : String
  autoClaim : Bool := false
  deriving Repr, LeanDb.Entity

/-- One act, in the wire form the boundary reconstructs into a `GameEvent`. -/
structure Act where
  wire : String
  deriving Repr, LeanDb.Inline

structure GameRow where
  white : Ref User
  black : Ref User
  rated : Bool
  initialMs : Nat
  incrementMs : Nat
  startMs : Nat
  acts : List Act
  deriving Repr, LeanDb.Entity

def schema : List TableSpec :=
  orderSpecs (Entity.specs User ++ Entity.specs GameRow)

def users : DbM (Array (Stored User)) := fetchAll User

def userByName (name : String) : DbM (Option (Stored User)) := do
  let all ← users
  return all.find? fun u => u.val.name == name

def userByToken (token : String) : DbM (Option (Stored User)) := do
  let all ← users
  return all.find? fun u => u.val.token == token

def gameById (id : Int64) : DbM (Option (Stored GameRow)) :=
  LeanDb.get (⟨id⟩ : LeanDb.Id GameRow)

/-- The domain person is the stored name. The token stays in the row. -/
def asPerson (u : User) : LeanChess.Person where
  id := u.name
  autoClaimThreefold := u.autoClaim

def agreementOf (g : GameRow) (white black : User) : LeanChess.Agreement where
  white := asPerson white
  black := asPerson black
  rated := g.rated
  time := .realtime g.initialMs g.incrementMs
  start := ⟨g.startMs⟩

end LeanChess.Api
