/-
  Register a person. Open a game against another. Attempt an act.
  A play is appended only when `admit` says it landed for the side to
  move. A clock flag is a look at the server's instant, not a stored move.
-/

import LeanDb
import api.Admit
import api.Bot
import api.Store
import api.Wire

namespace LeanChess.Api

open Lean LeanDb LeanChess

inductive Fail where
  | bad (message : String)
  | unauthorized
  | forbidden (message : String)
  | missing (message : String)
  | conflict (message : String)

def Fail.status : Fail → Nat
  | .bad _ => 400
  | .unauthorized => 401
  | .forbidden _ => 403
  | .missing _ => 404
  | .conflict _ => 409

def Fail.json : Fail → Json
  | .bad m => Json.mkObj [("ok", .bool false), ("error", .str m)]
  | .unauthorized => Json.mkObj [("ok", .bool false), ("error", .str "unknown token")]
  | .forbidden m => Json.mkObj [("ok", .bool false), ("error", .str m)]
  | .missing m => Json.mkObj [("ok", .bool false), ("error", .str m)]
  | .conflict m => Json.mkObj [("ok", .bool false), ("error", .str m)]

def idNum (id : LeanDb.Id α) : Int := id.toInt64.toInt

def freshToken : IO String := do
  let bytes ← IO.getRandomBytes 16
  let mut n : Nat := 0
  for b in bytes do
    n := n * 256 + b.toNat
  return toString n

def replay (g : GameRow) (white black : User) : Except String (Agreement × List GameEvent × GameState) := do
  let events ← g.acts.mapM fun a => parseAct a.wire
  let agr := agreementOf g white black
  return (agr, events, fold agr events)

def youAre (caller : LeanDb.Id User) (g : GameRow) : String :=
  let w := g.white == caller
  let b := g.black == caller
  if w && b then "both" else if w then "white" else "black"

def loadPair (g : GameRow) : DbM (Except Fail (Stored User × Stored User)) := do
  match ← LeanDb.get g.white, ← LeanDb.get g.black with
  | some w, some b => return .ok (w, b)
  | _, _ => return .error (.missing "a seated person is gone")

def register (body : Json) : DbM (Except Fail (Nat × Json)) := do
  let name ← match (do strField body "name") with
    | .ok n => pure n
    | .error m => return .error (.bad m)
  let name := name.trimAscii.toString
  if name.isEmpty then return .error (.bad "name is empty")
  if name == Bot.botName || name == "machine" then
    return .error (.conflict "that name is the machine's")
  let auto ← match optBool body "autoClaim" false with
    | .ok b => pure b
    | .error m => return .error (.bad m)
  if (← userByName name).isSome then return .error (.conflict s!"{name} is already registered")
  let token ← freshToken
  let row ← insert User { name, token, autoClaim := auto }
  return .ok (201, Json.mkObj [
    ("ok", .bool true),
    ("id", toJson (idNum row.id)),
    ("name", .str name),
    ("token", .str token)])

def ensureMachine : DbM (Stored User) := do
  match ← userByName Bot.botName with
  | some u => return u
  | none =>
      let token ← freshToken
      insert User { name := Bot.botName, token, autoClaim := false }

def machineToMove (s : GameState) (white black : User) : Bool :=
  s.ending.isNone &&
    match s.position.side with
    | .white => white.name == Bot.botName
    | .black => black.name == Bot.botName

/-- One act, at `now`, when the side to move is the machine.
    The same `admit` as a person's play: a flag does not store the move. -/
def answer (g : Stored GameRow) (events : List GameEvent) (s : GameState) (white black : User)
    (now : Nat) : DbM (Stored GameRow × List GameEvent × GameState) := do
  if !machineToMove s white black then return (g, events, s)
  else
    match Bot.choose s.position with
    | none => return (g, events, s)
    | some m =>
      match admit s s.position.side (.play m) now with
      | .ok ⟨.played, some ev⟩ =>
        let after := applyEvent s ev
        let g ← update g { g.val with acts := g.val.acts ++ [⟨renderAct ev⟩] }
        return (g, events ++ [ev], after)
      | _ => return (g, events, s)

def bearer (header : Option String) : DbM (Except Fail (Stored User)) := do
  match header with
  | none => return .error .unauthorized
  | some h =>
      let h := h.trimAscii.toString
      let token := if h.startsWith "Bearer " then (h.drop 7).trimAscii.toString else ""
      if token.isEmpty then return .error .unauthorized
      match ← userByToken token with
      | none => return .error .unauthorized
      | some u => return .ok u

def openGame (caller : Stored User) (body : Json) : DbM (Except Fail (Nat × Json)) := do
  if caller.val.name == Bot.botName then
    return .error (.bad "the machine does not open a game")
  let against ← match optBool body "bot" false with
    | .ok b => pure b
    | .error m => return .error (.bad m)
  let color ← match optStr body "color" with
    | .ok none => pure .white
    | .ok (some s) => match parseColor s with
      | .ok c => pure c
      | .error m => return .error (.bad m)
    | .error m => return .error (.bad m)
  let rated ← match optBool body "rated" true with
    | .ok b => pure b
    | .error m => return .error (.bad m)
  let clockMs ← match optNat body "initialMs" (5 * 60 * 1000) with
    | .ok n => pure n
    | .error m => return .error (.bad m)
  let inc ← match optNat body "incrementMs" 0 with
    | .ok n => pure n
    | .error m => return .error (.bad m)
  if clockMs == 0 then return .error (.bad "initialMs is the clock; zero is already a flag")
  let other ←
    if against then ensureMachine
    else
      let opponent ← match strField body "opponent" with
        | .ok n => pure n.trimAscii.toString
        | .error m => return .error (.bad m)
      if opponent == Bot.botName || opponent == "machine" then ensureMachine
      else
        match ← userByName opponent with
        | none => return .error (.missing s!"no person named {opponent}")
        | some u => pure u
  let rated := other.val.name != Bot.botName && rated
  let (white, black) :=
    if color == .white then (caller.id, other.id) else (other.id, caller.id)
  let start ← IO.monoMsNow
  let row ← insert GameRow {
    white, black, rated, initialMs := clockMs, incrementMs := inc, startMs := start, acts := [] }
  match ← loadPair row.val with
  | .error e => return .error e
  | .ok (w, b) =>
      let s := initial (agreementOf row.val w.val b.val)
      return .ok (201, Json.mkObj [
        ("ok", .bool true),
        ("id", toJson (idNum row.id)),
        ("now", toJson start),
        ("white", .str w.val.name),
        ("black", .str b.val.name),
        ("look", lookJson s ⟨start⟩ (youAre caller.id row.val) none)])

def requireGame (id : Int64) : DbM (Except Fail (Stored GameRow)) := do
  match ← gameById id with
  | none => return .error (.missing "no game with that id")
  | some g => return .ok g

def sits (caller : LeanDb.Id User) (g : GameRow) : Bool :=
  g.white == caller || g.black == caller

def chooseSeat (caller : LeanDb.Id User) (g : GameRow) (turn : Color) (asked : Option Color) :
    Except Fail Color := do
  let sitsC (c : Color) : Bool := match c with
    | .white => g.white == caller
    | .black => g.black == caller
  match asked with
  | some c =>
      if sitsC c then pure c else throw (.forbidden "that seat is not yours")
  | none =>
      let w := sitsC .white
      let b := sitsC .black
      if w && b then pure turn
      else if w then pure .white
      else if b then pure .black
      else throw (.forbidden "you are not sitting this game")

def actWires (g : GameRow) : List String :=
  g.acts.map (·.wire)

def lookAt (caller : Stored User) (id : Int64) (asked : Option Nat) :
    DbM (Except Fail (Nat × Json)) := do
  let g ← match ← requireGame id with
    | .ok g => pure g
    | .error e => return .error e
  if !sits caller.id g.val then return .error (.forbidden "you are not sitting this game")
  let now ← IO.monoMsNow
  let (observed, historical) ← match observe now asked with
    | .ok v => pure v
    | .error m => return .error (.bad m)
  match ← loadPair g.val with
  | .error e => return .error e
  | .ok (w, b) =>
      match replay g.val w.val b.val with
      | .error m => return .error (.bad m)
      | .ok (_, events, s) =>
          let (g, events, s) ← answer g events s w.val b.val now
          let (movedFrom, movedTo) := lastSquares events
          return .ok (200, Json.mkObj [
            ("ok", .bool true),
            ("id", toJson (idNum g.id)),
            ("now", toJson now),
            ("observedAt", toJson observed),
            ("historical", .bool historical),
            ("white", .str w.val.name),
            ("black", .str b.val.name),
            ("log", .arr (g.val.acts.map (fun a => Json.str a.wire)).toArray),
            ("look", lookJson s ⟨observed⟩ (youAre caller.id g.val) none movedFrom movedTo)])

private def judge (caller : Stored User) (g : Stored GameRow) (req : Requested)
    (asked : Option Color) (now : Nat) : DbM (Except Fail (Decision × GameState)) := do
  if !sits caller.id g.val then return .error (.forbidden "you are not sitting this game")
  match ← loadPair g.val with
  | .error e => return .error e
  | .ok (w, b) =>
      match replay g.val w.val b.val with
      | .error m => return .error (.bad m)
      | .ok (_, _, before) =>
          let seat ← match chooseSeat caller.id g.val before.position.side asked with
            | .ok c => pure c
            | .error e => return .error e
          match admit before seat req now with
          | .error .notYourTurn => return .error (.forbidden "it is not your turn")
          | .ok d => return .ok (d, before)

private def renderAttempt (caller : Stored User) (g : Stored GameRow) (before : GameState)
    (d : Decision) (now : Nat) : DbM (Except Fail (Nat × Json)) := do
  match ← loadPair g.val with
  | .error e => return .error e
  | .ok (w, b) =>
      let shown := match d.event with
        | some ev => applyEvent before ev
        | none => before
      let played := g.val.acts.filterMap fun a =>
        match parseAct a.wire with | .ok e => some e | .error _ => none
      let (movedFrom, movedTo) := lastSquares played
      let admitted := d.outcome == .played
      return .ok (200, Json.mkObj [
        ("ok", .bool true),
        ("id", toJson (idNum g.id)),
        ("now", toJson now),
        ("observedAt", toJson now),
        ("historical", .bool false),
        ("outcome", .str d.outcome.wire),
        ("white", .str w.val.name),
        ("black", .str b.val.name),
        ("log", .arr (g.val.acts.map (fun a => Json.str a.wire)).toArray),
        ("look", lookJson shown ⟨now⟩ (youAre caller.id g.val) (some admitted)
          movedFrom movedTo (some d.outcome.wire))])

/-- `clock` is the server instant. `none` samples it after the log is loaded. -/
def attemptAt (caller : Stored User) (id : Int64) (body : Json) (clock : Option Nat) :
    DbM (Except Fail (Nat × Json)) := do
  let g ← match ← requireGame id with
    | .ok g => pure g
    | .error e => return .error e
  if !sits caller.id g.val then return .error (.forbidden "you are not sitting this game")
  let (req, asked) ← match parseRequested body with
    | .ok v => pure v
    | .error m => return .error (.bad m)
  let rec go (fuel : Nat) : DbM (Except Fail (Nat × Json)) := do
    match fuel with
    | 0 => return .error (.conflict "the game changed; try again")
    | n + 1 =>
      let g ← match ← requireGame id with
        | .ok g => pure g
        | .error e => return .error e
      let now ← match clock with
        | some t => pure t
        | none => IO.monoMsNow
      match ← judge caller g req asked now with
      | .error e => return .error e
      | .ok (d, before) =>
        match d.event with
        | none => renderAttempt caller g before d now
        | some ev =>
          let g2 ← match ← gameById id with
            | some g2 => pure g2
            | none => return .error (.missing "no game with that id")
          if actWires g.val != actWires g2.val then
            go n
          else
            let g ← update g2 { g2.val with acts := g2.val.acts ++ [⟨renderAct ev⟩] }
            renderAttempt caller g before d now
  go 2

def attempt (caller : Stored User) (id : Int64) (body : Json) :
    DbM (Except Fail (Nat × Json)) :=
  attemptAt caller id body none

private def seatRow (w b : Nat) : GameRow := {
  white := ⟨Int64.ofNat w⟩, black := ⟨Int64.ofNat b⟩, rated := false,
  initialMs := 300000, incrementMs := 0, startMs := 0, acts := [] }

#guard match chooseSeat (⟨Int64.ofNat 2⟩ : LeanDb.Id User) (seatRow 1 2) .white none with
  | .ok seat => seat == .black
  | .error _ => false

#guard match chooseSeat (⟨Int64.ofNat 2⟩ : LeanDb.Id User) (seatRow 1 2) .white (some .white) with
  | .error (.forbidden _) => true
  | _ => false

#guard match chooseSeat (⟨Int64.ofNat 3⟩ : LeanDb.Id User) (seatRow 1 2) .white none with
  | .error (.forbidden _) => true
  | _ => false

#guard match chooseSeat (⟨Int64.ofNat 1⟩ : LeanDb.Id User) (seatRow 1 1) .white none with
  | .ok seat => seat == .white
  | .error _ => false
#guard match chooseSeat (⟨Int64.ofNat 1⟩ : LeanDb.Id User) (seatRow 1 1) .white (some .black) with
  | .ok seat => seat == .black
  | .error _ => false
#guard match chooseSeat (⟨Int64.ofNat 1⟩ : LeanDb.Id User) (seatRow 1 1) .black none with
  | .ok seat => seat == .black
  | .error _ => false

end LeanChess.Api
