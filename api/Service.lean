/-
  Register a person. Open a game against another. Attempt an act.
  The attempt is admitted only when the fold changes, and only then is
  it appended to the log.
-/

import LeanDb
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

def changed (before after : GameState) : Bool :=
  before.ply != after.ply || before.ending != after.ending || before.offer != after.offer ||
    before.position != after.position || before.whiteMs != after.whiteMs ||
    before.blackMs != after.blackMs || before.runningSince != after.runningSince

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
  let opponent ← match strField body "opponent" with
    | .ok n => pure n.trimAscii.toString
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
  match ← userByName opponent with
  | none => return .error (.missing s!"no person named {opponent}")
  | some other =>
      let (white, black) :=
        if color == .white then (caller.id, other.id) else (other.id, caller.id)
      let row ← insert GameRow {
        white, black, rated, initialMs := clockMs, incrementMs := inc, startMs := 0, acts := [] }
      match ← loadPair row.val with
      | .error e => return .error e
      | .ok (w, b) =>
          let s := initial (agreementOf row.val w.val b.val)
          return .ok (201, Json.mkObj [
            ("ok", .bool true),
            ("id", toJson (idNum row.id)),
            ("white", .str w.val.name),
            ("black", .str b.val.name),
            ("look", lookJson s ⟨0⟩ (youAre caller.id row.val) none)])

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

def lookAt (caller : Stored User) (id : Int64) (when? : Option Nat) :
    DbM (Except Fail (Nat × Json)) := do
  let g ← match ← requireGame id with
    | .ok g => pure g
    | .error e => return .error e
  if !sits caller.id g.val then return .error (.forbidden "you are not sitting this game")
  match ← loadPair g.val with
  | .error e => return .error e
  | .ok (w, b) =>
      match replay g.val w.val b.val with
      | .error m => return .error (.bad m)
      | .ok (_, events, s) =>
          let d := match when? with
            | some n => n
            | none => events.foldl (fun acc e => max acc (match e with
                | .moved _ t | .resigned _ t | .drawOffered _ t | .drawAccepted _ t
                | .drawDeclined _ t | .claimedThreefold _ _ t | .claimedFifty _ _ t
                | .aborted _ t => t.ms)) g.val.startMs
          return .ok (200, Json.mkObj [
            ("ok", .bool true),
            ("id", toJson (idNum g.id)),
            ("log", .arr (g.val.acts.map (fun a => Json.str a.wire)).toArray),
            ("look", lookJson s ⟨d⟩ (youAre caller.id g.val) none)])

def attempt (caller : Stored User) (id : Int64) (body : Json) :
    DbM (Except Fail (Nat × Json)) := do
  let g ← match ← requireGame id with
    | .ok g => pure g
    | .error e => return .error e
  if !sits caller.id g.val then return .error (.forbidden "you are not sitting this game")
  let (req, instant, asked) ← match parseRequested body with
    | .ok v => pure v
    | .error m => return .error (.bad m)
  match ← loadPair g.val with
  | .error e => return .error e
  | .ok (w, b) =>
      match replay g.val w.val b.val with
      | .error m => return .error (.bad m)
      | .ok (_, _, before) =>
          let seat ← match chooseSeat caller.id g.val before.position.side asked with
            | .ok c => pure c
            | .error e => return .error e
          let ev := eventOf seat instant req
          let after := applyEvent before ev
          let admitted := changed before after
          let g ← if !admitted then pure g else
              update g { g.val with acts := g.val.acts ++ [⟨renderAct ev⟩] }
          let d := ⟨instant⟩
          return .ok (200, Json.mkObj [
            ("ok", .bool true),
            ("id", toJson (idNum g.id)),
            ("log", .arr (g.val.acts.map (fun a => Json.str a.wire)).toArray),
            ("look", lookJson (if admitted then after else before) d (youAre caller.id g.val) (some admitted))])

end LeanChess.Api
