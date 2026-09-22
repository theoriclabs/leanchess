/-
  Persistence regressions for seat, clock, and the route `handle` calls.
  `POST /games/<id>/acts` is `attempt`. `GET /games/<id>` is `lookAt`.
-/

import LeanDb
import api.Service
import api.Store

open LeanChess.Api Lean LeanDb

def failText : Fail → String
  | .bad m => m
  | .unauthorized => "unauthorized"
  | .forbidden m => m
  | .missing m => m
  | .conflict m => m

def check (name : String) (ok : Bool) : IO Unit := do
  if !ok then throw <| IO.userError s!"failed: {name}"

def db {α} (conn : Conn) (act : DbM α) : IO α := do
  match ← DbM.run conn act with
  | .ok a => pure a
  | .error e => throw <| IO.userError (toString e)

def expect (r : Except Fail (Nat × Json)) (label : String) : IO (Nat × Json) := do
  match r with
  | .ok v => pure v
  | .error f => throw <| IO.userError s!"{label}: {failText f}"

def expectForbid (r : Except Fail (Nat × Json)) (label : String) : IO Unit := do
  match r with
  | .error (.forbidden _) => pure ()
  | .ok _ => throw <| IO.userError s!"{label}: accepted"
  | .error f => throw <| IO.userError s!"{label}: {failText f}"

def expectBad (r : Except Fail (Nat × Json)) (label : String) : IO Unit := do
  match r with
  | .error (.bad _) => pure ()
  | .ok _ => throw <| IO.userError s!"{label}: accepted"
  | .error f => throw <| IO.userError s!"{label}: {failText f}"

def field (j : Json) (k : String) : IO Json := do
  match j.getObjVal? k with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"{k}: {e}"

def jsonNat (j : Json) (k : String) : IO Nat := do
  let v ← field j k
  match v.getNat? with
  | .ok n => pure n
  | .error _ =>
    match v.getInt? with
    | .ok i =>
      if i < 0 then throw <| IO.userError s!"{k} is negative" else pure i.toNat
    | .error e => throw <| IO.userError s!"{k}: {e}"

def jsonStr (j : Json) (k : String) : IO String := do
  match (← field j k).getStr? with
  | .ok s => pure s
  | .error e => throw <| IO.userError s!"{k}: {e}"

def jsonBool (j : Json) (k : String) : IO Bool := do
  match (← field j k).getBool? with
  | .ok b => pure b
  | .error e => throw <| IO.userError s!"{k}: {e}"

def playBody (fromSq toSq : String) (seat : Option String) (at? : Option Nat) : Json :=
  let fields : List (String × Json) := [
    ("kind", .str "play"), ("from", .str fromSq), ("to", .str toSq)]
  let fields := match seat with
    | none => fields
    | some s => fields ++ [("seat", .str s)]
  let fields := match at? with
    | none => fields
    | some n => fields ++ [("at", toJson n)]
  Json.mkObj fields

def wires (conn : Conn) (id : Int64) : IO (List String) := do
  match ← db conn (gameById id) with
  | none => throw <| IO.userError "game is gone"
  | some g => pure (g.val.acts.map (·.wire))

def stamp (wire : String) : Option Nat :=
  match wire.splitOn " " with
  | ["moved", _, _, _, t] => t.toNat?
  | _ => none

def registerName (conn : Conn) (name : String) : IO (Stored User) := do
  let _ ← expect (← db conn (register (Json.mkObj [("name", .str name)]))) s!"register {name}"
  match ← db conn (userByName name) with
  | some u => pure u
  | none => throw <| IO.userError s!"missing {name}"

def openBetween (conn : Conn) (caller : Stored User) (body : Json) : IO Int64 := do
  let (status, j) ← expect (← db conn (openGame caller body)) "open"
  check "open status" (status == 201)
  pure <| Int64.ofNat (← jsonNat j "id")

def startOf (conn : Conn) (id : Int64) : IO Nat := do
  match ← db conn (gameById id) with
  | some g => pure g.val.startMs
  | none => throw <| IO.userError "game is gone"

def main : IO UInt32 := do
  let path : System.FilePath := "/tmp/leanchess-audit.sqlite"
  if ← path.pathExists then IO.FS.removeFile path
  match ← LeanDb.openDb path schema with
  | .error e =>
    IO.eprintln (toString e)
    return 1
  | .ok conn =>
    let ada ← registerName conn "ada"
    let bel ← registerName conn "bel"
    let cat ← registerName conn "cat"
    let seatId ← openBetween conn ada (Json.mkObj [
      ("opponent", .str "bel"), ("rated", .bool false),
      ("initialMs", toJson (300000 : Nat)), ("incrementMs", toJson (0 : Nat))])
    let start ← startOf conn seatId
    let forged := if start = 7 then 8 else 7
    let e4 := playBody "e2" "e4" none (some forged)
    expectForbid (← db conn (attemptAt bel seatId e4 (some start))) "black e4"
    check "black did not append" ((← wires conn seatId) == [])
    expectForbid (← db conn (attemptAt ada seatId (playBody "e2" "e4" (some "black") none) (some start)))
      "explicit black seat"
    check "explicit black did not append" ((← wires conn seatId) == [])
    expectForbid (← db conn (attemptAt cat seatId e4 (some start))) "spectator"
    check "spectator did not append" ((← wires conn seatId) == [])
    expectBad (← db conn (attemptAt ada seatId
      (Json.mkObj [("kind", .str "play"), ("from", .str "e2"), ("to", .str "e4"), ("at", .str "soon")])
      (some start))) "bad at"
    let (status, played) ← expect
      (← db conn (attemptAt ada seatId (playBody "e2" "e4" (some "white") (some forged)) (some start)))
      "white e4"
    check "white status" (status == 200)
    check "white outcome" ((← jsonStr played "outcome") == "played")
    let look ← field played "look"
    check "white ply" ((← jsonNat look "ply") == 1)
    match ← wires conn seatId with
    | [w] =>
      check "server stamp" (stamp w == some start)
      check "forged stamp ignored" (stamp w != some forged)
    | other => throw <| IO.userError s!"expected one act, got {other}"
    expectForbid (← db conn (attemptAt ada seatId (playBody "d2" "d4" none none) (some (start + 1000))))
      "white again"
    check "second white did not append" ((← wires conn seatId).length == 1)
    let (_, blackMove) ← expect
      (← db conn (attemptAt bel seatId (playBody "e7" "e5" none (some 0)) (some (start + 1000))))
      "black e5"
    check "black outcome" ((← jsonStr blackMove "outcome") == "played")
    check "two acts" ((← wires conn seatId).length == 2)
    match (← wires conn seatId).getLast? with
    | some w => check "black stamp is server time" (stamp w == some (start + 1000))
    | none => throw <| IO.userError "missing black act"

    let bothId ← openBetween conn ada (Json.mkObj [
      ("opponent", .str "ada"), ("rated", .bool false),
      ("initialMs", toJson (300000 : Nat)), ("incrementMs", toJson (0 : Nat))])
    let bothStart ← startOf conn bothId
    expectForbid (← db conn (attemptAt ada bothId (playBody "e7" "e5" (some "black") none) (some bothStart)))
      "both seats, asked black"
    check "both seats wrong ask" ((← wires conn bothId) == [])
    let _ ← expect (← db conn (attemptAt ada bothId (playBody "e2" "e4" none none) (some bothStart)))
      "both seats, side to move"
    expectForbid (← db conn (attemptAt ada bothId (playBody "d2" "d4" (some "white") none) (some (bothStart + 10))))
      "both seats, stale white"
    let _ ← expect (← db conn (attemptAt ada bothId (playBody "e7" "e5" none none) (some (bothStart + 10))))
      "both seats, now black"

    let flagId ← openBetween conn ada (Json.mkObj [
      ("opponent", .str "bel"), ("rated", .bool false),
      ("initialMs", toJson (1000 : Nat)), ("incrementMs", toJson (0 : Nat))])
    let flagStart ← startOf conn flagId
    let (_, flagged) ← expect
      (← db conn (attemptAt ada flagId (playBody "e2" "e4" none (some 0)) (some (flagStart + 1000))))
      "on the boundary"
    check "flag outcome" ((← jsonStr flagged "outcome") == "flagged")
    let flagLook ← field flagged "look"
    check "flag is not a played ply" ((← jsonNat flagLook "ply") == 0)
    check "flag admitted" ((← jsonBool flagLook "admitted") == false)
    match ← field flagLook "ending" with
    | .str s => check "flag ending" (s == "flag black")
    | _ => throw <| IO.userError "flag ending missing"
    check "flag not stored" ((← wires conn flagId) == [])
    let earlyId ← openBetween conn ada (Json.mkObj [
      ("opponent", .str "bel"), ("rated", .bool false),
      ("initialMs", toJson (1000 : Nat)), ("incrementMs", toJson (0 : Nat))])
    let earlyStart ← startOf conn earlyId
    let (_, early) ← expect
      (← db conn (attemptAt ada earlyId (playBody "e2" "e4" none (some (earlyStart + 1000))) (some (earlyStart + 999))))
      "just inside the clock"
    check "inside outcome" ((← jsonStr early "outcome") == "played")
    match ← wires conn earlyId with
    | [w] => check "inside stamp" (stamp w == some (earlyStart + 999))
    | other => throw <| IO.userError s!"expected the inside move, got {other}"

    let incId ← openBetween conn ada (Json.mkObj [
      ("opponent", .str "bel"), ("rated", .bool false),
      ("initialMs", toJson (60000 : Nat)), ("incrementMs", toJson (1000 : Nat))])
    let incStart ← startOf conn incId
    let (_, inc) ← expect
      (← db conn (attemptAt ada incId (playBody "e2" "e4" none none) (some (incStart + 2500))))
      "increment"
    let incLook ← field inc "look"
    check "white keeps the increment" ((← jsonNat incLook "whiteLeft") == 58500)
    check "black clock untouched" ((← jsonNat incLook "blackLeft") == 60000)

    let liveId ← openBetween conn ada (Json.mkObj [
      ("opponent", .str "bel"), ("rated", .bool false)])
    let before ← IO.monoMsNow
    let forgedLive := before + 50000000
    let (_, live) ← expect
      (← db conn (attempt ada liveId (playBody "e2" "e4" none (some forgedLive))))
      "production attempt"
    let after ← IO.monoMsNow
    check "production played" ((← jsonStr live "outcome") == "played")
    match ← wires conn liveId with
    | [w] =>
      match stamp w with
      | some t =>
        check "production stamp is the server clock" (decide (before ≤ t ∧ t ≤ after))
        check "production stamp is not the client clock" (decide (t ≠ forgedLive))
      | none => throw <| IO.userError s!"no stamp in {w}"
    | other => throw <| IO.userError s!"expected the production move, got {other}"
    let liveStart ← startOf conn liveId
    match ← db conn (lookAt bel liveId (some (liveStart + 1000000000000))) with
    | .error (.bad m) => check "future look" (m == "at is in the future")
    | .error f => throw <| IO.userError s!"future look: {failText f}"
    | .ok _ => throw <| IO.userError "future look was accepted"
    let (_, current) ← expect (← db conn (lookAt bel liveId none)) "current look"
    check "current is not historical" ((← jsonBool current "historical") == false)
    check "current observation" ((← jsonNat current "observedAt") ≥ liveStart)
    let (_, past) ← expect (← db conn (lookAt bel liveId (some liveStart))) "historical look"
    check "historical" ((← jsonBool past "historical") == true)
    check "historical instant" ((← jsonNat past "observedAt") == liveStart)

    let botId ← openBetween conn ada (Json.mkObj [
      ("bot", .bool true), ("color", .str "white"), ("rated", .bool false),
      ("initialMs", toJson (300000 : Nat))])
    let botStart ← startOf conn botId
    let _ ← expect (← db conn (attemptAt ada botId (playBody "e2" "e4" none none) (some botStart)))
      "against the machine"
    expectForbid (← db conn (attemptAt ada botId (playBody "d2" "d4" none none) (some (botStart + 10))))
      "human on the machine's turn"
    check "machine has not been moved for" ((← wires conn botId).length == 1)
    expectForbid (← db conn (attemptAt ada botId (playBody "e7" "e5" (some "black") none) (some (botStart + 10))))
      "human asks for the machine's seat"
    let _ ← expect (← db conn (lookAt ada botId none)) "machine replies on look"
    check "machine move stored" ((← wires conn botId).length == 2)

    IO.FS.removeFile path
    IO.println "audit ok"
    return 0
