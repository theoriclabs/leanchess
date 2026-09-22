import LeanDb
import api.Server
import api.Store

open Std

/- The server. `--db` is the LeanDB file. `--port` defaults to 8765,
   or `PORT` when the flag is absent. `--host` defaults to loopback.
   `--web` is the directory of the page, served on GET. -/

def arg (args : List String) (name : String) (default : String) : String :=
  match args with
  | f :: v :: rest => if f == name then v else arg rest name default
  | _ => default

def arg? (args : List String) (name : String) : Option String :=
  match args with
  | f :: v :: rest => if f == name then some v else arg? rest name
  | _ => none

def ipv4 (s : String) : Option Net.IPv4Addr :=
  match s.splitOn "." with
  | [a, b, c, d] =>
    match a.toNat?, b.toNat?, c.toNat?, d.toNat? with
    | some a, some b, some c, some d =>
      if a < 256 && b < 256 && c < 256 && d < 256 then
        some (Net.IPv4Addr.ofParts a.toUInt8 b.toUInt8 c.toUInt8 d.toUInt8)
      else none
    | _, _, _, _ => none
  | _ => none

def main (args : List String) : IO UInt32 := do
  let path : System.FilePath := arg args "--db" "data/leanchess.sqlite"
  let envPort ← IO.getEnv "PORT"
  let portStr := (arg? args "--port").orElse (fun () => envPort) |>.getD "8765"
  let port ← match portStr.toNat? with
    | some n =>
        if n == 0 || n > 65535 then
          IO.eprintln "port is 1–65535"
          return 1
        pure n.toUInt16
    | none =>
        IO.eprintln "port is a number"
        return 1
  let hostName := arg args "--host" "127.0.0.1"
  let some host := ipv4 hostName
    | IO.eprintln s!"host is an IPv4 address, got {hostName}"
      return 1
  if let some parent := path.parent then IO.FS.createDirAll parent
  let web ← LeanChess.Api.loadWeb (arg args "--web" "")
  let conn ← match ← LeanDb.openDbRaw path with
    | .ok conn => pure conn
    | .error e =>
        IO.eprintln (toString e)
        return 1
  -- A release that changes the schema carries its migration. An additive
  -- one (a column with a default, an index, an invariant) is applied here,
  -- after a backup beside the file. A destructive one is refused, and the
  -- server does not start until a person migrates by hand.
  let tag := (← IO.getRandomBytes 4).foldl (fun acc b => acc ++ (Nat.toDigits 16 b.toNat).asString) ""
  let backup : System.FilePath := path.toString ++ s!".before-migration-{tag}"
  match ← LeanDb.migrateOn conn LeanChess.Api.schema { apply := true, backup := some backup } with
  | .error e =>
      IO.eprintln s!"migration refused: {e}"
      return 1
  | .ok (_, some report) =>
      unless report.applied.isEmpty do
        IO.eprintln s!"migrated: {report.applied}; backup {backup}"
  | .ok (_, none) => pure ()
  match ← conn.verify LeanChess.Api.schema with
  | .error e =>
      IO.eprintln (toString e)
      return 1
  | .ok () =>
      LeanChess.Api.serve conn host hostName port web
