import LeanDb
import api.Server
import api.Store

/- The server. `--db` is the LeanDB file, `--port` defaults to 8765.
   Binds to 127.0.0.1. -/

def arg (args : List String) (name : String) (default : String) : String :=
  match args with
  | f :: v :: rest => if f == name then v else arg rest name default
  | _ => default

def main (args : List String) : IO UInt32 := do
  let path : System.FilePath := arg args "--db" "data/leanchess.sqlite"
  let port ← match (arg args "--port" "8765").toNat? with
    | some n =>
        if n == 0 || n > 65535 then
          IO.eprintln "port is 1–65535"
          return 1
        pure n.toUInt16
    | none =>
        IO.eprintln "port is a number"
        return 1
  if let some parent := path.parent then IO.FS.createDirAll parent
  match ← LeanDb.openDb path LeanChess.Api.schema with
  | .error e =>
      IO.eprintln (toString e)
      return 1
  | .ok conn =>
      LeanChess.Api.serve conn port
