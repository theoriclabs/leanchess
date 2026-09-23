/-
  HTTP surface. Loopback. A token from registration is the person.

  POST /users                  { "name", "autoClaim"? }
  POST /games                  Authorization: Bearer <token>
                               { "opponent", "color"?, "rated"?, "initialMs"?, "incrementMs"? }
                               { "bot": true, "color"? } seats the machine, unrated
  GET  /games/<id>            Authorization: Bearer <token>
                               current look; the observation is the server clock
  GET  /games/<id>?at=<ms>     historical look at that instant, which must
                               not be after the server clock
  POST /games/<id>/acts        Authorization: Bearer <token>
                               { "kind", "from"?, "to"?, "promotion"?, "claim"?, "seat"? }

  `kind` is play, resign, offer, accept, decline, claim, or abort.
  The seat is the person the token names, and a play is admitted only
  for the side to move. `at` on a command, if sent, is not the instant:
  a whole number is ignored and anything else is rejected. The instant
  is `IO.monoMsNow`, sampled inside this handler's lock after the log
  is loaded and immediately before admission. Time spent waiting for
  the lock is on the mover's clock.

  The POST acts branch is `ClientRoute.acts` in `api/Admit.lean`.

  `--web` serves the page from that directory on GET. The API paths stay
  the fold. `--host` defaults to loopback.
-/

import Std.Http
import Std.Sync.Mutex
import LeanDb
import api.Service

namespace LeanChess.Api

open Lean LeanDb Std Std.Http Std.Async

partial def readBody (stream : Body.Stream) (limit : Nat) : ContextAsync (Option ByteArray) := do
  let rec loop (bytes : ByteArray) : ContextAsync (Option ByteArray) := do
    match ← Body.Stream.NextChunk.nextChunk stream with
    | none => return some bytes
    | some chunk =>
        if bytes.size + chunk.data.size > limit then return none
        loop (bytes ++ chunk.data)
  loop ByteArray.empty

structure WebFile where
  name : String
  mime : String
  bytes : ByteArray

def mimeOf : String → String
  | "app.js" => "text/javascript; charset=utf-8"
  | "style.css" => "text/css; charset=utf-8"
  | "index.html" => "text/html; charset=utf-8"
  | _ => "application/octet-stream"

def loadWeb (root : String) : IO (List WebFile) := do
  if root.isEmpty then return []
  let mut files : List WebFile := []
  for name in ["index.html", "app.js", "style.css"] do
    let path := System.FilePath.mk root / name
    if ← path.pathExists then
      if !(← path.isDir) then
        files := { name, mime := mimeOf name, bytes := ← IO.FS.readBinFile path } :: files
  return files

/-- Headers every response carries: the page may not be framed, may not
    be sniffed away from its type, and is pinned to its own origin for
    script, style, and object. `connect-src` keeps the documented dev
    affordance (`?api=` to another loopback port) working; a production
    page is served from its own origin and never uses it. -/
def secure (line : Response.Head) : Response.Head :=
  let allow (line : Response.Head) (k v : String) : Response.Head :=
    { line with headers := line.headers.insert (Header.Name.ofString! k) (Header.Value.ofString! v) }
  let line := allow line "content-security-policy"
    "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' data:; \
    connect-src 'self' http://127.0.0.1:* http://localhost:* http://[::1]:*; \
    object-src 'none'; base-uri 'none'; frame-ancestors 'none'; form-action 'self'"
  let line := allow line "x-frame-options" "DENY"
  allow line "x-content-type-options" "nosniff"

def fileRespond (mime : String) (bytes : ByteArray) : ContextAsync (Response Body.Any) := do
  let r ← (Response.ok.header! "content-type" mime).fromBytes bytes
  let allow (line : Response.Head) (k v : String) : Response.Head :=
    { line with headers := line.headers.insert (Header.Name.ofString! k) (Header.Value.ofString! v) }
  let line := allow (secure r.line) "access-control-allow-origin" "*"
  return { line, body := Body.Any.ofBody r.body, extensions := r.extensions }

def respond (status : Nat) (j : Json) : ContextAsync (Response Body.Any) := do
  let code : Status :=
    if status == 200 then .ok
    else if status == 201 then .created
    else if status == 400 then .badRequest
    else if status == 401 then .unauthorized
    else if status == 403 then .forbidden
    else if status == 404 then .notFound
    else if status == 409 then .conflict
    else .internalServerError
  let r ← (Response.withStatus code).json j.compress
  let allow (line : Response.Head) (k v : String) : Response.Head :=
    { line with headers := line.headers.insert (Header.Name.ofString! k) (Header.Value.ofString! v) }
  let line := secure r.line
  -- The page is another origin. The token still has to be presented.
  let line := allow line "access-control-allow-origin" "*"
  let line := allow line "access-control-allow-headers" "authorization, content-type"
  let line := allow line "access-control-allow-methods" "GET, POST, OPTIONS"
  return { line, body := Body.Any.ofBody r.body, extensions := r.extensions }

def bearerHeader (req : Request Body.Stream) : Option String :=
  req.line.headers.get? (Header.Name.ofString! "authorization") |>.map toString

def queryPairs (req : Request Body.Stream) : List (String × String) :=
  req.line.uri.query.toList.filterMap fun (k, v) => do
    let k ← k.decode
    some (k, (v.bind (·.decode)).getD "")

def parseId (s : String) : Option Int64 :=
  match s.toInt? with
  | some i =>
      if i < 0 || i > Int64.maxValue.toInt then none else some (Int64.ofInt i)
  | none => none

def isApi (segs : List String) : Bool :=
  segs.head? == some "users" || segs.head? == some "games" || segs == ["healthz"]

def handle (lock : Std.Mutex Conn) (web : List WebFile) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let method := (toString req.line.method).toUpper
  let segs := (req.line.uri.path.toDecodedSegments.toList).filter (!·.isEmpty)
  if method == "OPTIONS" || (method == "GET" && segs == ["healthz"]) then
    return ← respond 200 (Json.mkObj [("ok", .bool true)])
  if method == "GET" && !web.isEmpty && !isApi segs then
    let name := if segs.isEmpty then "index.html" else "/".intercalate segs
    match web.find? (·.name == name) with
    | some file => return ← fileRespond file.mime file.bytes
    | none => return ← respond 404 (Json.mkObj [("ok", .bool false), ("error", .str "not found")])
  let some bytes ← readBody req.body (2 * 1024 * 1024) |
    return ← respond 400 (Json.mkObj [("ok", .bool false), ("error", .str "request body too large")])
  let body? := if bytes.isEmpty then none else String.fromUTF8? bytes
  let json? : Except String Json := match body? with
    | none => .ok .null
    | some s => Json.parse s |>.mapError fun e => s!"body is not JSON: {e}"
  let run (act : DbM (Except Fail (Nat × Json))) : ContextAsync (Response Body.Any) := do
    let result ← lock.atomically fun ref => do
      DbM.run (← ref.get) act
    match result with
    | .error e => respond 500 (Json.mkObj [("ok", .bool false), ("error", .str (toString e))])
    | .ok (.error f) => respond f.status f.json
    | .ok (.ok (status, j)) => respond status j
  match json? with
  | .error m => respond 400 (Json.mkObj [("ok", .bool false), ("error", .str m)])
  | .ok body =>
      match method, segs with
      | "POST", ["users"] => run (register body)
      | "POST", ["games"] =>
          run do
            match ← bearer (bearerHeader req) with
            | .error e => return .error e
            | .ok u => openGame u body
      | "GET", ["games", id] =>
          match parseId id with
          | none => respond 400 (Json.mkObj [("ok", .bool false), ("error", .str "game id is a number")])
          | some id =>
              let asked := (queryPairs req).find? (·.1 == "at")
              match asked with
              | some (_, s) =>
                match s.toNat? with
                | none => respond 400 (Json.mkObj [("ok", .bool false), ("error", .str "at must be a whole number")])
                | some n =>
                  run do
                    match ← bearer (bearerHeader req) with
                    | .error e => return .error e
                    | .ok u => lookAt u id (some n)
              | none =>
                run do
                  match ← bearer (bearerHeader req) with
                  | .error e => return .error e
                  | .ok u => lookAt u id none
      | "POST", ["games", id, "acts"] =>
          match parseId id with
          | none => respond 400 (Json.mkObj [("ok", .bool false), ("error", .str "game id is a number")])
          | some id =>
              run do
                match ← bearer (bearerHeader req) with
                | .error e => return .error e
                | .ok u => attempt u id body
      | _, _ => respond 404 (Json.mkObj [("ok", .bool false), ("error", .str "no such route")])

def serve (db : Conn) (host : Net.IPv4Addr) (hostName : String) (port : UInt16) (web : List WebFile) :
    IO UInt32 := do
  let addr : Net.SocketAddress := .v4 { addr := host, port }
  let lock ← Std.Mutex.new db
  let handler := Std.Http.Server.Handler.ofFn (handle lock web)
  IO.eprintln (Json.mkObj [
    ("event", .str "leanchess.ready"),
    ("host", .str hostName),
    ("port", toJson port.toNat),
    ("web", .bool !web.isEmpty)]).compress
  let config : Std.Http.Config := { generateDate := false }
  Async.block do
    let server ← Std.Http.Server.serve addr handler config
    server.waitShutdown
  return 0

end LeanChess.Api
