/-
  One seat in a browser. The board is the look the server folded.
  A click proposes an act. The server says whether it was admitted.
-/

import LeanReact

namespace LeanChess.Ui

open LeanReact

structure Session where
  name : String
  token : String

structure PieceView where
  square : String
  color : String
  kind : String

structure Look where
  ending : String
  turn : String
  offer : String
  whiteLeft : Nat
  blackLeft : Nat
  ply : Nat
  you : String
  admitted : String
  board : Array PieceView

structure Game where
  id : Nat
  white : String
  black : String
  look : Look

structure Api where
  register : String → Action (Except String Session)
  forget : Action Unit
  start : Session → String → Action (Except String Game)
  join : Session → String → Action (Except String Game)
  act : Session → Nat → String → String → String → String → Action (Except String Game)
  watch : Session → Nat → (Game → Action Unit) → Action (Action Unit)

structure Props where
  api : Api
  saved : Option Session

def pieceOn (board : Array PieceView) (sq : String) : Option PieceView :=
  board.foldl (fun found p =>
    match found with
    | some _ => found
    | none => if p.square == sq then some p else none) none

@[noinline] def glyph : String → String → String
  | "white", "king" => "♔" | "white", "queen" => "♕" | "white", "rook" => "♖"
  | "white", "bishop" => "♗" | "white", "knight" => "♘" | "white", "pawn" => "♙"
  | "black", "king" => "♚" | "black", "queen" => "♛" | "black", "rook" => "♜"
  | "black", "bishop" => "♝" | "black", "knight" => "♞" | "black", "pawn" => "♟"
  | _, _ => ""

def mine (you color : String) : Bool :=
  you == "both" || you == color

def fileIdx : String → Nat
  | "a" => 0 | "b" => 1 | "c" => 2 | "d" => 3
  | "e" => 4 | "f" => 5 | "g" => 6 | "h" => 7 | _ => 0

def rankIdx : String → Nat
  | "1" => 0 | "2" => 1 | "3" => 2 | "4" => 3
  | "5" => 4 | "6" => 5 | "7" => 6 | "8" => 7 | _ => 0

def files : Array String := #["a", "b", "c", "d", "e", "f", "g", "h"]

def rankOrder (you : String) : Array String :=
  if you == "black" then #["1", "2", "3", "4", "5", "6", "7", "8"]
  else #["8", "7", "6", "5", "4", "3", "2", "1"]

def fileOrder (you : String) : Array String :=
  if you == "black" then #["h", "g", "f", "e", "d", "c", "b", "a"] else files

def two (n : Nat) : String :=
  if n < 10 then "0" ++ toString n else toString n

def clockLabel (ms : Nat) : String :=
  let total := ms / 1000
  toString (total / 60) ++ ":" ++ two (total % 60)

def promoOf (kind toRank : String) : String :=
  if kind == "pawn" && (toRank == "8" || toRank == "1") then "queen" else ""

@[noinline] def squareEl (look : Look) (selected : String) (press : String → String → Action Unit) (f r : String) : Element :=
  let sq := f ++ r
  let piece := pieceOn look.board sq
  let dark := (fileIdx f + rankIdx r) % 2 == 0
  let cls := "sq"
    ++ (if dark then " dark" else " light")
    ++ (if selected == sq then " selected" else "")
  DOM.button {
    className := some cls
    ariaLabel := some sq
    onPress := some (press f r)
  } #[text (match piece with | some p => glyph p.color p.kind | none => "")]

@[noinline] def boardEl (look : Look) (selected : String) (press : String → String → Action Unit) : Element :=
  DOM.div { className := some "board", role := some "grid", ariaLabel := some "Board" }
    (rankOrder look.you |>.map fun r =>
      DOM.div { className := some "rank", role := some "row" }
        (fileOrder look.you |>.map fun f => squareEl look selected press f r))

def seatLine (game : Game) : String :=
  let you := match game.look.you with
    | "white" => "You are white"
    | "black" => "You are black"
    | "both" => "You sit both seats"
    | _ => "You are not seated"
  you ++ " · " ++ game.white ++ " vs " ++ game.black ++ " · game " ++ toString game.id

def statusLine (look : Look) : String :=
  if look.ending != "" then look.ending
  else
    let offer := if look.offer == "" then "" else " · " ++ look.offer ++ " offers a draw"
    look.turn ++ " to move" ++ offer

def App : Component Props := component fun props => do
  let session ← useState props.saved "session"
  let game ← useState (none : Option Game) "game"
  let notice ← useState "" "notice"
  let name ← useState "" "name"
  let opponent ← useState "" "opponent"
  let joinId ← useState "" "join"
  let selected ← useState "" "selected"
  let tokenDep := match session.value with | some s => s.token | none => ""
  let idDep := match game.value with | some g => g.id | none => 0
  useEffect #[.string tokenDep, .nat idDep] (match session.value, game.value with
    | some s, some g =>
        props.api.watch s g.id fun next => do
          let cur ← game.read
          match cur with
          | some prev => if next.look.ply ≥ prev.look.ply then game.set (some next) else pure ()
          | none => game.set (some next)
    | _, _ => pure (pure ())) "watch"
  let report (result : Except String Game) : Action Unit := do
    match result with
    | .error message => notice.set message
    | .ok next =>
        game.set (some next)
        selected.set ""
        notice.set (if next.look.admitted == "no" then "Refused. The log is unchanged." else "")
  let press (f r : String) : Action Unit := do
    let sq := f ++ r
    let current ← game.read
    let who ← session.read
    let origin ← selected.read
    match current, who with
    | some g, some s =>
        if g.look.ending != "" then pure ()
        else
          let fromKind := (pieceOn g.look.board origin |>.map (·.kind)).getD ""
          match pieceOn g.look.board sq with
          | some piece =>
              if mine g.look.you piece.color then selected.set sq
              else if origin != "" then report (← props.api.act s g.id "play" origin sq (promoOf fromKind r))
              else pure ()
          | none =>
              if origin == "" then pure ()
              else report (← props.api.act s g.id "play" origin sq (promoOf fromKind r))
    | _, _ => pure ()
  let send (kind : String) : Action Unit := do
    match (← game.read), (← session.read) with
    | some g, some s =>
        if g.look.ending != "" then pure () else report (← props.api.act s g.id kind "" "" "")
    | _, _ => pure ()
  let desk := match session.value with
    | none =>
        DOM.form { className := some "panel", onSubmit := (do
          match ← props.api.register name.value with
          | .ok s =>
              session.set (some s)
              notice.set ""
          | .error message => notice.set message) } #[
          DOM.h1 {} #[text "LeanChess"],
          DOM.label { htmlFor := "name" } #[text "Your name"],
          DOM.input { id := some "name", value := some name.value, onChange := some fun event => name.set event.value },
          DOM.button { className := some "primary", type := .submit } #[text "Register"]
        ]
    | some s =>
        DOM.div { className := some "panel" } #[
          DOM.header {} #[
            DOM.h1 {} #[text s.name],
            DOM.button { onPress := some (do
              session.set none
              game.set none
              selected.set ""
              props.api.forget) } #[text "Sign out"]
          ],
          DOM.form { className := some "row-form", onSubmit := (do
            report (← props.api.start s opponent.value)) } #[
            DOM.label { htmlFor := "opponent" } #[text "Play"],
            DOM.input {
              id := some "opponent"
              placeholder := some "Their name"
              value := some opponent.value
              onChange := some fun event => opponent.set event.value
            },
            DOM.button { className := some "primary", type := .submit } #[text "Start"]
          ],
          DOM.form { className := some "row-form", onSubmit := (do
            report (← props.api.join s joinId.value)) } #[
            DOM.label { htmlFor := "join" } #[text "Join"],
            DOM.input {
              id := some "join"
              placeholder := some "Game number"
              value := some joinId.value
              onChange := some fun event => joinId.set event.value
            },
            DOM.button { type := .submit } #[text "Open"]
          ]
        ]
  let table := match game.value with
    | none => DOM.p { className := some "note" } #[text "Start a game, or open one by its number."]
    | some g =>
        let top := if g.look.you == "black" then g.look.whiteLeft else g.look.blackLeft
        let bottom := if g.look.you == "black" then g.look.blackLeft else g.look.whiteLeft
        let topName := if g.look.you == "black" then g.white else g.black
        let bottomName := if g.look.you == "black" then g.black else g.white
        DOM.section { className := some "table" } #[
          DOM.p { className := some "meta" } #[text (seatLine g)],
          DOM.p { className := some "clock" } #[text (topName ++ " " ++ clockLabel top)],
          boardEl g.look selected.value press,
          DOM.p { className := some "clock" } #[text (bottomName ++ " " ++ clockLabel bottom)],
          DOM.p { className := some "status", role := some "status" } #[text (statusLine g.look)],
          DOM.div { className := some "controls" } #[
            DOM.button { onPress := some (send "resign") } #[text "Resign"],
            DOM.button { onPress := some (send "offer") } #[text "Offer draw"],
            DOM.button { onPress := some (send "accept") } #[text "Accept"],
            DOM.button { onPress := some (send "decline") } #[text "Decline"]
          ]
        ]
  pure <| DOM.main { className := some "page" } #[
    desk,
    table,
    DOM.p { className := some "note", role := some "status", ariaLive := some "polite" } #[text notice.value]
  ]

end LeanChess.Ui
