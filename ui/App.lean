/-
  One seat in a browser. The board is the look the server folded.
  A click proposes an act. The server says whether it was admitted.
  Which squares a piece may go to is `legalMoves` from `domain/Game.lean`,
  the same function that admits the move on the server.
-/

import LeanReact
import domain.Game

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
  check : String
  movedFrom : String
  movedTo : String
  /-- The castling rights still held, as `KQkq` letters. -/
  castling : String
  /-- The en passant square, or empty. -/
  ep : String

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
  machine : Session → String → Action (Except String Game)

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

def edgeFile (you : String) : String :=
  (fileOrder you).getD 0 "a"

def nearRank (you : String) : String :=
  let ranks := rankOrder you
  ranks.getD (ranks.size - 1) "1"

def two (n : Nat) : String :=
  if n < 10 then "0" ++ toString n else toString n

def clockLabel (ms : Nat) : String :=
  let total := ms / 1000
  toString (total / 60) ++ ":" ++ two (total % 60)

def squareOf (s : String) : Option Square :=
  match s.toList with
  | [f, r] =>
      if f < 'a' || r < '1' then none
      else do
        let file ← File.ofNat? (f.toNat - 'a'.toNat)
        let rank ← Rank.ofNat? (r.toNat - '1'.toNat)
        pure ⟨file, rank⟩
  | _ => none

def nameOf (sq : Square) : String :=
  files.getD sq.file.index "a" ++ toString (sq.rank.index + 1)

def colorOf : String → Option Color
  | "white" => some .white
  | "black" => some .black
  | _ => none

def kindOf : String → Option PieceKind
  | "king" => some .king | "queen" => some .queen | "rook" => some .rook
  | "bishop" => some .bishop | "knight" => some .knight | "pawn" => some .pawn
  | _ => none

def kindName : PieceKind → String
  | .king => "king" | .queen => "queen" | .rook => "rook"
  | .bishop => "bishop" | .knight => "knight" | .pawn => "pawn"

/-- The position the look shows, as the domain states it. -/
def positionOf (look : Look) : Option Position := do
  let board ← look.board.toList.mapM fun p => do
    let sq ← squareOf p.square
    let color ← colorOf p.color
    let kind ← kindOf p.kind
    pure (⟨sq, ⟨color, kind⟩⟩ : Placement)
  let side ← colorOf look.turn
  let has (c : Char) := look.castling.toList.contains c
  pure {
    board := sortBoard board
    side
    rights := ⟨has 'K', has 'Q', has 'k', has 'q'⟩
    ep := squareOf look.ep }

/-- The legal moves from `origin`, by the domain's `legalMoves`. -/
def legalFrom (look : Look) (origin : String) : List Move :=
  match positionOf look, squareOf origin with
  | some p, some o => (legalMoves p).filter (·.src == o)
  | _, _ => []

def targetsFrom (look : Look) (origin : String) : List String :=
  (legalFrom look origin).foldl (fun acc m =>
    let t := nameOf m.to
    if acc.contains t then acc else acc ++ [t]) []

def titled : String → String
  | "white" => "White"
  | "black" => "Black"
  | other => other

def spoken (name : String) : String :=
  if name == "Machine" then "the machine" else name

def pretty (look : Look) : String :=
  match look.ending with
  | "" =>
      let offer := if look.offer == "" then "" else " · draw offered by " ++ titled look.offer
      let chk := if look.check == "yes" then " · check" else ""
      titled look.turn ++ " to move" ++ chk ++ offer
  | "checkmate white" => "White wins · checkmate"
  | "checkmate black" => "Black wins · checkmate"
  | "resign white" => "White wins · resignation"
  | "resign black" => "Black wins · resignation"
  | "flag white" => "White wins · on time"
  | "flag black" => "Black wins · on time"
  | "abort" => "Aborted"
  | "draw stalemate" => "Draw · stalemate"
  | "draw dead" => "Draw · dead position"
  | "draw agreement" => "Draw · agreement"
  | "draw threefold" => "Draw · threefold repetition"
  | "draw fifty" => "Draw · fifty moves"
  | "draw fivefold" => "Draw · fivefold repetition"
  | "draw seventyFive" => "Draw · seventy-five moves"
  | "draw flagOffer" => "Draw · time, with a draw on offer"
  | "draw flagInsufficient" => "Draw · time, and not enough to mate"
  | "draw resignDead" => "Draw · resignation in a dead position"
  | other => other

@[noinline] def squareEl (look : Look) (selected : String) (targets : List String)
    (press : String → String → Action Unit) (f r : String) : Element :=
  let sq := f ++ r
  let piece := pieceOn look.board sq
  let dark := (fileIdx f + rankIdx r) % 2 == 0
  let inCheck := look.check == "yes" &&
    match piece with | some p => p.kind == "king" && p.color == look.turn | none => false
  let cls := "sq"
    ++ (if dark then " dark" else " light")
    ++ (if selected == sq then " selected" else "")
    ++ (if targets.contains sq then (if piece.isSome then " target take" else " target") else "")
    ++ (if look.movedFrom == sq || look.movedTo == sq then " moved" else "")
    ++ (if inCheck then " check" else "")
  let mark := match piece with | some p => glyph p.color p.kind | none => ""
  DOM.button {
    className := some cls
    ariaLabel := some sq
    onPress := some (press f r)
  } #[
    text mark,
    if f == edgeFile look.you then DOM.span { className := some "coord rank" } #[text r] else text "",
    if r == nearRank look.you then DOM.span { className := some "coord file" } #[text f] else text ""
  ]

@[noinline] def boardEl (look : Look) (selected : String) (press : String → String → Action Unit) : Element :=
  let targets := if selected == "" then [] else targetsFrom look selected
  DOM.div { className := some "board", role := some "grid", ariaLabel := some "Board" }
    (rankOrder look.you |>.map fun r =>
      DOM.div { className := some "rank", role := some "row" }
        (fileOrder look.you |>.map fun f => squareEl look selected targets press f r))

def clockEl (name time : String) (active : Bool) : Element :=
  DOM.div { className := some ("clock" ++ if active then " live" else "") } #[
    DOM.span { className := some "who" } #[text name],
    DOM.span { className := some "time" } #[text time]
  ]

def brand : Element :=
  DOM.div { className := some "brand" } #[
    DOM.span { className := some "mark" } #[text "♔"],
    DOM.span { className := some "word" } #[text "LeanChess"]
  ]

def App : Component Props := component fun props => do
  let session ← useState props.saved "session"
  let game ← useState (none : Option Game) "game"
  let notice ← useState "" "notice"
  let name ← useState "" "name"
  let opponent ← useState "" "opponent"
  let joinId ← useState "" "join"
  let selected ← useState "" "selected"
  let promoting ← useState "" "promoting"
  let promotingTo ← useState "" "promotingTo"
  let seat ← useState "white" "seat"
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
        promoting.set ""
        notice.set (if next.look.admitted == "no" then "Refused. The log is unchanged." else "")
  -- A drop the domain calls illegal never reaches the server. A legal
  -- promotion asks for the piece. The server still admits or refuses.
  let tryMove (g : Game) (s : Session) (origin sq : String) : Action Unit := do
    let moves := (legalFrom g.look origin).filter (nameOf ·.to == sq)
    if !mine g.look.you g.look.turn then
      selected.set ""
      notice.set "It is not your turn."
    else if moves.isEmpty then
      selected.set ""
      notice.set "Not a legal move."
    else if moves.any (·.promotion.isSome) then
      promoting.set origin
      promotingTo.set sq
      notice.set ""
    else report (← props.api.act s g.id "play" origin sq "")
  let press (f r : String) : Action Unit := do
    let sq := f ++ r
    let current ← game.read
    let who ← session.read
    let origin ← selected.read
    match current, who with
    | some g, some s =>
        if g.look.ending != "" then pure ()
        else
          promoting.set ""
          match pieceOn g.look.board sq with
          | some piece =>
              if mine g.look.you piece.color then
                selected.set sq
                notice.set ""
              else if origin != "" then tryMove g s origin sq
              else pure ()
          | none =>
              if origin == "" then pure ()
              else tryMove g s origin sq
    | _, _ => pure ()
  let promote (kind : PieceKind) : Action Unit := do
    let origin ← promoting.read
    let dest ← promotingTo.read
    match (← game.read), (← session.read) with
    | some g, some s =>
        promoting.set ""
        report (← props.api.act s g.id "play" origin dest (kindName kind))
    | _, _ => pure ()
  let send (kind : String) : Action Unit := do
    match (← game.read), (← session.read) with
    | some g, some s =>
        if g.look.ending != "" then pure () else report (← props.api.act s g.id kind "" "" "")
    | _, _ => pure ()
  let signOut : Action Unit := do
    session.set none
    game.set none
    selected.set ""
    notice.set ""
    props.api.forget
  match session.value with
  | none =>
      pure <| DOM.main { className := some "gate" } #[
        DOM.form { className := some "gate-card", onSubmit := (do
          match ← props.api.register name.value with
          | .ok s =>
              session.set (some s)
              notice.set ""
          | .error message => notice.set message) } #[
          brand,
          DOM.p { className := some "lede" } #[text "One game, from the opening to an ending, with a clock."],
          DOM.label { htmlFor := "name" } #[text "Your name"],
          DOM.input {
            id := some "name"
            autoComplete := some "nickname"
            placeholder := some "What should the other seat call you?"
            value := some name.value
            onChange := some fun event => name.set event.value
          },
          DOM.button { className := some "primary wide", type := .submit } #[text "Take a seat"],
          DOM.p { className := some "notice", role := some "status", ariaLive := some "polite" } #[text notice.value]
        ]
      ]
  | some s =>
      let table := match game.value with
        | none =>
            DOM.section { className := some "empty" } #[
              DOM.p { className := some "empty-mark" } #[text "♔"],
              DOM.h1 {} #[text "The board is empty."],
              DOM.p { className := some "lede" } #[
                text "Play the machine, or open a game with someone who already has a name."
              ]
            ]
        | some g =>
            let youBlack := g.look.you == "black"
            let topName := spoken (if youBlack then g.white else g.black)
            let bottomName := spoken (if youBlack then g.black else g.white)
            let topLeft := if youBlack then g.look.whiteLeft else g.look.blackLeft
            let bottomLeft := if youBlack then g.look.blackLeft else g.look.whiteLeft
            let topSide := if youBlack then "white" else "black"
            let bottomSide := if youBlack then "black" else "white"
            let going := g.look.ending == ""
            DOM.section { className := some "table", ariaLabel := some "Game" } #[
              clockEl topName (clockLabel topLeft) (going && g.look.turn == topSide),
              boardEl g.look selected.value press,
              clockEl bottomName (clockLabel bottomLeft) (going && g.look.turn == bottomSide),
              if promoting.value == "" then text ""
              else
                DOM.div { className := some "promote", role := some "group", ariaLabel := some "Promote to" }
                  (PieceKind.promotions.toArray.map fun k =>
                    DOM.button { ariaLabel := some (kindName k), onPress := some (promote k) } #[
                      text (glyph g.look.turn (kindName k))
                    ]),
              DOM.p { className := some "status", role := some "status" } #[text (pretty g.look)]
            ]
      let rail := DOM.aside { className := some "rail" } #[
        DOM.header { className := some "top" } #[
          brand,
          DOM.div { className := some "account" } #[
            DOM.span { className := some "you" } #[text s.name],
            DOM.button { className := some "ghost", onPress := some signOut } #[text "Sign out"]
          ]
        ],
        DOM.section { className := some "card" } #[
          DOM.h2 {} #[text "Play the machine"],
          DOM.p { className := some "fine" } #[text "Five minutes. It sits the other side and plays one move at a time."],
          DOM.div { className := some "seg", role := some "group", ariaLabel := some "Your color" } #[
            DOM.button {
              className := some (if seat.value == "white" then "on" else "")
              onPress := some (seat.set "white")
            } #[text "White"],
            DOM.button {
              className := some (if seat.value == "black" then "on" else "")
              onPress := some (seat.set "black")
            } #[text "Black"]
          ],
          DOM.button {
            className := some "primary wide"
            onPress := some (do report (← props.api.machine s seat.value))
          } #[text "Start"]
        ],
        DOM.form { className := some "card", onSubmit := (do
          report (← props.api.start s opponent.value)) } #[
          DOM.h2 {} #[text "Play a person"],
          DOM.label { htmlFor := "opponent" } #[text "Their name"],
          DOM.input {
            id := some "opponent"
            placeholder := some "Already registered"
            value := some opponent.value
            onChange := some fun event => opponent.set event.value
          },
          DOM.button { className := some "wide", type := .submit } #[text "Start"]
        ],
        DOM.form { className := some "card", onSubmit := (do
          report (← props.api.join s joinId.value)) } #[
          DOM.h2 {} #[text "Open a game"],
          DOM.label { htmlFor := "join" } #[text "Number"],
          DOM.div { className := some "inline" } #[
            DOM.input {
              id := some "join"
              placeholder := some "12"
              value := some joinId.value
              onChange := some fun event => joinId.set event.value
            },
            DOM.button { type := .submit } #[text "Open"]
          ]
        ],
        match game.value with
        | none => text ""
        | some g =>
            DOM.section { className := some "card quiet" } #[
              DOM.p { className := some "fine" } #[
                text (spoken g.white ++ " · " ++ spoken g.black ++ " · game " ++ toString g.id)
              ],
              DOM.div { className := some "controls" } #[
                DOM.button { onPress := some (send "resign"), disabled := g.look.ending != "" } #[text "Resign"],
                DOM.button { onPress := some (send "offer"), disabled := g.look.ending != "" } #[text "Offer draw"],
                DOM.button { onPress := some (send "accept"), disabled := g.look.ending != "" } #[text "Accept"],
                DOM.button { onPress := some (send "decline"), disabled := g.look.ending != "" } #[text "Decline"]
              ],
              DOM.button { className := some "ghost", onPress := some (do
                game.set none
                selected.set ""
                notice.set "") } #[text "Leave this board"]
            ],
        DOM.p { className := some "notice", role := some "status", ariaLive := some "polite" } #[text notice.value]
      ]
      pure <| DOM.main { className := some "page" } #[
        DOM.div { className := some "stage" } #[table, rail]
      ]

end LeanChess.Ui
