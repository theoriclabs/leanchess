/-
  The boundary. A request is reconstructed into an act. A look is the fold
  rendered back out. Nothing in here is stored as the position.
-/

import Lean.Data.Json
import domain.Game

namespace LeanChess.Api

open Lean LeanChess

def colorName : Color → String
  | .white => "white"
  | .black => "black"

def parseColor (s : String) : Except String Color :=
  match s with
  | "white" => .ok .white
  | "black" => .ok .black
  | _ => .error s!"color is white or black, got {s}"

def kindName : PieceKind → String
  | .king => "king" | .queen => "queen" | .rook => "rook"
  | .bishop => "bishop" | .knight => "knight" | .pawn => "pawn"

def parseKind (s : String) : Except String PieceKind :=
  match s with
  | "queen" => .ok .queen | "rook" => .ok .rook
  | "bishop" => .ok .bishop | "knight" => .ok .knight
  | _ => .error s!"promotion is queen, rook, bishop, or knight, got {s}"

def fileChar : File → Char
  | .a => 'a' | .b => 'b' | .c => 'c' | .d => 'd'
  | .e => 'e' | .f => 'f' | .g => 'g' | .h => 'h'

def parseFile (c : Char) : Except String File :=
  match c with
  | 'a' => .ok .a | 'b' => .ok .b | 'c' => .ok .c | 'd' => .ok .d
  | 'e' => .ok .e | 'f' => .ok .f | 'g' => .ok .g | 'h' => .ok .h
  | _ => .error s!"file is a–h, got {c}"

def rankChar : Rank → Char
  | .r1 => '1' | .r2 => '2' | .r3 => '3' | .r4 => '4'
  | .r5 => '5' | .r6 => '6' | .r7 => '7' | .r8 => '8'

def parseRank (c : Char) : Except String Rank :=
  match c with
  | '1' => .ok .r1 | '2' => .ok .r2 | '3' => .ok .r3 | '4' => .ok .r4
  | '5' => .ok .r5 | '6' => .ok .r6 | '7' => .ok .r7 | '8' => .ok .r8
  | _ => .error s!"rank is 1–8, got {c}"

def squareName (s : Square) : String :=
  s!"{fileChar s.file}{rankChar s.rank}"

def parseSquare (s : String) : Except String Square := do
  let bs := s.toUTF8
  if bs.size != 2 then throw s!"square is a file and a rank, like e2, got {s}"
  let file ← parseFile (Char.ofUInt8 bs[0]!)
  let r ← parseRank (Char.ofUInt8 bs[1]!)
  return ⟨file, r⟩

def parseNat (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"expected a number, got {s}"

def renderAct : GameEvent → String
  | .moved m t =>
      let promo := match m.promotion with | none => "-" | some k => kindName k
      s!"moved {squareName m.src} {squareName m.to} {promo} {t.ms}"
  | .resigned c t => s!"resigned {colorName c} {t.ms}"
  | .drawOffered c t => s!"offered {colorName c} {t.ms}"
  | .drawAccepted c t => s!"accepted {colorName c} {t.ms}"
  | .drawDeclined c t => s!"declined {colorName c} {t.ms}"
  | .claimedThreefold c intended t =>
      match intended with
      | none => s!"threefold {colorName c} - - - {t.ms}"
      | some m =>
          let promo := match m.promotion with | none => "-" | some k => kindName k
          s!"threefold {colorName c} {squareName m.src} {squareName m.to} {promo} {t.ms}"
  | .claimedFifty c intended t =>
      match intended with
      | none => s!"fifty {colorName c} - - - {t.ms}"
      | some m =>
          let promo := match m.promotion with | none => "-" | some k => kindName k
          s!"fifty {colorName c} {squareName m.src} {squareName m.to} {promo} {t.ms}"
  | .aborted c t => s!"aborted {colorName c} {t.ms}"

def parseMove (src to promo : String) : Except String Move := do
  let src ← parseSquare src
  let to ← parseSquare to
  let promotion ←
    if promo == "-" then pure none else some <$> parseKind promo
  return ⟨src, to, promotion⟩

def parseAct (line : String) : Except String GameEvent := do
  match line.splitOn " " with
  | ["moved", src, to, promo, t] =>
      return .moved (← parseMove src to promo) ⟨← parseNat t⟩
  | ["resigned", c, t] => return .resigned (← parseColor c) ⟨← parseNat t⟩
  | ["offered", c, t] => return .drawOffered (← parseColor c) ⟨← parseNat t⟩
  | ["accepted", c, t] => return .drawAccepted (← parseColor c) ⟨← parseNat t⟩
  | ["declined", c, t] => return .drawDeclined (← parseColor c) ⟨← parseNat t⟩
  | ["threefold", c, "-", "-", "-", t] =>
      return .claimedThreefold (← parseColor c) none ⟨← parseNat t⟩
  | ["threefold", c, src, to, promo, t] =>
      return .claimedThreefold (← parseColor c) (some (← parseMove src to promo)) ⟨← parseNat t⟩
  | ["fifty", c, "-", "-", "-", t] =>
      return .claimedFifty (← parseColor c) none ⟨← parseNat t⟩
  | ["fifty", c, src, to, promo, t] =>
      return .claimedFifty (← parseColor c) (some (← parseMove src to promo)) ⟨← parseNat t⟩
  | ["aborted", c, t] => return .aborted (← parseColor c) ⟨← parseNat t⟩
  | _ => throw s!"stored act does not reconstruct: {line}"

/-- A client's act. The seat is whoever the token sits. The instant is not here. -/
inductive Requested where
  | play (move : Move)
  | resign
  | offer
  | accept
  | decline
  | threefold (intended : Option Move)
  | fifty (intended : Option Move)
  | abort

def field (j : Json) (k : String) : Except String Json :=
  j.getObjVal? k |>.mapError fun _ => s!"missing {k}"

def strField (j : Json) (k : String) : Except String String := do
  match ← field j k with
  | .str s => pure s
  | _ => throw s!"{k} must be a string"

def natField (j : Json) (k : String) : Except String Nat := do
  match (← field j k).getNat? with
  | .ok n => pure n
  | .error _ => throw s!"{k} must be a whole number"

def optStr (j : Json) (k : String) : Except String (Option String) := do
  match j.getObjVal? k with
  | .error _ => pure none
  | .ok .null => pure none
  | .ok (.str s) => pure (some s)
  | .ok _ => throw s!"{k} must be a string"

def optBool (j : Json) (k : String) (default : Bool) : Except String Bool := do
  match j.getObjVal? k with
  | .error _ | .ok .null => pure default
  | .ok (.bool b) => pure b
  | .ok _ => throw s!"{k} must be true or false"

def optNat (j : Json) (k : String) (default : Nat) : Except String Nat := do
  match j.getObjVal? k with
  | .error _ | .ok .null => pure default
  | .ok v =>
      match v.getNat? with
      | .ok n => pure n
      | .error _ => throw s!"{k} must be a whole number"

/-- `at`, when present, must be a whole number. Its value is not the command time. -/
def ignoreClientAt (j : Json) : Except String Unit := do
  match j.getObjVal? "at" with
  | .error _ | .ok .null => pure ()
  | .ok v =>
    match v.getNat? with
    | .ok _ => pure ()
    | .error _ => throw "at must be a whole number"

def parseRequested (j : Json) : Except String (Requested × Option Color) := do
  let kind ← strField j "kind"
  ignoreClientAt j
  let seat ← match ← optStr j "seat" with
    | none => pure none
    | some s => some <$> parseColor s
  let move? : Except String (Option Move) := do
    match ← optStr j "from", ← optStr j "to" with
    | none, none => pure none
    | some src, some dst =>
        let promo ← match ← optStr j "promotion" with
          | none => pure "-"
          | some s => pure s
        some <$> parseMove src dst promo
    | _, _ => throw "a play names both from and to"
  let req ← match kind with
    | "play" =>
        match ← move? with
        | some m => pure (.play m)
        | none => throw "a play names from and to"
    | "resign" => pure .resign
    | "offer" => pure .offer
    | "accept" => pure .accept
    | "decline" => pure .decline
    | "claim" =>
        let which ← strField j "claim"
        let intended ← move?
        match which with
        | "threefold" => pure (.threefold intended)
        | "fifty" => pure (.fifty intended)
        | _ => throw "claim is threefold or fifty"
    | "abort" => pure .abort
    | _ => throw s!"kind is play, resign, offer, accept, decline, claim, or abort, got {kind}"
  return (req, seat)

def eventOf (seat : Color) (instant : Nat) : Requested → GameEvent
  | .play m => .moved m ⟨instant⟩
  | .resign => .resigned seat ⟨instant⟩
  | .offer => .drawOffered seat ⟨instant⟩
  | .accept => .drawAccepted seat ⟨instant⟩
  | .decline => .drawDeclined seat ⟨instant⟩
  | .threefold m => .claimedThreefold seat m ⟨instant⟩
  | .fifty m => .claimedFifty seat m ⟨instant⟩
  | .abort => .aborted seat ⟨instant⟩

def endingJson : Option Ending → Json
  | none => .null
  | some (.checkmate c) => .str s!"checkmate {colorName c}"
  | some (.resign c) => .str s!"resign {colorName c}"
  | some (.flag c) => .str s!"flag {colorName c}"
  | some (.draw r) => .str s!"draw {match r with
      | .stalemate => "stalemate" | .dead => "dead" | .agreement => "agreement"
      | .threefold => "threefold" | .fifty => "fifty" | .fivefold => "fivefold"
      | .seventyFive => "seventyFive" | .flagOffer => "flagOffer"
      | .flagInsufficient => "flagInsufficient" | .resignDead => "resignDead"}"
  | some .abort => .str "abort"

def boardJson (b : Board) : Json :=
  .arr (b.map fun p => Json.mkObj [
    ("square", .str (squareName p.square)),
    ("color", .str (colorName p.piece.color)),
    ("kind", .str (kindName p.piece.kind))
  ]).toArray

def lastSquares (events : List GameEvent) : String × String :=
  events.foldl (fun acc e =>
    match e with
    | .moved m _ => (squareName m.src, squareName m.to)
    | _ => acc) ("", "")

def lookJson (s : GameState) (d : Instant) (you : String) (admitted : Option Bool)
    (movedFrom : String := "") (movedTo : String := "") (outcome : Option String := none) : Json :=
  let rights := s.position.rights
  let base := [
    ("ending", endingJson (resultAt s d)),
    ("turn", .str (colorName s.position.side)),
    ("offer", match s.offer with | none => .null | some c => .str (colorName c)),
    ("whiteLeft", toJson (remaining s .white d)),
    ("blackLeft", toJson (remaining s .black d)),
    ("ply", toJson s.ply),
    ("counts", .bool (countsForRating s)),
    ("you", .str you),
    ("check", .bool ((resultAt s d).isNone && inCheck s.position)),
    ("movedFrom", if movedFrom == "" then .null else .str movedFrom),
    ("movedTo", if movedTo == "" then .null else .str movedTo),
    ("board", boardJson s.position.board),
    ("rights", Json.mkObj [
      ("wk", .bool rights.wk), ("wq", .bool rights.wq),
      ("bk", .bool rights.bk), ("bq", .bool rights.bq)]),
    ("ep", match s.position.ep with | none => .null | some sq => .str (squareName sq)),
    ("halfmove", toJson s.position.halfmove),
    ("fullmove", toJson s.position.fullmove)
  ]
  let base := match outcome with
    | none => base
    | some o => ("outcome", .str o) :: base
  Json.mkObj <| match admitted with
    | none => base
    | some b => ("admitted", .bool b) :: base

end LeanChess.Api
