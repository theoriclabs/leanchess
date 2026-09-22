/-
  A seated player. It proposes one legal move. The fold still admits it.
-/

import domain.Game

namespace LeanChess.Api.Bot

open LeanChess

def botName : String := "Machine"

def pieceValue : PieceKind → Int
  | .pawn => 100
  | .knight => 320
  | .bishop => 330
  | .rook => 500
  | .queen => 900
  | .king => 0

/-- 0 in a corner, 12 on d4, d5, e4, and e5. -/
def centrality (s : Square) : Int :=
  let f : Int := s.file.index
  let r : Int := s.rank.index
  let fd := (f * 2 - 7).natAbs
  let rd := (r * 2 - 7).natAbs
  14 - (fd + rd)

def pawnCenter (pl : Placement) : Int :=
  let midFile := pl.square.file == .d || pl.square.file == .e
  let midRank := pl.square.rank == .r4 || pl.square.rank == .r5
  if pl.piece.kind == .pawn && midFile && midRank then 12 else 0

/-- Material, then where the pieces stand. Mate dwarfs both. -/
def score (p : Position) (root : Color) : Int :=
  let placed := p.board.foldl (init := (0 : Int)) fun acc pl =>
    let v := pieceValue pl.piece.kind * 16 + centrality pl.square + pawnCenter pl
    if pl.piece.color == root then acc + v else acc - v
  if (legalMoves p).isEmpty then
    if inCheck p then
      if p.side == root then placed - 100000 else placed + 100000
    else
      0
  else
    placed

/-- One reply by the other seat, taken at its best. -/
def afterReply (p : Position) (root : Color) : Int :=
  match legalMoves p with
  | [] => score p root
  | m :: ms =>
    let ofMove (mv : Move) : Int :=
      match applyMove p mv with
      | none => score p root
      | some next => score next root
    ms.foldl (fun acc mv => min acc (ofMove mv)) (ofMove m)

/-- The move the side to move prefers, seeing one reply. -/
def choose (p : Position) : Option Move :=
  match legalMoves p with
  | [] => none
  | m :: ms =>
    let ofMove (mv : Move) : Int :=
      match applyMove p mv with
      | none => -200000
      | some next => afterReply next p.side
    some <| ms.foldl (fun best mv => if ofMove mv > ofMove best then mv else best) m

end LeanChess.Api.Bot
