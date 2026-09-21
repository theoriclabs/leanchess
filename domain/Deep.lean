/-
  The same game, as a deep embedding with lazy evaluation.

  A law is a value. `eval` is what it means. The play of a line is a spine of
  thunks: the position now is present, and the position after the next move
  is not computed until that thunk is forced.
-/

import domain.Game

namespace LeanChess.Deep

open LeanChess

/- ====================================================================
   Lazy streams. The tail of a stream is a thunk.
   ==================================================================== -/

inductive Stream (α : Type) where
  | nil
  | cons (head : α) (tail : Thunk (Stream α))
  deriving Nonempty

namespace Stream

def one (x : α) : Stream α :=
  .cons x (Thunk.pure .nil)

partial def ofList : List α → Stream α
  | [] => .nil
  | x :: xs => .cons x (Thunk.mk fun () => ofList xs)

partial def append (a : Stream α) (b : Thunk (Stream α)) : Stream α :=
  match a with
  | .nil => b.get
  | .cons x xs => .cons x (Thunk.mk fun () => append xs.get b)

partial def bind (a : Stream α) (f : α → Stream β) : Stream β :=
  match a with
  | .nil => .nil
  | .cons x xs => append (f x) (Thunk.mk fun () => bind xs.get f)

partial def filter (p : α → Bool) : Stream α → Stream α
  | .nil => .nil
  | .cons x xs =>
    if p x then .cons x (Thunk.mk fun () => filter p xs.get)
    else filter p xs.get

partial def any (p : α → Bool) : Stream α → Bool
  | .nil => false
  | .cons x xs => if p x then true else any p xs.get

partial def toList : Stream α → List α
  | .nil => []
  | .cons x xs => x :: toList xs.get

def length (s : Stream α) : Nat :=
  s.toList.length

end Stream

/- ====================================================================
   Syntax. The laws of movement are values of these types.
   ==================================================================== -/

structure Delta where
  df : Int
  dr : Int
  deriving Repr, BEq, DecidableEq

inductive Gen where
  | leaps (ds : List Delta)
  | rays (ds : List Delta)
  | pawnForward (squares : Nat)
  | pawnTake
  | castle (kingside : Bool)
  deriving Repr, BEq, DecidableEq

inductive Atom where
  | destEmpty
  | destEnemy
  | pathClear
  | onStartRank
  | onPromoteRank
  | notOnPromoteRank
  | epIsDest
  | hasRight (kingside : Bool)
  | moverNotInCheck
  | passedSquareSafe
  | homeRook (kingside : Bool)
  | castlePathEmpty (kingside : Bool)
  | kingSafeAfter
  deriving Repr, BEq, DecidableEq

inductive Cond where
  | holds (a : Atom)
  | and (a b : Cond)
  | or (a b : Cond)
  | not (c : Cond)
  deriving Repr, BEq, DecidableEq

structure Law where
  piece : PieceKind
  gen : Gen
  when : Cond
  promotions : Bool := false
  deriving Repr, BEq, DecidableEq

inductive Verdict where
  | checkmate
  | stalemate
  | dead
  | fivefold
  | seventyFive
  deriving Repr, BEq, DecidableEq

inductive EndAtom where
  | inCheck
  | noLegalMove
  | cannotMate (c : Color)
  | repetitionsAtLeast (n : Nat)
  | halfmoveAtLeast (n : Nat)
  deriving Repr, BEq, DecidableEq

inductive EndCond where
  | holds (a : EndAtom)
  | and (a b : EndCond)
  | not (c : EndCond)
  deriving Repr, BEq, DecidableEq

structure EndLaw where
  name : Verdict
  when : EndCond
  deriving Repr, BEq, DecidableEq

/- Directions are data the laws name. The interpreter does not know
   which piece owns which direction until it reads a law. -/

def ortho : List Delta := [⟨0, 1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]

def diag : List Delta := [⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩]

def around : List Delta := ortho ++ diag

def knightLeaps : List Delta :=
  [⟨1, 2⟩, ⟨1, -2⟩, ⟨-1, 2⟩, ⟨-1, -2⟩, ⟨2, 1⟩, ⟨2, -1⟩, ⟨-2, 1⟩, ⟨-2, -1⟩]

def requires (atoms : List Atom) : Cond :=
  atoms.foldr (fun a rest => .and (.holds a) rest) (.holds .kingSafeAfter)

def law (piece : PieceKind) (gen : Gen) (must : List Atom) (promotions : Bool := false) : Law where
  piece := piece
  gen := gen
  when := requires must
  promotions := promotions

/-- The rules of how a piece may move. A value. -/
def standardLaws : List Law := [
  law .rook (.rays ortho) [.destEmpty],
  law .rook (.rays ortho) [.destEnemy],
  law .bishop (.rays diag) [.destEmpty],
  law .bishop (.rays diag) [.destEnemy],
  law .queen (.rays (ortho ++ diag)) [.destEmpty],
  law .queen (.rays (ortho ++ diag)) [.destEnemy],
  law .knight (.leaps knightLeaps) [.destEmpty],
  law .knight (.leaps knightLeaps) [.destEnemy],
  law .king (.leaps around) [.destEmpty],
  law .king (.leaps around) [.destEnemy],
  law .pawn (.pawnForward 1) [.destEmpty, .notOnPromoteRank],
  law .pawn (.pawnForward 1) [.destEmpty, .onPromoteRank] true,
  law .pawn (.pawnForward 2) [.destEmpty, .pathClear, .onStartRank],
  law .pawn (.pawnTake) [.destEnemy, .notOnPromoteRank],
  law .pawn (.pawnTake) [.destEnemy, .onPromoteRank] true,
  law .pawn (.pawnTake) [.destEmpty, .epIsDest],
  law .king (.castle true)
    [.hasRight true, .moverNotInCheck, .passedSquareSafe, .homeRook true, .castlePathEmpty true],
  law .king (.castle false)
    [.hasRight false, .moverNotInCheck, .passedSquareSafe, .homeRook false, .castlePathEmpty false],
]

/-- What ends a game on the board, in priority order. Checkmate is first,
    so it wins over the seventy-five-move draw. -/
def endLaws : List EndLaw := [
  { name := .checkmate
    when := .and (.holds .inCheck) (.holds .noLegalMove) },
  { name := .stalemate
    when := .and (.not (.holds .inCheck)) (.holds .noLegalMove) },
  { name := .dead
    when := .and (.holds (.cannotMate .white)) (.holds (.cannotMate .black)) },
  { name := .fivefold
    when := .holds (.repetitionsAtLeast 5) },
  { name := .seventyFive
    when := .and (.holds (.halfmoveAtLeast 150))
      (.not (.and (.holds .inCheck) (.holds .noLegalMove))) },
]

def isAttackGen : Gen → Bool
  | .rays _ | .leaps _ | .pawnTake => true
  | _ => false

/-- Which piece motions attack a square. Read off the laws, not written twice. -/
def attackSpecs : List (PieceKind × Gen) :=
  standardLaws.foldl (init := []) fun acc l =>
    if isAttackGen l.gen && !acc.any fun s => s.1 == l.piece && s.2 == l.gen
    then acc ++ [(l.piece, l.gen)]
    else acc

def mentionsCastle (laws : List Law) : Bool :=
  laws.any fun l =>
    match l.gen with
    | .castle _ => true
    | _ => false

/- ====================================================================
   Semantics.
   ==================================================================== -/

structure Env where
  pos : Position
  src : Square
  dest : Square

partial def ray (b : Board) (src : Square) (d : Delta) : Stream Square :=
  let rec go (s : Square) : Stream Square :=
    match s.offset d.df d.dr with
    | none => .nil
    | some s' =>
      match b.get s' with
      | none => .cons s' (Thunk.mk fun () => go s')
      | some _ => .cons s' (Thunk.pure .nil)
  go src

def squares (b : Board) (c : Color) (src : Square) : Gen → Stream Square
  | .leaps ds => Stream.ofList (ds.filterMap fun d => src.offset d.df d.dr)
  | .rays ds =>
    Stream.ofList ds |>.bind fun d => ray b src d
  | .pawnForward n =>
    match src.offset 0 (pawnDir c * (n : Int)) with
    | none => .nil
    | some s => Stream.one s
  | .pawnTake =>
    let d := pawnDir c
    Stream.ofList ([src.offset 1 d, src.offset (-1) d].filterMap id)
  | .castle kingside =>
    let dest :=
      if c == .white then
        if kingside then ⟨.g, .r1⟩ else ⟨.c, .r1⟩
      else if kingside then ⟨.g, .r8⟩ else ⟨.c, .r8⟩
    Stream.one dest

def occupiedBy (b : Board) (s : Square) (c : Color) : Bool :=
  match b.get s with
  | some pc => pc.color == c
  | none => false

/-- Does `by_` attack `target`? Walks the attack specs from the laws and
    stops at the first hit. A pin does not remove the attack. -/
def attacked (b : Board) (by_ : Color) (target : Square) : Bool :=
  attackSpecs.any fun (kind, gen) =>
    b.any fun pl =>
      pl.piece.color == by_ && pl.piece.kind == kind &&
        (squares b by_ pl.square gen).any (· == target) &&
        !(occupiedBy b target by_)

def sideInCheck (p : Position) (c : Color) : Bool :=
  match p.board.king c with
  | none => true
  | some s => attacked p.board c.other s

def place (p : Position) (m : Move) : Position := Id.run do
  let some pc := p.board.get m.src | return p
  let df := (m.to.file.index : Int) - m.src.file.index
  let dr := (m.to.rank.index : Int) - m.src.rank.index
  let mut board := p.board
  let mut rights := p.rights.vacate m.src |>.vacate m.to
  let mut ep : Option Square := none
  let mut capture := false
  let arrived :=
    match m.promotion with
    | some k => ⟨pc.color, k⟩
    | none => pc
  if pc.kind == .king && df.natAbs == 2 && dr == 0 then
    let kingside := df > 0
    let rookFrom : Square :=
      if pc.color == .white then
        if kingside then ⟨.h, .r1⟩ else ⟨.a, .r1⟩
      else if kingside then ⟨.h, .r8⟩ else ⟨.a, .r8⟩
    let rookTo ←
      match m.src.offset (if kingside then 1 else -1) 0 with
      | some s => pure s
      | none => return p
    board := board.set m.src none |>.set rookFrom none
      |>.set m.to (some pc) |>.set rookTo (some ⟨pc.color, .rook⟩)
    rights := rights.vacate rookFrom
  else if pc.kind == .pawn && m.to == p.ep.getD m.src && p.ep.isSome && board.get m.to == none then
    let dir := pawnDir pc.color
    let some capSq := m.to.offset 0 (-dir) | return p
    capture := true
    board := board.set m.src none |>.set capSq none |>.set m.to (some arrived)
  else
    capture := board.get m.to |>.isSome
    board := board.set m.src none |>.set m.to (some arrived)
    if pc.kind == .pawn && df == 0 && dr.natAbs == 2 then
      ep := m.src.offset 0 (pawnDir pc.color)
  let half := if pc.kind == .pawn || capture then 0 else p.halfmove + 1
  let full := if p.side == .black then p.fullmove + 1 else p.fullmove
  return {
    board
    side := p.side.other
    rights
    ep
    halfmove := half
    fullmove := full
  }

def evalAtom (e : Env) : Atom → Bool
  | .destEmpty => e.pos.board.get e.dest == none
  | .destEnemy => occupiedBy e.pos.board e.dest e.pos.side.other
  | .pathClear => pathClear e.pos.board e.src e.dest
  | .onStartRank =>
    e.src.rank == (match e.pos.side with | .white => .r2 | .black => .r7)
  | .onPromoteRank =>
    e.dest.rank == (match e.pos.side with | .white => .r8 | .black => .r1)
  | .notOnPromoteRank =>
    e.dest.rank != (match e.pos.side with | .white => .r8 | .black => .r1)
  | .epIsDest => e.pos.ep == some e.dest
  | .hasRight kingside => e.pos.rights.allows e.pos.side kingside
  | .moverNotInCheck => !sideInCheck e.pos e.pos.side
  | .passedSquareSafe =>
    let df := (e.dest.file.index : Int) - e.src.file.index
    let sign : Int := if df < 0 then -1 else 1
    match e.src.offset sign 0 with
    | none => false
    | some cross => !attacked e.pos.board e.pos.side.other cross
  | .homeRook kingside =>
    let rook : Square :=
      if e.pos.side == .white then
        if kingside then ⟨.h, .r1⟩ else ⟨.a, .r1⟩
      else if kingside then ⟨.h, .r8⟩ else ⟨.a, .r8⟩
    e.pos.board.get rook == some ⟨e.pos.side, .rook⟩
  | .castlePathEmpty kingside =>
    let rook : Square :=
      if e.pos.side == .white then
        if kingside then ⟨.h, .r1⟩ else ⟨.a, .r1⟩
      else if kingside then ⟨.h, .r8⟩ else ⟨.a, .r8⟩
    pathClear e.pos.board e.src rook
  | .kingSafeAfter =>
    !sideInCheck (place e.pos ⟨e.src, e.dest, none⟩) e.pos.side

def eval (e : Env) : Cond → Bool
  | .holds a => evalAtom e a
  | .and a b => if eval e a then eval e b else false
  | .or a b => if eval e a then true else eval e b
  | .not c => !eval e c

def promoOk (law : Law) (m : Move) : Bool :=
  if law.promotions then
    match m.promotion with
    | some k => k.promotes
    | none => false
  else
    m.promotion.isNone

/-- The moves one law produces. The tail of the stream is not forced
    until a consumer asks for the next move. -/
def movesFrom (p : Position) (law : Law) : Stream Move :=
  let pieces := p.board.filter fun pl =>
    pl.piece.color == p.side && pl.piece.kind == law.piece
  Stream.ofList pieces |>.bind fun pl =>
    (squares p.board p.side pl.square law.gen).bind fun dest =>
      let env : Env := { pos := p, src := pl.square, dest := dest }
      if !eval env law.when then .nil
      else if law.promotions then
        Stream.ofList [
          ⟨pl.square, dest, some .queen⟩,
          ⟨pl.square, dest, some .rook⟩,
          ⟨pl.square, dest, some .bishop⟩,
          ⟨pl.square, dest, some .knight⟩]
      else
        Stream.one ⟨pl.square, dest, none⟩

def legal (p : Position) : Stream Move :=
  Stream.ofList standardLaws |>.bind fun law => movesFrom p law

def accepts (p : Position) (m : Move) : Bool :=
  match p.board.get m.src with
  | none => false
  | some pc =>
    if pc.color != p.side then false
    else
      standardLaws.any fun law =>
        law.piece == pc.kind && promoOk law m &&
          (squares p.board p.side m.src law.gen).any (· == m.to) &&
            eval { pos := p, src := m.src, dest := m.to } law.when

def step (p : Position) (m : Move) : Option Position :=
  if accepts p m then some (place p m) else none

def epLive (p : Position) : Bool :=
  match p.ep with
  | none => false
  | some sq =>
    (legal p).any fun m =>
      m.to == sq &&
        match p.board.get m.src with
        | some pc => pc.kind == .pawn
        | none => false

def key (p : Position) : PosKey where
  board := sortBoard p.board
  side := p.side
  rights := p.rights
  ep := if epLive p then p.ep else none

/- ====================================================================
   A line of moves, suspended. Forcing ply n computes n steps and
   leaves the rest as a thunk.
   ==================================================================== -/

set_option genSizeOfSpec false in
structure Node where
  pos : Position
  seen : List PosKey
  next : Thunk (Option Node)

instance : Inhabited Node where
  default := { pos := opening, seen := [], next := Thunk.pure none }

partial def line (p : Position) (seen : List PosKey) : List Move → Node
  | [] => { pos := p, seen := seen, next := Thunk.pure none }
  | m :: ms =>
    { pos := p
      seen := seen
      next := Thunk.mk fun () =>
        match step p m with
        | none => none
        | some p' => some (line p' (key p' :: seen) ms) }

def start (moves : List Move) : Node :=
  line opening [key opening] moves

partial def nodeAt (n : Nat) (node : Node) : Node :=
  match n with
  | 0 => node
  | k + 1 =>
    match node.next.get with
    | none => node
    | some nxt => nodeAt k nxt

def times (node : Node) : Nat :=
  match node.seen with
  | [] => 0
  | k :: _ => (node.seen.filter (· == k)).length

def evalEnd (p : Position) (reps : Nat) : EndCond → Bool
  | .holds .inCheck => sideInCheck p p.side
  | .holds .noLegalMove => (legal p).toList.isEmpty
  | .holds (.cannotMate c) => !canMate p c
  | .holds (.repetitionsAtLeast n) => reps ≥ n
  | .holds (.halfmoveAtLeast n) => p.halfmove ≥ n
  | .and a b => if evalEnd p reps a then evalEnd p reps b else false
  | .not c => !evalEnd p reps c

def judge (node : Node) : Option Verdict :=
  (endLaws.find? fun l => evalEnd node.pos (times node) l.when).map (·.name)

/- ====================================================================
   Checks. Castle is found by matching the law, not by playing a game.
   The opening of a line is the opening, before any thunk is forced.
   ==================================================================== -/

#guard mentionsCastle standardLaws
#guard attackSpecs.any fun s => s.1 == .rook

#guard (legal opening).length == 20
#guard (step opening (mv .e .r2 .e .r5)).isNone

def scholarLine : List Move := [
  mv .e .r2 .e .r4, mv .e .r7 .e .r5,
  mv .d .r1 .h .r5, mv .b .r8 .c .r6,
  mv .f .r1 .c .r4, mv .g .r8 .f .r6,
  mv .h .r5 .f .r7,
]

#guard (start scholarLine).pos == opening
#guard judge (nodeAt 7 (start scholarLine)) == some .checkmate

def castleLine : List Move := [
  mv .e .r2 .e .r4, mv .e .r7 .e .r5,
  mv .g .r1 .f .r3, mv .b .r8 .c .r6,
  mv .f .r1 .c .r4, mv .f .r8 .c .r5,
  mv .e .r1 .g .r1,
]

#guard Board.get (nodeAt 7 (start castleLine)).pos.board ⟨.g, .r1⟩ == some ⟨.white, .king⟩
#guard Board.get (nodeAt 7 (start castleLine)).pos.board ⟨.f, .r1⟩ == some ⟨.white, .rook⟩

def epLine : List Move := [
  mv .e .r2 .e .r4, mv .a .r7 .a .r6,
  mv .e .r4 .e .r5, mv .d .r7 .d .r5,
  mv .e .r5 .d .r6,
]

#guard Board.get (nodeAt 5 (start epLine)).pos.board ⟨.d, .r6⟩ == some ⟨.white, .pawn⟩
#guard Board.get (nodeAt 5 (start epLine)).pos.board ⟨.d, .r5⟩ == none

def twoKings : Position where
  board := [⟨⟨.e, .r1⟩, ⟨.white, .king⟩⟩, ⟨⟨.e, .r8⟩, ⟨.black, .king⟩⟩]
  side := .white
  rights := Rights.none
  ep := none
  halfmove := 0
  fullmove := 1

#guard evalEnd twoKings 1 (.holds (.cannotMate .white))
#guard evalEnd twoKings 1 (.holds (.cannotMate .black))

end LeanChess.Deep
