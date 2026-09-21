/-
  The same game, one step past `domain/Deep.lean` on both axes.

  Deeper. The interpreter does not name castling, en passant, or promotion.
  It evaluates a query (`empty`, `piece`, `rank`, `betweenEmpty`, `notAttacked`,
  `kingSafe`, …) and applies an effect (`clear`, `put`, `setEp`, `vacate`,
  `half`, `turn`). The rook's move in castling is a `put` in the law.

  Lazier. A position's board is the opening plus the writes of the moves
  played, and a square is read by walking those writes. The repetition key
  sits in a thunk. Forcing a ply, or judging checkmate, does not force it:
  `judge` only forces the thunk when the law it is reading mentions repetitions.
-/

import domain.Game

namespace LeanChess.Lazier

open LeanChess

/- ====================================================================
   Lazy streams. The tail is a thunk.
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

partial def any (p : α → Bool) : Stream α → Bool
  | .nil => false
  | .cons x xs => if p x then true else any p xs.get

def isEmpty : Stream α → Bool
  | .nil => true
  | .cons _ _ => false

partial def length : Stream α → Nat
  | .nil => 0
  | .cons _ xs => length xs.get + 1

end Stream

/- ====================================================================
   Syntax. Locations, queries, and effects. No chess-move atom.
   ==================================================================== -/

/-- A step. `forward` is in the mover's pawn direction. -/
inductive Off where
  | rel (df dr : Int)
  | forward (df n : Int)
  deriving Repr, BEq

/-- Whose piece, relative to the side to move. -/
inductive Side where
  | mover
  | opponent
  deriving Repr, BEq

/-- Which piece a `put` writes. -/
inductive KindOf where
  | mover
  | fixed (k : PieceKind)
  | promoted
  deriving Repr, BEq

/-- A square named from the move, not a stored coordinate. -/
inductive Loc where
  | src
  | dest
  | off (base : Loc) (o : Off)
  | here (s : Square)
  | king (c : Side)
  | home (isKing kingside : Bool)
  deriving Repr, BEq

inductive Query where
  | empty (loc : Loc)
  | piece (loc : Loc) (c : Side) (k : KindOf)
  | enemy (loc : Loc)
  | rank (loc : Loc) (white black : Rank)
  | hasRight (kingside : Bool)
  | betweenEmpty (a b : Loc)
  | epAt (loc : Loc)
  | notAttacked (loc : Loc)
  | kingSafe
  | and (a b : Query)
  | not (q : Query)
  deriving Repr

/-- What a law does to the position. The interpreter applies these and
    nothing else. -/
inductive Effect where
  | clear (loc : Loc)
  | put (loc : Loc) (k : KindOf)
  | setEp (loc : Option Loc)
  | vacate (loc : Loc)
  | half (reset : Bool)
  | turn
  deriving Repr

inductive Gen where
  | leaps (os : List Off)
  | rays (os : List Off)
  | one (loc : Loc)
  | pawnTakes
  deriving Repr, BEq

structure Law where
  piece : PieceKind
  gen : Gen
  when : Query
  does : List Effect
  promotions : Bool := false
  deriving Repr

/- ====================================================================
   The board as an overlay. Reading one square walks the writes and
   stops. It does not rebuild the placement list.
   ==================================================================== -/

inductive Overlay where
  | base (b : Board)
  | above (sq : Square) (pc : Option Piece) (rest : Overlay)

namespace Overlay

def get : Overlay → Square → Option Piece
  | .base b, s => b.get s
  | .above sq pc rest, s => if sq == s then pc else get rest s

/-- The placement list. Used when a consumer asks for the whole board,
    which the repetition key does and a square lookup does not. -/
def materialize : Overlay → Board
  | .base b => b
  | .above sq pc rest => rest.materialize.set sq pc

end Overlay

structure LazyPos where
  board : Overlay
  side : Color
  rights : Rights
  ep : Option Square
  halfmove : Nat
  fullmove : Nat

def lazyOpening : LazyPos where
  board := .base opening.board
  side := opening.side
  rights := opening.rights
  ep := opening.ep
  halfmove := opening.halfmove
  fullmove := opening.fullmove

def allSquares : List Square :=
  File.all.flatMap fun file =>
    [Rank.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8].map fun r => ⟨file, r⟩

def findKing (o : Overlay) (c : Color) : Option Square :=
  allSquares.find? fun s =>
    match o.get s with
    | some pc => pc.color == c && pc.kind == .king
    | none => false

def paint (mover : Color) : Side → Color
  | .mover => mover
  | .opponent => mover.other

def homeSq (isKing kingside : Bool) (c : Color) : Square :=
  let rank := if c == .white then Rank.r1 else Rank.r8
  let file := if isKing then File.e else if kingside then File.h else File.a
  ⟨file, rank⟩

def offNums (c : Color) : Off → Int × Int
  | .rel df dr => (df, dr)
  | .forward df n => (df, n * pawnDir c)

def resolve (mover : Color) (board : Overlay) (src dest : Square) : Loc → Option Square
  | .src => some src
  | .dest => some dest
  | .here s => some s
  | .king c => findKing board (paint mover c)
  | .home isKing kingside => some (homeSq isKing kingside mover)
  | .off base o => do
      let s ← resolve mover board src dest base
      let (df, dr) := offNums mover o
      s.offset df dr

/- ====================================================================
   Laws. Castling is a list of effects, including the rook's `put`.
   ==================================================================== -/

def ortho : List Off := [.rel 0 1, .rel 0 (-1), .rel 1 0, .rel (-1) 0]

def diag : List Off := [.rel 1 1, .rel 1 (-1), .rel (-1) 1, .rel (-1) (-1)]

def around : List Off := ortho ++ diag

def knightLeaps : List Off :=
  [.rel 1 2, .rel 1 (-2), .rel (-1) 2, .rel (-1) (-2),
   .rel 2 1, .rel 2 (-1), .rel (-2) 1, .rel (-2) (-1)]

def qAnd (qs : List Query) : Query :=
  qs.foldr (fun a b => .and a b) .kingSafe

def reloc (reset : Bool) (arrived : KindOf) : List Effect :=
  [.clear .src, .put .dest arrived, .setEp none, .vacate .src, .vacate .dest, .half reset, .turn]

def castleDoes (kingside : Bool) : List Effect :=
  let rookFrom := Loc.home false kingside
  let step : Int := if kingside then 1 else -1
  [
    .clear .src,
    .clear rookFrom,
    .put .dest .mover,
    .put (Loc.off .src (.rel step 0)) (.fixed .rook),
    .setEp none,
    .vacate .src,
    .vacate .dest,
    .vacate rookFrom,
    .half false,
    .turn,
  ]

def castleWhen (kingside : Bool) : List Query :=
  let step : Int := if kingside then 1 else -1
  [
    .hasRight kingside,
    .piece (Loc.home false kingside) .mover (.fixed .rook),
    .betweenEmpty .src (Loc.home false kingside),
    .notAttacked (Loc.king .mover),
    .notAttacked (Loc.off .src (.rel step 0)),
  ]

def law (piece : PieceKind) (gen : Gen) (must : List Query) (does : List Effect)
    (promotions : Bool := false) : Law where
  piece := piece
  gen := gen
  when := qAnd must
  does := does
  promotions := promotions

def standardLaws : List Law := [
  law .rook (.rays ortho) [.empty .dest] (reloc false .mover),
  law .rook (.rays ortho) [.enemy .dest] (reloc true .mover),
  law .bishop (.rays diag) [.empty .dest] (reloc false .mover),
  law .bishop (.rays diag) [.enemy .dest] (reloc true .mover),
  law .queen (.rays (ortho ++ diag)) [.empty .dest] (reloc false .mover),
  law .queen (.rays (ortho ++ diag)) [.enemy .dest] (reloc true .mover),
  law .knight (.leaps knightLeaps) [.empty .dest] (reloc false .mover),
  law .knight (.leaps knightLeaps) [.enemy .dest] (reloc true .mover),
  law .king (.leaps around) [.empty .dest] (reloc false .mover),
  law .king (.leaps around) [.enemy .dest] (reloc true .mover),
  law .pawn (.one (Loc.off .src (.forward 0 1)))
    [.empty .dest, .not (.rank .dest .r8 .r1)] (reloc true .mover),
  law .pawn (.one (Loc.off .src (.forward 0 1)))
    [.empty .dest, .rank .dest .r8 .r1] (reloc true .promoted) true,
  law .pawn (.one (Loc.off .src (.forward 0 2)))
    [.empty .dest, .betweenEmpty .src .dest, .rank .src .r2 .r7]
    [.clear .src, .put .dest .mover,
     .setEp (some (Loc.off .src (.forward 0 1))),
     .vacate .src, .vacate .dest, .half true, .turn],
  law .pawn (.pawnTakes) [.enemy .dest, .not (.rank .dest .r8 .r1)] (reloc true .mover),
  law .pawn (.pawnTakes) [.enemy .dest, .rank .dest .r8 .r1] (reloc true .promoted) true,
  law .pawn (.pawnTakes)
    [.empty .dest, .epAt .dest]
    [.clear .src, .put .dest .mover, .clear (Loc.off .dest (.forward 0 (-1))),
     .setEp none, .vacate .src, .vacate .dest, .half true, .turn],
  law .king (.one (Loc.off .src (.rel 2 0))) (castleWhen true) (castleDoes true),
  law .king (.one (Loc.off .src (.rel (-2) 0))) (castleWhen false) (castleDoes false),
]

/-- A pawn's two-step law records the square it passed as data. -/
def setsEp (l : Law) : Bool :=
  l.does.any fun e =>
    match e with
    | .setEp (some _) => true
    | _ => false

/-- Castling's rook move is an effect on the law, not a branch in `apply`. -/
def putsRook (l : Law) : Bool :=
  l.does.any fun e =>
    match e with
    | .put _ (.fixed .rook) => true
    | _ => false

def isAttackGen : Gen → Bool
  | .rays _ | .leaps _ | .pawnTakes => true
  | .one _ => false

def attackSpecs : List (PieceKind × Gen) :=
  standardLaws.foldl (init := []) fun acc l =>
    if isAttackGen l.gen && !acc.any fun s => s.1 == l.piece && s.2 == l.gen
    then acc ++ [(l.piece, l.gen)]
    else acc

/- ====================================================================
   Semantics. `evalQ` and `apply` are the whole interpreter.
   ==================================================================== -/

partial def ray (b : Overlay) (src : Square) (df dr : Int) : Stream Square :=
  let rec go (s : Square) : Stream Square :=
    match s.offset df dr with
    | none => .nil
    | some s' =>
      match b.get s' with
      | none => .cons s' (Thunk.mk fun () => go s')
      | some _ => .cons s' (Thunk.pure .nil)
  go src

partial def squares (p : LazyPos) (src : Square) : Gen → Stream Square
  | .leaps os =>
    Stream.ofList (os.filterMap fun o =>
      let (df, dr) := offNums p.side o
      src.offset df dr)
  | .rays os =>
    Stream.ofList os |>.bind fun o =>
      let (df, dr) := offNums p.side o
      ray p.board src df dr
  | .one loc =>
    match resolve p.side p.board src src loc with
    | some s => Stream.one s
    | none => .nil
  | .pawnTakes =>
    let d := pawnDir p.side
    Stream.ofList ([src.offset 1 d, src.offset (-1) d].filterMap id)

def occupiedBy (b : Overlay) (s : Square) (c : Color) : Bool :=
  match b.get s with
  | some pc => pc.color == c
  | none => false

def attacked (p : LazyPos) (by_ : Color) (target : Square) : Bool :=
  let b := p.board.materialize
  let q : LazyPos := { p with board := .base b }
  attackSpecs.any fun (kind, gen) =>
    b.any fun pl =>
      pl.piece.color == by_ && pl.piece.kind == kind &&
        (squares q pl.square gen).any (· == target) &&
        !occupiedBy q.board target by_

def pieceOf (origin : Option Piece) (promo : Option PieceKind) (mover : Color) : KindOf → Option Piece
  | .mover => origin
  | .fixed k => some ⟨mover, k⟩
  | .promoted => promo.map (⟨mover, ·⟩)

def apply1 (mover : Color) (origin : Option Piece) (promo : Option PieceKind)
    (src dest : Square) (p : LazyPos) : Effect → LazyPos
  | .clear loc =>
    match resolve mover p.board src dest loc with
    | some s => { p with board := .above s none p.board }
    | none => p
  | .put loc k =>
    match resolve mover p.board src dest loc, pieceOf origin promo mover k with
    | some s, some pc => { p with board := .above s (some pc) p.board }
    | _, _ => p
  | .setEp none => { p with ep := none }
  | .setEp (some loc) =>
    match resolve mover p.board src dest loc with
    | some s => { p with ep := some s }
    | none => { p with ep := none }
  | .vacate loc =>
    match resolve mover p.board src dest loc with
    | some s => { p with rights := p.rights.vacate s }
    | none => p
  | .half reset => { p with halfmove := if reset then 0 else p.halfmove + 1 }
  | .turn =>
    { p with
      side := p.side.other
      fullmove := if p.side == .black then p.fullmove + 1 else p.fullmove }

def apply (p : LazyPos) (src dest : Square) (promo : Option PieceKind) (fx : List Effect) : LazyPos :=
  let origin := p.board.get src
  fx.foldl (apply1 p.side origin promo src dest) p

def evalQ (p : LazyPos) (src dest : Square) (promo : Option PieceKind) (fx : List Effect) : Query → Bool
  | .empty loc =>
    match resolve p.side p.board src dest loc with
    | some s => p.board.get s == none
    | none => false
  | .piece loc c k =>
    match resolve p.side p.board src dest loc, pieceOf (p.board.get src) promo p.side k with
    | some s, some want =>
      match p.board.get s with
      | some pc => pc.color == paint p.side c && pc.kind == want.kind
      | none => false
    | _, _ => false
  | .enemy loc =>
    match resolve p.side p.board src dest loc with
    | some s => occupiedBy p.board s p.side.other
    | none => false
  | .rank loc rw rb =>
    match resolve p.side p.board src dest loc with
    | some s => s.rank == (if p.side == .white then rw else rb)
    | none => false
  | .hasRight kingside => p.rights.allows p.side kingside
  | .betweenEmpty a b =>
    match resolve p.side p.board src dest a, resolve p.side p.board src dest b with
    | some a, some b =>
      match between a b with
      | some ss => ss.all fun s => p.board.get s == none
      | none => false
    | _, _ => false
  | .epAt loc =>
    match resolve p.side p.board src dest loc with
    | some s => p.ep == some s
    | none => false
  | .notAttacked loc =>
    match resolve p.side p.board src dest loc with
    | some s => !attacked p p.side.other s
    | none => false
  | .kingSafe =>
    let p' := apply p src dest promo fx
    match findKing p'.board p.side with
    | some s => !attacked p' p.side.other s
    | none => false
  | .and a b =>
    if evalQ p src dest promo fx a then evalQ p src dest promo fx b else false
  | .not q => !evalQ p src dest promo fx q

def promoOk (l : Law) (m : Move) : Bool :=
  if l.promotions then
    match m.promotion with
    | some k => k.promotes
    | none => false
  else
    m.promotion.isNone

def movesFrom (p : LazyPos) (l : Law) : Stream Move :=
  let pieces := p.board.materialize.filter fun pl =>
    pl.piece.color == p.side && pl.piece.kind == l.piece
  Stream.ofList pieces |>.bind fun pl =>
    (squares p pl.square l.gen).bind fun dest =>
      let emit (m : Move) : Stream Move :=
        if evalQ p pl.square dest m.promotion l.does l.when then Stream.one m else .nil
      if l.promotions then
        Stream.ofList [PieceKind.queen, .rook, .bishop, .knight] |>.bind fun k =>
          emit ⟨pl.square, dest, some k⟩
      else
        emit ⟨pl.square, dest, none⟩

def legal (p : LazyPos) : Stream Move :=
  Stream.ofList standardLaws |>.bind fun l => movesFrom p l

def matching (p : LazyPos) (m : Move) : Option Law :=
  match p.board.get m.src with
  | none => none
  | some pc =>
    if pc.color != p.side then none
    else
      standardLaws.find? fun l =>
        l.piece == pc.kind && promoOk l m &&
          (squares p m.src l.gen).any (· == m.to) &&
            evalQ p m.src m.to m.promotion l.does l.when

def step (p : LazyPos) (m : Move) : Option LazyPos :=
  (matching p m).map fun l => apply p m.src m.to m.promotion l.does

/- ====================================================================
   Repetition. The key is computed only when its thunk is forced.
   `ep` counts only when a pawn capture to that square is legal.
   ==================================================================== -/

def epLive (p : LazyPos) : Bool :=
  match p.ep with
  | none => false
  | some sq =>
    (legal p).any fun m =>
      m.to == sq &&
        match p.board.get m.src with
        | some pc => pc.kind == .pawn
        | none => false

def key (p : LazyPos) : PosKey where
  board := sortBoard p.board.materialize
  side := p.side
  rights := p.rights
  ep := if epLive p then p.ep else none

/- ====================================================================
   A line. Forcing the next ply applies that move's effects and leaves
   the repetition key of every ply unforced.
   ==================================================================== -/

set_option genSizeOfSpec false in
structure Node where
  pos : LazyPos
  reps : Thunk (List PosKey)
  next : Thunk (Option Node)

instance : Inhabited Node where
  default := { pos := lazyOpening, reps := Thunk.pure [], next := Thunk.pure none }

partial def line (p : LazyPos) (earlier : Thunk (List PosKey)) : List Move → Node
  | [] =>
    { pos := p
      reps := Thunk.mk fun () => key p :: earlier.get
      next := Thunk.pure none }
  | m :: ms =>
    { pos := p
      reps := Thunk.mk fun () => key p :: earlier.get
      next := Thunk.mk fun () =>
        match step p m with
        | none => none
        | some p' => some (line p' (Thunk.mk fun () => key p :: earlier.get) ms) }

def start (moves : List Move) : Node :=
  line lazyOpening (Thunk.pure []) moves

def nodeAt : Nat → Node → Node
  | 0, node => node
  | n + 1, node =>
    match node.next.get with
    | none => node
    | some nxt => nodeAt n nxt

def times (node : Node) : Nat :=
  match node.reps.get with
  | [] => 0
  | k :: rest => (k :: rest).filter (· == k) |>.length

/- ====================================================================
   Endings, as queries. Checkmate does not mention repetitions, so
   judging it does not force the key.
   ==================================================================== -/

inductive Verdict where
  | checkmate
  | stalemate
  | dead
  | fivefold
  | seventyFive
  deriving Repr, BEq

/-- Whether `c` can still deliver mate, under the same safe approximation
    as the other files: a pawn, rook, or queen can; two knights can; a
    lone knight or a lone bishop against a bare king cannot. -/
inductive Help where
  | major (c : Color)
  | several (c : Color)
  | minor (c : Color)
  | or (a b : Help)
  deriving Repr

inductive EndQ where
  | inCheck
  | noMove
  | help (h : Help)
  | repsAtLeast (n : Nat)
  | halfAtLeast (n : Nat)
  | and (a b : EndQ)
  | not (q : EndQ)
  deriving Repr

structure EndLaw where
  name : Verdict
  when : EndQ
  deriving Repr

def canHelp (c : Color) : Help :=
  .or (.major c) (.or (.several c) (.minor c))

def endLaws : List EndLaw := [
  { name := .checkmate, when := .and .inCheck .noMove },
  { name := .stalemate, when := .and (.not .inCheck) .noMove },
  { name := .dead, when := .and (.not (.help (canHelp .white))) (.not (.help (canHelp .black))) },
  { name := .fivefold, when := .repsAtLeast 5 },
  { name := .seventyFive,
    when := .and (.halfAtLeast 150) (.not (.and .inCheck .noMove)) },
]

def usesReps : EndQ → Bool
  | .repsAtLeast _ => true
  | .and a b => usesReps a || usesReps b
  | .not q => usesReps q
  | _ => false

def bishopsSame (b : Board) : Bool :=
  let bs := b.filter fun p => p.piece.kind == .bishop
  match bs with
  | [] => true
  | p :: ps => ps.all fun q => q.square.isLight == p.square.isLight

def evalHelp (p : LazyPos) : Help → Bool
  | .or a b => evalHelp p a || evalHelp p b
  | .major c =>
    let b := p.board.materialize
    b.any fun pl => pl.piece.color == c && (pl.piece.kind == .queen || pl.piece.kind == .rook || pl.piece.kind == .pawn)
  | .several c =>
    let b := p.board.materialize
    let mine := b.filter fun pl => pl.piece.color == c && pl.piece.kind != .king
    let theirs := b.filter fun pl => pl.piece.color == c.other && pl.piece.kind != .king
    mine.length ≥ 2 &&
      !(mine.all (·.piece.kind == .bishop) && bishopsSame b && theirs.all (·.piece.kind == .bishop))
  | .minor c =>
    let b := p.board.materialize
    let mine : List PieceKind := b.filterMap fun pl =>
      if pl.piece.color == c && pl.piece.kind != .king then some pl.piece.kind else none
    let theirs := b.filter fun pl => pl.piece.color == c.other && pl.piece.kind != .king
    match mine with
    | [PieceKind.knight] => theirs.length > 0
    | [PieceKind.bishop] => theirs.length > 0 && !(theirs.all (·.piece.kind == .bishop) && bishopsSame b)
    | _ => false

def evalEnd (p : LazyPos) (reps : Nat) : EndQ → Bool
  | .inCheck =>
    match findKing p.board p.side with
    | some s => attacked p p.side.other s
    | none => true
  | .noMove => (legal p).isEmpty
  | .help h => evalHelp p h
  | .repsAtLeast n => reps ≥ n
  | .halfAtLeast n => p.halfmove ≥ n
  | .and a b => if evalEnd p reps a then evalEnd p reps b else false
  | .not q => !evalEnd p reps q

def judge (node : Node) : Option Verdict :=
  (endLaws.find? fun l =>
    let reps := if usesReps l.when then times node else 0
    evalEnd node.pos reps l.when).map (·.name)

/- ====================================================================
   Checks.
   ==================================================================== -/

#guard standardLaws.any fun l => l.piece == .king && putsRook l
#guard standardLaws.any setsEp
#guard attackSpecs.any fun s => s.1 == .rook

#guard endLaws.any fun l => l.name == .checkmate && !usesReps l.when
#guard endLaws.any fun l => l.name == .fivefold && usesReps l.when

#guard (legal lazyOpening).length == 20
#guard (step lazyOpening (mv .e .r2 .e .r5)).isNone

def scholarLine : List Move := [
  mv .e .r2 .e .r4, mv .e .r7 .e .r5,
  mv .d .r1 .h .r5, mv .b .r8 .c .r6,
  mv .f .r1 .c .r4, mv .g .r8 .f .r6,
  mv .h .r5 .f .r7,
]

#guard (start scholarLine).pos.board.get ⟨.e, .r2⟩ == some ⟨.white, .pawn⟩
#guard judge (nodeAt 7 (start scholarLine)) == some .checkmate

def castleLine : List Move := [
  mv .e .r2 .e .r4, mv .e .r7 .e .r5,
  mv .g .r1 .f .r3, mv .b .r8 .c .r6,
  mv .f .r1 .c .r4, mv .f .r8 .c .r5,
  mv .e .r1 .g .r1,
]

#guard (nodeAt 7 (start castleLine)).pos.board.get ⟨.g, .r1⟩ == some ⟨.white, .king⟩
#guard (nodeAt 7 (start castleLine)).pos.board.get ⟨.f, .r1⟩ == some ⟨.white, .rook⟩
#guard (nodeAt 7 (start castleLine)).pos.board.get ⟨.e, .r1⟩ == none
#guard (nodeAt 7 (start castleLine)).pos.board.get ⟨.h, .r1⟩ == none

def epLine : List Move := [
  mv .e .r2 .e .r4, mv .a .r7 .a .r6,
  mv .e .r4 .e .r5, mv .d .r7 .d .r5,
  mv .e .r5 .d .r6,
]

#guard (nodeAt 5 (start epLine)).pos.board.get ⟨.d, .r6⟩ == some ⟨.white, .pawn⟩
#guard (nodeAt 5 (start epLine)).pos.board.get ⟨.d, .r5⟩ == none

def twoKings : LazyPos where
  board := .base [⟨⟨.e, .r1⟩, ⟨.white, .king⟩⟩, ⟨⟨.e, .r8⟩, ⟨.black, .king⟩⟩]
  side := .white
  rights := Rights.none
  ep := none
  halfmove := 0
  fullmove := 1

#guard !evalHelp twoKings (canHelp .white)
#guard !evalHelp twoKings (canHelp .black)

end LeanChess.Lazier
