/-
  One game of standard chess.
  Vocabulary: vocabulary.md. Facts: facts.md.
  The agreement is the prior world. The log is the acts.
  The snapshot is the fold of a prefix of that log.

  What this file does not decide is named where it stops:
  * `Material.dead` is a detector, not the meaning of a dead position.
    The meaning, and what is proved of the detector, are in `domain/Mate.lean`.
  * `applyEvent` is total. Which acts a seat may propose, and what the
    server appends, is `admit` in `domain/Command.lean`.
  * A position is the placement, the side to move, the rights, and the
    en passant square (FIDE 9.2.3). The halfmove count and the move
    number are the fold's, not the position's.
-/

namespace LeanChess

/- ====================================================================
   Seats, people, squares
   ==================================================================== -/

inductive Color where
  | white
  | black
  deriving Repr, DecidableEq, Ord, Hashable

def Color.other : Color → Color
  | .white => .black
  | .black => .white

/-- Someone who can sit a game. `autoClaimThreefold` binds only this person. -/
structure Person where
  id : String
  autoClaimThreefold : Bool := false
  deriving Repr, DecidableEq

inductive File where
  | a | b | c | d | e | f | g | h
  deriving Repr, DecidableEq, Ord, Hashable

inductive Rank where
  | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8
  deriving Repr, DecidableEq, Ord, Hashable

def File.index : File → Nat
  | .a => 0 | .b => 1 | .c => 2 | .d => 3
  | .e => 4 | .f => 5 | .g => 6 | .h => 7

def Rank.index : Rank → Nat
  | .r1 => 0 | .r2 => 1 | .r3 => 2 | .r4 => 3
  | .r5 => 4 | .r6 => 5 | .r7 => 6 | .r8 => 7

def File.ofNat? : Nat → Option File
  | 0 => some .a | 1 => some .b | 2 => some .c | 3 => some .d
  | 4 => some .e | 5 => some .f | 6 => some .g | 7 => some .h
  | _ => none

def Rank.ofNat? : Nat → Option Rank
  | 0 => some .r1 | 1 => some .r2 | 2 => some .r3 | 3 => some .r4
  | 4 => some .r5 | 5 => some .r6 | 6 => some .r7 | 7 => some .r8
  | _ => none

def File.shift (file : File) (d : Int) : Option File :=
  let i := (file.index : Int) + d
  if 0 ≤ i && i < 8 then File.ofNat? i.toNat else none

def Rank.shift (r : Rank) (d : Int) : Option Rank :=
  let i := (r.index : Int) + d
  if 0 ≤ i && i < 8 then Rank.ofNat? i.toNat else none

structure Square where
  file : File
  rank : Rank
  deriving Repr, DecidableEq, Ord, Hashable

def Square.offset (s : Square) (df dr : Int) : Option Square :=
  match s.file.shift df, s.rank.shift dr with
  | some file, some r => some ⟨file, r⟩
  | _, _ => none

/-- a1 is dark. h1, White's near right-hand corner, is light. -/
def Square.isLight (s : Square) : Bool :=
  (s.file.index + s.rank.index) % 2 == 1

def File.all : List File := [.a, .b, .c, .d, .e, .f, .g, .h]

def Rank.all : List Rank := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8]

/-- Every square, in the order `Ord Square` sorts them. -/
def Square.all : List Square :=
  File.all.flatMap fun file => Rank.all.map fun r => ⟨file, r⟩

inductive PieceKind where
  | king | queen | rook | bishop | knight | pawn
  deriving Repr, DecidableEq, Ord, Hashable

structure Piece where
  color : Color
  kind : PieceKind
  deriving Repr, DecidableEq, Ord, Hashable

structure Placement where
  square : Square
  piece : Piece
  deriving Repr, DecidableEq, Hashable

/-- A board is a list of placements. A board the fold produces is sorted by
    square, so two boards with the same pieces on the same squares are the
    same list. `Board.set` keeps that order. -/
abbrev Board := List Placement

def insertBySquare (p : Placement) : List Placement → List Placement
  | [] => [p]
  | q :: qs =>
    match compare p.square q.square with
    | .gt => q :: insertBySquare p qs
    | _ => p :: q :: qs

def sortBoard : Board → Board
  | [] => []
  | p :: ps => insertBySquare p (sortBoard ps)

def Board.get (b : Board) (s : Square) : Option Piece :=
  (b.find? fun p => p.square == s).map (·.piece)

def Board.set (b : Board) (s : Square) (piece : Option Piece) : Board :=
  let b := b.filter fun p => p.square != s
  match piece with
  | none => b
  | some pc => insertBySquare ⟨s, pc⟩ b

def Board.king (b : Board) (c : Color) : Option Square :=
  (b.find? fun p => p.piece.color == c && p.piece.kind == .king).map (·.square)

/- ====================================================================
   Position. Placement plus what the placement does not show.
   ==================================================================== -/

/-- Kingside and queenside, per color. Lost when that king or that rook leaves its square. -/
structure Rights where
  wk : Bool
  wq : Bool
  bk : Bool
  bq : Bool
  deriving Repr, DecidableEq, Hashable

def Rights.opening : Rights := ⟨true, true, true, true⟩

def Rights.none : Rights := ⟨false, false, false, false⟩

def Rights.vacate (r : Rights) (s : Square) : Rights :=
  match s.file, s.rank with
  | .e, .r1 => { r with wk := false, wq := false }
  | .a, .r1 => { r with wq := false }
  | .h, .r1 => { r with wk := false }
  | .e, .r8 => { r with bk := false, bq := false }
  | .a, .r8 => { r with bq := false }
  | .h, .r8 => { r with bk := false }
  | _, _ => r

def Rights.allows (r : Rights) (c : Color) (kingside : Bool) : Bool :=
  if c == .white then
    if kingside then r.wk else r.wq
  else if kingside then r.bk else r.bq

/-- `a` keeps no right `b` has lost. A right, once lost, stays lost. -/
def Rights.le (a b : Rights) : Prop :=
  (a.wk → b.wk) ∧ (a.wq → b.wq) ∧ (a.bk → b.bk) ∧ (a.bq → b.bq)

/-- The position, in the sense of FIDE 9.2.3. -/
structure Position where
  board : Board
  side : Color
  rights : Rights
  /-- Square the capturing pawn would land on. Empty when no capture is waiting. -/
  ep : Option Square
  deriving Repr, DecidableEq, Hashable

def backRank (c : Color) (rank : Rank) : Board :=
  let kinds : List PieceKind := [.rook, .knight, .bishop, .queen, .king, .bishop, .knight, .rook]
  File.all.zip kinds |>.map fun (file, k) => ⟨⟨file, rank⟩, ⟨c, k⟩⟩

def pawnRow (c : Color) (rank : Rank) : Board :=
  File.all.map fun file => ⟨⟨file, rank⟩, ⟨c, .pawn⟩⟩

def opening : Position where
  board := sortBoard (
    backRank .white .r1 ++ pawnRow .white .r2 ++
    pawnRow .black .r7 ++ backRank .black .r8)
  side := .white
  rights := Rights.opening
  ep := none

/- ====================================================================
   Motion. Each kind of piece has rays, and slides along them or steps
   once. A pawn is the exception, and is written out below.
   ==================================================================== -/

/-- One act on the board. Castling is the king moving two squares.
    The promotion kind is part of a promoting move, and absent otherwise. -/
structure Move where
  src : Square
  to : Square
  promotion : Option PieceKind := none
  deriving Repr, DecidableEq, Hashable

def orthogonal : List (Int × Int) := [(1, 0), (-1, 0), (0, 1), (0, -1)]

def diagonal : List (Int × Int) := [(1, 1), (1, -1), (-1, 1), (-1, -1)]

def PieceKind.rays : PieceKind → List (Int × Int)
  | .knight => [(1, 2), (1, -2), (-1, 2), (-1, -2), (2, 1), (2, -1), (-2, 1), (-2, -1)]
  | .rook => orthogonal
  | .bishop => diagonal
  | .queen | .king => orthogonal ++ diagonal
  | .pawn => []

def PieceKind.slides : PieceKind → Bool
  | .rook | .bishop | .queen => true
  | _ => false

def PieceKind.promotions : List PieceKind := [.queen, .rook, .bishop, .knight]

def pawnDir : Color → Int
  | .white => 1
  | .black => -1

def homeRank : Color → Rank
  | .white => .r1
  | .black => .r8

def pawnRank : Color → Rank
  | .white => .r2
  | .black => .r7

def lastRank (c : Color) : Rank := homeRank c.other

/-- Squares along `(df, dr)` from `src`, up to and including the first occupied one. -/
def slide (b : Board) (src : Square) (df dr : Int) : List Square :=
  let rec go (fuel : Nat) (s : Square) : List Square :=
    match fuel with
    | 0 => []
    | n + 1 =>
      match s.offset df dr with
      | none => []
      | some s' =>
        match b.get s' with
        | none => s' :: go n s'
        | some _ => [s']
  go 7 src

/-- Squares a piece of kind `k` on `s` reaches: every step, or every slide. -/
def reach (b : Board) (s : Square) (k : PieceKind) : List Square :=
  k.rays.flatMap fun (df, dr) =>
    if k.slides then slide b s df dr else (s.offset df dr).toList

def pawnAttacks (c : Color) (s : Square) : List Square :=
  [s.offset 1 (pawnDir c), s.offset (-1) (pawnDir c)].filterMap id

/-- Squares `pc` on `s` attacks. A pin does not remove an attack. -/
def attacksFrom (b : Board) (s : Square) (pc : Piece) : List Square :=
  if pc.kind == .pawn then pawnAttacks pc.color s else reach b s pc.kind

def attacked (b : Board) (by_ : Color) (target : Square) : Bool :=
  b.any fun p =>
    p.piece.color == by_ && (attacksFrom b p.square p.piece).contains target

def kingAttacked (p : Position) (c : Color) : Bool :=
  match p.board.king c with
  | none => true
  | some s => attacked p.board c.other s

def inCheck (p : Position) : Bool :=
  kingAttacked p p.side

/- ====================================================================
   Moves. `candidates` names every move the geometry allows, each with
   what it does. `enact` writes that. A legal move is a candidate after
   which the mover's king is safe.
   ==================================================================== -/

/-- What a move does besides moving the piece. -/
structure Effect where
  /-- The piece that lands on `to`: the mover's piece, or the promotion. -/
  arrives : Piece
  /-- A captured piece that does not stand on `to`: en passant. -/
  taken : Option Square := none
  /-- The rook's displacement inside castling. -/
  rook : Option (Square × Square) := none
  /-- The en passant square this move leaves for the reply. -/
  ep : Option Square := none
  deriving Repr, DecidableEq

/-- A piece other than a pawn: every square it reaches that its own side does not hold. -/
def pieceMoves (p : Position) (s : Square) (pc : Piece) : List (Move × Effect) :=
  (reach p.board s pc.kind).filterMap fun t =>
    if (p.board.get t).any (·.color == pc.color) then none
    else some (⟨s, t, none⟩, { arrives := pc })

/-- Pushes, the double step, captures, en passant, and promotion on the last rank. -/
def pawnMoves (p : Position) (s : Square) : List (Move × Effect) :=
  let c := p.side
  let d := pawnDir c
  let pawn : Piece := ⟨c, .pawn⟩
  let promote (t : Square) (e : Effect) : List (Move × Effect) :=
    if t.rank == lastRank c then
      PieceKind.promotions.map fun k => (⟨s, t, some k⟩, { e with arrives := ⟨c, k⟩ })
    else [(⟨s, t, none⟩, e)]
  let empty (t : Square) := p.board.get t == none
  let pushes := match s.offset 0 d with
    | some t =>
      if !empty t then []
      else
        let double := match s.offset 0 (2 * d) with
          | some t2 =>
            if s.rank == pawnRank c && empty t2 then [(⟨s, t2, none⟩, { arrives := pawn, ep := some t })]
            else []
          | none => []
        promote t { arrives := pawn } ++ double
    | none => []
  let captures := (pawnAttacks c s).flatMap fun t =>
    match p.board.get t with
    | some v => if v.color == c then [] else promote t { arrives := pawn }
    | none =>
      match t.offset 0 (-d) with
      | some behind =>
        if p.ep == some t && p.board.get behind == some ⟨c.other, .pawn⟩ then
          [(⟨s, t, none⟩, { arrives := pawn, taken := some behind })]
        else []
      | none => []
  pushes ++ captures

def rookHome (c : Color) (kingside : Bool) : Square :=
  ⟨if kingside then .h else .a, homeRank c⟩

/-- The king two squares toward a rook: the right is kept, the king is not in
    check, the squares between are empty, and the square it crosses is not
    attacked. The square it lands on is king safety, like any move. -/
def castles (p : Position) (s : Square) : List (Move × Effect) :=
  let c := p.side
  if s != ⟨.e, homeRank c⟩ || inCheck p then []
  else
    [true, false].filterMap fun kingside => do
      let dir : Int := if kingside then 1 else -1
      let rook := rookHome c kingside
      let crossed ← s.offset dir 0
      let landing ← s.offset (2 * dir) 0
      if !p.rights.allows c kingside then none
      if p.board.get rook != some ⟨c, .rook⟩ then none
      if !(slide p.board s dir 0).contains rook then none
      if attacked p.board c.other crossed then none
      pure (⟨s, landing, none⟩, { arrives := ⟨c, .king⟩, rook := some (rook, crossed) })

def candidates (p : Position) : List (Move × Effect) :=
  p.board.flatMap fun ⟨s, pc⟩ =>
    if pc.color != p.side then []
    else match pc.kind with
      | .pawn => pawnMoves p s
      | .king => pieceMoves p s pc ++ castles p s
      | _ => pieceMoves p s pc

/-- Write a move. Clears `src` and the taken square, lands the arriving
    piece, moves the rook, vacates the rights of every square left, hands
    the turn over. -/
def enact (p : Position) (m : Move) (e : Effect) : Position :=
  let board := p.board.set m.src none
  let board := match e.taken with
    | some sq => board.set sq none
    | none => board
  let board := board.set m.to (some e.arrives)
  let board := match e.rook with
    | some (f, t) => board.set f none |>.set t (some ⟨p.side, .rook⟩)
    | none => board
  let rights := p.rights.vacate m.src |>.vacate m.to
  let rights := match e.rook with
    | some (f, _) => rights.vacate f
    | none => rights
  { board, side := p.side.other, rights, ep := e.ep }

/-- `m` among the candidates `cs` of `p`, played, if the mover's king is then safe. -/
def playIn (p : Position) (cs : List (Move × Effect)) (m : Move) : Option Position := do
  let (_, e) ← cs.find? (·.1 == m)
  let p' := enact p m e
  if kingAttacked p' p.side then none else pure p'

/-- A legal move in `p`, played. `none` otherwise. -/
def applyMove (p : Position) (m : Move) : Option Position :=
  playIn p (candidates p) m

/-- The legal moves: exactly those `applyMove` accepts (`mem_legalMoves`). -/
def legalMoves (p : Position) : List Move :=
  let cs := candidates p
  cs.map (·.1) |>.filter fun m => (playIn p cs m).isSome

/-- What a legal move is: a candidate, written by `enact`, the mover's king safe. -/
theorem applyMove_spec {p : Position} {m : Move} {p' : Position}
    (h : applyMove p m = some p') :
    ∃ e, (m, e) ∈ candidates p ∧ p' = enact p m e ∧ kingAttacked p' p.side = false := by
  unfold applyMove playIn at h
  cases hf : (candidates p).find? (·.1 == m) with
  | none => simp [hf] at h
  | some c =>
    obtain ⟨m', e⟩ := c
    have hm : m' = m := by simpa using List.find?_some hf
    subst hm
    simp only [hf] at h
    by_cases hk : kingAttacked (enact p m' e) p.side = true
    · simp [hk] at h
    · simp [hk] at h
      subst h
      exact ⟨e, List.mem_of_find?_eq_some hf, rfl, by simpa using hk⟩

theorem mem_legalMoves {p : Position} {m : Move} :
    m ∈ legalMoves p ↔ ∃ p', applyMove p m = some p' := by
  simp only [legalMoves, List.mem_filter, List.mem_map, Option.isSome_iff_exists]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨p', h⟩
    obtain ⟨e, he, -, -⟩ := applyMove_spec h
    exact ⟨⟨(m, e), he, rfl⟩, p', h⟩

/-- After a legal move the mover's king is not attacked. -/
theorem applyMove_king_safe {p : Position} {m : Move} {p' : Position}
    (h : applyMove p m = some p') : kingAttacked p' p.side = false :=
  (applyMove_spec h).choose_spec.2.2

/-- The turn is handed over. -/
theorem applyMove_side {p : Position} {m : Move} {p' : Position}
    (h : applyMove p m = some p') : p'.side = p.side.other := by
  obtain ⟨e, -, rfl, -⟩ := applyMove_spec h
  rfl

theorem Rights.le_refl (r : Rights) : Rights.le r r := by
  simp [Rights.le]

theorem Rights.le_trans {a b c : Rights} (h1 : Rights.le a b) (h2 : Rights.le b c) : Rights.le a c := by
  obtain ⟨h1k, h1q, h1bk, h1bq⟩ := h1
  obtain ⟨h2k, h2q, h2bk, h2bq⟩ := h2
  exact ⟨fun h => h2k (h1k h), fun h => h2q (h1q h), fun h => h2bk (h1bk h), fun h => h2bq (h1bq h)⟩

theorem Rights.vacate_le (r : Rights) (s : Square) : Rights.le (r.vacate s) r := by
  unfold Rights.vacate
  split <;> simp [Rights.le]

theorem enact_rights (p : Position) (m : Move) (e : Effect) :
    Rights.le (enact p m e).rights p.rights := by
  simp only [enact]
  have h1 := Rights.vacate_le p.rights m.src
  have h2 := Rights.vacate_le (p.rights.vacate m.src) m.to
  split
  · rename_i f _ _
    exact Rights.le_trans (Rights.vacate_le _ f) (Rights.le_trans h2 h1)
  · exact Rights.le_trans h2 h1

/-- A right, once lost, stays lost. -/
theorem applyMove_rights {p : Position} {m : Move} {p' : Position}
    (h : applyMove p m = some p') : Rights.le p'.rights p.rights := by
  obtain ⟨e, -, rfl, -⟩ := applyMove_spec h
  exact enact_rights p m e

def isCheckmate (p : Position) : Bool :=
  inCheck p && legalMoves p == []

def isStalemate (p : Position) : Bool :=
  !inCheck p && legalMoves p == []

/-- A pawn move or a capture on `to`. An en passant capture is a pawn move. -/
def resetsHalfmove (p : Position) (m : Move) : Bool :=
  (p.board.get m.src).any (·.kind == .pawn) || (p.board.get m.to).isSome

/- ====================================================================
   Material. A detector, not the meaning of a dead position.

   `Material.mayMate p c = false` says `c` has no series of legal moves
   that mates, judged from material alone. `true` says nothing: mate is
   not ruled out. `Material.dead` is the two-sided negative verdict.
   What is proved of these is in `domain/Mate.lean`. The exact meaning
   is `CanMate` and `Dead` there. A blocked position that still holds a
   pawn is not reported dead here, and the game goes on.
   ==================================================================== -/

namespace Material

def bishopsSameColor (b : Board) : Bool :=
  let bs := b.filter fun p => p.piece.kind == .bishop
  match bs with
  | [] => true
  | p :: ps => ps.all fun q => q.square.isLight == p.square.isLight

def mayMate (p : Position) (c : Color) : Bool :=
  let mine : List PieceKind := p.board.filterMap fun pl =>
    if pl.piece.color == c && pl.piece.kind != .king then some pl.piece.kind else none
  let theirs : List PieceKind := p.board.filterMap fun pl =>
    if pl.piece.color == c.other && pl.piece.kind != .king then some pl.piece.kind else none
  if mine.any fun k => k == .queen || k == .rook || k == .pawn then true
  else if mine.length ≥ 2 then
    !(mine.all (· == .bishop) && bishopsSameColor p.board && theirs.all (· == .bishop))
  else
    match mine with
    | [.knight] => theirs.length > 0
    | [.bishop] =>
      theirs.length > 0 && !(theirs.all (· == .bishop) && bishopsSameColor p.board)
    | _ => false

def dead (p : Position) : Bool :=
  !mayMate p .white && !mayMate p .black

end Material

/- ====================================================================
   Repetition key. En passant counts only when a capture is legal.
   ==================================================================== -/

def epCapturable (p : Position) : Bool :=
  match p.ep with
  | none => false
  | some sq =>
    legalMoves p |>.any fun m => m.to == sq && (p.board.get m.src).any (·.kind == .pawn)

structure PosKey where
  board : Board
  side : Color
  rights : Rights
  ep : Option Square
  deriving Repr, DecidableEq, Hashable

def posKey (p : Position) : PosKey where
  board := sortBoard p.board
  side := p.side
  rights := p.rights
  ep := if epCapturable p then p.ep else none

/- ====================================================================
   Agreement, clock, log, fold
   ==================================================================== -/

structure Instant where
  ms : Nat
  deriving Repr, DecidableEq, Ord

inductive TimeControl where
  | realtime (initialMs : Nat) (incrementMs : Nat)
  | correspondence (days : Nat)
  deriving Repr, DecidableEq

def TimeControl.initialMs : TimeControl → Nat
  | .realtime init _ => init
  | .correspondence days => days * 24 * 60 * 60 * 1000

def TimeControl.incrementMs : TimeControl → Nat
  | .realtime _ inc => inc
  | .correspondence _ => 0

inductive Speed where
  | ultraBullet | bullet | blitz | rapid | classical | correspondence
  deriving Repr, DecidableEq

def Speed.ofControl : TimeControl → Speed
  | .correspondence _ => .correspondence
  | .realtime init inc =>
    let secs := (init + 40 * inc) / 1000
    if secs ≤ 29 then .ultraBullet
    else if secs ≤ 179 then .bullet
    else if secs ≤ 479 then .blitz
    else if secs ≤ 1499 then .rapid
    else .classical

/-- The pairing, agreed before the first move. The prior world of this game. -/
structure Agreement where
  white : Person
  black : Person
  rated : Bool
  time : TimeControl
  start : Instant
  deriving Repr, DecidableEq

def Agreement.effectiveRated (a : Agreement) : Bool :=
  a.rated && a.white.id != a.black.id

def Agreement.person (a : Agreement) : Color → Person
  | .white => a.white
  | .black => a.black

inductive DrawReason where
  | stalemate
  | dead
  | agreement
  | threefold
  | fifty
  | fivefold
  | seventyFive
  | flagOffer
  | flagInsufficient
  | resignDead
  deriving Repr, DecidableEq

inductive Ending where
  | checkmate (winner : Color)
  | resign (winner : Color)
  | flag (winner : Color)
  | draw (reason : DrawReason)
  | abort
  deriving Repr, DecidableEq

inductive GameEvent where
  | moved (move : Move) (time : Instant)
  | resigned (seat : Color) (time : Instant)
  | drawOffered (seat : Color) (time : Instant)
  | drawAccepted (seat : Color) (time : Instant)
  | drawDeclined (seat : Color) (time : Instant)
  | claimedThreefold (seat : Color) (intended : Option Move) (time : Instant)
  | claimedFifty (seat : Color) (intended : Option Move) (time : Instant)
  | aborted (seat : Color) (time : Instant)
  deriving Repr, DecidableEq

def GameEvent.time : GameEvent → Instant
  | .moved _ t | .resigned _ t | .drawOffered _ t | .drawAccepted _ t
  | .drawDeclined _ t | .claimedThreefold _ _ t | .claimedFifty _ _ t | .aborted _ t => t

/-- The fold's memory of a prefix of the log. -/
structure GameState where
  agreement : Agreement
  position : Position
  /-- Plies since the last pawn move or capture. -/
  halfmove : Nat
  whiteMs : Nat
  blackMs : Nat
  /-- When the running clock started: the last accepted move, or the agreement. -/
  runningSince : Instant
  /-- The color whose draw offer is standing. A decline, the opponent's
      move, or an ending clears it. -/
  offer : Option Color
  /-- The side to move, when it has offered or claimed a draw this turn.
      Its move, if it makes the third occurrence, is a claimed threefold.
      A decline clears `offer` and not this; the move that ends the turn
      clears both. -/
  claim : Option Color
  ending : Option Ending
  history : List PosKey
  ply : Nat
  deriving Repr, DecidableEq

/-- The move number. White's first move is 1. -/
def fullmove (s : GameState) : Nat :=
  s.ply / 2 + 1

def elapsed (s : GameState) (t : Instant) : Nat :=
  if t.ms < s.runningSince.ms then 0 else t.ms - s.runningSince.ms

def allowance (s : GameState) : Nat :=
  match s.agreement.time with
  | .correspondence days => days * 24 * 60 * 60 * 1000
  | .realtime _ _ =>
    if s.position.side == .white then s.whiteMs else s.blackMs

def repetitions (s : GameState) : Nat :=
  let k := posKey s.position
  (s.history.filter (· == k)).length

/-- Mate is possible for the opponent, in the safe direction of FIDE 6.9:
    material that does not rule mate out is read as able to mate. -/
def flagEnding (s : GameState) : Ending :=
  let opp := s.position.side.other
  if s.offer == some opp then .draw .flagOffer
  else if !Material.mayMate s.position opp then .draw .flagInsufficient
  else .flag opp

/-- Charge the running clock up to `t`. The stored figure for the side to
    move becomes what is left; the clock restarts at `t`. -/
def spend (s : GameState) (t : Instant) : GameState :=
  let used := elapsed s t
  let left := allowance s
  let left := if used ≥ left then 0 else left - used
  if s.position.side == .white then { s with whiteMs := left, runningSince := t }
  else { s with blackMs := left, runningSince := t }

def addIncrement (s : GameState) (mover : Color) : GameState :=
  match s.agreement.time with
  | .correspondence _ => s
  | .realtime _ inc =>
    if mover == .white then { s with whiteMs := s.whiteMs + inc }
    else { s with blackMs := s.blackMs + inc }

/-- What the position after `mover`'s move forces. Precedence: mate, then
    stalemate, then a dead position, then five occurrences, then
    seventy-five moves, then the mover's claim, then the opponent's
    standing choice to claim. -/
def settle (s : GameState) (mover : Color) : GameState :=
  let p := s.position
  let n := repetitions s
  let ending : Option Ending :=
    if isCheckmate p then some (.checkmate mover)
    else if isStalemate p then some (.draw .stalemate)
    else if Material.dead p then some (.draw .dead)
    else if n ≥ 5 then some (.draw .fivefold)
    else if s.halfmove ≥ 150 then some (.draw .seventyFive)
    else if s.claim == some mover && n ≥ 3 then some (.draw .threefold)
    else if (s.agreement.person p.side).autoClaimThreefold && n ≥ 3 then
      some (.draw .threefold)
    else none
  { s with ending }

/-- The game ends at `t`. The running clock is charged up to `t` and stops;
    no offer or claim survives an ending. -/
def endAt (s : GameState) (t : Instant) (e : Ending) : GameState :=
  { spend s t with ending := some e, offer := none, claim := none }

/-- Play `m` at `t`: the clock, the position, the offer the opponent left,
    the history, the ply, and whatever the new position forces. The
    increment is not added here. `none` when `m` is not legal. -/
def playMove (s : GameState) (m : Move) (t : Instant) : Option GameState :=
  match applyMove s.position m with
  | none => none
  | some p =>
    let mover := s.position.side
    let spent := spend s t
    let offer := if s.offer == some mover.other then none else s.offer
    let s' : GameState := {
      spent with
      position := p
      halfmove := if resetsHalfmove s.position m then 0 else s.halfmove + 1
      offer
      history := s.history ++ [posKey p]
      ply := s.ply + 1
    }
    let s' := settle s' mover
    some { s' with claim := none, offer := if s'.ending.isSome then none else s'.offer }

/-- A play ends the game, or continues it with the mover's increment. -/
def finishPlay (s : GameState) (mover : Color) : GameState :=
  if s.ending.isSome then s else addIncrement s mover

def commitMove (s : GameState) (m : Move) (t : Instant) : GameState :=
  match playMove s m t with
  | none => s
  | some s' => finishPlay s' s.position.side

def expired (s : GameState) (t : Instant) : Bool :=
  s.ending.isNone && t.ms ≥ s.runningSince.ms && elapsed s t ≥ allowance s

/-- The flag: the side to move has nothing left. Its clock reads zero from
    here on, and the ending is what FIDE 6.9 and the standing offer say. -/
def freezeFlag (s : GameState) : GameState :=
  let e := flagEnding s
  let s :=
    if s.position.side == .white then { s with whiteMs := 0 }
    else { s with blackMs := 0 }
  { s with ending := some e, offer := none, claim := none }

/-- An act at `t` reaches the game only if the game is open, `t` is not
    before the running clock started, and the clock has not run out. A
    clock that has run out is the flag, whatever the act was. -/
def guardTime (s : GameState) (t : Instant) (k : GameState → GameState) : GameState :=
  match s.ending with
  | some _ => s
  | none =>
    if t.ms < s.runningSince.ms then s
    else if expired s t then freezeFlag s
    else k s

/-- The side to move offers, or claims and fails: the offer stands, and the
    move that ends this turn carries the claim. -/
def offerNow (s : GameState) (c : Color) : GameState :=
  { s with offer := some c, claim := some c }

/-- A claim naming a move: the claim is an offer (FIDE 9.1.2.3), then the
    move is played. `holds` reads the position the move produced; when it
    holds and the move did not already end the game, the draw is claimed. -/
def claimWith (s : GameState) (c : Color) (m : Move) (t : Instant)
    (holds : GameState → Bool) (reason : DrawReason) : GameState :=
  match playMove (offerNow s c) m t with
  | none => s
  | some s' =>
    if s'.ending.isSome then s'
    else if holds s' then { s' with ending := some (.draw reason), offer := none }
    else addIncrement s' c

def applyEvent (s : GameState) : GameEvent → GameState
  | .moved m t => guardTime s t fun s => commitMove s m t
  | .resigned c t => guardTime s t fun s =>
      if s.ply < 2 then s
      else if Material.dead s.position then endAt s t (.draw .resignDead)
      else endAt s t (.resign c.other)
  | .drawOffered c t => guardTime s t fun s =>
      if s.position.side != c then s else offerNow s c
  | .drawAccepted c t => guardTime s t fun s =>
      if s.offer == some c.other && s.ply ≥ 2 then endAt s t (.draw .agreement) else s
  | .drawDeclined c t => guardTime s t fun s =>
      if s.offer == some c.other then { s with offer := none } else s
  | .claimedThreefold c intended t => guardTime s t fun s =>
      if s.position.side != c then s
      else
        match intended with
        | none =>
          if repetitions s ≥ 3 then endAt s t (.draw .threefold) else offerNow s c
        | some m => claimWith s c m t (fun s' => repetitions s' ≥ 3) .threefold
  | .claimedFifty c intended t => guardTime s t fun s =>
      if s.position.side != c then s
      else
        match intended with
        | none =>
          if s.halfmove ≥ 100 then endAt s t (.draw .fifty) else offerNow s c
        | some m => claimWith s c m t (fun s' => s'.halfmove ≥ 100) .fifty
  | .aborted _ t => guardTime s t fun s =>
      if s.ply < 2 then endAt s t .abort else s

def applyEvents (s : GameState) : List GameEvent → GameState
  | [] => s
  | e :: es => applyEvents (applyEvent s e) es

def initial (a : Agreement) : GameState where
  agreement := a
  position := opening
  halfmove := 0
  whiteMs := a.time.initialMs
  blackMs := a.time.initialMs
  runningSince := a.start
  offer := none
  claim := none
  ending := none
  history := [posKey opening]
  ply := 0

def fold (a : Agreement) (events : List GameEvent) : GameState :=
  applyEvents (initial a) events

/- ====================================================================
   Queries
   ==================================================================== -/

/-- Milliseconds `c` still has at `d`. The side to move is charged up to
    `d`; the other side's clock is where its last move left it, or, in
    correspondence, a fresh period. After an ending, the stored figures:
    the ending charged the running clock up to its own instant. -/
def remaining (s : GameState) (c : Color) (d : Instant) : Nat :=
  let stored := if c == .white then s.whiteMs else s.blackMs
  if c != s.position.side then
    match s.agreement.time with
    | .correspondence _ => s.agreement.time.initialMs
    | .realtime _ _ => stored
  else if s.ending.isSome then stored
  else
    let left := allowance s
    let used := elapsed s d
    if used ≥ left then 0 else left - used

/-- The ending at `d`: the one an act forced, or the flag `d` reveals. -/
def resultAt (s : GameState) (d : Instant) : Option Ending :=
  match s.ending with
  | some e => some e
  | none => if expired s d then some (flagEnding s) else none

inductive Points where
  | zero | half | one
  deriving Repr, DecidableEq

structure Score where
  white : Points
  black : Points
  deriving Repr, DecidableEq

def Score.ofEnding : Ending → Option Score
  | .abort => none
  | .draw _ => some ⟨.half, .half⟩
  | .checkmate .white | .resign .white | .flag .white => some ⟨.one, .zero⟩
  | .checkmate .black | .resign .black | .flag .black => some ⟨.zero, .one⟩

/-- Whether this game, seen at `d`, is an input to its speed's pool. A
    flag `d` reveals counts like any other ending. -/
def countsForRating (s : GameState) (d : Instant) : Bool :=
  s.agreement.effectiveRated && s.ply ≥ 2 &&
    match resultAt s d with
    | some .abort | none => false
    | some _ => true

/-- Glicko-2 inputs for one person in one speed pool.
    Fresh deviation 500 is the reading on which the published ±1000 band is two deviations.
    The update formula is not in this file. `countsForRating` says whether a game is an input. -/
structure PoolRating where
  rating : Int
  deviation : Nat
  /-- Millionths. 60000 is 0.06. -/
  volatilityMicro : Nat
  deriving Repr, DecidableEq

def PoolRating.fresh : PoolRating := ⟨1500, 500, 60000⟩

def PoolRating.provisional (r : PoolRating) : Bool :=
  r.deviation > 110

def PoolRating.band (r : PoolRating) : Int :=
  2 * r.deviation

/- ====================================================================
   Checks. The opening, a mate, a castle, an en passant, a flag, an abort.
   ==================================================================== -/

def mv (f1 : File) (ra : Rank) (f2 : File) (rb : Rank) (promo : Option PieceKind := none) : Move :=
  ⟨⟨f1, ra⟩, ⟨f2, rb⟩, promo⟩

def sample : Agreement where
  white := ⟨"w", false⟩
  black := ⟨"b", false⟩
  rated := true
  time := .realtime (5 * 60 * 1000) 0
  start := ⟨0⟩

def replay (moves : List Move) : GameState :=
  let rec go (i : Nat) (s : GameState) : List Move → GameState
    | [] => s
    | m :: ms => go (i + 1) (applyEvent s (.moved m ⟨i * 1000⟩)) ms
  go 1 (initial sample) moves

#guard Square.isLight ⟨.h, .r1⟩ && !Square.isLight ⟨.a, .r1⟩
#guard opening.board.length == 32
#guard Square.all.length == 64
#guard (legalMoves opening).length == 20

/-- Leaf positions `d` legal moves deep. Published counts check the generator. -/
def perft (p : Position) : Nat → Nat
  | 0 => 1
  | d + 1 => (legalMoves p).foldl (fun n m => n + ((applyMove p m).map (perft · d)).getD 0) 0

#guard perft opening 3 == 8902
#guard (replay [mv .e .r2 .e .r5]).ply == 0

def scholar : List Move := [
  mv .e .r2 .e .r4, mv .e .r7 .e .r5,
  mv .d .r1 .h .r5, mv .b .r8 .c .r6,
  mv .f .r1 .c .r4, mv .g .r8 .f .r6,
  mv .h .r5 .f .r7,
]

#guard (replay scholar).ending == some (.checkmate .white)
#guard Score.ofEnding (.checkmate .white) == some ⟨.one, .zero⟩
#guard fullmove (replay scholar) == 4

def castled : List Move := [
  mv .e .r2 .e .r4, mv .e .r7 .e .r5,
  mv .g .r1 .f .r3, mv .b .r8 .c .r6,
  mv .f .r1 .c .r4, mv .f .r8 .c .r5,
  mv .e .r1 .g .r1,
]

#guard Board.get (replay castled).position.board ⟨.g, .r1⟩ == some ⟨.white, .king⟩
#guard Board.get (replay castled).position.board ⟨.f, .r1⟩ == some ⟨.white, .rook⟩
#guard Board.get (replay castled).position.board ⟨.e, .r1⟩ == none
#guard (replay castled).position.rights == { wk := false, wq := false, bk := true, bq := true }

def enPassant : List Move := [
  mv .e .r2 .e .r4, mv .a .r7 .a .r6,
  mv .e .r4 .e .r5, mv .d .r7 .d .r5,
  mv .e .r5 .d .r6,
]

#guard Board.get (replay enPassant).position.board ⟨.d, .r6⟩ == some ⟨.white, .pawn⟩
#guard Board.get (replay enPassant).position.board ⟨.d, .r5⟩ == none
#guard (replay enPassant).halfmove == 0
#guard (replay enPassant).position.board == sortBoard (replay enPassant).position.board

def kings : Position where
  board := [⟨⟨.e, .r1⟩, ⟨.white, .king⟩⟩, ⟨⟨.e, .r8⟩, ⟨.black, .king⟩⟩]
  side := .white
  rights := Rights.none
  ep := none

#guard Material.dead kings

def short : Agreement := { sample with time := .realtime 1000 0 }

#guard resultAt (initial short) ⟨999⟩ == none
#guard resultAt (initial short) ⟨1000⟩ == some (.flag .black)

#guard (applyEvent (initial sample) (.aborted .black ⟨100⟩)).ending == some .abort
#guard Score.ofEnding .abort == none

def offered : GameState :=
  applyEvent (replay [mv .e .r2 .e .r4, mv .e .r7 .e .r5]) (.drawOffered .white ⟨3000⟩)

#guard (applyEvent offered (.drawAccepted .black ⟨4000⟩)).ending == some (.draw .agreement)
#guard countsForRating (applyEvent offered (.drawAccepted .black ⟨4000⟩)) ⟨4000⟩

#guard PoolRating.fresh.rating == 1500
#guard PoolRating.fresh.band == 1000
#guard PoolRating.provisional PoolRating.fresh
#guard Speed.ofControl (.realtime (5 * 60 * 1000) 0) == .blitz
#guard !({ sample with white := ⟨"same", false⟩, black := ⟨"same", false⟩ }).effectiveRated

end LeanChess
