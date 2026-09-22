# Facts

One game of standard chess between two people, from the opening position to an ending, with a clock. The laws are the FIDE Laws of Chess. A public server's published rule is marked as Lichess's when the result depends on it.

These sentences are indicative. What we want of the server — open source, secure, fast, and that it just works — is in `vision.md`. LeanDB, LeanHttp, and LeanReact are not facts of chess.

Each sentence is `prior` (true before the game starts), `derived` (computed from named inputs), or `observed` (said by a named observer, and not computed).

## People and seats

A person is someone who can sit down to a game. `prior`

A game has two seats, White and Black. A seat is a color for that game. The same person sits White in one game and Black in another. `prior`

White moves first. After that the players alternate. The player to move is the one whose opponent's move has been made. `prior` (FIDE 1.2, 1.3)

A rated game is between two distinct people. One person sitting both seats is not rated. `prior` (Lichess)

## The board

The board has 64 squares: files a–h and ranks 1–8, light and dark alternating. Each player's near right-hand corner is light. White's is h1. `prior` (FIDE 2.1)

A square is one file and one rank. Files are the columns, ranks the rows. A diagonal is a straight line of one color from one edge to an adjacent edge. `prior` (FIDE 2.4)

## The pieces and the opening

There are six kinds: king, queen, rook, bishop, knight, pawn. Every piece has a color. `prior`

Each side begins with one king, one queen, two rooks, two bishops, two knights, and eight pawns. `prior` (FIDE 2.2)

The opening arrangement is a rule, not a move. White's pawns stand on rank 2 and Black's on rank 7. On ranks 1 and 8, from a to h: rook, knight, bishop, queen, king, bishop, knight, rook. The queen stands on her own color. `prior` (FIDE 2.3)

## How a piece may move

A piece may not land on its own color. Landing on an opponent's piece captures it and removes it, as part of that same move. `prior` (FIDE 3.1, 3.1.1)

A piece attacks a square when a capture there would be legal by the move of that piece. A pin does not stop the attack: a piece that cannot move somewhere, because the move would expose its own king, still attacks that square. `prior` (FIDE 3.1.2, 3.1.3)

The bishop moves any distance on a diagonal and does not pass through a piece. The rook does the same on a rank or a file. The queen does either. The knight moves to a nearest square that shares neither rank, file, nor diagonal; squares in between are irrelevant. The king moves one square to an adjoining square, or castles. `prior` (FIDE 3.2–3.6, 3.8.1)

A pawn moves one square straight forward onto an empty square. From its original square it may instead move two squares forward when both are empty. It captures one square diagonally forward, onto an opponent's piece. It does not capture straight ahead and it does not move backward. `prior` (FIDE 3.7.1–3.7.3)

En passant. A pawn that has just moved two squares forward from its original square may be captured by an opposing pawn standing on an adjacent file of the same rank, as though it had moved only one square. That capture is legal only on the immediate next move. `prior` (FIDE 3.7.3.1, 3.7.3.2)

Promotion. A pawn played to the last rank is replaced, as part of that same move, by a queen, rook, bishop, or knight of its own color. The replacement may be a piece of a kind still on the board. The new piece takes effect at once. `prior` (FIDE 3.7.3.3–3.7.3.5)

Castling is one move. The king travels two squares toward one of its own rooks on the first rank, and that rook travels to the square the king crossed. `prior` (FIDE 3.8.2)

The king loses both castling rights by moving. A rook loses the right on its own side by moving. A right, once lost, stays lost. `prior` (FIDE 3.8.2.1). For a game that began at the opening, which rights remain is `derived` from whether that king and that rook have moved in the log.

On a given move, castling can be impossible without the right being lost: the king is in check, the square it crosses or the square it lands on is attacked, or a piece stands between the king and that rook. `derived` from the position and the rights.

A move that leaves the mover's own king in check is not legal. The king is not captured. `prior` (FIDE 1.4.1, 3.9.2)

A move is legal when it satisfies those rules in the position it is played from. `derived` from the position and FIDE 3.1–3.9.

A position no series of legal moves can reach is illegal. `derived` from the laws (FIDE 3.10.3). A game that starts at the opening and admits only legal moves does not produce one.

## What a position is

The pieces on the squares do not determine the position.

A position is the placement, which side is to move, the castling rights, and whether an en passant capture is available. Placements that differ in any of those are different positions. `prior` (FIDE 9.2.3)

For a game that started at the opening, all of the following are `derived` from the log of legal moves, and from nothing stored beside it:

- the placement, by playing the moves
- the side to move, from the length of the log, White having moved first
- the castling rights, from whether the king and each rook have moved
- the en passant right, from whether the last move was a two-square pawn advance that an opposing pawn can capture
- the halfmove count: how many plies since the last pawn move or capture
- the move number

A diagram that states castling rights, an en passant square, or a halfmove count is reporting them. Those statements are `observed`. The observer is whoever published the diagram. They become `derived` only when the log from the opening is in hand.

Check: the king of the side to move is attacked. `derived` from the placement and the attack rules.

The legal moves of the side to move. `derived` from the position.

## How the game ends

An ending is a win for White, a win for Black, a draw, or an abort. An abort has no score. `prior`

These endings are immediate, and they are `derived` from the position after a legal move:

- Checkmate. The side to move is in check and has no legal move. The other side wins. (FIDE 1.4, 5.1.1)
- Stalemate. The side to move is not in check and has no legal move. Draw. (FIDE 5.2.1)
- Dead position. No series of legal moves lets either player checkmate the other king. Draw. (FIDE 1.5, 5.2.2) The piece count does not decide this. A bishop or a knight can mate a king that still has a piece able to interpose. King and queen against a lone king is not dead.

These endings are immediate, and they are `derived` from the log:

- The same position has occurred five times. Draw. (FIDE 9.6.1)
- Each side has made 75 moves with no pawn move and no capture. Draw, unless that last move is checkmate, which wins. (FIDE 9.6.2)

These are acts. The act itself is not derived. Whether the act may succeed is `derived` from the log and the position.

- Resignation. The player declares it. That player loses, unless the position is already dead, in which case the result is a draw. (FIDE 5.1.2) The declaration is the act. The exception is `derived` from the position.
- Agreement to a draw. Both players agree, and both have already made at least one move. Draw. (FIDE 5.2.3) The two agreements are acts. That both have moved is `derived` from the log.
- A draw offer carries no condition and cannot be withdrawn. It stands until it is accepted, it is rejected, or the game ends some other way. (FIDE 9.1.2.1) The offer and the reply are acts.
- Threefold. The player to move claims a draw because this position is about to appear for the third time on a move they indicate, or has just appeared and it is their move. (FIDE 9.2) The claim is an act. A claim that indicates a move that is not legal is not a claim: here a move that is not legal is not a move, and the act that names it is refused as a whole. `prior` (this server) That the positions match is `derived` from the log: same side to move, the same kinds and colors on the same squares, and the same moves available. En passant available in one and not the other makes them different. A castling right that has since been lost makes them different. (FIDE 9.2.3) The repeated thing is the position, not a run of moves, and the occurrences need not be consecutive.
- Fifty moves. The player to move claims a draw because fifty moves by each side, with no pawn move and no capture, have been made or will have been made by the move they indicate. (FIDE 9.3) The claim is an act. The count is `derived` from the log.
- A threefold claim or a fifty-move claim is itself a draw offer. `prior` (FIDE 9.1.2.3)
- On Lichess, a draw offer made before the move that would complete the third occurrence claims the threefold even when the opponent rejects the offer. `prior` (Lichess)
- A player may choose that their own threefold claims be made for them. The choice binds that player only. `prior` (Lichess)
- Abort. A game that has started, and that a competition has not marked mandatory, may be aborted while Black has not yet moved: no moves yet, or only White's first. Either player may abort it. There is no winner and no rating change. Once Black has moved, that act is resignation instead. `prior` (Lichess). Whether Black has moved is `derived` from the log.

A game has one ending. A move after the ending is not a move of that game. `prior`

A win scores 1 and 0. A draw scores ½ and ½. The two scores add to 1. An abort scores nothing. `derived` from the ending (FIDE 10.1, 10.2).

## The clock

A realtime time control is an initial duration and an increment, agreed before the first move. The increment is added to the mover after each of their moves, and it may be zero. `prior`

Correspondence is a separate clock: days for the move, not an increment. The board rules are unchanged. On Lichess an opening book is allowed in correspondence and an engine is not. `prior` (Lichess)

The running clock is the clock of the side to move. A legal move stops it, adds that side's increment, and starts the opponent's clock. A move that ends the game does not start the opponent's clock. `prior` (FIDE 6.2)

The estimated duration in seconds is the initial time plus forty times the increment. The speed is `derived` from that duration: up to 29 seconds ultraBullet, up to 179 bullet, up to 479 blitz, up to 1499 rapid, and 1500 or more classical. (Lichess) The speed is not chosen separately from the time control.

Remaining time is `derived` from the time control, the instants at which legal moves were accepted, and the instant the question is asked, for as long as that side's clock is the one running. A figure announced by a player's own client is `observed`. The observer is that client. It is not the derivation.

A flag is a side's remaining time reaching zero on their turn, with the game not already over. `derived` from the clock.

On a flag that side loses, unless the opponent has no series of legal moves that checkmates the flagging king, in which case the game is drawn. `derived` from the position (FIDE 6.9). Where that question cannot be settled, Lichess decides for the side that did not run out of time. `prior` (Lichess) A flag is not a checkmate.

Whether a series of legal moves checkmates is a question about the position. A rule of thumb from the material on the board answers it in one direction only: two bare kings, a lone knight or bishop against a bare king, and bishops all on one colour cannot mate. Material that does not fit those shapes does not show that mate is possible: sixteen pawns locked face to face with the kings shut behind them is dead, and the material does not say so. A verdict from material is a verdict, and its absence is not one. `derived` from the placement, with that limit.

While a draw offer from the opponent is still standing, Lichess records a flag as a draw. `prior` (Lichess)

## Rating

A rating is a person's number in one pool. Standard chess keeps a separate pool for each speed. A result in one pool does not change another pool. `prior` (Lichess)

The method is Glicko-2. A person new to a pool starts at 1500, with a confidence interval of ±1000. `prior` (Lichess)

When a rated game counts, the new rating, deviation, and volatility of each player are `derived` from the two ratings, the two deviations, the two volatilities, the result, and how long it has been since each of them last played in that pool. A casual game is not an input. An abort is not an input. A game counts once both players have moved. `derived`, by that rule. (Lichess)

The rating is provisional while its Glicko-2 deviation is greater than 110. `derived` from the deviation. (Lichess)

Inside a pool, the number is a relation among the people in that pool. It is not a reading of one game, and it is not a FIDE rating. `prior` (Lichess)

## Kept apart

- A person, and the color they sit for one game.
- A game, the position it has reached, and the moves that reached it.
- The placement of the pieces, and the position. The position adds the side to move, the castling rights, and en passant.
- Castling rights `derived` from a log that started at the opening, and castling rights `observed` on a diagram.
- Castling, one move, and the two piece displacements inside it.
- A promoting move, and the piece it becomes. The piece is part of the move.
- Check, checkmate, stalemate, and a dead position.
- How many pieces remain, and whether the position is dead.
- A threefold claim, which is an act, and fivefold repetition, which ends the game.
- A fifty-move claim, which is an act, and seventy-five moves, which ends the game. Checkmate on that last move wins.
- Resignation, an agreed draw, a flag, and an abort.
- A draw offer, and a draw.
- An ending read off the board, and an ending read off the clock.
- Remaining time `derived` from the move instants, and remaining time `observed` from a client.
- A time control, and the speed `derived` from it.
- A person, and that person's rating in one pool.
- A rated game and a casual game. The board is the same. The rating derivation runs on one of them.
- A centipawn figure for a position. It does not enter the result.
- Whether a player used an engine. The log does not contain it. A judgment that says so is `observed`, and the observer is whoever judged.

## Not in these facts

Variants. Tournaments and the competitions that mark a game mandatory. Studies, puzzles, and an analysis board. Spectators, chat, and messages. Teams, forums, moderation, and titles. Takeback and premove.

The rules that assume a hand on a wooden piece: touch-move, adjusting a piece, and an arbiter's penalty for an illegal move that was completed on a clock. Here a move that is not legal is not a move, and the position stays as it was.
