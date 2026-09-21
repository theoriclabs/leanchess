# Vocabulary

The game in `facts.md`, sorted. One game. Standard chess, from the opening. A query reads the agreement `W`, a prefix of the log `L`, and an instant `d` when the clock is involved.

`S` is `apply W L`. It is the fold. Castling rights, the en passant square, the halfmove count, and the remaining time live here because the fold computed them. They are not inputs beside the log.

## Prior world `W`

True before any act in the log.

| Concept | What it is |
|---|---|
| `Person` | Someone who can sit. An id. Their own choice to claim threefold for themselves. |
| `Color` | The seat. White or Black. Not a person. |
| `Agreement` | This game's pairing: which person sits White, which sits Black, whether they asked for a rated game, the time control, and the instant White's clock starts. |
| `TimeControl` | Realtime: initial milliseconds and an increment. Correspondence: days for the move. |
| The laws | Piece motion, the opening arrangement, what a legal move is, what ends the game. Functions, not a row. |
| `PoolRating.fresh` | A person new to a pool: rating 1500, deviation 500, so the band is ±1000. Volatility 0.06. |

`Agreement.effectiveRated` is `derived` from the agreement: they asked for rated, and the two ids differ.

`Speed.ofControl` is `derived` from the time control. Correspondence is its own pool. A realtime control's pool comes from initial seconds plus forty times the increment: ≤29 ultraBullet, ≤179 bullet, ≤479 blitz, ≤1499 rapid, otherwise classical.

## Log `L`

`GameEvent`. Every constructor carries `time`, the instant it was accepted. An act the fold refuses leaves `S` unchanged.

| Constructor | Act |
|---|---|
| `moved` | A move: `src`, `to`, and the promotion kind if it is a promotion. Castling is the king moving two squares. The rook's move is not its own event. |
| `resigned` | That color declares resignation. |
| `drawOffered` | That color offers a draw. Only the side to move. It stands until accepted, declined, refused by the opponent's move, or the game ends. |
| `drawAccepted` | The other color accepts. Succeeds only after both have moved. |
| `drawDeclined` | The other color declines. |
| `claimedThreefold` | The side to move claims. Optional intended move: the position that move would produce is the third occurrence (FIDE 9.2.1). With no move: the current position already is (FIDE 9.2.2). |
| `claimedFifty` | The same shape, for the halfmove count reaching 100. |
| `aborted` | Either color, while Black has not moved. |

A move that is not legal is not in the fold. The position stays.

A draw offer already standing from the mover, followed by the move that makes the third occurrence, ends the game as a threefold claim. That is the Lichess reading of an offer made before the repeating move.

## Snapshot `S`

What the fold remembers, and the questions it can answer without walking the log again.

| Field | Question |
|---|---|
| `position` | Placement, side to move, castling rights, en passant square, halfmove count, move number. |
| `history` | The position key after every ply, including the opening. Repetition is a count in this list. |
| `ply` | How many moves were accepted. Black has moved when this is at least 2. |
| `whiteMs`, `blackMs`, `runningSince` | The clock as of the last accepted act. |
| `offer` | The color whose draw offer is standing, if any. |
| `ending` | An ending an act or a move already forced. |

`history` is the repetition record. It is the fold of the log, not a second source. A key is the placement, the side to move, the rights, and the en passant square only when a legal en passant capture exists. Two keys are the same position in the sense of FIDE 9.2.3.

`S` forgets the order of draw offers that were cleared, and it forgets a refused act. Those questions read `L`.

## Clock `d`

An `Instant`, milliseconds. These queries take it.

| Query | Answers |
|---|---|
| `remaining s color d` | Milliseconds that color still has at `d`. |
| `resultAt s d` | The stored ending, or the flag if `d` is past the running clock and the game has not already ended. |

A figure a client states for the clock is not a field and not an event.

On a flag, the side to move loses, unless a draw offer from the opponent is standing (draw), unless that opponent has no series of moves that mates the flagging king (draw). A pawn, rook, or queen is treated as able to mate. Some blocked positions are dead and this will not say so; when it cannot settle the question, the side that still has time wins.

## Derived, and from what

| Query | From |
|---|---|
| `legalMoves` | The position. |
| `inCheck`, `isCheckmate`, `isStalemate` | The position. Checkmate and stalemate end the game on the move that produced them. |
| `isDead` | The position's material. Both sides unable to mate. Ends the game on the move that produced it. Resignation in a dead position is a draw. |
| `repetitions` | `history`. Five occurrences end the game. Three do not, until a claim. |
| Halfmove ≥ 150 | The position. Seventy-five moves. Draw, unless that move is checkmate. |
| `Score.ofEnding` | The ending. Win is 1 and 0, draw is ½ and ½, abort has no score. |
| `countsForRating` | Effective rated, both have moved, and the ending is not an abort and not still open. |
| `PoolRating.provisional` | The deviation is greater than 110. |

The Glicko-2 update itself is not a function here. `countsForRating` says whether this game is an input. The new rating is a function of the two `PoolRating`s, the score, and the time since each last played in that pool. The formula is not transcribed.

## Not in this universe

A client-reported clock. A diagram's rights, as a way to start: every game here starts at the opening, so those rights are the fold. An engine's centipawn figure. A judgment that someone used an engine. Variants, tournaments, studies, puzzles, spectators, chat, takeback, premove, touch-move. Consulting an opening book in correspondence: permitted by the correspondence rule, and absent from the log.
