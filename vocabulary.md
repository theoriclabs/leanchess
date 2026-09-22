# Vocabulary

The game in `facts.md`, sorted. One game. Standard chess, from the opening. A query reads the agreement `W`, a prefix of the log `L`, and an instant `d` when the clock is involved.

`S` is `apply W L`. It is the fold. Castling rights, the en passant square, the halfmove count, the remaining time, and the offer standing live here because the fold computed them. They are not inputs beside the log.

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
| `resigned` | That color declares resignation. Once both have moved. |
| `drawOffered` | That color offers a draw. Only the side to move. It stands until accepted, declined, refused by the opponent's move, or the game ends. |
| `drawAccepted` | The other color accepts. Succeeds only after both have moved. |
| `drawDeclined` | The other color declines. |
| `claimedThreefold` | The side to move claims. Optional intended move: the position that move would produce is the third occurrence (FIDE 9.2.1). With no move: the current position already is (FIDE 9.2.2). |
| `claimedFifty` | The same shape, for the halfmove count reaching 100. |
| `aborted` | Either color, while Black has not moved. |

A move that is not legal is not in the fold. The position stays. A claim naming a move that is not legal is not in the fold either: the whole act is refused.

A claim is an offer (FIDE 9.1.2.3). A claim that does not hold leaves the claimant's offer standing, and the other seat may accept it. A claim naming a move is that offer followed by that move: the fold is the same as `drawOffered` then `moved`, and when the move makes the claim true, the draw is on the move.

A draw offer from the side to move, followed by the move that makes the third occurrence, ends the game as a threefold claim. That is the Lichess reading of an offer made before the repeating move. The claim survives a decline: the decline clears the offer, not the claim it carried. A claim that holds ends the game the instant the claiming act is accepted.

A proposed act and an accepted act are different things. `Command` is what a person proposes: no seat, no instant. `admit` fixes the seat and the server's instant and asks the fold. It answers accepted, with the one `GameEvent` to store; refused, with the reason (the game has ended, the instant is before the clock, it is not that seat's turn, or the fold is unchanged); or flagged, with nothing to store. A stored log is `validLog`: every event is the accepted event of its own admission, in order.

## Snapshot `S`

What the fold remembers, and the questions it can answer without walking the log again.

| Field | Question |
|---|---|
| `position` | Placement, side to move, castling rights, en passant square. The position in the sense of FIDE 9.2.3, and nothing else. |
| `halfmove` | Plies since the last pawn move or capture. The fold's, not the position's. |
| `history` | The position key after every ply, including the opening. Repetition is a count in this list. |
| `ply` | How many moves were accepted. Black has moved when this is at least 2. The move number is `ply / 2 + 1`. |
| `whiteMs`, `blackMs`, `runningSince` | The clock as of the last accepted move, or the ending. |
| `offer` | The color whose draw offer is standing, if any. |
| `claim` | The side to move, when it has offered or claimed this turn. Its move, if it repeats, is a claimed threefold. A decline clears `offer` and not this. The move that ends the turn clears both. |
| `ending` | An ending an act or a move already forced. |

`history` is the repetition record. It is the fold of the log, not a second source. A key is the placement, the side to move, the rights, and the en passant square only when a legal en passant capture exists. Two keys are the same position in the sense of FIDE 9.2.3.

A board the fold holds is sorted by square, so two boards with the same pieces on the same squares are one list.

`S` forgets the order of draw offers that were cleared, and it forgets a refused act. Those questions read `L`.

## Clock `d`

An `Instant`, milliseconds. These queries take it.

| Query | Answers |
|---|---|
| `remaining s color d` | Milliseconds that color still has at `d`. |
| `resultAt s d` | The stored ending, or the flag if `d` is past the running clock and the game has not already ended. |
| `countsForRating s d` | Whether the game, seen at `d`, is an input to its pool. A flag `d` reveals counts. |
| `lookback W L d` | A historical look: the fold of the events at or before `d`, observed at `d`. |

A figure a client states for the clock is not a field and not an event.

The instant of an act is the server's, fixed at admission. Time passing is not an event. The flag is derived: a look reveals it, an act after it is flagged and not stored. The allowance runs out at exactly `runningSince + allowance`: a play at that instant is the flag.

An act that ends the game (resignation, an agreed draw, a claim that holds, an abort) charges the running clock up to its own instant and stops it. A look after the ending, at any instant, reads those figures. A move charges the clock the same way and then adds the increment, unless the move ended the game.

On a flag, the side to move loses, unless a draw offer from the opponent is standing (draw), unless that opponent has no series of moves that mates the flagging king (draw). Whether the opponent can mate is asked of `Material.mayMate`, which clears a side only by material: a lone king, a lone minor piece, or bishops on one colour against nothing that could help. When it cannot rule mate out, the side that still has time wins. That direction is Lichess's, and it is site policy, not a fact of chess.

## Derived, and from what

| Query | From |
|---|---|
| `legalMoves` | The position. The one notion of legality: `applyMove` accepts exactly these. |
| `inCheck`, `isCheckmate`, `isStalemate` | The position. Checkmate and stalemate end the game on the move that produced them. |
| `Material.dead` | The position's material. A detector: `true` is a verdict that neither side can mate, `false` says nothing. The meaning of a dead position is `Dead` in `domain/Mate.lean`: no series of legal moves mates. What the detector's verdict has been proved to establish is listed there; on two kings it is proved, on a lone minor piece and on same-coloured bishops it is open. Ends the game on the move that produced it. Resignation in a position the detector calls dead is a draw. Both are site policy on the detector, not on `Dead`. |
| `repetitions` | `history`. Five occurrences end the game. Three do not, until a claim. |
| Halfmove ≥ 150 | `halfmove`. Seventy-five moves. Draw, unless that move is checkmate. |
| `Score.ofEnding` | The ending. Win is 1 and 0, draw is ½ and ½, abort has no score. |
| `countsForRating` | Effective rated, both have moved, and `resultAt` at `d` is an ending that is not an abort. |
| `PoolRating.provisional` | The deviation is greater than 110. |

The Glicko-2 update itself is not a function here. `countsForRating` says whether this game is an input. The new rating is a function of the two `PoolRating`s, the score, and the time since each last played in that pool. The formula is not transcribed.

## What is kept true

`Position.structural` says what a position the fold could hold looks like: distinct squares, one king each, no pawn on an edge rank, a right only while its king and rook are home, an en passant square only behind a pawn that just moved two. `GameState.Consistent` says what the fold keeps in step: one key per ply, the side to move by the ply's parity, a claim only from the side to move, no offer after an ending, the clock not before the agreement. Every fold of every log is `Consistent`; that is proved. That every reachable position is `structural` is stated and not yet proved (`domain/Valid.lean`, `Spec`).

A stored projection of the fold is not a fact. It is a copy at a revision of the log, under a named version of these rules, and it counts only with the evidence that it is the fold (`domain/Projection.lean`). A stale or corrupt projection is rebuilt from the log.

## Not in this universe

A client-reported clock. A diagram's rights, as a way to start: every game here starts at the opening, so those rights are the fold. An engine's centipawn figure. A judgment that someone used an engine. Variants, tournaments, studies, puzzles, spectators, chat, takeback, premove, touch-move. Consulting an opening book in correspondence: permitted by the correspondence rule, and absent from the log. An exhaustive decision of whether a position is dead: `Dead` is the meaning, and this program decides it only where a finite closure or a material argument settles it.
