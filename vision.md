# Vision

LeanChess is an open-source place to play chess. A person sits down, gets a game, and plays it to an ending. The destination is a public server used the way Lichess is used. It is secure, it is fast, and it just works.

`facts.md` is what chess already is. This file is what we want true of the server. Requirements, later, are cut from here and checked against the model. They are not this file.

## Just works

The first game is the one in `facts.md`. Standard chess, two people, the opening position, a clock, an ending.

A move that is legal is the only move that changes the board. Checkmate, stalemate, a dead position, fivefold repetition, and seventy-five moves end the game on their own. Resignation, an agreed draw, a threefold claim, a fifty-move claim, a flag, and an abort end it only in the ways those facts allow. A rated game updates the rating of its speed pool. A casual game and an abort do not.

The player and the server are looking at one log. The board on the screen is that log played forward. When the game ends, both sides can see why, in the terms of those facts: mate, flag, claim, agreement, abort.

## Secure

The server is the one that derives the position and the clock. A client proposes a move. The server accepts it when it is legal in the position the log has reached, and otherwise the position stays. A client does not declare the placement, the castling rights, the side to move, or the remaining time.

Only the person sitting a color can move, resign, offer a draw, claim, or abort for that color. The other seat cannot. A game against oneself is not rated.

A value that arrives from a browser, a socket, or a stored row is reconstructed before it counts. A row that does not decode is refused.

A judgment that someone used an engine is a separate act, made by someone, about a finished log. The log itself does not contain it, and the result of the game does not wait on it.

## Fast

Bullet is part of the destination, so accepting a move and telling the other seat has to finish inside the time a bullet clock cares about. The other seat hears the move when it is accepted. They do not hear it by reloading the page.

The position is a fold of the log. Playing that fold for one move is ordinary work, done on the acceptance, not a search of the whole history in front of the player.

## Open

The rules of a game, the program that accepts a move, and the program that draws the board are published. A person can read, run, and change them. A finished game can be exported as its log.

No license is chosen in this file.

## How it is built

One Lean definition of the game is the meaning. It does not import a widget, a table, or a request.

LeanReact draws the board from that definition. The same legality that accepts a move on the server is the legality that refuses a piece dropped on the wrong square.

LeanDB stores the prior world and the log: the people, the seats, the time control, the moves and their instants. A derived fact — the position, the rights, the remaining time, the rating — is computed when asked. It is not a column that can drift from the log.

LeanHttp carries HTTP and WebSocket for this program as a client, in Lean's own request and message types. Live play is a socket: accepted moves go out on it, and proposed moves come in on it.

LeanApp, in the LeanReact repository, assembles this. Each act a person can perform is a contract with a policy. The policy names who may perform it. The domain stays free of the assembly.

## Where it goes

The first finished thing is that one game, played by two people to an ending, with a clock and a rating when the game is rated.

After that game holds, the same server grows into the rest of a public chess site: watching a game, correspondence as a full way to play, variants, tournaments, puzzles, and studies. Each of those is its own cut, with its own facts. None of them changes the result of the game already described.
