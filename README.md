# LeanChess

A place to play chess, where the rules are a Lean program and the server is a fold of that program over a log.

Live at **[leanchess.org](https://leanchess.org)**.

A person sits down, gets a game, and plays it to an ending: against another person, or against the machine. The board on the screen is the log played forward. The server derives the position and the clock. A client proposes a move; the server accepts it when it is legal in the position the log has reached, and otherwise nothing changes.

## The idea

One Lean definition of the game is the meaning. It does not import a widget, a table, or a request. Everything else refines it.

- **The log is the truth.** The database stores the prior world (people, seats, time control) and the acts, with their instants. The position, the castling rights, the remaining time, and the result are functions of that log. None of them is a column that can drift.
- **Derived facts are computed, never stored as facts.** A stored copy of a derived answer is a projection. It is trusted only with evidence that it is the function's answer at a named revision of the log, under a named version of the rules (`domain/Projection.lean`).
- **Time passing is not an event.** A flag is what a look at a given instant shows. It appends nothing.
- **Evidence matches the claim.** Proved, checked, assumed, and open are kept apart. An open obligation is a named `Spec` proposition with no proof. It is never an `axiom` or a `sorry`, and nothing uses it.

`facts.md` is what chess already is (FIDE, Lichess practice). `vision.md` is what we want true of the server. `vocabulary.md` sorts every fact into the prior world, the log, or a derivation.

## What the build establishes

`lake build` checks every claim below. The full inventory, with the theorem behind each row, is in [`evidence.md`](evidence.md).

| | |
|---|---|
| **Legality** | Motion is stated once: each kind of piece has rays, and slides or steps. A legal move is a candidate that leaves the mover's king safe, and is exactly what `legalMoves` lists. |
| **Admission** | An accepted event is this command, for this seat, at the server's instant. Only the side to move can play, offer, or claim. A refusal appends nothing. |
| **Consistency** | Every fold of every log is consistent: one key per ply, side by parity, halfmove ≤ ply, nothing changes after an ending. |
| **Time** | Once a flag falls, every later look sees it. An ending stops the clock at its own instant. A game that counts for rating at `d` counts at every later `d'`. |
| **Dead positions** | `Dead` means no series of legal moves reaches mate. The material detector is proved sound on two kings, and proved incomplete by a locked-pawn position it misses. |
| **Projections** | Incremental and rebuilt projections agree. A `Verified` projection cannot be built without the evidence. |
| **Boundary** | A play by the seat not to move is never appended. A look appends nothing, except the machine's own legal move when it is to move. |

What is still open is named in the same file: that a legal move preserves the structural validity of a position, and that the detector is sound beyond two kings.

The page in `web/` and `ui/` reads the look. No claim above covers it.

## Layout

```
domain/          The meaning. No I/O.
  Game.lean        Board, moves, legality, the event log and its fold, endings
  Command.lean     What a seat may propose; one `admit` that accepts, refuses, or flags
  Clock.lean       Remaining time, flags, frozen clocks, historical looks
  Valid.lean       What every fold keeps true
  Mate.lean        What a dead position means, and what the detector establishes
  Projection.lean  When a stored copy of the fold may be trusted
  Semantics.lean   The server's step, built on `admit`
example_cases/   The user flows, inhabited: one agreement, one log, one look each
api/             The boundary: HTTP, the LeanDB store, the machine player, the audit
ui/              The board, written in LeanReact and compiled to JavaScript
web/             The page shell and the browser client
deploy/          Dockerfile and production maintenance
product_intent/  User stories as a separate Lean project
```

## Building

LeanChess depends on two sibling repositories, checked out next to it:

```
code/
  leanchess/
  leandb/       LeanDB, the SQLite-backed store
  leanreact/    LeanReact, the UI compiler
```

The toolchain is pinned in `lean-toolchain` (Lean 4.33.0). With [elan](https://github.com/leanprover/elan) installed:

```sh
lake build                  # the domain and the example flows
lake build api              # the HTTP boundary and its proofs
```

Most flow proofs are `native_decide`, since the kernel does not reduce the fold. Expect about 30 s for `LeanChess`, 80 s for `ExampleCases`, and 2 min for `api` from a cold build.

## Running locally

Build the page compiler once, then the server and the page:

```sh
(cd ../leanreact && npm ci && lake build LeanReact.Compiler)

lake build leanchess-api ui
lake env lean ui/Generate.lean
NODE_PATH=../leanreact/node_modules ../leanreact/node_modules/.bin/esbuild web/main.mjs \
  --bundle --format=esm --platform=browser --target=es2022 --outfile=web/dist/app.js
cp web/index.html web/style.css web/dist/

.lake/build/bin/leanchess-api --web web/dist
```

The server listens on `127.0.0.1:8765` and stores games in `data/leanchess.sqlite`. Flags: `--host`, `--port` (or `PORT`), `--db`, `--web`.

To run the persistence regressions against a scratch database:

```sh
lake build leanchess-audit && .lake/build/bin/leanchess-audit
```

## API

| | |
|---|---|
| `POST /users` | Register. Returns a bearer token. |
| `POST /games` | Open a game with a time control, against a person or the machine. |
| `GET /games/:id` | Look at a game now. `?at=<ms>` looks at an earlier instant by folding the prefix. |
| `POST /games/:id/acts` | Propose an act: a move, a resignation, a draw offer or acceptance, a claim, an abort. |
| `GET /healthz` | Liveness. |

The server stamps every act with its own instant. A time sent by the client is ignored.

## Deploying

Production runs on Railway from `deploy/Dockerfile`. The build context is the parent of `leanchess`, `leandb`, and `leanreact`, with the Dockerfile and `.dockerignore` at its root. Stage that context with symlinks rather than uploading the whole parent directory:

```sh
ctx=$(mktemp -d)
cp deploy/Dockerfile deploy/.dockerignore "$ctx/"
ln -s "$PWD/../leandb" "$PWD/../leanreact" "$PWD" "$ctx/"
railway up "$ctx" --path-as-root --service leanchess --environment production
```

The database lives on a Railway volume at `/data`. When a release changes what counts as an admitted log, stored games from the old rules are refused on read. `deploy/flush-production-db.sh` deletes the database after a typed confirmation and restarts the service. It must be run by a person.

## Reading further

| | |
|---|---|
| [`vision.md`](vision.md) | What the server should be: it just works, it is secure, it is fast, it is open |
| [`facts.md`](facts.md) | The rules of chess this model is cut from, with sources |
| [`vocabulary.md`](vocabulary.md) | Every concept sorted into prior world, log, or derivation |
| [`userflows.md`](userflows.md) | The flows in prose; `example_cases/flows.lean` inhabits them |
| [`production_process.md`](production_process.md) | The staged method: cut, facts, vocabulary, model, flows |
| [`evidence.md`](evidence.md) | What is proved, checked, assumed, and open |
| [`theoric_vision.md`](theoric_vision.md) | The larger project this is the proving ground for |

## License

MIT. Copyright (c) 2026 Theoriclabs, Inc. See [`LICENSE`](LICENSE).
