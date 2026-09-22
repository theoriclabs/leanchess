# Evidence

What the build establishes, and how. Four kinds are kept apart:

- **Proved.** A theorem the kernel checked. `native_decide` proofs rest on the compiled evaluation (`Lean.ofReduceBool`), and are marked.
- **Checked.** A `#guard`: one closed evaluation, at build time. An example, not a law.
- **Assumed.** A property of the host this program relies on and does not check. Listed where it is relied on.
- **Open.** A named proposition with no proof (`Spec` namespaces). Not an axiom; nothing uses it.

No file under `domain/`, `api/`, or `example_cases/` contains `sorry` or a custom axiom. `lake build` checks the domain and the flows; `lake build api leanchess-audit` checks the boundary; the audit binary runs the persistence regressions.

## The game (`domain/Game.lean`)

| Claim | Kind | Where |
|---|---|---|
| A legal move is one `legalMoves` lists, and nothing else | Proved | `applyMove_pseudo`, `mem_legalMoves` |
| After a legal move the mover's king is not attacked | Proved | `applyMove_king_safe` |
| A legal move hands the turn over | Proved | `applyMove_side` |
| A right, once lost, stays lost | Proved | `applyMove_rights` |
| Opening, scholar's mate, castling, en passant, a flag, an abort, an agreed draw | Checked | `#guard` at the end of the file |

## Admission (`domain/Command.lean`, `domain/Semantics.lean`)

| Claim | Kind | Where |
|---|---|---|
| An accepted event is this command, for this seat, at the server's instant, and the fold after it is `applyEvent` | Proved | `accepted_event`, `accepted_time`, `accepted_command`, `accepted_seat` |
| A play, an offer, or a claim is accepted only for the side to move | Proved | `accepted_turn` |
| An accepted play is a legal move; the fold after it has the move's position, one more ply, one more key | Proved | `accepted_play` |
| A flag appends nothing; the flag is what a look at that instant shows | Proved | `flagged_frame`, `flagged_look`, `step_flagged` |
| A refusal appends nothing | Proved | `not_accepted_append`, `step_not_accepted` |
| An accepted step's log folds to the promised state | Proved | `step_accepted` |
| A log grown by accepted steps is an admitted log | Proved | `step_admitted`, `admittedLog_snoc` |
| A second delivery of an accepted act is not accepted, given idempotence of the act | Proved (with premise) | `retry_not_accepted` |
| Idempotence, for each of the eight commands | Checked | `#guard twice …` |
| Two racing writes: one of the two sequential results | Proved | `cas_linear`, `cas_fold` |
| A play at the instant the clock runs out is a flag, not a stored move | Checked | `#guard` in `Semantics.lean` |

Assumed: the server samples one monotonic clock inside the handler's lock; the process mutex keeps a second writer from appending between read and update (`api/Admit.lean` header).

## Time (`domain/Clock.lean`)

| Claim | Kind | Where |
|---|---|---|
| Once a flag has fallen, every later look sees it | Proved | `resultAt_mono`, `expired_mono` |
| A game that counts at `d` counts at every later `d'` | Proved | `counts_mono`, `counts_iff` |
| An ending charges the running clock to its instant and stops it; a later look reads the same figures | Proved | `remaining_endAt`, `remaining_frozen` |
| The side to move has nothing left once the flag has fallen | Proved | `remaining_at_flag` |
| A historical look at or after the last act is the current fold; nothing after `d` is in the prefix | Proved | `lookback_current`, `prefixAt_time`, `prefixAt_isPrefix` |
| The boundary instant, the increment, correspondence, the two reproductions from #35, repeated terminal observations | Checked | `#guard` in `Clock.lean`; `flagCounts`, `resignFreezesClock`, `endingsFreezeClock` in `example_cases/flows.lean` |

Assumed: `IO.monoMsNow` is not a durable epoch across restart (#25).

## Validity (`domain/Valid.lean`)

| Claim | Kind | Where |
|---|---|---|
| The opening is structurally valid, with the opponent's king safe | Proved | `opening_structural`, `opening_opponentSafe` |
| Every fold of every log is `Consistent`: one key per ply, the first key the opening's, the last the position's, the side by the ply's parity, a claim only from the side to move, no offer or claim after an ending, halfmove ≤ ply, the clock not before the agreement | Proved | `applyEvent_consistent`, `reachable_consistent` |
| After an ending no event changes the fold | Proved | `ended_stable`, `ended_stable_log` |
| Malformed positions are refused by the structural check; a valid-but-unreached one passes it | Checked | `#guard` in `Valid.lean` |
| A legal move from a structural, opponent-safe position produces a structural position (distinct squares, one king each, no pawn on an edge rank, rights consistent, en passant consistent) | Open | `Spec.structuralPreserved` |
| The fold keeps the opponent's king safe | Open | `Spec.opponentSafePreserved` |
| Every reachable position is structural | Open | `Spec.reachableStructural` |
| `applyMove` agrees with the rules stated independently of it | Open | `Spec.legalityMatchesRules` (the independent statement is not written) |

## Dead positions (`domain/Mate.lean`)

| Claim | Kind | Where |
|---|---|---|
| `Dead` is: no series of legal moves reaches checkmate | Definition | `Reaches`, `CanMate`, `Dead`, `dead_iff` |
| A position in a closed, mate-free set is dead | Proved | `dead_of_invariant`, `dead_of_closure`, `deadByExploration_sound` |
| A line that mates establishes `CanMate` and refutes `Dead` | Proved | `matesWith_sound`, `not_dead_of_matesWith` |
| Two kings and nothing else, with the opponent's king safe: dead, and the detector says so | Proved (`native_decide` over every such position) | `kings_dead`, `material_dead_kings_sound`, `kvk_closed`, `kvk_safe` |
| Completeness of the detector is refuted: `blocked` is dead and reported not dead | Proved (`native_decide` closure of 768 positions) | `blocked_dead`, `material_incomplete` |
| The opening is not dead; king and rook can mate | Proved (`native_decide`) | `opening_not_dead`, `krk_can_mate` |
| The detector on a lone knight, a lone bishop, same- and opposite-coloured bishops, knight against knight, a rook | Checked | `#guard` in `Mate.lean` |
| The detector's dead verdict is sound on structural positions beyond two kings | Open | `Spec.materialDeadSound` |
| A side the detector clears cannot mate (what `flagInsufficient` relies on) | Open | `Spec.mayMateSound` |

Site policy, named in `vocabulary.md`: the fold ends the game on the detector's verdict, turns a resignation into a draw on it, and decides a flag for the side with time when mate is not ruled out.

## Projections (`domain/Projection.lean`)

| Claim | Kind | Where |
|---|---|---|
| The initial and rebuilt projections represent their logs | Proved | `init_represents`, `rebuild_represents` |
| The incremental step of a projection of `log` represents `log ++ [ev]` | Proved | `step_represents` |
| Two projections of one log agree | Proved | `represents_unique` |
| A stale revision or other rules is rebuilt; a matching one is trusted only on the adapter's word | Proved (with the adapter's premise explicit) | `refresh_represents`, `refresh_stale`, `refresh_other_rules` |
| A `Verified` projection cannot be built without the evidence; admission against it is admission against the fold | Proved | `Verified`, `Verified.admit_outcome`, `observe_verified` |
| Incremental equals replay; one revision, two instants, two clocks | Checked | `#guard` in `Projection.lean` |

Assumed (adapter obligation, not discharged): a stored projection is written in the same transaction as the event it folds, or rebuilt on read; a matching revision with a corrupt state is not detected without a rebuild.

## The boundary (`api/`)

| Claim | Kind | Where |
|---|---|---|
| An appended play was authorized for the side to move, at the server instant, and is legal | Proved | `accepted_play_seat`, `played_is_accepted` |
| A play by the seat not to move is never appended | Proved | `wrong_seat_never_appends`, `stale_read_cannot_authorize` |
| A flag appends nothing | Proved | `flagged_appends_nothing` |
| Register and open-game append nothing; a look appends nothing unless the machine is to move, and then only its own legal play | Proved | `inactive_route_appends_nothing`, `look_appends_nothing`, `look_appends_machine_play` |
| A stored row that is not an admitted, ordered log is refused, not folded | Code | `Service.replay` checks `validLog` |
| Server-stamped instants, forged `at` ignored, seat authority, the flag boundary, increments, historical looks fold the prefix, an ending stops the clock, a flag counts once a look reaches it | Checked at runtime | `leanchess-audit` |

The web page (`web/`, `ui/`) reads the look and is not covered by any claim above.
