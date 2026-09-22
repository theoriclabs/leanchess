# LeanChess: stories before implementation

This is a proposed, implementation-independent account of the experience we want a person to have. It starts with people and their intentions, not with the existing program's modules, endpoints, tables, or controls. It is a separate specification, not a description of what the current product already supports.

The broad product direction comes from [the product vision](../vision.md): sit down, play a game to an ending, and understand what happened. The independent product model is [Stories.lean](Stories.lean). The stories are also authored through a reusable DSL in [ChessStories.lean](ChessStories.lean); the [DSL guide](README.md) explains the language, its certification rules, and a second product example. Neither the vocabulary nor the acceptance conditions below are derived from implementation types.

## Scope and decisions

This first cut begins after two seats and a game agreement exist. Finding an opponent, creating an account, rating changes, moderation, and detailed chess adjudication are separate stories. A person is an abstract, established identity here; how that identity is established is deliberately unspecified.

Private personal notes are a proposed feature that makes the privacy intention concrete. They are not shared annotations, and the other player has no right to inspect them. Whether sharing should ever be possible is a future product decision, not a storage setting.

The game rules determine which attempts are permitted and what situation follows. We do not copy the implementation's chess rules into this document. Moves, resignations, draw offers, claims, and similar acts can inhabit that vocabulary when the independent rule specification defines them.

“Unchanged” below means that a refused attempt makes no change to the game's accepted facts. It does not mean the passage of time stops. Clock rules and claims about wall-clock responsiveness require their own model and are not established in this first cut.

## S1 — Understand the game I have entered

As a player, I want to see the agreed game and its current situation so that I know what I am joining and what I may do next.

Flow:

1. I enter a game whose seats have already been agreed.
2. I ask to see its situation.
3. I receive the game's confirmed situation, including an ending if it has one.
4. Looking does not itself change the game.

Acceptance conditions: two people looking at the same confirmed revision see the same game facts. Their personal notes are not part of that shared view. This does not require their screens to look identical or their observations to occur simultaneously.

## S2 — Make a permitted attempt and know it counted

As a player, I want an attempt made for my seat to count when the game permits it, so that I can actually play rather than merely receive safe refusals.

Flow:

1. The game is ongoing and I occupy the seat for which I am acting.
2. I make an attempt permitted in this situation.
3. It is accepted.
4. The confirmed situation becomes exactly the one prescribed by the game rules, at the next revision.
5. Another player who subsequently sees that revision sees the same resulting situation.

Acceptance conditions: acceptance is not just a success message. The game's accepted facts must agree with it. A permitted attempt has an accepting continuation in the story model; “always refuse” does not satisfy this story. Eventual completion in a running service is an additional progress requirement, not a consequence of that existence statement.

## S3 — Recover from a refused attempt without damaging the game

As a player, I want a refused attempt to leave the accepted game intact and to be recognizably refused, so that a mistake does not corrupt or silently advance the game.

Flow:

1. I try to act for a seat I do not occupy, or the game does not permit my attempt.
2. The attempt is refused.
3. Looking again shows no change caused by that attempt.
4. I can choose what to try next from the confirmed situation.

Acceptance conditions: a person cannot act for another person's seat. Refusal cannot secretly advance the game. These are obligations on the complete admitted behavior, not requirements that a particular button be disabled.

## S4 — Reach an ending that remains an ending

As a player, I want both sides to be able to discover the game's ending and for later attempts not to rewrite it, so that the result is dependable.

Flow:

1. A permitted attempt leads to a situation the rules identify as finished.
2. Either player looks and can discover that conclusion.
3. A later game-changing attempt is refused.
4. The accepted situation and conclusion remain the same.

Acceptance conditions: the rules, not a player's unsupported assertion, supply the conclusion. This first model treats a conclusion as a win, draw, or abort; detailed explanations and time-driven endings remain obligations of the independent chess specification.

## S5 — Return without mistaking uncertainty for a confirmed result

As a returning player, I want to distinguish what is confirmed from what is unknown, so that an interrupted experience does not trick me into acting on an assumed result.

Flow:

1. I leave the experience or lose contact with it.
2. On returning, I am catching up, not immediately ready to make a new attempt.
3. I receive a confirmed game snapshot.
4. I can continue from that snapshot.

If I was waiting for the result of an attempt, losing contact makes the result unknown. It does not turn the attempt into a refusal. I need an actual decision to resolve that uncertainty.

Acceptance conditions: an old local picture alone cannot justify the transition back to ready. Confirmation refers to the snapshot at the confirmation boundary, not a promise that no other person can change the game afterwards. Automatically repeating an uncertain attempt safely requires a separate action-identity and deduplication story, which is not specified here.

Progress intention: if I remain connected and confirmation remains available, catching up should eventually finish. The Lean companion states this as a property to establish for a future realization; it does not prove that a network or scheduler will make progress.

## S6 — Keep my personal notes personal

As a player, I want to write and revisit personal notes without revealing them to another player, so that private analysis remains private.

Flow:

1. I add a note to my own collection.
2. I revisit my collection and see the note appended to its existing contents.
3. The accepted game has not changed because I wrote a note.
4. Another person trying to read or change my collection is refused.

Acceptance conditions: owner reads return the actual collection, not an empty answer presented as success. An unauthorized attempt changes nothing. More strongly, changing only another person's private notes must not change what I can observe through the specified interactions. This includes accepted/refused answers and subsequent game observations, not merely the direct note-reading answer.

That last requirement is about information flow. The formal model gives it a precise scope: the same person makes the same finite sequence of requests, starting with the same public game and their own notes. The observations must match even when everybody else's notes differ. Timing, logs, notifications, other people's adaptive actions, and any future interaction must be addressed when enlarging the observation model.

## S7 — Have the same intention mean the same thing across input methods

As a player, I want keyboard, touch, and assistive interaction to express the same game intentions, so that changing devices or input methods does not change the rules or silently remove an action.

Flow: I choose an intention through a supported input method; the experience carries out the corresponding story, with the same admission conditions and consequences as any other method expressing that intention.

Acceptance conditions: the stories above contain no browser, phone, gesture, layout, or framework concepts. A future realization must map every supported input method to these intentions and preserve the stories. Merely ignoring an input method is not a valid realization of a story that promises it.

The Lean companion states both soundness and coverage requirements for an abstract vocabulary of expressed inputs. It does not invent keyboard events or native callbacks. Actual accessibility, gesture normalization, and rendering need their own refinement evidence.

## Reading the formal companion

The formal document uses an abstract `GameFacts` vocabulary, an agreed seat assignment, intentions, replies, and a declarative `Step` relation. A relation says which before/intention/reply/after combinations are acceptable. It is not an algorithm, a request dispatcher, or a storage design. Finite `Journey` values connect these acceptable interactions into flows.

`Step` describes resolved interactions. `ReturnStage` and `Knowledge` separately describe what the person currently knows; an interrupted attempt need not have a resolved reply yet. `MayExpress` gates new game attempts on readiness. A future realization must preserve both the resolved stories and these knowledge transitions, rather than assuming every request immediately produces an observable reply.

| Story | Main Lean declarations | Status |
|---|---|---|
| S1: understand the game | `look_exact`, `both_can_see_same_revision` | Proved in the specification |
| S2: an attempt counts | `acceptance_has_exact_consequence`, `permitted_attempt_has_continuation`, `accepted_then_seen` | Proved, conditional on independent rule facts |
| S3: safe refusal | `refusal_changes_nothing`, `cannot_act_for_someone_elses_seat` | Proved in the specification |
| S4: stable ending | `ending_is_stable_under_attempts` | Proved in the specification |
| S5: return and uncertainty | `return_flow`, `confirmation_is_exact`, `losing_contact_is_uncertainty`, `MayExpress` | Safety checked; `ReturnProgress` remains an obligation |
| S6: private notes | `note_then_read`, `other_person_cannot_read_notes`, `other_person_cannot_write_notes`, `journey_noninterference` | Proved for the specified interactions and observations |
| S7: input equivalence | `PreservesStories`, `CoversIntentions` | Obligations stated; no platform realization supplied |

Check it from the repository root without building or importing the application:

```sh
lean product_intent/Stories.lean
```

The file imports only Lean's standard library. It contains no `sorry` declarations or custom axioms. The displayed key proofs use at most Lean's standard propositional extensionality axiom.

The proofs establish consequences of this proposed specification. They do not establish that the existing application realizes it. Some requirements are deliberately left as named propositions for a future realization: progress and preservation across input methods. Connecting the application to these stories is a separate task.

The specification should be allowed to disagree with the implementation. We then have a concrete product question: is the story wrong, or is the implementation wrong? Silently deriving the story from the current code would erase that question.
