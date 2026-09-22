# User stories as a small Lean language

The [prose stories](stories.md) now have a reusable authoring layer, separate from both product-specific meaning and application code.

The useful distinction is between three things: what a person wants to accomplish, what those intentions mean in a product, and how an implementation realizes them. This package covers the first two and checks their relationship. It does not provide the third.

## The pieces

| File | Responsibility |
|---|---|
| [UserStories.lean](UserStories.lean) | General vocabulary, typed flows, story declarations, laws, and certification rules. Imports only `Std`. |
| [Stories.lean](Stories.lean) | The independent LeanChess product model from the first experiment: agreement, attempts, observations, privacy, and knowledge. No application imports. |
| [ChessStories.lean](ChessStories.lean) | The prose stories authored through the general language, plus evidence that the product model satisfies them. |
| [ReservationStories.lean](ReservationStories.lean) | A different product vocabulary and model, using the same language unchanged. Imports no chess definitions. |
| [StoryChecks.lean](StoryChecks.lean) | Counterexamples, negative type checks, and proof-dependency checks. |

The package has no external dependencies and is not a target of the application build. From the repository root:

```sh
lake -d product_intent build
```

Intentional negative type checks print diagnostics while the build succeeds. Any `sorry` placeholders shown inside those expected diagnostics are not admitted declarations; the proof-dependency checks contain no `sorryAx` or custom axioms.

## What authoring a story looks like

Here is the private-note story's core, using ordinary Lean record syntax and a typed `do` block:

```lean
def rememberNote (facts : GameFacts) (actor : Person) (body : String) :
    Story (vocabulary facts) (Reply facts × Reply facts) where
  id := "S6"
  asA := actor
  iWant := "Write and revisit a private personal note"
  soThat := "My analysis remains available to me without becoming shared game data"
  given := fun _ => True
  scenario := do
    let acknowledgment ← askGame actor (.appendNote actor body)
    let notes ← askGame actor (.readNotes actor)
    pure (acknowledgment, notes)
  ensures := fun before replies after =>
    replies.1 = .saved ∧ replies.2 = .notes (before.notes actor ++ [body]) ∧
      after.game = before.game
  laws := [privateNotes facts]
```

This is an embedded DSL, not a new parser. `askGame` only specializes the generic `ask` operation to the product's vocabulary. It does not call the application. The `do` block constructs a flow value; a separately supplied relation gives it meaning.

The protagonist and individual requests are typed. The intention's result is typed too: the general vocabulary defines `Observation : Intention → Type`. A product can therefore give different intentions different observation types. The reservation example returns a `Decision` for reserving and a `Bool` for inspecting availability; Lean rejects treating a reservation decision as a Boolean.

Flow continuations can choose the next intention from the preceding observation. The reservation example includes “inspect; if available, reserve; otherwise stop.” Multiple people can participate in a flow, as in “make an attempt; let the other player look.” The `asA` field names the protagonist; it does not restrict every step to that person.

The prose labels explain purpose and provide traceability. Lean does not prove an English `soThat` sentence. The checked content is in the typed flow, `given`, `ensures`, and attached laws. Whether those faithfully express the human intention remains a specification-review question.

## What it means to satisfy a story

A product supplies this relation:

```lean
Actor → State → (intent : Intention) → Observation intent → State → Prop
```

It describes permitted before/intention/observation/after combinations without selecting a database, request protocol, scheduler, or widget.

`Certified semantics story` requires three kinds of evidence:

1. **A feasible starting situation.** There is a state satisfying `given`. An impossible precondition cannot make a story vacuously certified.
2. **A fulfilled flow.** From every allowed starting state, each modeled request has at least one response, and every response the supplied semantics permits must continue to satisfy the story's outcome. A bad branch cannot be ignored because a good branch also exists.
3. **The attached laws.** Every additional law must hold of that exact semantics.

The certificate is indexed by both the story and its meaning. It cannot be moved to a different implementation relation or a strengthened story merely because method names or prose labels match. Changing an outcome, a policy-dependent law, or the supplied semantics changes the required evidence.

The language intentionally has no assertion-as-filter constructor. Acceptance conditions judge behavior; they must not erase failing executions from the model before those executions are judged.

The generic theorems establish that certification gives an actual finite model run and that every completed run has the promised outcome. This is not a wall-clock progress guarantee: the relational model has no network waiting, scheduling, or latency. Those conditions require additional temporal laws.

## Laws that do not fit inside one example journey

An owner successfully reading a note does not prove privacy. Privacy compares observations in different worlds, including worlds containing different private values.

The general language therefore provides `Law Subject`, whose meaning is an arbitrary Lean proposition about its subject. It also provides reusable invariant, noninterference, and eventuality vocabulary. The product chooses the observation equivalence and the policy; owner-only access is not built into the language.

LeanChess supplies `SameFor`: the public game and the observer's own notes agree. Its privacy law states that other private values cannot affect the observer's interactions. A generic lifting theorem extends one-step noninterference to finite personal flows whose subsequent intentions depend on earlier observations. The private-note story uses that theorem; the generic proof contains no chess or notes concepts.

Progress is represented separately by `returnProgress`. Cross-modality preservation and coverage are represented by `inputMeaning`. Neither is falsely certified by the existence of a happy-path journey. They remain obligations for a future realization with explicit opportunity conditions and supported input methods.

## The current storybook

| Prose story | DSL declaration | Evidence |
|---|---|---|
| S1: understand the game | `seeGame` | Certified against the independent product model |
| S2: make a permitted attempt | `makeAttempt` | Certified given an independently permitted starting example |
| S3: recognize refusal | `refusedAttempt` | Certified given a refused starting example |
| S4: retain an ending | `keepEnding` | Certified given a finished starting example |
| S5: catch up before continuing | `returnToGame` | Certified in the confirmation model; temporal progress remains open |
| S6: retain a private note | `rememberNote`, with `privateNotes` | Certified, including the modeled information-flow law |
| S7: preserve input meaning | `inputMeaning` | Law stated; no platform realization supplied |
| R1: reserve a free slot | `reserveFree` | Certified in the separate reservation product model |

`GameFacts` is still abstract: these certificates do not establish detailed chess legality. Finite flows also do not introduce concurrent environmental steps automatically. Interruption, concurrent changes, time, retry identity, and additional observations must be modeled explicitly where the stories depend on them.

## Checks that matter

The checks refute certification for a silent model, a model that always refuses, a model that sometimes refuses a promised successful reservation, an impossible starting condition, and a story with an unfulfilled law. Four negative type checks also reject a mismatched observation type and attempts to reuse evidence across changed semantics or laws.

The existing application was not changed. The next connection would supply a relation between actual application executions and this independent story vocabulary, then prove that the implementation's complete exposed behavior satisfies the selected stories and laws. API coverage and the behavior of native code cannot be inferred from the certificates in this package.
