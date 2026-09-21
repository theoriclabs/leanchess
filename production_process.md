# Production process

Turn a domain into a closed model a machine can query. Chess is this run. The precedent is `medical_billing`: the same stages, produced in this order, over one story rather than the whole field.

The harness is this sequence plus the gates. A gate is implemented only once its artifact exists. Until then the stage is open, and the harness reports it open. It does not invent a pass.

## Invariant

Every stage holds these. A later stage may add a constructor, a derived function, or a theorem. It may not break them.

1. **Derive the derivable.** A fact that follows from other facts is a function. Age from birth year. Enrollment-in-force from coverage dates. It is never a stored field and never an event.
2. **Observe the unobservable.** A fact this world cannot compute is a dated observation from whoever can. Remaining deductible, and whether the plan is active today, are a 271. They stay on that observation.
3. **Each role keeps its own type.** Patient owns coverages. BenefitPlan is the payer's product. EligibilityResponse is a 271. Three types.
4. **The query universe is closed.** A query reads the prior world `W`, a prefix of the log `L`, and a clock `d` when the answer changes with time on the same log. A fact in neither `W` nor any prefix of `L` is unknown. The snapshot `S = apply(empty, L)` is a lossy view: what is current is asked of `S`; what happened is asked of `L`.
5. **Facts, then events.** Prior facts are things true before the log starts. Events are acts performed or observations received, and they modify the situation. Time passing is not an event. A derived fact is not an event.
6. **Indicative, then optative.** Facts and laws say what is true of the world anyway. Requirements say what we want true. The machine is not a domain concept. It shows up only when a requirement constrains an act.

## Stages

Four stages, in order. Each leaves one artifact. The next stage reads it. Starting stage *n* requires stage *n−1*'s gate to pass. On a failure, the fix goes in that stage's artifact.

The cut is stage 0 because the precedent never modelled the whole field. It modelled Dana's ninety days.

### 0. Cut

One story, small enough that stage 4 can be a finished log. Name the phenomena inside it and the phenomena refused. Actors and acts in ordinary words.

Artifact: `scope.md`

Gate: the in-list, the out-list, and the story are all non-empty. No types in this file.

### 1. Facts

What is true of the cut, whether or not anyone builds anything.

Artifact: `facts.md`

Indicative sentences. Tag each `prior`, `derived`, or `observed`. A derived fact names its inputs. An observed fact names the observer. List the collapses refused, as concepts that stay separate.

Gate: every sentence is tagged; every derived tag names inputs; every observed tag names the observer; the refused collapses are listed. No Lean in this file. Every fact is about the cut in `scope.md`.

### 2. Vocabulary

What is what, and how the concepts combine.

Artifact: `vocabulary.md`

Sort every fact into `W` (true before the log), `L` (one event constructor: an act or an observation), or a derivation from `S` or from `L`. Say which questions `S` answers and which it forgets. Name the clock, and which queries take it. End with the questions that are not in the universe, each with the reason.

Gate: every concept in `facts.md` is in exactly one of `W`, `L`, or derived. Concepts stage 1 kept apart stay apart. History questions are on `L`; current questions are on `S`. The not-in-universe list is non-empty.

### 3. Lean model

The vocabulary as a shallow embedding. Lean's types are the concepts: structures, inductives, predicates, functions. Not an interpreted AST.

Artifact: a Lake project whose domain library is `domain/`. Types for `W`. One inductive for the events of `L`. A state. `apply` as a fold of a prefix. Derived facts as functions. The example story is not in this stage.

Gate: `lake build` of the domain target succeeds. Every event in `vocabulary.md` is a constructor. `apply` is total on that inductive. No `axiom` and no `sorry` stands in for a fact tagged derived. Types stage 2 kept apart are separate declarations.

### 4. Userflow

The story from stage 0, inhabited. One prior world, one log, and a theorem for each query the story turns on. Discharged by `decide` or `rfl`. This is the first gate that executes.

Artifact: `example_cases/`.

Gate: `lake build` of the example target succeeds. The log is a list of the event type from stage 3. Each theorem names the query and the prefix it is asked of. A query the snapshot forgets is asked of `L`.

## Later stages

These are part of the precedent. They stay unopened until stage 4 passes. Each becomes a harness stage when we reach it, with the same rule: implement the gate only after the artifact exists.

### Laws

A law is data, not software. First the prose a practitioner could read (`laws/examples.md`), then a closed structure and a corpus (`laws/universe.lean`, `laws/corpus.lean`), then queries that evaluate over the corpus (`laws/queries.lean`).

Dimensions, the ones the billing corpus uses: author, provenance, subject, modality, defeasibility, conflict rule, determinacy, world assumption, valid time, revisability, limitation period. Each dimension is a finite enumeration or a finite tree. The wording inside an open-textured term stays a string; the atom's kind records that the term is open.

Gate: every corpus entry inhabits the law structure. A query over the corpus is evaluation, and where the answer is worth keeping it is pinned by `decide`.

### Query catalog

The questions the model exists to answer. `QUERIES.md` is the target. `QUERY_UNIVERSE.md` is the subset the current model admits, including what it refuses.

Shape: `W → prefix of L → d → α`. Answer shapes are named (a verdict, an amount, a deadline, a cause). Each answer carries an epistemic tag: derived from `W`, observation, act, derived from `W ∪ L ∪ d`, predicted by our model, classified by us. A theorem about an observation is about what was said, and the tag says so.

Counterfactuals name what they vary: a different rule set, a different clock, a different log. Varying `W` is a different universe.

Gate: every query's inputs are among `W`, `L`, `d`, and a named counterfactual. A query `S` forgets is typed against `L`.

### Requirements and admissibility

Requirements are optative and stated in the world (`requirements/`). Admissibility reads each one against the model and marks it:

- `admissible` — expressible, and a witness discharges it
- `gap` — the signature is expressible; a type or constructor is missing, and it is named
- `outside` — it needs a type the universe does not have, and it is named

Missing types live as definitions in a `Spec` namespace. They are not axioms, and they are not used as if they were proved.

Gate: every requirement has one verdict. `admissible` names a witness. `gap` and `outside` name what is missing.

## How the harness grows

- The stage order and the artifact path of each stage live in this file. The checker reads them from here.
- A gate is code only after its artifact exists. An open stage is reported open.
- Stage *n* does not start while stage *n−1* fails.
- The checker re-runs the invariant, not only the newest gate: a derived fact stored as a field, two roles merged into one type, or an answer to a question the universe excludes, fails the stage that introduced it.
- Definitions stay in Lean. Other systems are called later, for a specific input and output, against a query this universe already has a type for.

## This run

| | |
|---|---|
| Domain | Chess. One standard game, from the opening to an ending, with a clock. |
| Precedent | `medical_billing` — discipline in `MODELLING_NOTES.md`, closed universe in `QUERY_UNIVERSE.md`, model in `domain/main.lean`, userflow in `example_cases/dana.lean`, laws in `laws/`, requirements in `requirements/` |
| Cut | Stated at the top of `facts.md`. No separate `scope.md`. |
| Vision | `vision.md`. Optative. It does not enter the query universe. Later requirements are cut from it. |
| Vocabulary | `vocabulary.md`. |
| Open stage | 3, Lean model. `domain/Game.lean` defines the game. `lake build` succeeds. The gate is not a checker yet. |
| Next artifact | `example_cases/`, when a story is played through the definition. |
