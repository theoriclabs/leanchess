# Workshop: a typed, queryable execution substrate

The substrate should expose the meaning and evidence of its operations in a form an application can query. The application should be able to ask which implementation meets its requirements, what assumptions that answer depends on, and which guarantees remain unestablished.

Lean can express more of this relationship than the current integration uses. The important opportunity is to connect values, implementations, and propositions through dependent types. Merely adding more names or Boolean feature flags would leave the central question unanswered: what establishes that this particular implementation has the advertised behavior?

The accompanying [Lean workshop](workshop/Substrate.lean) contains compiled reference examples. Run it with:

```sh
lake env lean workshop/Substrate.lean
```

The [cross-platform workshop](platform_workshop.md) continues with interaction, session recovery, and lifecycle examples across web, iOS, and Android, including additional checked Lean models.

It is separate from the production build. Its negative compilation checks deliberately print type errors, while the command exits successfully when those checks behave as expected. The examples introduce no `sorry` or custom axioms; the printed proof dependencies are standard Lean axioms. They certify pure models, not the real database, authentication, HTTP host, or JavaScript runtime.

## A property needs both a description and a meaning

The prototype starts with:

```lean
structure Catalogue (Implementation : Type) where
  Claim : Type
  meaning : Implementation → Claim → Prop

structure Registry (catalogue : Catalogue Implementation) where
  implementation : Implementation
  evidence : (claim : catalogue.Claim) →
    Evidence (catalogue.meaning implementation claim)
```

`Claim` is data that can be inspected and queried. `meaning implementation claim` is the exact proposition the claim denotes. The evidence field is indexed by both. A proof concerning one reader cannot certify a different reader merely because both expose the same method name.

The prototype distinguishes five evidence states: proved, conditional on a premise, tested, unknown, and refuted. A conditional entry carries an actual function from the premise to the conclusion. A tested entry carries no proof. Consumers that demand an established property accept only the proved case; `Registry.require` recovers the proposition from that case.

This gives us computable discovery without pretending to decide arbitrary theorems. Querying a registry asks what evidence it contains. An unknown entry means evidence is missing, not that the property is false. Lean's `Decidable` can supply executable checks for particular predicates; classical decidability does not give a general executable property checker. See [Lean's type-class documentation](https://lean-lang.org/doc/reference/latest/Type-Classes/) and [`Classical.propDecidable`](https://lean-lang.org/doc/api/Init/Classical.html).

Each property family supplies its own claim type and interpretation. We can add storage, delivery, clock, or cost catalogues without hardcoding their meanings into a universal list of business rules. Domain-specific predicates remain parameters or named definitions in those meanings.

## Example 1: two readers, the same answer, different guarantees

Suppose Alice requests her private notes. Consider two implementations:

- `scopedReader` obtains only Alice's rows and returns them.
- `scanThenFilter` obtains every user's rows, filters by Alice's identity, and returns the same answer.

The reference execution records both the returned rows and the owners of values obtained by the application-level read. This deliberately excludes physical page access inside a database engine.

The catalogue defines three propositions about these actual functions:

| Claim | Meaning | Scoped reader | Scan then filter |
|---|---|---|---|
| `confinedReads` | Every value obtained by this read belongs to its caller | Proved | Refuted by a concrete counterexample |
| `exactResult` | The answer equals the complete authorized view | Proved | Proved |
| `responseNoninterference` | Equal authorized views produce equal answers | Proved | Proved |

These results are checked in Lean. They demonstrate why output types and even exact-result proofs do not establish the stronger access-confinement requirement. The response theorem concerns this pure query result; it does not cover timing, logging, or the complete application trace.

A private repository consumer requires both confined reads and exact results. The selection function needs evidence of those claims for the selected implementation. Supplying the scan-then-filter registry is rejected by Lean. Querying the two candidates for those requirements finds only the scoped reader.

This also prevents a vacuous solution: an implementation that returns nothing can avoid disclosing rows but cannot satisfy exactness when Alice has notes.

The native upgrade would describe the actual query plan, decoder, read effects, failure behavior, and configuration. Its evidence must connect those to the reference operation. A trace that is merely self-reported by arbitrary native code would not establish confinement. The generic planner must preserve a compulsory authorization restriction before protected values cross into application execution.

For a different domain, the authorized view could depend on membership, delegated access, or a resource classification. The catalogue machinery stays the same. The view and permission definitions change, and the dependent proofs must be supplied for that policy.

## Example 2: a prepared chess move carries its exact context

The second example separates the domain-specific model from a reusable commit mechanism:

```lean
structure Model where
  State : Type
  Command : Type
  permits : String → State → Command → Prop
  next : State → Command → State

structure Prepared (model : Model) (actor : String)
    (base : Snapshot model.State) where
  command : model.Command
  authorized : model.permits actor base.state command
```

`Prepared` is indexed by the exact model, actor, and snapshot. Its proof establishes a permission predicate for that command in that state. The chess instantiation references the real `domain/Game.lean`: the actor must occupy the side to move, and the game transition must advance the ply by one.

Incoming data is still untrusted. `prepare` performs a decidable check and constructs the evidence only on success. In the opening example, White's `e4` produces a prepared command; Black proposing that move does not. A term indexed by Black cannot be passed where a prepared White command is required.

The pure commit implementation compares the prepared snapshot with the current snapshot, then applies the model's transition. A snapshot includes resource identity, revision, and state. Its catalogue establishes:

- A stale or different-resource snapshot is refused.
- Success has the specified transition, preserves resource identity, and increments the revision.
- A permitted command against the current snapshot succeeds.

The same implementation and proofs are instantiated for a minimal reservation domain in the file. The permission becomes “the actor owns this resource and it is available”; the transition marks it reserved. No chess branch is added to the committer.

This is a stronger use of Lean than attaching `authorized : Bool` to an unqualified command. It still does not authenticate the supplied actor or prove that the current snapshot came from a database. Nor does a proof of permission against an old state make that state current. Those are explicit obligations of the identity and commit interpreters.

The reference checks full snapshot equality. An efficient adapter could compare a resource revision instead, after establishing an invariant that the revision identifies the relevant state. Concurrent execution then needs a separate proof of the atomic comparison and update. Crash durability, receipt-based retry behavior, and authoritative clock sourcing are additional properties; the prototype does not advertise them as proved.

## What should be queryable about real substrates?

A production registry should associate evidence with a specific implementation, configuration, property statement, and assumption set. For example, “SQLite supports transactions” is too broad to select an application commit operation. We need to know which transaction protocol, which state it covers, what constitutes acknowledgement, and which crash model is assumed.

Useful queries would include:

| Query | Required typed information |
|---|---|
| Which readers satisfy this policy without obtaining unauthorized rows? | Policy identity, authorized-view semantics, read-effect semantics, evidence |
| Can this committer implement this application's transition? | Model, resource scope, snapshot relation, conflict behavior, preservation evidence |
| Is a read and its preceding authorization check based on one consistent state? | Transaction/session scope and a consistency proposition |
| What breaks if policy or session validity changes? | Versioned dependencies, evidence premises, cache and revocation rules |
| Which acknowledged actions survive this failure? | Acknowledgement semantics, failure model, recovery contract |
| Which implementation meets a resource budget? | Typed units, workload/environment assumptions, a cost bound or separately identified measurements |
| Why is this implementation ineligible? | Refuted requirement, missing evidence, or an undischarged premise |

The prototype implements the first two families at the reference-model level. The others are proposed extensions.

Conditional claims need particular care. The assumption should be a typed, identifiable obligation with provenance and dependencies, so a deployment can show which premises it actually meets. A string saying “trusted” is insufficient. The prototype carries a premise as `Prop` plus a description; a production assumption catalogue would add this structured discovery layer.

Likewise, a JSON manifest can expose names, parameters, dependencies, and evidence status for inspection. It cannot turn a claimed status into a Lean proof. Verified assembly must obtain the evidence from checked declarations or a validated certificate mechanism tied to the exact artifact. Runtime descriptions and proof objects serve different purposes.

## Where Lean's type system can do more

The existing stack already uses nominal IDs, operation-kind indices, typed field queries, codec-law propositions, and scoped grants. The gap is that these guarantees are not consistently required at the points where implementations are selected and exposed.

| Current mechanism | Stronger use of Lean |
|---|---|
| An operation carries input/output codecs | Its specification also references the transition, permission, and observations; the selected implementation must satisfy that specification |
| `Codec.Laws` exists beside a codec | Verified assembly accepts a codec bundled with the laws it requires |
| A policy returns success or a description string | The consumer receives evidence indexed by the relevant actor, resource, action, and state |
| A read capability runs in a chosen monad | A restricted effect program, or a behavioral proof, accounts for every possible effect |
| An adapter advertises supported features | A typed catalogue ties each advertised property to its semantics and evidence for that adapter |
| General theorems are separate declarations | Assembly consumes their instantiated results, making missing obligations visible at construction time |

Dependent structures fit explicit adapter selection well. Type classes can package reusable algebraic laws and infer routine instances once the implementation is fixed. They should not silently choose a security policy, an execution mode, or a different backend. Those choices deserve explicit values in the application assembly.

Keep machine-queryable descriptions in `Type` and semantic obligations in `Prop`, connected by an interpretation. Lean erases proof fields from compiled values; a subtype's proof therefore need not add runtime payload. Checks needed to construct evidence from external input still execute. See the [Lean reference on inductive types and subtypes](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/).

A dependent type also does not make a value single-use. An ordinary Lean value can be retained and reused. Request identity, stale-state rejection, revocation, and resource lifetimes need operational enforcement and corresponding proofs. Similarly, putting a native implementation behind a function field does not establish its side effects or correctness.

## The next design experiment

The working recommendation is a small typed property catalogue with executable discovery and proof-requiring consumers, built around the existing LeanApp and PrivateNotes mechanisms. Keep domain predicates and transitions ordinary Lean definitions. Reify the effects and property descriptors that need inspection, and give each a precise interpretation.

The next useful experiment is to connect the scoped read model to one native adapter and represent its remaining assumptions explicitly. Then ask the catalogue to explain why that adapter satisfies, conditionally satisfies, or fails the private-repository requirements. This would test the difficult connection between a useful typed description and real execution, while preserving the distinction between evidence we have and evidence we still need.
