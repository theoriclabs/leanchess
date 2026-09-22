# Theoric: software through domain semantics

The aim of theoric.com is to reach a world where software is fast and bug free.

We want to make software by expressing what is true in a domain, what people can do, and what must follow from their actions. We want to reason, build, and change applications in those terms. The execution machinery should carry that meaning into the world with guarantees we can inspect.

This is the ambition of operating purely in domain semantics: the author works with the meaning of the application. The system takes responsibility for realizing that meaning efficiently and preserving it through storage, communication, concurrency, and presentation.

The result should be software whose behavior we can explain, whose important properties we can prove, and whose implementation we can improve without reopening every question about whether it is correct.

## Make meaning the primary artifact

A chess game has players, positions, legal moves, clocks, and endings. A reservation has an owner, a resource, an interval, and conditions under which it can be changed. An account has a balance derived from transactions and rules governing who may transact. These are the concepts people intend to build with.

Today, the meaning of an application is often distributed across database constraints, request handlers, background jobs, frontend checks, and conventions that developers must remember. To determine whether a rule holds, someone has to reconstruct it from those pieces. A change to the rule requires finding every place that encodes it.

Theoric makes the domain model the authoritative expression of that meaning. It contains the concepts, the relationships between them, the admissible actions, and the questions the application can answer. Application behavior is constructed from this model, and implementation choices are accountable to it.

The model must be executable enough to answer questions and precise enough to support proofs. It must also remain recognizable to someone who understands the domain. A domain expert should be able to dispute a rule by discussing the rule itself.

## Keep facts, intentions, and execution separate

Domain facts describe the world being modeled. A bishop moves diagonally. A completed transaction contributes to a balance. Some facts are given, some are observed, and some follow from other facts. A derived fact has a derivation; an observation has a source and the circumstances under which it was received.

Application intentions describe what we want the software to permit, prevent, or guarantee. Only a seated player may submit that side's move. A user's private information must remain private. An accepted reservation must survive a process restart. These are policies and obligations of the application. They belong in an explicit application model, alongside the domain model they constrain.

Execution describes how those meanings become a running system: how requests arrive, identity is established, records are stored, clocks are read, work is scheduled, and results reach people.

These distinctions matter. Authentication cannot establish whether a chess move is legal. Chess legality cannot establish who sent a request. A successful database write cannot establish that the act was authorized. Each part needs its own meaning, its own evidence, and a precise relationship to the others.

External reality still enters the model. Identity, time, payment confirmation, and human decisions may require observations from outside it. Their sources and guarantees must be explicit. Operating in domain semantics means being precise about those observations, including what remains unknown.

## Let contracts evolve with the domain

Semantic contracts belong to the evolving meaning of the application. The framework supplies reusable ways to express and compose them. The domain and application models supply the particular states, actions, policies, transitions, and observations they describe.

A chess application supplies the meaning of a legal move. A reservation application supplies the meaning of an available interval. Both can use the same machinery for authorized actions, atomic commits, durable history, and delivery. The storage engine should not acquire a special branch for castling or double bookings.

Contracts should reference these authoritative definitions and be assembled from them. Changing a domain rule changes the dependent obligations; the build must recheck the affected proofs and generated artifacts. General proofs remain reusable wherever their premises still hold. Changes to persisted meanings may also require a migration or an explicit choice of which rule version governs existing history.

This does not mean every policy can be inferred from domain facts. Ownership alone does not decide whether sharing is permitted. People must state such intentions in the application semantics. Once stated, the rule should flow through the system from that definition, with evidence that each implementation preserves it.

## Give execution a contract

The execution substrate supplies the facilities an application needs. Its boundary should describe their semantic effects: read an authorized value, commit an admissible transition, observe time, deliver a result to a recipient. The domain does not need to name SQL statements, sockets, framework callbacks, or memory layouts.

That boundary is more than an interface with convenient function names. It states what each operation is allowed to do, what it returns, what can fail, what other operations it can race with, and what information becomes observable. It also states the obligations of its implementation.

An in-memory evaluator, a database-backed service, and a distributed deployment can realize the same application semantics. They may use different representations and algorithms. Each must establish that its observable behavior is permitted by the application model. Where the application promises progress, an implementation must establish that too; refusing every request would satisfy many safety rules while failing to implement the application.

This relationship is refinement: the concrete execution realizes the abstract meaning. Theoric needs a path from domain definitions to application semantics to actual execution, with evidence at every connection. A theorem about an isolated model becomes an application guarantee only when that connection reaches the running program.

For application authors, the benefit is a stable place to work. A change in database, rendering engine, or scheduling strategy should require new evidence at the execution boundary, while preserving domain definitions and the proofs that still apply to them.

## Why this could make software fast

A precise meaning gives us freedom to choose its implementation.

Consider a game position defined by replaying its accepted moves. That definition is simple to understand and reason about. An efficient implementation may maintain the current position incrementally, retain a snapshot, or cache answers. Each optimization must return the same answers as the reference meaning at the same logical point in the game.

The same opportunity appears in queries, indexes, batching, specialized representations, parallel execution, and moving computation closer to data. We can change how an answer is obtained while proving that the answer and its permitted effects are preserved. Derived state can be materialized for speed when its relationship to the authoritative facts is maintained.

This makes optimization a search among correct executions. Developers, compilers, and automated agents can propose alternatives. Proof obligations reject changes that alter the promised behavior; measurement distinguishes the alternatives that actually run faster.

Semantic equivalence alone does not prove a latency target. Cost models, resource bounds, workload assumptions, and measurements remain necessary. The vision is to make those concerns explicit at the execution layer, and to reuse their solutions across applications. Domain authors should be able to state a performance requirement without having to rebuild the machinery that meets it.

## Why this could make software bug free

Many bugs arise where one interpretation of a rule meets another: the browser permits what the server rejects, the stored state disagrees with the log, a retry repeats an effect, a concurrent update erases another action, or a new endpoint bypasses a privacy rule.

An authoritative semantic model removes sources of disagreement. Proofs can then establish properties across all modeled inputs and executions, including combinations that examples have not exercised.

The ambition is especially valuable for negative claims. A user should be able to trust that nobody else can read their private data. That requires a statement about every relevant API execution, including indirect paths through errors, shared state, and later requests. A collection of endpoint examples cannot establish that universal claim.

“Bug free” is the destination. A precise intermediate achievement is that an implementation satisfies a stated specification under explicit assumptions. The specification can still misunderstand the world, omit a necessary behavior, or promise too little. We therefore need domain review, concrete examples, and useful positive requirements as well as proofs. We also need to identify which parts of the execution substrate remain trusted and progressively reduce that boundary.

The goal is to make the evidence match the claim. A proved invariant, a tested adapter, an assumed property of an identity provider, and an unmodeled timing channel are different kinds of evidence. Theoric should keep those distinctions visible.

## Properties we want applications to carry

The particular statements depend on the domain. The recurring obligations are broad enough to shape the platform:

1. **Valid state stays valid.** Every admitted action preserves the domain's invariants, starting from a valid initial world.
2. **Actions have legitimate authority.** Every admitted act is attributable to a principal who is permitted to perform that act on that resource. A request cannot manufacture authority by naming someone else.
3. **Private information stays private.** Unauthorized executions cannot read private data, and changes to that data cannot influence what an unauthorized observer can learn through the application.
4. **Accepted actions have their specified effects.** A successful response corresponds to the promised transition. Rejection has exactly its specified effects, including any permitted audit record.
5. **Derived answers agree with their meaning.** Stored projections, caches, and incremental computations agree with the facts and history from which the answer is defined.
6. **Concurrency preserves the application contract.** Racing operations have only allowed outcomes. For operations requiring a sequential order, execution corresponds to such an order without losing accepted work.
7. **Retries preserve intent.** Repeating the same identified request cannot repeat an effect that the contract permits only once. Distinct requests remain distinct even if their payloads happen to match.
8. **Boundaries preserve meaning and authority.** Parsing, serialization, persistence, and rendering preserve relevant values and permissions. Invalid inputs cannot become authoritative domain facts.
9. **Time has a defined source and meaning.** Deadlines, expiration, and elapsed time follow the declared clock contract. Client claims cannot substitute for authoritative observations.
10. **Recovery preserves commitments.** Under a stated failure model, acknowledged durable actions survive recovery and partial operations cannot create forbidden states.
11. **Implementations and optimizations preserve semantics.** Changing representation, evaluator, or substrate preserves the promised observations and effects, including confidentiality.
12. **Permitted work can complete within its stated conditions.** Progress, resource bounds, and performance obligations name their scheduling, dependency, hardware, and workload assumptions.

These should become obligations of the assembled application. Adding an endpoint, an effect, or a new execution adapter should expose the new proof obligations automatically. Existing proofs should compose where their assumptions still hold.

## Why it is valuable to work at this level

The domain is where a change acquires its meaning. Working there lets us ask whether a new rule is consistent, what it changes, which guarantees it preserves, and which examples distinguish it from the old rule. We can explore those questions before involving a production database or a network.

It also changes how software can be generated. An agent can propose an implementation, but the accepted result must meet obligations that are independent of the agent's confidence. A proposed optimization can be checked for equivalence. A proposed product change must make its change of meaning explicit. Human judgment remains responsible for what the software ought to mean.

The investment compounds. Proving the storage boundary, the authorization boundary, or the delivery boundary once can support many applications built within those contracts. Domain authors spend more of their effort on the facts and decisions that distinguish their application. Improvements in execution can benefit those applications together.

## LeanChess as a concrete proving ground

LeanChess gives this ambition a small, demanding world: one game with legal actions, two seats, a clock, concurrent requests, durable history, and a visible result. Its [product vision](vision.md) describes the experience we want to deliver.

The existing pure game model and log theorems are a starting point. The next architectural achievement is to connect that meaning to the complete application: identity and authority, admitted commands, storage, responses, and every exposed route. Alternative rule evaluators need equivalence evidence before they can serve as interchangeable implementations. The current repository does not yet establish these application-wide guarantees.

The general vision is larger than chess or any particular framework. A person should be able to describe the world their software operates in, state the guarantees people depend on, and obtain an efficient execution with evidence that it keeps those guarantees. As the software changes, its meaning and its evidence should remain things we can understand and maintain.

The [connecting-pieces upgrade plan](connecting_pieces.md) describes how the current libraries and application boundaries could evolve to support this vision. The [private-data sketch](private_data_sketch.md) develops one specific proof obligation.
