# Upgrading the connecting pieces

The [Theoric vision](theoric_vision.md) asks application authors to work in domain semantics while the platform supplies efficient, correct execution. The connecting pieces must therefore carry more than values of the right type. They must preserve meaning, authority, and observable behavior across each boundary.

This document proposes how those pieces could evolve. It distinguishes mechanisms already present in the local repositories from guarantees still to establish. It is an architectural plan, not an assertion that the current stack has been verified.

The [typed-substrate workshop](substrate_workshop.md) develops the proposal through compiled Lean examples: a queryable property catalogue, private readers with different guarantees, and a domain-parameterized commit mechanism.

The [cross-platform workshop](platform_workshop.md) applies the same ideas to extending LeanReact toward React Native: shared intentions, typed platform differences, and mandatory interpretation and recovery obligations.

## The common upgrade

Each connection needs four things: an abstract meaning, an executable interface, an implementation, and evidence relating the implementation to that meaning. A typed signature is the beginning of this relationship. Its contract must also describe errors, effects, ordering, recipients, and relevant failure conditions.

The structure we want is:

```text
Domain facts and definitions
            ↓
Application semantics: actions, authority, observations, invariants
            ↓
Declared operations and restricted effect programs
            ↓
Interpreters: storage, identity, clocks, transport, scheduling
            ↓
Native service and generated clients
```

The lower layers depend on the meaning above them. Domain definitions remain ordinary Lean types and functions. A restricted representation of application effects helps close the execution surface; it does not require turning the whole domain into an interpreted language.

The main responsibility split is:

| Piece | What it should own | What its connection must establish |
|---|---|---|
| Domain library | Concepts, facts, legal transitions, derived answers | Domain invariants and the meaning of each computation |
| LeanOntology and LeanContract | Public identities, representations, operation contracts | Values and declared outcomes retain their meaning across encoding |
| LeanApp | Authority, effect composition, application assembly | Every exposed execution obeys the application's policies and transition rules |
| Identity adapter | Credential and session processing | Issued authority corresponds to validated session facts at the declared point in execution |
| LeanDB and storage adapters | Representation, queries, atomic persistence | Reads and commits implement the abstract storage contract |
| HTTP and channel hosts | Ingress, dispatch, delivery | Requests enter covered operations; outputs reach only permitted audiences |
| LeanReact and LeanJS | Interaction, presentation, portable execution | Views and proposed actions correspond to the declared model and current session |
| Build and verification tooling | Composition of evidence | The checked definitions and assumptions describe the artifacts actually shipped |

These are responsibilities, not necessarily eight new packages. Existing modules should acquire the missing contracts and evidence where they already provide the corresponding mechanism.

## Reusable machinery, evolving contracts

The semantic contracts are supplied by the domain and application models. The connecting libraries provide the machinery for expressing, interpreting, and proving them. A library should not contain a fixed catalog of chess rules, ownership policies, or business workflows.

Separate three levels:

| Level | Examples | How it changes |
|---|---|---|
| Domain and application meaning | Legal moves, reservation conflicts, who may read a document | Authors revise the authoritative definitions and intended guarantees |
| Reusable semantic machinery | Transition composition, authorization evidence, observer equivalence, commit and delivery contracts | Libraries provide general constructions and theorems parameterized by the relevant definitions |
| Concrete execution | SQLite transactions, session validation, JavaScript encoding, network delivery | Adapters establish that their implementations meet the instantiated contracts |

For example, a general composition theorem can say: if every admitted transition preserves an invariant, then every reachable state preserves it. Chess supplies its state, transition, and invariant and proves the premise. Reservations supply different definitions and prove their premise. The composition theorem is shared. It cannot invent either domain's rules or discharge arbitrary new premises automatically.

The operation contract should reference the model's authorization predicate and transition relation directly. The implementation may use a different, faster algorithm, but its evidence must relate that algorithm to the same reference meaning. Domain-specific contracts should not become another handwritten copy of the rules in a server configuration file.

Policy intentions still require authorship. Whether documents permit delegated readers is a product decision; it cannot be derived solely from the existence of an owner field. Likewise, the platform must not define a contract from whatever the implementation currently does and treat their agreement as evidence that the intended requirement holds. Reviewed requirements, useful examples, and independent properties remain necessary.

Semantic evolution should follow a concrete dependency chain:

1. Change the domain or application definition and identify whether its observable meaning changes.
2. Rebuild the contracts and generated artifacts that depend on it; recheck their proof dependencies.
3. Reuse general theorems whose premises still hold, and discharge changed premises or report the corresponding guarantee as open.
4. Establish compatibility for existing callers, stored data, event history, sessions, and caches. Where compatibility does not hold, version the behavior and provide the required migration or transition policy.

A change to chess rules may require keeping existing games on their agreed rule version. Adding delegated document readers changes the authorization relation and the privacy theorem's permitted audience; it must not silently weaken the owner-only promise. Optimizing the evaluator with unchanged meaning instead requires preservation evidence and can leave domain contracts intact.

The effect vocabulary can evolve too. “Closed” means all effects in a particular verified application are accounted for. New domains may introduce new abstract effects, together with their semantics, interpreters, and composition obligations. Extensibility must not permit an unmodeled execution escape. Framework-level laws such as atomicity and codec preservation also have explicit versions; changing them requires rechecking their consumers.

## LeanApp: make application behavior a thing we can prove

LeanApp already has [typed capabilities](../leanreact/engine/LeanApp/Capability.lean), [policy bindings](../leanreact/engine/LeanApp/Binding.lean), [evidence-producing policies](../leanreact/engine/LeanApp/Policy.lean), and an [application registry](../leanreact/engine/LeanApp/Application.lean). Queries receive a read capability; commands can receive writes. Application construction validates publication metadata and rejects collisions. This is useful assembly machinery.

The next step is to make an operation describe its behavior as well as its input and output by referencing the domain and application definitions. It should name the state it reads, the authority it requires, the transition it can perform, its permitted observations, and its success and failure meanings. A policy description string remains documentation; the guarantee must refer to an executable predicate or proposition.

For LeanChess, an application-level `Play` command would include a game identity and proposed move. Its semantic admission rule connects the authenticated principal to the occupied seat and that seat to the moving piece. The pure chess function can continue to decide move legality without importing authentication.

Handlers currently run in a chosen host monad, often `IO`. A read-only capability record cannot prevent such a handler from using other imported IO functions. Introduce a verified application fragment whose effects are represented explicitly, with a reference interpreter and a native interpreter. Handlers in that fragment cannot escape into arbitrary database, network, filesystem, or logging operations. Alternatively, a handler can be admitted through a direct proof of its full effect behavior; the escape is an obligation, not an invisible convenience.

Define executions and observations for this fragment. Prove that approved operations preserve invariants, exercise only authorized effects, and compose over request sequences. Then prove the application dispatcher selects only such operations. This turns adding a route or effect into an explicit extension of the theorem's cases.

LeanChess would migrate the policy and transition orchestration in `api/Service.lean` into this layer. The native service would interpret the operations. The first milestone is one real operation passing through that complete path, with a useful success theorem and a refusal theorem.

## Identity and privacy: bind authority to the exact operation

LeanApp's [request context](../leanreact/engine/LeanApp/Context.lean) already distinguishes host-issued claims from browser data. Its comments correctly describe the trusted issuer as an API boundary, not a sandbox against arbitrary importing code. The [native authentication implementation](../leanreact/adapters/native/LeanAppNative/Auth/Store.lean) has account and session records, session generations, expiration, and invalidation machinery. LeanChess currently uses its own simpler bearer lookup.

The upgrade is to connect these mechanisms to an explicit authentication contract. Separate a stable actor identity from a display name, credential, tenant, and game seat. Define when session validity is observed, how revocation races with an operation, and when a cached authentication result remains valid.

Authorization evidence should identify the principal, resource or permitted scope, operation, and relevant session or policy version. Checking that someone is authenticated must not accidentally authorize a different resource. A request must not choose its own trusted context. The native interpreter must enforce the modeled lifetime and ordering; a proof index or a private constructor alone does not establish that runtime facts were obtained honestly.

There is already a valuable precursor in [PrivateNotes.Model](../leanreact/examples/security/PrivateNotes/Model.lean): request-scoped grants, ownership and provenance theorems, and `response_noninterference` for five modeled read operations. Its [native adapter](../leanreact/adapters/native/LeanAppNative/Notes.lean) uses an owner-and-tenant query and certifies decoded rows. The model theorem assumes equal session facts and equal authorized views. It does not establish confidentiality of the entire host, its logs, physical timing, or later state-changing interactions.

Generalize that work into reusable authorized repositories and recipient-aware outputs. Keep credential storage separate from public identity and private application data. Extend the evidence to complete execution traces, including errors and future reads of shared state. The [privacy sketch](private_data_sketch.md) describes the intended stronger claim.

## LeanOntology and LeanContract: preserve semantics through representation

[LeanOntology](../leanreact/engine/LeanOntology/Codec.lean) already defines `Codec.Laws.roundTrip`. [LeanContract](../leanreact/engine/LeanContract/Operation.lean) retains input, output, and error types until the wire boundary, and operation identities have versions. These are foundations to reuse.

Require evidence for the codecs used by the verified fragment. Encoding a valid value and decoding it must recover that value. Accepted external representations must reconstruct values satisfying the domain's validity conditions. A schema match alone does not establish those conditions. Invalid representations must produce bounded, classified errors without disclosing protected inputs or stored values.

Storage mappings also need laws, including the meaning of partial encoding: if a valid domain value cannot be represented by a storage type, the boundary must report that limitation. Numeric bounds, exact identifiers, nulls, enums, and time representations must not change silently. The native stack's [checked storage representations](../leanreact/adapters/native/LeanAppNative/Storage.lean) are an existing place to attach this evidence.

Generate operation clients, codecs, and route descriptions from a shared declaration. The current [client generator](../leanreact/engine/LeanContract/Generate.lean) explicitly generates schema-shaped checks; custom validations beyond the schema remain on the server. To claim identical client and server validation, either compile the relevant validator to the client with preservation evidence or represent it in a shared supported language. Until then, the guarantee should remain server validation plus client shape checking.

LeanChess's `api/Wire.lean` and `web/api.mjs` currently reconstruct the boundary separately, including positional constructor fields. Replace that duplication with generated bindings. Operation versions must account for behavioral compatibility, not just record shape: changing an authorization rule or retry meaning can matter without changing a JSON field.

## LeanDB: give reads and commits a semantic contract

LeanDB already supplies typed entities, decoding, transactions, a reference [selection meaning](../leandb/LeanDb/Select.lean), and predicate theorems such as [`approx_sound`](../leandb/LeanDb/Pred.lean). That theorem establishes that the approximated predicate does not exclude rows accepted by the original predicate. It is not a proof of SQL execution fidelity or private-data confinement.

For general queries, fetching candidates and evaluating a residual Lean predicate is useful. For a protected repository, the authorization restriction must be mandatory before rows become available to application code. A planner must not weaken an ownership predicate into a broad fetch followed by filtering. Define an authorized source or compulsory scope predicate that every candidate plan preserves. Apply counting, sorting, joins, search, pagination, and export within that authorized relation.

The query correctness obligation must include both soundness and completeness, along with specified ordering and multiplicity. Returning only permitted rows is insufficient if valid rows disappear, a count includes hidden rows, or a page changes because of someone else's private data. Connect the Lean reference meaning to rendering, bound parameters, row reconstruction, and the assumptions made about SQLite. Differential tests help validate this connection while its proofs are incomplete.

For writes, introduce an application-facing operation with a contract like this design notation:

```text
commit(resource, expectedRevision, requestIdentity, authorizedTransition)
  → committed(newRevision, receipt) | conflict | classifiedFailure
```

The commit atomically checks the authoritative revision, validates the transition against the relevant state and authority, records its events, advances the revision, and stores the receipt. Repeating the same identified request returns the recorded outcome without reapplying the effect. Bind request identity to caller and operation, detect reuse with a different payload, and define the retention period of this guarantee. Returning a cached private response still requires current delivery authority.

One concrete LeanChess issue matters here. Its event list is a LeanDB child table, while [`update`](../leandb/LeanDb/Db.lean) compares the parent's own columns and then replaces child lists. An event-list change alone need not change those parent columns. The current process-wide mutex serializes this service, but the pure `cas` theorems in `domain/Semantics.lean` do not establish a database guard against another writer. A revision participating in the atomic parent update, or a suitable serialized transaction protocol covering the whole state, must connect the actual write to the concurrency claim.

## HTTP, channels, and jobs: cover the whole reachable execution

LeanChess currently serves requests through `Std.Http`. The sibling [LeanHttp](../leanhttp/README.md) supplies an HTTP/WebSocket client; it is not the server's authorization layer. Keep protocol mechanics in their hosts and application policy in LeanApp, with adapters connecting them.

A single application description should determine exposed operations, routes, codecs, policies, and proof obligations. Cover malformed requests, method and identity mismatches, unknown routes, health and manifest endpoints, static assets, and error paths. Administrative or generic database listeners must be separately scoped; they cannot quietly create a second path into application data outside the declared proof boundary.

Replace arbitrary error strings with deliberate public error values and separately classified diagnostics. Trace errors through status codes, headers, and logs as well as response bodies. Parsing and request limits are part of the host contract, while privacy requires evidence that their observable behavior fits the declared model.

The existing [channel bindings](../leanreact/engine/LeanApp/Channel.lean) already apply policy to subscription and inbound operations. Extend the delivery contract to recipient authorization, revocation, snapshots, stream revisions, replay, and reconnects. Use the same application command whether it arrives by HTTP, a socket, or an authorized job.

Commit and publication need a shared failure story. An in-memory after-commit callback can be lost if a process fails after the database commit. For promised recoverable delivery, record an outbox entry in the same durable transaction as the domain event, then deliver and deduplicate according to a stated protocol. Network delivery may repeat; the application can still apply one identified effect once. Do not promise unconditional exactly-once delivery.

In LeanChess, `lookAt` currently triggers the bot's move. Make looking a semantic query and schedule the bot as an explicit actor responding to committed game state. Its proposed move goes through the same authority and revision checks as a human move. Jobs need their own authority, retry identity, and observable effects.

## Time and scheduling: make the environment explicit

Introduce clock observations into the application contract, with a declared choice of when a command is timed: arrival, admission, or another specified point. That choice affects game results under load and must agree with the ordering used to commit moves. Client-estimated time can animate a display; it must not authorize a server-side clock transition.

Recovery also needs a clock policy. LeanChess persists values from `IO.monoMsNow`; such readings cannot simply be treated as a universal durable epoch across reboot or movement between machines. Specify how elapsed durations, deadlines, restart, and downtime relate, then implement and test that conversion at the boundary.

The native runtime already has writer admission and reader-pool mechanisms. State which consistency and progress properties each execution mode supplies. A policy read followed by a write on another lane needs a transaction or revalidation rule if the relevant facts may change between them.

Model overload, cancellation, and uncertain completion. A caller disconnecting after commit does not undo an accepted action. A timed-out request may need receipt lookup before retry. Bounded queues and cost budgets help meet performance goals, but latency guarantees must retain their workload and hardware assumptions.

## LeanReact and LeanJS: connect interaction to authoritative meaning

LeanReact already provides typed components and action machinery, while [its compiler integration](../leanreact/engine/LeanReact/Compiler.lean) maps operations to JavaScript runtime intrinsics. LeanChess uses it for the interface but supplies the API bridge manually.

Make view models explicit projections of authorized application state. Generate typed command calls from the application contract. Keep public, owner-private, and session-local values distinct through the client cache and rendering path. Logout or a change of principal must invalidate private state and cancel delivery from the previous session.

Give responses a revision and a session identity sufficient to reject stale delivery. LeanChess currently orders watched updates by ply; offers, endings, and other state changes can share a ply. A complete application revision can order these changes, and a separate request/session generation can prevent a response from an old game or account replacing the current view. Time-dependent views also need the server observation time: two clock readings can differ without a new committed revision.

For local legality checks or other shared domain computations, define the LeanJS subset whose semantics are supported and the obligations of each runtime intrinsic. Exact integers, constructor layouts, strings, exceptions, and evaluation order matter. ABI compatibility and a matching manifest are useful checks, but neither proves the generated JavaScript computes the Lean function. Begin with small portable kernels and comparison tests; expand preservation proofs without implying the whole browser has been verified.

The server remains the authority for accepted actions. Optimistic rendering can be supported with a reconciliation contract. UI responsiveness can improve independently of commit semantics when the distinction is explicit.

## Proof tooling and optimization: make the evidence composable

The build should produce an evidence inventory for the assembled application: domain invariants, operation proofs, route coverage, adapter obligations, compiler assumptions, and unmodeled observations. Distinguish proved claims, tested mechanisms, explicit assumptions, and open work. Include theorem dependency auditing and the identity of the source and generated artifacts those claims concern.

Extend the existing LeanApp test harness and example proofs rather than treating examples as universal coverage. Add counterexamples for unauthorized callers, malformed values, retries, concurrent updates, recovery, and secret-dependent outputs. Bind those checks to the same operation registry used by the host. A new route, compiler intrinsic, or raw native escape must be visible in the evidence inventory.

Keep a simple reference interpretation while optimizing execution. Incremental game state should equal replay at its committed revision. Query indexes and cached views should match their reference queries. Cache keys and invalidation must include the authority and policy dependencies relevant to private results. State-dependent optimizations must preserve confidentiality as well as returned values; ordinary single-execution trace refinement alone is insufficient to establish that relational claim.

For speed, measure the compiled path: request parsing, authorization, queueing, database work, domain computation, and delivery. Prove cost bounds where the model supports them, and use benchmarks to compare correct candidates. The existing `Deep` and `Lazier` evaluators are candidates for study, not interchangeable engines until their relevant equivalence properties have been established.

## A practical order of work

1. **Define the shared semantic boundary.** Specify principals, observations, operation outcomes, revisions, and a small effect vocabulary. Keep chess facts independent. Deliver a reference interpreter and a written inventory of assumptions.
2. **Connect one privacy operation end to end.** Reuse the private-notes specification and grants, strengthen the protected repository contract, and cover its codec, route, response, and native adapter. Record exactly which confidentiality claims are proved and which remain conditional.
3. **Connect one chess command end to end.** Move `Play` through LeanApp with seat evidence and authoritative time. Implement a revisioned atomic commit with request receipts. Relate the accepted stored event to the pure transition.
4. **Cover the entire reachable application.** Migrate the remaining routes, errors, jobs, and channels. Produce route coverage and a checked application-level composition of the established properties.
5. **Generate clients and add recoverable delivery.** Remove the manual wire bridge, order views by revision, and connect publication to committed state. Validate reconnect, revocation, and crash behavior under the declared contracts.
6. **Optimize within those contracts.** Introduce incremental state, narrower locking, query plans, and caching as separately evidenced implementations. Expand compiler and substrate proofs as the remaining trust boundary becomes clear.

Each step should deliver a usable vertical slice and name the guarantee it adds. The connecting pieces have reached their intended role when a domain author can change a rule, see the affected obligations, and obtain a fast implementation without having to rediscover the semantics of storage, identity, transport, and UI execution.
