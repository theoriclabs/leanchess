# Sketch: private data across the complete API

This is a proposed first application of the [Theoric vision](theoric_vision.md). It describes proof obligations and an architectural direction. It is not an implemented privacy guarantee.

The intended policy is: a user's private application data can be read and received only under that user's authority. There is no administrator exception or implicit sharing in this first model. Authentication credentials are a separate class of secrets with a separate protocol; they are not ordinary profile data returned by this API.

Owner-only access is this application's chosen policy, not a rule hardcoded into the platform. Other domains can supply different authorization relations and permitted audiences to the same proof machinery. Evolving this policy requires revising its stated guarantee and rechecking the dependent proofs, adapters, and compatibility obligations, as described in the [contract evolution plan](connecting_pieces.md#reusable-machinery-evolving-contracts).

## Start with the meaning

We need a stable user identity, a principal making a request, an owner of each private resource, and an observation of what a recipient can learn. A display name, a chess seat, and a user identity are different concepts.

The first resource can be a private note belonging to a user. It has no intended influence on chess games or public profiles. This makes the initial confidentiality requirement precise without declaring existing game preferences private when they intentionally affect shared play.

The policy is simple:

```text
CanRead(principal, owner) := principal = AuthenticatedUser(owner)
CanWrite(principal, owner) := principal = AuthenticatedUser(owner)
```

Ownership is established when a resource is created. A submitted owner field cannot grant access or reassign someone else's resource. Missing resources, their contents, and private metadata all fall within the privacy policy.

We do not yet have a semantic account of authentication. The existing bearer-token lookup is an implementation mechanism, not a proof of identity. Initially, the application theorem must be conditional on an authentication contract: it supplies a valid principal bound to the incoming request and its response channel, under a defined session and revocation policy. An unauthenticated request has no user authority.

This makes the missing work visible. Proving that the application respects its principal does not prove that the identity mechanism assigns the right principal, that a credential cannot be stolen, or that the transport reaches the intended human.

## State two different guarantees

The first is access confinement. For every API execution, a logical read of a private resource must carry the authority of its owner:

```text
For every reachable execution trace t:
  ReadPrivate(request, owner, resource) occurs in t
    implies Principal(request) = AuthenticatedUser(owner).
```

Here a read means that application execution obtains the protected value. A storage engine may inspect physical pages while implementing an authorized operation; physical memory and disk access require a separate threat model. The application must not fetch all users' private records and then filter them.

The second is confidentiality of observations. A handler could legitimately read Alice's note on her behalf, write its length into public state, and let Bob retrieve the length later. The first theorem alone would permit that leak.

Define two worlds as equivalent for Bob when they agree on everything Bob may observe or access, including public state and his own private data. They may differ in Alice's note, its existence, and its private metadata. Under related inputs and the same permitted public environmental choices, Bob must receive indistinguishable observations from both executions. This is the proposed noninterference property.

Observations include response bodies, status codes, headers, redirects, message counts and logical ordering, subscription deliveries, and effects visible through later requests. Logs, exports, caches, and diagnostic endpoints are output channels too; their permitted audiences must be modeled. An error cannot reveal a private row merely because the successful response was filtered.

The theorem must cover sequences of requests and adversarial choices based on earlier responses. For a coalition, the observation is everything its members are authorized to see. Other users' actions must be related across the compared executions; the claim cannot prevent Alice from voluntarily copying her note into a public message herself.

The first proof should cover logical observations, with termination of modeled request handling established. It should explicitly exclude physical latency, cache behavior, traffic timing, and resource contention until there is a model and evidence for them. Secret-dependent timeout behavior cannot silently be treated as covered. A broader claim requires stronger execution contracts.

## Make every execution pass through the contract

Application programs should use a closed set of semantic operations. For this example, those operations include authenticating a request through the boundary, reading or writing an authorized private resource, reading public state, and delivering a result to an authorized recipient.

The following signatures are design notation, not compiled Lean declarations:

```text
readPrivate(context, owner, resource, proof of CanRead(context.principal, owner))
  → value protected for owner

replyPrivate(context, protectedValue, proof recipient is authorized)
  → delivery on the response channel bound to context
```

A handler cannot choose its authenticated context from request fields. The dispatcher constructs that context from the authentication result. The storage operation uses the authorized owner as part of its lookup, and authorization is evaluated against the session state at the defined operation boundary. Revocation and concurrent policy changes need an explicit ordering rule.

A protected-value wrapper is useful, but does not establish confidentiality by itself. Ordinary code could unwrap a value and branch on it. We need either an information-flow discipline with a proved soundness theorem, or direct proofs for the application programs that manipulate private values. Both data dependencies and control dependencies matter.

For the first slice, use a small restricted program representation and prove its semantics directly. Private reads can lead to owner-private replies and owner-private updates. There is no primitive for publishing their contents, deriving public counts from them, or sending them to arbitrary recipients. Any later release policy must be modeled explicitly and changes the theorem being promised.

The representation must have no arbitrary `IO`, raw SQL, filesystem, network, or unclassified logging escape inside application handlers. Those facilities belong in the interpreter, whose behavior has separate obligations. Import restrictions help enforce this architecture; they do not prove the interpreter correct.

## Connect the proof to the actual API

The proof boundary must include request decoding, dispatch, every reachable handler, error handling, persistence, and response encoding. A proof of one private-profile endpoint leaves other endpoints unconstrained.

Use a single route description to construct the dispatcher and enumerate its obligations. All methods, unknown routes, malformed inputs, and authentication failures must have modeled outcomes. Adding a route or an effect should make the application proof incomplete until the new case is discharged. Jobs and callbacks reachable from requests also belong to the execution model.

The evidence should be built in this order:

1. Define well-formed worlds, ownership, request authority, audiences, and observer equivalence. Show that authorized owners can successfully read their own resources, so the specification cannot be satisfied merely by refusing everyone.
2. Give each semantic operation a transition rule. Prove ownership preservation, authorized access, and preservation of observer equivalence for the relevant cases.
3. Prove those properties compose over the actual handler programs and arbitrary finite request traces. Include future observations of state changed by earlier requests.
4. Prove the complete dispatcher constructs only covered executions. Tie the theorem to the route definitions used to build the service.
5. Establish that storage, identity, and transport adapters realize their contracts. For confidentiality, this must preserve indistinguishability across executions, including the adapter's extra outputs and choices. Matching successful return values alone is insufficient.
6. Tie the source, generated artifacts, configuration, and deployed entry points to the checked application. Record any unproved compiler, runtime, driver, operating-system, or transport assumptions.

The final claim has a conditional form: under the named authentication, execution, and deployment assumptions, every execution exposed by this API satisfies access confinement and the stated observational confidentiality property. An assumption that the whole API preserves privacy would merely assume the desired result; boundary assumptions must describe specific facilities that can be independently examined and discharged.

## The first LeanChess slice

The sibling LeanReact repository already contains a useful precursor: [PrivateNotes.Model](../leanreact/examples/security/PrivateNotes/Model.lean) proves ownership, response provenance, and equality of modeled responses when session facts and authorized views agree. Its [native adapter](../leanreact/adapters/native/LeanAppNative/Notes.lean) implements scoped queries and checked row reconstruction. Reuse and extend that work. It does not yet supply the stronger whole-API trace claim proposed here; the [connecting-pieces plan](connecting_pieces.md) identifies the remaining connections.

Keep the chess domain independent. Introduce an application identity and policy model, a private-note resource, and an owner-only read/update operation. Provide a pure reference interpreter first, with model-level examples for Alice, Bob, and an unauthenticated caller. Then connect it to storage and the API through the stated contracts.

The current storage shape needs attention before making this claim: `api/Store.lean` puts names, tokens, and preferences in one `User` record, and lookup helpers load all users. `api/Service.lean` passes stored user records into handlers, while `api/Server.lean` renders database errors as strings. These are proof-boundary concerns even where no external disclosure has been demonstrated.

Separate public identity, authentication secrets, and private application data. Give each operation only the projection and authority it requires. Include all existing routes in the privacy analysis: an owner-only endpoint added beside unconstrained handlers is not sufficient.

Completion means having the two general theorems, positive owner-access behavior, complete route coverage, and an explicit account of the connection to execution. Examples and build success remain useful evidence, but must not be reported as that completion.

For proof auditing, record theorem dependencies rather than relying on a search for `sorry`. Lean exposes axiom dependencies, and native-evaluation proofs have a broader trust basis than ordinary kernel reduction. See the [Lean reference on axioms](https://lean-lang.org/doc/reference/latest/Axioms/). For a precedent in distinguishing functional correctness, confidentiality, and execution assumptions, see [seL4's proof descriptions](https://sel4.systems/Verification/proofs.html) and [assumptions](https://sel4.systems/Verification/assumptions.html). These inform the proposed discipline; they supply no proof about LeanChess.
