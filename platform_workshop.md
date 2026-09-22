# Workshop: shared meaning across web, iOS, and Android

Theoric should let us reuse an application's meaning without pretending every execution environment behaves alike. Extending LeanReact to React Native is a good test: the chess rules, user intentions, and application policies should survive the move; DOM conventions should not accidentally become universal laws.

The principle is: **share intentions; require evidence for each realization.** A platform difference should become an explicit implementation obligation, an explicit product decision, or a compile-time incompatibility. It should not silently disappear behind a common method name.

This extends the [general vision](theoric_vision.md) and the [typed-substrate workshop](substrate_workshop.md). The accompanying [Lean examples](workshop/Platforms.lean) compile independently:

```sh
lake env lean workshop/Platforms.lean
```

They are reference models, not an implemented React Native backend. The file includes positive examples, proofs, executable checks, and nine intentional negative compilation checks. Expected diagnostics are printed even when the command succeeds. No custom axioms or `sorry` declarations are introduced.

## Three examples, three platforms, several interaction modalities

| Example | Shared meaning | Browser realization | iOS realization | Android realization |
|---|---|---|---|---|
| Interaction | A named, enabled action delivers the intended command through every required input modality | Semantic controls; keyboard, pointer, and assistive activation | Native controls, touch and assistive activation, native text containment | Native controls, touch and assistive activation, native text containment |
| Session recovery | Stored material is a candidate for validation, not authority; recovery obeys the selected policy | Browser/server session protocol | Configured protected store with retention and recovery obligations | Configured protected store with retention, backup, and recovery obligations |
| Lifecycle | Attention and freshness determine whether an interaction is currently permitted | Visibility and focus observations | Active, inactive, and background observations | Foreground state plus separate focus/blur observations |

Platform and modality are separate axes. A phone can have a hardware keyboard; a browser can have touch input. The model's small input sets are examples of declared support, not claims that native devices lack other input methods. A production target should combine OS, runtime version, configuration, and supported modalities.

## 1. One semantic action, different interaction and rendering rules

Consider “Confirm this move.” The domain command does not change because the user clicks, presses Enter, taps, or activates a control with assistive technology.

The shared contract in the prototype is:

```lean
structure ActivationAdapter (Source Command : Type) where
  activate : ActionSpec Command → Source → Option Command
  preserves : ∀ spec source, activate spec source = intended spec
```

`ActionSpec` carries a nonempty accessible name, an enabled flag, and an application-supplied command. `intended` returns that command when enabled and no command otherwise. Every declared activation source must have this behavior. The mechanism knows nothing about chess: a reservation or document editor supplies a different command type.

This is stronger than requiring handlers to exist. A touch-only adapter that exhaustively handles assistive activation by returning `none` has the right function type, but cannot satisfy the law. The example proves that contradiction and includes a rejected adapter construction. Conversely, always emitting a command would violate disabled behavior.

For React Native, custom accessibility actions require declaration and handling; its standard activation action is intended to perform the same action with or without assistive technology. That is an excellent candidate for a semantic equality obligation. [React Native accessibility](https://reactnative.dev/docs/accessibility).

Rendering has its own target-specific grammar. React Native requires raw text to be contained in a `Text` component, rather than placed directly under `View`. The prototype represents this with `NativeNode context`: raw strings inhabit the text context, while `Text` wraps them into a layout node. A raw string under a layout container is rejected by Lean. Shared `label` intent can lower to an appropriate tree on each target. [React Native Text](https://reactnative.dev/docs/text).

The browser has a different temporal obligation. Existing LeanReact documents that browser default cancellation must happen synchronously; an asynchronous cancellation result is too late. The proposed `Dispatch Work` separates an immediate default decision from deferred work. Lean rejects putting an `IO DefaultDecision` in the immediate field. This is a type-level improvement over the current `KeyEvent → Action KeyOutcome` shape. See the local [runtime contract](../leanreact/engine/runtime/README.md) and [Core definitions](../leanreact/engine/LeanReact/Core.lean).

That does not mean manually duplicating built-in button behavior. Prefer native semantic controls and normalize their activation. The actual bridge must establish that a physical gesture produces the intended normalized event, without duplicate activation, and consumes the immediate decision before yielding. The prototype proves behavior *after* normalization, not the raw browser or OS event trace. UI enabledness also does not replace server-side authorization.

An especially revealing extension is modal dismissal. Android modal closure uses `onRequestClose`, and ordinary `BackHandler` events are not emitted while the modal is open. On iOS, swipe-dismiss configuration can make the callback occur after dismissal. A future contract should distinguish `beforeDismiss` from `afterDismiss`; an after-the-fact notification cannot implement a product requirement to obtain confirmation before closing. The compiler should demand a different presentation strategy or an explicit policy change. This extension is a design sketch, not part of the checked prototype. [React Native Modal](https://reactnative.dev/docs/modal).

## 2. “Remember my session” is not one portable key-value operation

Suppose our future identity model adds two requirements: credentials must use an approved persistence strategy, and a fresh installation must not silently inherit the previous installation's session. Those are selected application policies, not universal facts about sessions or storage.

Real differences matter:

- React Native's AsyncStorage is unencrypted, and the React Native guidance excludes tokens and secrets from its intended uses. [React Native security](https://reactnative.dev/docs/security).
- Expo SecureStore documents different reinstall behavior: Android entries are removed, while iOS keychain entries may remain. It also documents biometric invalidation and Android backup exclusions. These are properties of a particular adapter and configuration, not one universal `secureStorage` capability. [Expo SecureStore](https://docs.expo.dev/versions/latest/sdk/securestore/).
- A browser can use an HTTP-only cookie session protocol without exposing the cookie value to application JavaScript. That is not the same interface as reading a native token. HTTP-only cookies still accompany appropriate JavaScript-initiated requests; the application needs a complete session/request policy, not just this flag. [MDN Set-Cookie](https://developer.mozilla.org/en-US/docs/Web/HTTP/Reference/Headers/Set-Cookie).

The shared operation should therefore be closer to “attempt to resume this session” than “get the token as a string.” Browser and native implementations can realize that intention differently. The checked storage example explores native profile selection; it does not implement the browser protocol or authentication.

Its `Profile` declares protection and reinstall behavior. `Policy` supplies the acceptable-profile predicate and whether fresh-install separation is required. `Plan policy profile` requires evidence that the chosen profile is acceptable and that its recovery strategy satisfies the policy-dependent retention obligation.

The same query machinery produces different answers for two policies: credential persistence admits two protected profiles, whereas ordinary preferences admit all three example profiles. Preferences can also permit retained state. Nothing about the generic selector needs to know what a credential or preference means.

For the strict session policy, Lean rejects an unprotected profile and rejects an iOS retention-aware plan that omits installation checking. The shared recovery function distinguishes a candidate, absent-or-invalidated data, and temporary unavailability. Omitting unavailability is a compilation error. A candidate from the wrong installation is proved to be rejected when installation checking is selected; matching material merely proceeds to server verification.

These are intentionally modest guarantees. The profile values are declared model inputs, not proofs of native encryption or deletion. Installation identifiers also need their own provenance, persistence, and backup contract; an identifier restored alongside the credential would defeat the intended separation. Native error translation must not invent distinctions the host cannot observe. Device unlock is not application-user authentication, and deleting a local credential is not server-side revocation.

A real backend would connect each profile claim to the [property registry's evidence model](substrate_workshop.md): established in a model, conditional on named host assumptions, tested, unknown, or refuted. A manifest saying `osProtected` cannot by itself establish confidentiality. Backup configuration and the compiled artifact must participate in the evidence chain.

## 3. A live chess board across focus loss, suspension, and recovery

The shared application intention might be: “accept a new move only while the user is interacting with a current view.” Foreground status alone is insufficient to express that intention.

React Native distinguishes iOS `inactive` from `active` and `background`. On Android, pulling down the notification drawer can emit `blur` without changing AppState. Initial state may also be unavailable in the legacy architecture. These differences should be inputs to a declared lifecycle model, not scattered checks that every feature author must remember. [React Native AppState](https://reactnative.dev/docs/appstate).

The prototype separates platform event types from shared state:

```text
platform event → declared interpretation → attention + freshness + generation
```

Web visibility and focus remain separate. iOS active/inactive observations have their own interpretation. Android foreground and focus remain separate, so another foreground observation does not silently undo an earlier blur. Unknown observations conservatively remove permission to interact. These are explicit product-selected interpretations of the modeled signals.

The shared reducer invalidates freshness and advances a generation after each delivered lifecycle change. Interaction requires foreground, focus, and a synchronized view. A returned snapshot is accepted only for the current generation.

Lean checks that:

- Every modeled lifecycle change requires resynchronization before interaction.
- An Android blur removes focus even while foreground remains true.
- A late response from an old generation is rejected.
- Resynchronization does not itself restore focus.
- An iOS mapping missing `inactive` is incomplete.
- An Android adapter that receives `blur` but maps it to “foreground” violates the declared interpretation. A separate theorem refutes that adapter's preservation law.

The event vocabulary and its meaning remain parameters at the adapter boundary. Another domain can choose a different policy: a music player may continue playback when backgrounded while disabling foreground-only controls. That is a different requirement, not a reason to make the lifecycle facts false.

The prototype is conservative: even a repeated lifecycle observation invalidates work. It does not prove reconnection progress, real network freshness, or delivery of every OS event. A production adapter needs initial snapshots, subscription ordering, cleanup, event-loss assumptions, and a policy for repeated observations. Generation identity must also cover relevant account, game, and mount changes—not just focus changes.

For chess clocks, the corresponding intention is an authoritative deadline, not an assumption that a UI timer executes once per second. Resume should re-establish the current view and clock relation. That extension requires an explicit clock model and is not proved here.

## What this asks of LeanReact and the compiler

The current implementation has useful separation, but some browser assumptions are still embedded in the connecting pieces:

| Current piece | Upgrade motivated by these examples |
|---|---|
| [DOM props and string-valued styles](../leanreact/engine/LeanReact/DOM.lean) | Keep them as a browser-specific API. Add shared semantic components and target-specific typed trees/props, rather than declaring all DOM props portable. |
| [Core event and action types](../leanreact/engine/LeanReact/Core.lean) | Separate immediate event decisions from deferred effects; specify activation meaning and handle lifetime obligations. |
| [Compiler intrinsic mappings](../leanreact/engine/LeanReact/Compiler.lean) | Index binding sets by target/configuration and connect bindings to contracts. Names and arities alone do not establish behavior. |
| [Browser-aware channel runtime](../leanreact/engine/runtime/channels.mjs) | Inject a lifecycle/attention interpreter and scheduler with declared behavior instead of depending directly on document visibility. |
| [LeanChess UI generation](ui/Generate.lean) | Assemble a release from explicit per-target adapters and evidence, instead of selecting only a JavaScript module path. |

React Native already provides platform-specific modules and fallback selection. The proposed extra layer is not another spelling of platform selection: it is an obligation to show why the chosen implementation satisfies the application's requirements on that target. [React Native platform-specific code](https://reactnative.dev/docs/platform-specific-code).

In Lean, dependent functions can require an adapter for every declared target; indexed inductive types can rule out invalid host trees; proof fields can connect handlers to meaning; and decidable predicates can query concrete profile compatibility. Type classes are useful for shared lawful interfaces, but consequential backend and policy choices should remain explicit. Different domains supply their own specifications rather than being squeezed into one fixed global contract list.

Do not rely on exhaustiveness alone. A wildcard can absorb a new platform or event, and a no-op can satisfy an ordinary function signature. Behavioral laws must quantify over the supported cases. Adding a target then requires an implementation and evidence; changing a policy rechecks the affected plans; adding a host behavior rechecks interpretations and preservation proofs. If a generic implementation genuinely satisfies the new obligation unchanged, it should remain valid.

The next practical slice is a semantic action component and a lifecycle port, with web and native reference interpreters, followed by an actual React Native bridge. Track the exact host dependencies and configuration, test event normalization on devices, and state any remaining host/compiler assumptions. Arbitrary foreign components, raw JavaScript, and unrestricted IO cannot be permitted to bypass these boundaries while retaining the same whole-application guarantee.

The outcome we want is not identical UI code everywhere. It is one understandable application meaning, with the compiler showing exactly where a new platform still owes us an implementation, a product decision, or evidence.
