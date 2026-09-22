import Std

/-!
Three isolated cross-platform design experiments, not a React Native implementation.
Run: lake env lean workshop/Platforms.lean
The #check_failure commands are intentional negative compilation tests.
-/
namespace Theoric.PlatformWorkshop

inductive Target where
  | web | ios | android
  deriving Repr, BEq, DecidableEq

/-! 1. Shared intentions, platform-specific input and tree grammars. -/
namespace Interaction

inductive WebActivation where
  | pointer | keyboard | assistive
  deriving DecidableEq

inductive NativeActivation where
  | press | assistive
  deriving DecidableEq

/-- Normalized activation sources, NOT raw OS events or the complete device input space. -/
def Input : Target → Type
  | .web => WebActivation
  | .ios | .android => NativeActivation

structure ActionSpec (Command : Type) where
  label : String
  named : label ≠ ""
  enabled : Bool
  command : Command

def intended (spec : ActionSpec Command) : Option Command :=
  if spec.enabled then some spec.command else none

/-- The contract is parameterized by the application's command type. -/
structure ActivationAdapter (Source Command : Type) where
  activate : ActionSpec Command → Source → Option Command
  preserves : ∀ spec source, activate spec source = intended spec

def sharedActivation (Source Command : Type) : ActivationAdapter Source Command where
  activate := fun spec _ => intended spec
  preserves := by intros; rfl

/-- One adapter for EVERY member of the declared release target set. -/
abbrev Release (Command : Type) := (target : Target) → ActivationAdapter (Input target) Command

def release (Command : Type) : Release Command
  | .web => sharedActivation WebActivation Command
  | .ios => sharedActivation NativeActivation Command
  | .android => sharedActivation NativeActivation Command

def confirm : ActionSpec Nat := ⟨"Confirm move", by decide, true, 42⟩

def touchOnly (spec : ActionSpec Nat) : NativeActivation → Option Nat
  | .press => intended spec
  | .assistive => none

theorem touchOnly_not_semantic :
    ¬ (∀ spec source, touchOnly spec source = intended spec) := by
  intro h
  have impossible := h confirm .assistive
  simp [touchOnly, intended, confirm] at impossible

-- A complete match with a no-op branch still fails the behavioral obligation.
#check_failure (show ActivationAdapter NativeActivation Nat from
  { activate := touchOnly, preserves := by intros; rfl })

-- A target is not silently supplied by a default/fallback backend.
#check_failure (show Release Nat from fun
  | .web => sharedActivation WebActivation Nat
  | .ios => sharedActivation NativeActivation Nat)

inductive Context where
  | layout | text

/-- A deliberately small native tree grammar: raw text belongs only in Text. -/
inductive NativeNode : Context → Type where
  | raw : String → NativeNode .text
  | text : List (NativeNode .text) → NativeNode .layout
  | view : List (NativeNode .layout) → NativeNode .layout

def nativeLabel (value : String) : NativeNode .layout := .text [.raw value]
def nativePanel : NativeNode .layout := .view [nativeLabel "Your turn"]

#check_failure (show NativeNode .layout from .view [.raw "Your turn"])

-- Browser default decisions must be available before deferred work begins.
inductive DefaultDecision where
  | continue | prevent
  deriving DecidableEq

structure Dispatch (Work : Type) where
  immediate : DefaultDecision
  deferred : Work

def intercept (work : IO Unit) : Dispatch (IO Unit) := ⟨.prevent, work⟩
#check_failure (show Dispatch (IO Unit) from
  { immediate := (pure .prevent : IO DefaultDecision), deferred := pure () })

#guard (release Nat .web).activate confirm .keyboard == some 42
#guard (release Nat .android).activate confirm .assistive == some 42
#guard (release Nat .ios).activate { confirm with enabled := false } .press == none

end Interaction

/-! 2. Storage profiles drive selection and additional recovery obligations. -/
namespace Persistence

inductive Protection where
  | unprotected | osProtected
  deriving Repr, BEq, DecidableEq

inductive Reinstall where
  | removed | mayRemain
  deriving Repr, BEq, DecidableEq

/-- These are declarative model inputs, not attestations about real storage. -/
structure Profile where
  target : Target
  protection : Protection
  reinstall : Reinstall
  deriving Repr, DecidableEq

def iosSecure : Profile := ⟨.ios, .osProtected, .mayRemain⟩
def androidSecure : Profile := ⟨.android, .osProtected, .removed⟩
def androidPlain : Profile := ⟨.android, .unprotected, .removed⟩

structure Policy where
  accepts : Profile → Prop
  decideAccepts : DecidablePred accepts
  freshInstall : Bool

def credentials : Policy :=
  ⟨fun p => p.protection = .osProtected, inferInstance, true⟩

def ordinaryPreferences : Policy := ⟨fun _ => True, inferInstance, false⟩

def candidates (policy : Policy) (profiles : List Profile) : List Profile :=
  profiles.filter fun p => @decide (policy.accepts p) (policy.decideAccepts p)

inductive InstallBinding where
  | checkCurrentInstall | unchecked
  deriving Repr, BEq, DecidableEq

structure Plan (policy : Policy) (profile : Profile) where
  accepted : policy.accepts profile
  binding : InstallBinding
  handlesRetention : policy.freshInstall = true →
    profile.reinstall = .mayRemain → binding = .checkCurrentInstall

def iosPlan : Plan credentials iosSecure :=
  ⟨rfl, .checkCurrentInstall, by intros; rfl⟩

def androidPlan : Plan credentials androidSecure :=
  ⟨rfl, .unchecked, by intro _ h; cases h⟩

-- A different domain policy intentionally permits retained, non-sensitive preferences.
def preferencesPlan : Plan ordinaryPreferences iosSecure :=
  ⟨True.intro, .unchecked, by intro h; cases h⟩

#check_failure (show Plan credentials androidPlain from
  ⟨rfl, .unchecked, by intro _ h; cases h⟩)

#check_failure (show Plan credentials iosSecure from
  ⟨rfl, .unchecked, by intros; rfl⟩)

#guard (candidates credentials [iosSecure, androidSecure, androidPlain]).length == 2
#guard (candidates ordinaryPreferences [iosSecure, androidSecure, androidPlain]).length == 3

/-- IDs are symbolic: stored material is only a candidate, not an authenticated user. -/
structure StoredCandidate where
  installation : Nat
  reference : Nat
  deriving DecidableEq

inductive RestoreOutcome where
  | candidate : StoredCandidate → RestoreOutcome
  | absentOrInvalidated
  | unavailable
  deriving DecidableEq

inductive NextStep where
  | verifyWithServer : Nat → NextStep
  | signIn | retryLater
  deriving BEq, DecidableEq

def restore (binding : InstallBinding) (currentInstall : Nat) : RestoreOutcome → NextStep
  | .candidate value =>
    if binding = .checkCurrentInstall ∧ value.installation ≠ currentInstall then .signIn
    else .verifyWithServer value.reference
  | .absentOrInvalidated => .signIn
  | .unavailable => .retryLater

theorem foreign_install_rejected (current : Nat) (value : StoredCandidate)
    (h : value.installation ≠ current) :
    restore .checkCurrentInstall current (.candidate value) = .signIn := by
  simp [restore, h]

-- Losing the distinction between absent and unavailable is an explicit policy change.
#check_failure (show RestoreOutcome → NextStep from fun
  | .candidate value => .verifyWithServer value.reference
  | .absentOrInvalidated => .signIn)

#guard restore iosPlan.binding 2 (.candidate ⟨1, 99⟩) == .signIn
#guard restore iosPlan.binding 2 (.candidate ⟨2, 99⟩) == .verifyWithServer 99
#guard restore androidPlan.binding 2 .unavailable == .retryLater

end Persistence

/-! 3. Distinct lifecycle events refine a shared attention/freshness state machine. -/
namespace Lifecycle

inductive WebEvent where
  | visible | hidden | focus | blur | unknown
  deriving DecidableEq
inductive IOSEvent where
  | active | inactive | background | unknown
  deriving DecidableEq
inductive AndroidEvent where
  | active | background | focus | blur | unknown
  deriving DecidableEq

def Event : Target → Type
  | .web => WebEvent
  | .ios => IOSEvent
  | .android => AndroidEvent

inductive Change where
  | foreground : Bool → Change
  | focus : Bool → Change
  | both : Bool → Bool → Change
  | unknown
  deriving DecidableEq

/-- A product-selected interpretation of the declared host event model. -/
def meaning : (target : Target) → Event target → Change
  | .web, .visible => .foreground true
  | .web, .hidden => .both false false
  | .web, .focus => .focus true
  | .web, .blur => .focus false
  | .web, .unknown => .unknown
  | .ios, .active => .both true true
  | .ios, .inactive => .focus false
  | .ios, .background => .both false false
  | .ios, .unknown => .unknown
  | .android, .active => .foreground true
  | .android, .background => .both false false
  | .android, .focus => .focus true
  | .android, .blur => .focus false
  | .android, .unknown => .unknown

structure Adapter (HostEvent : Type) (spec : HostEvent → Change) where
  decode : HostEvent → Change
  preserves : ∀ event, decode event = spec event

def reference (target : Target) : Adapter (Event target) (meaning target) :=
  ⟨meaning target, by intros; rfl⟩

structure State where
  foreground : Bool
  focused : Bool
  synchronized : Bool
  generation : Nat
  deriving BEq, DecidableEq

def initial : State := ⟨false, false, false, 0⟩

/-- Conservative policy: every delivered lifecycle change invalidates prior work. -/
def step (state : State) (change : Change) : State :=
  let next := { state with synchronized := false, generation := state.generation + 1 }
  match change with
  | .foreground active => { next with foreground := active }
  | .focus focused => { next with focused }
  | .both active focused => { next with foreground := active, focused }
  | .unknown => { next with foreground := false, focused := false }

def canInteract (state : State) : Bool :=
  state.foreground && state.focused && state.synchronized

def deliver (target : Target) (state : State) (event : Event target) : State :=
  step state ((reference target).decode event)

def acceptSnapshot (state : State) (replyGeneration : Nat) : Option State :=
  if replyGeneration = state.generation then some { state with synchronized := true }
  else none

theorem old_reply_rejected (state : State) (old : Nat) (h : old ≠ state.generation) :
    acceptSnapshot state old = none := by simp [acceptSnapshot, h]

theorem change_requires_resync (state : State) (change : Change) :
    canInteract (step state change) = false := by
  cases change <;> simp [canInteract, step]

theorem android_blur_loses_focus (state : State) :
    (deliver .android state .blur).focused = false := rfl

def ignoresAndroidBlur : AndroidEvent → Change
  | .blur => .foreground true
  | event => meaning .android event

theorem ignoresAndroidBlur_not_semantic :
    ¬ (∀ event, ignoresAndroidBlur event = meaning .android event) := by
  intro h
  have impossible := h .blur
  cases impossible

#check_failure (show Adapter AndroidEvent (meaning .android) from
  ⟨ignoresAndroidBlur, by intro event; cases event <;> rfl⟩)

#check_failure (show IOSEvent → Change from fun
  | .active => .both true true
  | .background => .both false false
  | .unknown => .unknown)

def ready : State := ⟨true, true, true, 7⟩
def blurred : State := deliver .android ready .blur

#guard !canInteract blurred
#guard blurred.foreground
#guard !(deliver .android blurred .active).focused
#guard acceptSnapshot blurred 7 == none
#guard (acceptSnapshot blurred blurred.generation).isSome
-- A fresh reply does not restore attention when the app is still blurred.
#guard !(canInteract { blurred with synchronized := true })

end Lifecycle

#print axioms Interaction.touchOnly_not_semantic
#print axioms Persistence.foreign_install_rejected
#print axioms Lifecycle.old_reply_rejected
#print axioms Lifecycle.change_requires_resync
#print axioms Lifecycle.ignoresAndroidBlur_not_semantic

end Theoric.PlatformWorkshop
