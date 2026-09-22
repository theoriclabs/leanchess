import Std

/-! A small embedded language for user stories. No product or execution substrate imports. -/
namespace UserStories

structure Vocabulary where
  Actor : Type
  State : Type
  Intention : Type
  Observation : Intention → Type

/-- The observation type may depend on the intention. -/
abbrev Semantics (v : Vocabulary) :=
  v.Actor → v.State → (intent : v.Intention) → v.Observation intent → v.State → Prop

/-- Flows choose subsequent intentions from observations, not hidden state.
There is deliberately no assertion/filter constructor that could discard a bad run. -/
inductive Flow (v : Vocabulary) (Result : Type) where
  | done : Result → Flow v Result
  | request (actor : v.Actor) (intent : v.Intention)
      (next : v.Observation intent → Flow v Result) : Flow v Result

def Flow.bind (flow : Flow v α) (next : α → Flow v β) : Flow v β :=
  match flow with
  | .done value => next value
  | .request actor intent continuation =>
      .request actor intent fun observation => (continuation observation).bind next

instance : Monad (Flow v) where
  pure := .done
  bind := Flow.bind

def ask (actor : v.Actor) (intent : v.Intention) : Flow v (v.Observation intent) :=
  .request actor intent .done

/-- A completed semantic run, not a scheduling or latency model. -/
inductive Run (semantics : Semantics v) : Flow v α → v.State → α → v.State → Prop where
  | done (value) (state) : Run semantics (.done value) state value state
  | request {actor intent next before observation middle result after}
      (first : semantics actor before intent observation middle)
      (later : Run semantics (next observation) middle result after) :
      Run semantics (.request actor intent next) before result after

/-- At every step, a response exists and EVERY permitted response must continue to
satisfy the outcome. This is stronger than checking only successful completed runs. -/
def Guarantees (semantics : Semantics v) : Flow v α → v.State → (α → v.State → Prop) → Prop
  | .done value, state, outcome => outcome value state
  | .request actor intent next, state, outcome =>
      (∃ observation after, semantics actor state intent observation after) ∧
      ∀ observation after, semantics actor state intent observation after →
        Guarantees semantics (next observation) after outcome

theorem guarantees_sound {v : Vocabulary} {semantics : Semantics v}
    {flow : Flow v α} {before after : v.State} {result : α} {outcome : α → v.State → Prop}
    (guaranteed : Guarantees semantics flow before outcome)
    (run : Run semantics flow before result after) : outcome result after := by
  induction run with
  | done => exact guaranteed
  | request first later ih => exact ih (guaranteed.2 _ _ first)

theorem guarantees_possible {v : Vocabulary} {semantics : Semantics v}
    {flow : Flow v α} {before : v.State} {outcome : α → v.State → Prop}
    (guaranteed : Guarantees semantics flow before outcome) :
    ∃ result after, Run semantics flow before result after := by
  induction flow generalizing before with
  | done value => exact ⟨value, before, .done value before⟩
  | request actor intent next ih =>
      obtain ⟨observation, middle, first⟩ := guaranteed.1
      obtain ⟨result, after, later⟩ := ih observation (guaranteed.2 observation middle first)
      exact ⟨result, after, .request first later⟩

/-- Laws are open-ended predicates. Privacy, invariants, progress, and refinement
do not have to masquerade as the postcondition of one example journey. -/
structure Law (Subject : Type) where
  id : String
  description : String
  holds : Subject → Prop

structure Story (v : Vocabulary) (Result : Type) where
  id : String
  asA : v.Actor
  iWant : String
  soThat : String
  given : v.State → Prop
  scenario : Flow v Result
  ensures : v.State → Result → v.State → Prop
  laws : List (Law (Semantics v)) := []

/-- Evidence is indexed by the exact story AND semantics. A feasible starting
state is required, so an impossible Given clause cannot certify a story vacuously. -/
structure Certified (semantics : Semantics v) (story : Story v α) : Prop where
  feasible : ∃ state, story.given state
  fulfilled : ∀ before, story.given before →
    Guarantees semantics story.scenario before (story.ensures before)
  lawsHold : ∀ law ∈ story.laws, law.holds semantics

theorem Certified.outcome {v : Vocabulary} {semantics : Semantics v}
    {story : Story v α} (certificate : Certified semantics story)
    {before after : v.State} {result : α} (given : story.given before)
    (run : Run semantics story.scenario before result after) : story.ensures before result after :=
  guarantees_sound (certificate.fulfilled before given) run

theorem Certified.hasRun {v : Vocabulary} {semantics : Semantics v}
    {story : Story v α} (certificate : Certified semantics story)
    {before : v.State} (given : story.given before) :
    ∃ result after, Run semantics story.scenario before result after :=
  guarantees_possible (certificate.fulfilled before given)

def Invariant (semantics : Semantics v) (valid : v.State → Prop) : Prop :=
  ∀ actor before intent observation after, valid before →
    semantics actor before intent observation after → valid after

/-- The PRODUCT supplies what the observer is allowed to distinguish. -/
def Noninterference (semantics : Semantics v)
    (sameFor : v.Actor → v.State → v.State → Prop) : Prop :=
  ∀ actor left right intent observation leftAfter,
    sameFor actor left right → semantics actor left intent observation leftAfter →
    ∃ rightAfter, semantics actor right intent observation rightAfter ∧
      sameFor actor leftAfter rightAfter

/-- All requests in this flow are made by this actor, including every branch. -/
inductive Personal {v : Vocabulary} {α : Type} (actor : v.Actor) : Flow v α → Prop where
  | done (value) : Personal actor (.done value)
  | request {intent next} (rest : ∀ observation, Personal actor (next observation)) :
      Personal actor (.request actor intent next)

/-- Reusable lifting theorem: one-step noninterference gives noninterference for
finite, observation-dependent personal flows in ANY vocabulary. -/
theorem personal_flow_noninterference {v : Vocabulary} {semantics : Semantics v}
    {sameFor : v.Actor → v.State → v.State → Prop} {actor : v.Actor}
    {flow : Flow v α} {left right leftAfter : v.State} {result : α}
    (law : Noninterference semantics sameFor) (personal : Personal actor flow)
    (same : sameFor actor left right) (run : Run semantics flow left result leftAfter) :
    ∃ rightAfter, Run semantics flow right result rightAfter ∧
      sameFor actor leftAfter rightAfter := by
  induction run generalizing right with
  | done value state => exact ⟨right, .done value right, same⟩
  | request first later ih =>
      cases personal with
      | request rest =>
          obtain ⟨middle, firstRight, sameMiddle⟩ := law _ _ _ _ _ _ same first
          obtain ⟨last, laterRight, sameLast⟩ := ih (rest _) sameMiddle
          exact ⟨last, .request firstRight laterRight, sameLast⟩

def Eventually (history : Nat → State) (start : Nat) (goal : State → Prop) : Prop :=
  ∃ later, start ≤ later ∧ goal (history later)

end UserStories
