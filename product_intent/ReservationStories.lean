import UserStories

/-! A second product: reserve one shared slot. No chess imports or DSL changes. -/
namespace ReservationStoryBook
open UserStories

abbrev Person := Nat
abbrev State := Option Person

inductive Intention where
  | reserve | inspect

inductive Decision where
  | reserved | unavailable
  deriving DecidableEq

/-- Inspecting returns availability; reserving returns a decision. These are different types. -/
abbrev Observation : Intention → Type
  | .reserve => Decision
  | .inspect => Bool

abbrev vocabulary : Vocabulary where
  Actor := Person
  State := State
  Intention := Intention
  Observation := Observation

inductive Meaning (actor : Person) : State → (intent : Intention) → Observation intent → State → Prop where
  | reserve : Meaning actor none .reserve .reserved (some actor)
  | unavailable (owner) : Meaning actor (some owner) .reserve .unavailable (some owner)
  | inspect (state) : Meaning actor state .inspect state.isNone state

abbrev askSlot (actor : Person) (intent : Intention) : Flow vocabulary (Observation intent) :=
  ask (v := vocabulary) actor intent

def reserveFree (actor : Person) : Story vocabulary (Decision × Bool) where
  id := "R1"
  asA := actor
  iWant := "Reserve the available slot and see that it is no longer available"
  soThat := "I can rely on the reservation"
  given := fun before => before = none
  scenario := do
    let decision ← askSlot actor .reserve
    let available ← askSlot actor .inspect
    pure (decision, available)
  ensures := fun _ replies after =>
    replies.1 = .reserved ∧ replies.2 = false ∧ after = some actor

theorem reserveFree_checked (actor : Person) : Certified (v := vocabulary) Meaning (reserveFree actor) where
  feasible := ⟨none, rfl⟩
  fulfilled := by
    intro before empty
    cases empty
    constructor
    · exact ⟨.reserved, some actor, .reserve⟩
    · intro decision middle first
      cases first
      constructor
      · exact ⟨false, some actor, .inspect _⟩
      · intro available after second
        cases second
        exact ⟨rfl, rfl, rfl⟩
  lawsHold := by intro law member; cases member

/-- The flow can branch on a typed observation without inspecting hidden state. -/
def inspectThenReserve (actor : Person) : Flow vocabulary (Option Decision) := do
  let available ← askSlot actor .inspect
  if available = true then
    let decision ← askSlot actor .reserve
    pure (some decision)
  else
    pure none

theorem occupied_branch (actor owner : Person) :
    Run (v := vocabulary) Meaning (inspectThenReserve actor) (some owner) none (some owner) :=
  .request (.inspect _) (.done _ _)

theorem available_branch (actor : Person) :
    Run (v := vocabulary) Meaning (inspectThenReserve actor) none (some .reserved) (some actor) :=
  .request (.inspect _) (.request .reserve (.done _ _))

end ReservationStoryBook
