import ChessStories
import ReservationStories

/-! Positive certificates, counterexamples, and intentional negative compilation checks. -/
namespace StoryChecks
open UserStories ReservationStoryBook

def silent : Semantics vocabulary := fun _ _ _ _ _ => False

def alwaysRefuse : Semantics vocabulary := fun _ before intent observation after =>
  match intent with
  | .reserve => observation = .unavailable ∧ after = before
  | .inspect => observation = before.isNone ∧ after = before

theorem silent_cannot_certify : ¬ Certified silent (reserveFree 1) := by
  intro certificate
  have promise := certificate.fulfilled none rfl
  obtain ⟨observation, after, impossible⟩ := promise.1
  exact impossible

theorem alwaysRefuse_cannot_certify : ¬ Certified alwaysRefuse (reserveFree 1) := by
  intro certificate
  have badRun : Run alwaysRefuse (reserveFree 1).scenario none (.unavailable, true) none :=
    .request ⟨rfl, rfl⟩ (.request ⟨rfl, rfl⟩ (.done _ _))
  have impossible := (certificate.outcome rfl badRun).1
  cases impossible

/-- Even one permitted bad branch invalidates a certificate, despite good branches existing. -/
def sometimesRefuse : Semantics vocabulary := fun actor before intent observation after =>
  Meaning actor before intent observation after ∨ alwaysRefuse actor before intent observation after

theorem sometimesRefuse_cannot_certify : ¬ Certified sometimesRefuse (reserveFree 1) := by
  intro certificate
  have badRun : Run sometimesRefuse (reserveFree 1).scenario none (.unavailable, true) none :=
    .request (.inr ⟨rfl, rfl⟩) (.request (.inr ⟨rfl, rfl⟩) (.done _ _))
  have impossible := (certificate.outcome rfl badRun).1
  cases impossible

def impossibleGiven : Story vocabulary Unit where
  id := "impossible"
  asA := 1
  iWant := "An impossible starting condition must not count as verified"
  soThat := "Vacuous guarantees do not masquerade as useful stories"
  given := fun _ => False
  scenario := pure ()
  ensures := fun _ _ _ => True

theorem impossibleGiven_cannot_certify : ¬ Certified Meaning impossibleGiven := by
  intro certificate
  obtain ⟨state, impossible⟩ := certificate.feasible
  exact impossible

def unsatisfiedLaw : Law (Semantics vocabulary) :=
  ⟨"unfulfilled", "An explicit obligation with no evidence", fun _ => False⟩

def storyWithLaw : Story vocabulary (Decision × Bool) :=
  { reserveFree 1 with laws := [unsatisfiedLaw] }

theorem missing_law_cannot_certify : ¬ Certified Meaning storyWithLaw := by
  intro certificate
  exact certificate.lawsHold unsatisfiedLaw (by simp [storyWithLaw])

-- The result type follows the intention: reserve does NOT return Bool.
#check_failure (show Flow vocabulary Bool from askSlot 1 .reserve)

-- A proof about the intended model does not certify a different model.
#check_failure (show Certified alwaysRefuse (reserveFree 1) from reserveFree_checked 1)
#check_failure (show Certified silent (reserveFree 1) from reserveFree_checked 1)

-- Adding a law changes the exact certificate required.
#check_failure (show Certified Meaning storyWithLaw from reserveFree_checked 1)

#guard (reserveFree 1).id == "R1"
#guard (reserveFree 1).asA == 1

#print axioms UserStories.guarantees_sound
#print axioms UserStories.guarantees_possible
#print axioms UserStories.personal_flow_noninterference
#print axioms ChessStoryBook.seeGame_checked
#print axioms ChessStoryBook.makeAttempt_checked
#print axioms ChessStoryBook.refusedAttempt_checked
#print axioms ChessStoryBook.keepEnding_checked
#print axioms ChessStoryBook.rememberNote_checked
#print axioms ChessStoryBook.rememberNote_flow_private
#print axioms ChessStoryBook.returnToGame_checked
#print axioms ReservationStoryBook.reserveFree_checked
#print axioms silent_cannot_certify
#print axioms alwaysRefuse_cannot_certify
#print axioms sometimesRefuse_cannot_certify
#print axioms impossibleGiven_cannot_certify
#print axioms missing_law_cannot_certify

end StoryChecks
