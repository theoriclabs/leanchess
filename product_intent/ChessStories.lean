import UserStories
import Stories

/-! User stories authored in a reusable language and interpreted by independent product semantics. -/
namespace ChessStoryBook
open UserStories LeanChessIntent

abbrev vocabulary (facts : GameFacts) : Vocabulary where
  Actor := Person
  State := World facts
  Intention := Intention facts
  Observation := fun _ => Reply facts

abbrev meaning (facts : GameFacts) (agreement : Agreement) : Semantics (vocabulary facts) :=
  Step facts agreement

/-- Product vocabulary shorthand; the flow machinery remains domain-independent. -/
abbrev askGame {facts : GameFacts} (actor : Person) (intent : Intention facts) :
    Flow (vocabulary facts) (Reply facts) := ask (v := vocabulary facts) actor intent

def seeGame (facts : GameFacts) (agreement : Agreement) (actor : Person) :
    Story (vocabulary facts) (Reply facts) where
  id := "S1"
  asA := actor
  iWant := "See the agreed game and its confirmed situation"
  soThat := "I understand the game without changing it"
  given := fun _ => True
  scenario := askGame actor .look
  ensures := fun before reply after => reply = .seen agreement before.game ∧ after = before

theorem seeGame_checked (facts : GameFacts) (agreement : Agreement)
    (actor : Person) (initial : World facts) :
    Certified (meaning facts agreement) (seeGame facts agreement actor) where
  feasible := ⟨initial, True.intro⟩
  fulfilled := by
    intro before _
    constructor
    · exact ⟨.seen agreement before.game, before, .look before⟩
    · intro reply after step
      exact look_exact step
  lawsHold := by intro law member; cases member

def makeAttempt (facts : GameFacts) (agreement : Agreement) (actor other : Person)
    (seat : Seat) (attempt : facts.Attempt) :
    Story (vocabulary facts) (Reply facts × Reply facts) where
  id := "S2"
  asA := actor
  iWant := "Make a permitted attempt and have the other player see its consequence"
  soThat := "My action counts in the game we share"
  given := fun before => CanAttempt facts agreement actor before seat attempt
  scenario := do
    let decision ← askGame actor (.attempt seat attempt)
    let observation ← askGame other .look
    pure (decision, observation)
  ensures := fun before replies after =>
    replies.1 = .accepted after.game ∧ replies.2 = .seen agreement after.game ∧
      after = afterAttempt before seat attempt

theorem makeAttempt_checked (facts : GameFacts) (agreement : Agreement) (actor other : Person)
    (seat : Seat) (attempt : facts.Attempt) (initial : World facts)
    (initialAllowed : CanAttempt facts agreement actor initial seat attempt) :
    Certified (meaning facts agreement) (makeAttempt facts agreement actor other seat attempt) where
  feasible := ⟨initial, initialAllowed⟩
  fulfilled := by
    intro before allowed
    constructor
    · exact ⟨.accepted (afterAttempt before seat attempt).game,
        afterAttempt before seat attempt, .accept allowed⟩
    · intro reply middle first
      cases first with
      | accept _ =>
          constructor
          · exact ⟨.seen agreement _, _, .look _⟩
          · intro observation after second
            cases second
            exact ⟨rfl, rfl, rfl⟩
      | refuse denied => exact False.elim (denied allowed)
  lawsHold := by intro law member; cases member

def refusedAttempt (facts : GameFacts) (agreement : Agreement) (actor : Person)
    (seat : Seat) (attempt : facts.Attempt) :
    Story (vocabulary facts) (Reply facts × Reply facts) where
  id := "S3"
  asA := actor
  iWant := "Recognize a refusal and see the accepted game intact"
  soThat := "A mistaken attempt does not damage the game"
  given := fun before => ¬ CanAttempt facts agreement actor before seat attempt
  scenario := do
    let decision ← askGame actor (.attempt seat attempt)
    let observation ← askGame actor .look
    pure (decision, observation)
  ensures := fun before replies after =>
    replies.1 = .refused ∧ replies.2 = .seen agreement before.game ∧ after = before

theorem refusedAttempt_checked (facts : GameFacts) (agreement : Agreement) (actor : Person)
    (seat : Seat) (attempt : facts.Attempt) (initial : World facts)
    (initialDenied : ¬ CanAttempt facts agreement actor initial seat attempt) :
    Certified (meaning facts agreement) (refusedAttempt facts agreement actor seat attempt) where
  feasible := ⟨initial, initialDenied⟩
  fulfilled := by
    intro before denied
    constructor
    · exact ⟨.refused, before, .refuse denied⟩
    · intro reply middle first
      cases first with
      | accept allowed => exact False.elim (denied allowed)
      | refuse _ =>
          constructor
          · exact ⟨.seen agreement before.game, before, .look before⟩
          · intro observation after second
            cases second
            exact ⟨rfl, rfl, rfl⟩
  lawsHold := by intro law member; cases member

def keepEnding (facts : GameFacts) (agreement : Agreement) (actor : Person)
    (seat : Seat) (attempt : facts.Attempt) : Story (vocabulary facts) (Reply facts × Reply facts) :=
  { refusedAttempt facts agreement actor seat attempt with
    id := "S4"
    iWant := "Discover an ending that later attempts cannot rewrite"
    soThat := "The result is dependable"
    given := fun before => ∃ conclusion, facts.conclusion before.game.situation = some conclusion }

theorem keepEnding_checked (facts : GameFacts) (agreement : Agreement) (actor : Person)
    (seat : Seat) (attempt : facts.Attempt) (initial : World facts) (conclusion : Conclusion)
    (finished : facts.conclusion initial.game.situation = some conclusion) :
    Certified (meaning facts agreement) (keepEnding facts agreement actor seat attempt) where
  feasible := ⟨initial, conclusion, finished⟩
  fulfilled := by
    intro before hasEnding
    obtain ⟨ending, ended⟩ := hasEnding
    have denied : ¬ CanAttempt facts agreement actor before seat attempt := by
      intro allowed
      have ongoing := allowed.1
      rw [ended] at ongoing
      cases ongoing
    exact (refusedAttempt_checked facts agreement actor seat attempt before denied).fulfilled before denied
  lawsHold := by intro law member; cases member

def privateNotes (facts : GameFacts) : Law (Semantics (vocabulary facts)) where
  id := "S6.private-observations"
  description := "Other people's private notes do not change my observations"
  holds := fun semantics => Noninterference semantics (fun actor left right => SameFor actor left right)

theorem privateNotes_checked (facts : GameFacts) (agreement : Agreement) :
    (privateNotes facts).holds (meaning facts agreement) := by
  intro actor left right intent observation leftAfter same step
  exact step_noninterference same step

def rememberNote (facts : GameFacts) (actor : Person) (body : String) :
    Story (vocabulary facts) (Reply facts × Reply facts) where
  id := "S6"
  asA := actor
  iWant := "Write and revisit a private personal note"
  soThat := "My analysis remains available to me without becoming shared game data"
  given := fun _ => True
  scenario := do
    let acknowledgment ← askGame actor (.appendNote actor body)
    let notes ← askGame actor (.readNotes actor)
    pure (acknowledgment, notes)
  ensures := fun before replies after =>
    replies.1 = .saved ∧ replies.2 = .notes (before.notes actor ++ [body]) ∧
      after.game = before.game
  laws := [privateNotes facts]

theorem rememberNote_checked (facts : GameFacts) (agreement : Agreement)
    (actor : Person) (body : String) (initial : World facts) :
    Certified (meaning facts agreement) (rememberNote facts actor body) where
  feasible := ⟨initial, True.intro⟩
  fulfilled := by
    intro before _
    constructor
    · exact ⟨.saved, afterNote before actor body, .appendOwn before body⟩
    · intro reply middle first
      cases first with
      | appendOwn =>
          constructor
          · exact ⟨.notes _, _, .readOwn _⟩
          · intro observation after second
            cases second with
            | readOwn => exact ⟨rfl, by simp [afterNote], rfl⟩
            | readOther notOwner => exact False.elim (notOwner rfl)
      | appendOther => contradiction
  lawsHold := by
    intro law member
    change law ∈ [privateNotes facts] at member
    have equality := List.mem_singleton.mp member
    subst law
    exact privateNotes_checked facts agreement

theorem rememberNote_is_personal (facts : GameFacts) (actor : Person) (body : String) :
    Personal actor (rememberNote facts actor body).scenario := by
  apply Personal.request
  intro acknowledgment
  apply Personal.request
  intro notes
  exact .done (acknowledgment, notes)

/-- Reuses the generic lifting theorem, rather than a chess-specific induction over flows. -/
theorem rememberNote_flow_private {facts : GameFacts} {agreement : Agreement}
    {actor : Person} {body : String} {left right after : World facts}
    {observations : Reply facts × Reply facts} (same : SameFor actor left right)
    (run : Run (meaning facts agreement) (rememberNote facts actor body).scenario left observations after) :
    ∃ rightAfter, Run (meaning facts agreement) (rememberNote facts actor body).scenario
      right observations rightAfter ∧ SameFor actor after rightAfter :=
  personal_flow_noninterference (privateNotes_checked facts agreement)
    (rememberNote_is_personal facts actor body) same run

/-! S5 uses the SAME story language with a different product vocabulary: knowledge. -/
inductive ReturnIntent where
  | begin | awaitConfirmation

def ReturnObservation (facts : GameFacts) : ReturnIntent → Type
  | .begin => Unit
  | .awaitConfirmation => Snapshot facts

abbrev returnVocabulary (facts : GameFacts) : Vocabulary where
  Actor := Person
  State := ReturnStage facts
  Intention := ReturnIntent
  Observation := ReturnObservation facts

abbrev askReturn {facts : GameFacts} (actor : Person) (intent : ReturnIntent) :
    Flow (returnVocabulary facts) (ReturnObservation facts intent) :=
  ask (v := returnVocabulary facts) actor intent

inductive ReturnMeaning (confirmed : Snapshot facts) (actor : Person) :
    ReturnStage facts → (intent : ReturnIntent) → ReturnObservation facts intent → ReturnStage facts → Prop where
  | begin : ReturnMeaning confirmed actor .away .begin () .catchingUp
  | confirm : ReturnMeaning confirmed actor .catchingUp .awaitConfirmation confirmed (.ready confirmed)

theorem returnMeaning_agrees
    (h : ReturnMeaning confirmed actor before intent observation after) : ReturnStep confirmed before after := by
  cases h with
  | begin => exact .begin
  | confirm => exact .confirm

def returnToGame (facts : GameFacts) (actor : Person) (confirmed : Snapshot facts) :
    Story (returnVocabulary facts) (Snapshot facts) where
  id := "S5"
  asA := actor
  iWant := "Catch up before continuing from a confirmed game"
  soThat := "An old picture does not masquerade as a new confirmation"
  given := fun stage => stage = .away
  scenario := do
    let _ ← askReturn actor .begin
    askReturn actor .awaitConfirmation
  ensures := fun _ observation after => observation = confirmed ∧ after = .ready confirmed

theorem returnToGame_checked (facts : GameFacts) (actor : Person) (confirmed : Snapshot facts) :
    Certified (v := returnVocabulary facts) (ReturnMeaning confirmed) (returnToGame facts actor confirmed) where
  feasible := ⟨.away, rfl⟩
  fulfilled := by
    intro before away
    cases away
    constructor
    · exact ⟨(), .catchingUp, .begin⟩
    · intro observation middle first
      cases first
      constructor
      · exact ⟨confirmed, .ready confirmed, .confirm⟩
      · intro snapshot after second
        cases second
        exact ⟨rfl, rfl⟩
  lawsHold := by intro law member; cases member

/-- Named but NOT certified: a real realization owes this conditional progress law. -/
def returnProgress (facts : GameFacts) (opportunity : Nat → Prop) : Law (Nat → ReturnStage facts) where
  id := "S5.progress"
  description := "Sustained opportunity to return eventually leads to readiness"
  holds := fun history => ∀ start, history start = .catchingUp →
    (∀ later, start ≤ later → opportunity later) → Eventually history start Ready

/-- S7 is a law of realizations, not just the outcome of one happy-path flow.
Required modalities and intentions are product parameters, not built into the DSL. -/
def inputMeaning (facts : GameFacts) (agreement : Agreement)
    (Modality : Type) (Input : Modality → Type) (promised : Modality → Intention facts → Prop) :
    Law (Realization facts Modality Input) where
  id := "S7.input-equivalence"
  description := "Every promised input expresses and preserves the intended story"
  holds := fun realization => PreservesStories agreement realization ∧ CoversIntentions realization promised

end ChessStoryBook
