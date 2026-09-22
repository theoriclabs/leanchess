import Std

/-!
Implementation-independent companion to stories.md.
Check with: lean product_intent/Stories.lean
No application imports, IO, platform types, or assumptions about persistence.
GameFacts is supplied by a separate rule specification, not by the current code.
-/
namespace LeanChessIntent

abbrev Person := Nat

inductive Seat where
  | white | black
  deriving DecidableEq

inductive Conclusion where
  | win : Seat → Conclusion
  | draw | abort
  deriving DecidableEq

structure Agreement where
  occupant : Seat → Person

/-- Deliberately abstract: this file does not purport to define or prove chess rules. -/
structure GameFacts where
  Situation : Type
  Attempt : Type
  conclusion : Situation → Option Conclusion
  permits : Situation → Seat → Attempt → Prop
  following : Situation → Seat → Attempt → Situation

structure Snapshot (facts : GameFacts) where
  revision : Nat
  situation : facts.Situation

/-- Semantic facts, not a proposed database or in-memory representation. -/
structure World (facts : GameFacts) where
  game : Snapshot facts
  notes : Person → List String

inductive Intention (facts : GameFacts) where
  | look
  | attempt : Seat → facts.Attempt → Intention facts
  | readNotes : Person → Intention facts
  | appendNote : Person → String → Intention facts

inductive Reply (facts : GameFacts) where
  | seen : Agreement → Snapshot facts → Reply facts
  | accepted : Snapshot facts → Reply facts
  | refused
  | notes : List String → Reply facts
  | saved

def CanAttempt (facts : GameFacts) (agreement : Agreement) (actor : Person)
    (world : World facts) (seat : Seat) (attempt : facts.Attempt) : Prop :=
  facts.conclusion world.game.situation = none ∧
  agreement.occupant seat = actor ∧
  facts.permits world.game.situation seat attempt

def afterAttempt (world : World facts) (seat : Seat) (attempt : facts.Attempt) : World facts :=
  { world with game := ⟨world.game.revision + 1,
      facts.following world.game.situation seat attempt⟩ }

def afterNote (world : World facts) (owner : Person) (body : String) : World facts :=
  { world with notes := fun person =>
      if person = owner then world.notes person ++ [body] else world.notes person }

/-- Allowed resolved interactions. This relation is a specification, not a dispatcher. -/
inductive Step (facts : GameFacts) (agreement : Agreement) (actor : Person) :
    World facts → Intention facts → Reply facts → World facts → Prop where
  | look (world) : Step facts agreement actor world .look (.seen agreement world.game) world
  | accept {world seat attempt} (allowed : CanAttempt facts agreement actor world seat attempt) :
      Step facts agreement actor world (.attempt seat attempt)
        (.accepted (afterAttempt world seat attempt).game) (afterAttempt world seat attempt)
  | refuse {world seat attempt} (denied : ¬ CanAttempt facts agreement actor world seat attempt) :
      Step facts agreement actor world (.attempt seat attempt) .refused world
  | readOwn (world) :
      Step facts agreement actor world (.readNotes actor) (.notes (world.notes actor)) world
  | readOther (world) {owner} (notOwner : actor ≠ owner) :
      Step facts agreement actor world (.readNotes owner) .refused world
  | appendOwn (world) (body) :
      Step facts agreement actor world (.appendNote actor body) .saved (afterNote world actor body)
  | appendOther (world) {owner} (body) (notOwner : actor ≠ owner) :
      Step facts agreement actor world (.appendNote owner body) .refused world

/-- One person's finite sequence of intentions and observations. -/
inductive Journey (facts : GameFacts) (agreement : Agreement) (actor : Person) :
    World facts → List (Intention facts × Reply facts) → World facts → Prop where
  | nil (world) : Journey facts agreement actor world [] world
  | cons {before middle after intention reply rest}
      (first : Step facts agreement actor before intention reply middle)
      (later : Journey facts agreement actor middle rest after) :
      Journey facts agreement actor before ((intention, reply) :: rest) after

/-! S1: a look returns the shared game facts and makes no change. -/
theorem look_exact
    (h : Step facts agreement actor before .look reply after) :
    reply = .seen agreement before.game ∧ after = before := by
  cases h
  exact ⟨rfl, rfl⟩

theorem both_can_see_same_revision (facts : GameFacts) (agreement : Agreement)
    (first second : Person) (world : World facts) :
    Step facts agreement first world .look (.seen agreement world.game) world ∧
    Step facts agreement second world .look (.seen agreement world.game) world :=
  ⟨.look world, .look world⟩

/-! S2: authority, exact consequences, and an accepting continuation. -/
theorem acceptance_requires_permission
    (h : Step facts agreement actor before (.attempt seat attempt) (.accepted snapshot) after) :
    CanAttempt facts agreement actor before seat attempt := by
  cases h with
  | accept allowed => exact allowed

theorem acceptance_has_exact_consequence
    (h : Step facts agreement actor before (.attempt seat attempt) (.accepted snapshot) after) :
    after = afterAttempt before seat attempt ∧ snapshot = after.game := by
  cases h
  exact ⟨rfl, rfl⟩

theorem permitted_attempt_has_continuation
    (allowed : CanAttempt facts agreement actor before seat attempt) :
    ∃ after, Step facts agreement actor before (.attempt seat attempt) (.accepted after.game) after :=
  ⟨afterAttempt before seat attempt, .accept allowed⟩

theorem permitted_attempt_cannot_be_refused
    (allowed : CanAttempt facts agreement actor before seat attempt) :
    ¬ Step facts agreement actor before (.attempt seat attempt) .refused after := by
  intro h
  cases h with
  | refuse denied => exact denied allowed

/-- A two-person flow: an accepted attempt followed by the other person's look. -/
theorem accepted_then_seen (other : Person)
    (allowed : CanAttempt facts agreement actor before seat attempt) :
    ∃ after,
      Step facts agreement actor before (.attempt seat attempt) (.accepted after.game) after ∧
      Step facts agreement other after .look (.seen agreement after.game) after :=
  ⟨afterAttempt before seat attempt, .accept allowed, .look _⟩

/-! S3: refused interactions make no changes; an occupied seat is not transferable. -/
theorem refusal_changes_nothing
    (h : Step facts agreement actor before intention .refused after) : after = before := by
  cases h <;> rfl

theorem cannot_act_for_someone_elses_seat
    (notSeated : agreement.occupant seat ≠ actor) :
    ¬ Step facts agreement actor before (.attempt seat attempt) (.accepted snapshot) after := by
  intro h
  exact notSeated (acceptance_requires_permission h).2.1

/-! S4: a finished game cannot be changed by another game attempt. -/
theorem ending_is_stable_under_attempts
    (finished : facts.conclusion before.game.situation = some conclusion)
    (h : Step facts agreement actor before (.attempt seat attempt) reply after) :
    reply = .refused ∧ after = before := by
  cases h with
  | accept allowed =>
      have ongoing := allowed.1
      rw [finished] at ongoing
      cases ongoing
  | refuse _ => exact ⟨rfl, rfl⟩

/-! S6: owner reads are exact, and other people's notes cannot affect this person's story. -/
theorem owner_reads_exact_collection
    (h : Step facts agreement actor before (.readNotes actor) (.notes entries) after) :
    entries = before.notes actor := by
  cases h
  rfl

theorem other_person_cannot_read_notes (notOwner : actor ≠ owner)
    (h : Step facts agreement actor before (.readNotes owner) reply after) :
    reply = .refused ∧ after = before := by
  cases h with
  | readOwn => exact False.elim (notOwner rfl)
  | readOther _ => exact ⟨rfl, rfl⟩

theorem other_person_cannot_write_notes (notOwner : actor ≠ owner)
    (h : Step facts agreement actor before (.appendNote owner body) reply after) :
    reply = .refused ∧ after = before := by
  cases h with
  | appendOwn => exact False.elim (notOwner rfl)
  | appendOther _ => exact ⟨rfl, rfl⟩

theorem note_then_read (facts : GameFacts) (agreement : Agreement)
    (actor : Person) (world : World facts) (body : String) :
    Journey facts agreement actor world
      [(.appendNote actor body, .saved), (.readNotes actor, .notes (world.notes actor ++ [body]))]
      (afterNote world actor body) := by
  apply Journey.cons (.appendOwn world body)
  have read := Step.readOwn (facts := facts) (agreement := agreement) (actor := actor)
    (afterNote world actor body)
  simp only [afterNote] at read
  exact .cons read (.nil _)

def SameFor (actor : Person) (left right : World facts) : Prop :=
  left.game = right.game ∧ left.notes actor = right.notes actor

private theorem attempt_preserves_same {facts : GameFacts} {left right : World facts}
    (same : SameFor actor left right)
    (seat : Seat) (attempt : facts.Attempt) :
    SameFor actor (afterAttempt left seat attempt) (afterAttempt right seat attempt) := by
  constructor
  · simp only [afterAttempt, same.1]
  · exact same.2

private theorem note_preserves_same {facts : GameFacts} {left right : World facts}
    (same : SameFor actor left right) (body : String) :
    SameFor actor (afterNote left actor body) (afterNote right actor body) := by
  constructor
  · exact same.1
  · simp only [afterNote, same.2]

/-- Same visible starting facts and same intention permit exactly the same observation. -/
theorem step_noninterference {facts : GameFacts} {agreement : Agreement} {actor : Person}
    {left right leftAfter : World facts} {intention : Intention facts} {reply : Reply facts}
    (same : SameFor actor left right)
    (h : Step facts agreement actor left intention reply leftAfter) :
    ∃ rightAfter, Step facts agreement actor right intention reply rightAfter ∧
      SameFor actor leftAfter rightAfter := by
  cases h with
  | look =>
      refine ⟨right, ?_, same⟩
      rw [same.1]
      exact .look right
  | accept allowed =>
      rename_i seat attempt
      have permitted : CanAttempt facts agreement actor right seat attempt := by
        simpa only [CanAttempt, same.1] using allowed
      have afterwards := attempt_preserves_same same seat attempt
      refine ⟨afterAttempt right seat attempt, ?_, afterwards⟩
      rw [afterwards.1]
      exact .accept permitted
  | refuse denied =>
      refine ⟨right, .refuse ?_, same⟩
      simpa only [CanAttempt, same.1] using denied
  | readOwn =>
      refine ⟨right, ?_, same⟩
      rw [same.2]
      exact .readOwn right
  | readOther notOwner => exact ⟨right, .readOther right notOwner, same⟩
  | appendOwn body =>
      exact ⟨afterNote right actor body, .appendOwn right body, note_preserves_same same body⟩
  | appendOther body notOwner => exact ⟨right, .appendOther right body notOwner, same⟩

/-- The information-flow property extends to all finite personal journeys in this vocabulary. -/
theorem journey_noninterference {facts : GameFacts} {agreement : Agreement} {actor : Person}
    {left right leftAfter : World facts} {transcript : List (Intention facts × Reply facts)}
    (h : Journey facts agreement actor left transcript leftAfter)
    (same : SameFor actor left right) :
    ∃ rightAfter, Journey facts agreement actor right transcript rightAfter ∧
      SameFor actor leftAfter rightAfter := by
  induction h generalizing right with
  | nil _ => exact ⟨right, .nil right, same⟩
  | cons first later ih =>
      obtain ⟨middle, firstRight, sameMiddle⟩ := step_noninterference same first
      obtain ⟨last, restRight, sameLast⟩ := ih sameMiddle
      exact ⟨last, .cons firstRight restRight, sameLast⟩

/-! S5: knowledge of the game is distinct from the game itself. -/
inductive ReturnStage (facts : GameFacts) where
  | away | catchingUp
  | ready : Snapshot facts → ReturnStage facts

def Ready : ReturnStage facts → Prop
  | .ready _ => True
  | .away | .catchingUp => False

/-- Readiness gates the expression of a NEW game attempt, not its later adjudication. -/
def MayExpress (stage : ReturnStage facts) : Intention facts → Prop
  | .attempt _ _ => Ready stage
  | .look | .readNotes _ | .appendNote _ _ => True

/-- The parameter is the game's confirmed snapshot AT this confirmation boundary. -/
inductive ReturnStep (confirmed : Snapshot facts) : ReturnStage facts → ReturnStage facts → Prop where
  | begin : ReturnStep confirmed .away .catchingUp
  | confirm : ReturnStep confirmed .catchingUp (.ready confirmed)
  | leave (old) : ReturnStep confirmed (.ready old) .away

theorem return_requires_catching_up (confirmed old : Snapshot facts) :
    ¬ ReturnStep confirmed .away (.ready old) := by
  intro h
  cases h

theorem catching_up_is_not_ready : ¬ Ready (facts := facts) .catchingUp := by
  intro h
  exact h

theorem cannot_express_attempt_while_catching_up (seat : Seat) (attempt : facts.Attempt) :
    ¬ MayExpress (.catchingUp : ReturnStage facts) (.attempt seat attempt) := by
  intro h
  exact h

theorem confirmation_is_exact
    (h : ReturnStep confirmed .catchingUp (.ready snapshot)) : snapshot = confirmed := by
  cases h
  rfl

theorem return_flow (confirmed : Snapshot facts) :
    ReturnStep confirmed .away .catchingUp ∧
    ReturnStep confirmed .catchingUp (.ready confirmed) := ⟨.begin, .confirm⟩

inductive Decision (facts : GameFacts) where
  | accepted : Snapshot facts → Decision facts
  | refused

inductive Knowledge (facts : GameFacts) where
  | waiting | unknown
  | resolved : Decision facts → Knowledge facts

inductive Notice (facts : GameFacts) where
  | lostContact
  | decision : Decision facts → Notice facts

/-- A decision notice represents an actual decision in the proposed experience. -/
inductive Learn : Knowledge facts → Notice facts → Knowledge facts → Prop where
  | lost : Learn .waiting .lostContact .unknown
  | answered (decision) : Learn .waiting (.decision decision) (.resolved decision)
  | recovered (decision) : Learn .unknown (.decision decision) (.resolved decision)

theorem losing_contact_is_uncertainty
    (h : Learn (facts := facts) .waiting .lostContact later) : later = .unknown := by
  cases h
  rfl

/-- An obligation, NOT an established progress theorem. Opportunity includes the
person's continuing intention and the availability/fairness conditions a realization names. -/
def ReturnProgress (history : Nat → ReturnStage facts) (opportunity : Nat → Prop) : Prop :=
  ∀ start, history start = .catchingUp →
    (∀ later, start ≤ later → opportunity later) →
    ∃ later, start ≤ later ∧ Ready (history later)

/-! S7: an abstract input vocabulary must preserve meaning AND cover promised intentions. -/
structure Realization (facts : GameFacts) (Modality : Type) (Input : Modality → Type) where
  expresses : (mode : Modality) → Input mode → Intention facts
  happens : (mode : Modality) → Person → ReturnStage facts →
    World facts → Input mode → Reply facts → World facts → Prop

/-- Both directions matter: soundness alone would allow an implementation that does nothing. -/
def PreservesStories (agreement : Agreement)
    (realization : Realization facts Modality Input) : Prop :=
  ∀ mode actor stage before input reply after,
    realization.happens mode actor stage before input reply after ↔
      MayExpress stage (realization.expresses mode input) ∧
      Step facts agreement actor before (realization.expresses mode input) reply after

def CoversIntentions (realization : Realization facts Modality Input)
    (promised : Modality → Intention facts → Prop) : Prop :=
  ∀ mode intention, promised mode intention →
    ∃ input, realization.expresses mode input = intention

-- No realization, progress theorem, or chess-rule implementation is supplied here.
#print axioms permitted_attempt_cannot_be_refused
#print axioms ending_is_stable_under_attempts
#print axioms journey_noninterference
#print axioms confirmation_is_exact

end LeanChessIntent
