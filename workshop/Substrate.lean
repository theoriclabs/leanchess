import domain.Game

/-!
An executable design workshop, separate from the application build.
Run: lake env lean workshop/Substrate.lean

The read and commit implementations below are PURE REFERENCE MODELS.
Their proofs do not certify SQLite, authentication, concurrent IO, or JavaScript.
-/

namespace Theoric.Workshop

/- Queryable claims are data; their meanings are propositions about an implementation. -/

structure Catalogue (Implementation : Type) where
  Claim : Type
  meaning : Implementation → Claim → Prop

inductive Status where
  | proved | conditional | tested | unknown | refuted
  deriving Repr, BEq, DecidableEq

inductive Evidence (P : Prop) where
  | proved (proof : P)
  | conditional (premise : Prop) (description : String) (proof : premise → P)
  | tested (description : String)
  | unknown
  | refuted (proof : ¬ P)

def Evidence.status : Evidence P → Status
  | .proved _ => .proved
  | .conditional _ _ _ => .conditional
  | .tested _ => .tested
  | .unknown => .unknown
  | .refuted _ => .refuted

theorem Evidence.established (e : Evidence P) (h : e.status = .proved) : P := by
  cases e <;> simp_all [Evidence.status]

structure Registry (catalogue : Catalogue Implementation) where
  implementation : Implementation
  evidence : (claim : catalogue.Claim) → Evidence (catalogue.meaning implementation claim)

def Registry.query (r : Registry catalogue) (claim : catalogue.Claim) : Status :=
  (r.evidence claim).status

theorem Registry.require (r : Registry catalogue) (claim : catalogue.Claim)
    (h : r.query claim = .proved) : catalogue.meaning r.implementation claim :=
  (r.evidence claim).established h

/- Example 1: exact answers do not imply confined reads. -/

structure Note where
  owner : Nat
  body : String
  deriving Repr, BEq, DecidableEq

def visible (actor : Nat) (rows : List Note) : List Note :=
  rows.filter fun row => row.owner == actor

structure ReadExecution where
  /-- Owners of values obtained by the modeled application read operation.
      This is not a trace of physical disk-page accesses. -/
  readOwners : List Nat
  result : List Note

abbrev Reader := Nat → List Note → ReadExecution

def scopedReader : Reader := fun actor rows =>
  let allowed := visible actor rows
  ⟨allowed.map Note.owner, allowed⟩

def scanThenFilter : Reader := fun actor rows =>
  ⟨rows.map Note.owner, visible actor rows⟩

inductive ReadClaim where
  | confinedReads
  | exactResult
  | responseNoninterference
  deriving Repr, BEq, DecidableEq

def readCatalogue : Catalogue Reader where
  Claim := ReadClaim
  meaning run
    | .confinedReads => ∀ actor rows owner,
        owner ∈ (run actor rows).readOwners → owner = actor
    | .exactResult => ∀ actor rows, (run actor rows).result = visible actor rows
    | .responseNoninterference => ∀ actor left right,
        visible actor left = visible actor right →
          (run actor left).result = (run actor right).result

theorem scopedReader_confined : readCatalogue.meaning scopedReader .confinedReads := by
  intro actor rows owner h
  obtain ⟨row, hr, he⟩ := List.mem_map.mp h
  have ho : row.owner = actor := by
    simpa using (List.mem_filter.mp hr).2
  exact he.symm.trans ho

theorem scanThenFilter_not_confined :
    ¬ readCatalogue.meaning scanThenFilter .confinedReads := by
  intro h
  have impossible := h 1 [⟨2, "Bob's note"⟩] 2 (by simp [scanThenFilter])
  contradiction

def scopedRegistry : Registry readCatalogue where
  implementation := scopedReader
  evidence
    | .confinedReads => .proved scopedReader_confined
    | .exactResult => .proved (by intro actor rows; rfl)
    | .responseNoninterference => .proved (by intro actor left right h; exact h)

def scanRegistry : Registry readCatalogue where
  implementation := scanThenFilter
  evidence
    | .confinedReads => .refuted scanThenFilter_not_confined
    | .exactResult => .proved (by intro actor rows; rfl)
    | .responseNoninterference => .proved (by intro actor left right h; exact h)

/-- A consumer requires propositions tied to the exact selected reader. -/
structure PrivateRepository where
  run : Reader
  confined : readCatalogue.meaning run .confinedReads
  exact : readCatalogue.meaning run .exactResult

def selectPrivateRepository (r : Registry readCatalogue)
    (hc : r.query .confinedReads = .proved)
    (he : r.query .exactResult = .proved) : PrivateRepository :=
  ⟨r.implementation, r.require .confinedReads hc, r.require .exactResult he⟩

def privateRepository := selectPrivateRepository scopedRegistry rfl rfl

/-- The unqualified registry is extensible; a consumer decides its required claims. -/
def readRequirements : List ReadClaim := [.confinedReads, .exactResult]

def candidates (available : List (Registry readCatalogue)) : List (Registry readCatalogue) :=
  available.filter fun candidate =>
    readRequirements.all fun claim => candidate.query claim == .proved

#guard (candidates [scanRegistry, scopedRegistry]).length == 1
#guard scopedRegistry.query .confinedReads == .proved
#guard scanRegistry.query .confinedReads == .refuted
#guard scanRegistry.query .exactResult == .proved
#guard scanRegistry.query .responseNoninterference == .proved

-- Even the truthful result-equality proof cannot be used as read-confinement evidence.
#check_failure selectPrivateRepository scanRegistry rfl rfl

#eval ("scoped reader", readRequirements.map scopedRegistry.query)
#eval ("scan then filter", readRequirements.map scanRegistry.query)

/- Example 2: the same commit mechanism accepts different domain semantics. -/

structure Model where
  State : Type
  Command : Type
  permits : String → State → Command → Prop
  next : State → Command → State

structure Snapshot (State : Type) where
  resource : Nat
  revision : Nat
  state : State
  deriving DecidableEq

/-- A command whose permission is proved for an exact model, actor and snapshot.
    It carries no proof of external authentication or current database state. -/
structure Prepared (model : Model) (actor : String) (base : Snapshot model.State) where
  command : model.Command
  authorized : model.permits actor base.state command

abbrev Committer (model : Model) := (actor : String) →
  (base live : Snapshot model.State) → Prepared model actor base → Option (Snapshot model.State)

/-- Pure atomic-step reference. Full equality makes the snapshot relation explicit.
    Replacing it by a revision comparison needs a resource/version uniqueness invariant. -/
def commitReference (model : Model) [DecidableEq model.State] : Committer model :=
  fun _actor base live proposal =>
    if base = live then
      some ⟨live.resource, live.revision + 1, model.next live.state proposal.command⟩
    else none

inductive CommitClaim where
  | rejectsStale
  | specifiedSuccess
  | succeedsWhenCurrent
  deriving Repr, BEq, DecidableEq

def commitCatalogue (model : Model) : Catalogue (Committer model) where
  Claim := CommitClaim
  meaning run
    | .rejectsStale => ∀ actor base live proposal,
        base ≠ live → run actor base live proposal = none
    | .specifiedSuccess => ∀ actor base live proposal after,
        run actor base live proposal = some after →
          model.permits actor live.state proposal.command ∧
          after.resource = live.resource ∧
          after.revision = live.revision + 1 ∧
          after.state = model.next live.state proposal.command
    | .succeedsWhenCurrent => ∀ actor base proposal,
        ∃ after, run actor base base proposal = some after

def commitRegistry (model : Model) [DecidableEq model.State] :
    Registry (commitCatalogue model) where
  implementation := commitReference model
  evidence
    | .rejectsStale => .proved (by
        intro actor base live proposal h
        simp [commitReference, h])
    | .specifiedSuccess => .proved (by
        intro actor base live proposal after h
        by_cases eq : base = live
        · subst live
          simp [commitReference] at h
          subst after
          exact ⟨proposal.authorized, rfl, rfl, rfl⟩
        · simp [commitReference, eq] at h)
    | .succeedsWhenCurrent => .proved (by
        intro actor base proposal
        exact ⟨⟨base.resource, base.revision + 1, model.next base.state proposal.command⟩,
          by simp [commitReference]⟩)

namespace Chess
open LeanChess

structure Play where
  move : Move
  instant : Instant

def next (state : GameState) (command : Play) : GameState :=
  applyEvent state (.moved command.move command.instant)

/-- Reuse the actual game transition. The separate application policy supplies authority.
    Clock-source authenticity is deliberately outside this pure model. -/
abbrev model : Model where
  State := GameState
  Command := Play
  permits actor state command :=
    (state.agreement.person state.position.side).id = actor ∧
      (next state command).ply = state.ply + 1
  next := next

def base : Snapshot GameState := ⟨10, 0, initial sample⟩

def e4 : Play := ⟨mv .e .r2 .e .r4, ⟨1000⟩⟩

def prepare (actor : String) (base : Snapshot GameState) (command : Play) :
    Option (Prepared model actor base) :=
  if h : model.permits actor base.state command then some ⟨command, h⟩ else none

#guard (prepare "w" base e4).isSome
#guard (prepare "b" base e4).isNone

def runExample (live : Snapshot GameState) : Option Nat := do
  let proposal ← prepare "w" base e4
  let after ← commitReference model "w" base live proposal
  return after.state.ply

#guard runExample base == some 1
#guard runExample { base with revision := 1 } == none
#guard runExample { base with resource := 11 } == none

-- An independently obtained proof of a Black command cannot stand in for a White proposal.
#check_failure (fun (p : Prepared model "b" base) => commitReference model "w" base base p)

end Chess

namespace Reservation

structure State where
  owner : String
  reserved : Bool
  deriving DecidableEq

inductive Command where
  | reserve

abbrev model : Model where
  State := State
  Command := Command
  permits actor state _ := actor = state.owner ∧ state.reserved = false
  next state _ := { state with reserved := true }

def base : Snapshot State := ⟨20, 0, ⟨"Alice", false⟩⟩

def proposal : Prepared model "Alice" base := ⟨.reserve, by decide⟩

#guard ((commitReference model "Alice" base base proposal).map (·.state.reserved)) == some true
#guard (commitRegistry model).query .specifiedSuccess == .proved

end Reservation

/- This is an admission predicate on evidence, not a promise about an IO adapter. -/
#guard (commitRegistry Chess.model).query .rejectsStale == .proved
#guard (commitRegistry Chess.model).query .succeedsWhenCurrent == .proved

#print axioms scopedReader_confined
#print axioms scanThenFilter_not_confined
#print axioms Registry.require
#print axioms commitRegistry

end Theoric.Workshop
