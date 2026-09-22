/-
  Admission. What a seat may propose, and what the server appends.

  A person proposes a `Command` for a seat. The server fixes the seat and
  the instant and asks the fold. The answer is one of three:

  * accepted: one event, and the fold after it;
  * refused: nothing, and why;
  * flagged: nothing appended. The clock had run out before the act, and
    the fold at that instant already shows the flag. Time passing is not
    an event.

  This file imports the game and nothing else. A store, a socket, a page,
  and a clock reading are the host's. `api/Admit.lean` connects them to
  this and adds nothing to the meaning.
-/

import domain.Game

namespace LeanChess

/-- What a person proposes. No seat and no instant: admission fixes both. -/
inductive Command where
  | play (move : Move)
  | resign
  | offer
  | accept
  | decline
  | claimThreefold (intended : Option Move)
  | claimFifty (intended : Option Move)
  | abort
  deriving Repr, DecidableEq

/-- The event this command becomes, for `seat` at `t`. -/
def Command.event (seat : Color) (t : Instant) : Command → GameEvent
  | .play m => .moved m t
  | .resign => .resigned seat t
  | .offer => .drawOffered seat t
  | .accept => .drawAccepted seat t
  | .decline => .drawDeclined seat t
  | .claimThreefold m => .claimedThreefold seat m t
  | .claimFifty m => .claimedFifty seat m t
  | .abort => .aborted seat t

/-- Only the side to move may play, offer, or claim. Resigning, answering
    an offer, and aborting are for either seat; the fold says when. -/
def Command.needsTurn : Command → Bool
  | .play _ | .offer | .claimThreefold _ | .claimFifty _ => true
  | .resign | .accept | .decline | .abort => false

/-- The command a stored event was. -/
def GameEvent.command : GameEvent → Command
  | .moved m _ => .play m
  | .resigned _ _ => .resign
  | .drawOffered _ _ => .offer
  | .drawAccepted _ _ => .accept
  | .drawDeclined _ _ => .decline
  | .claimedThreefold _ m _ => .claimThreefold m
  | .claimedFifty _ m _ => .claimFifty m
  | .aborted _ _ => .abort

/-- The seat a stored event was for. A move is for the side to move in `s`. -/
def GameEvent.seat (s : GameState) : GameEvent → Color
  | .moved _ _ => s.position.side
  | .resigned c _ | .drawOffered c _ | .drawAccepted c _ | .drawDeclined c _
  | .claimedThreefold c _ _ | .claimedFifty c _ _ | .aborted c _ => c

theorem GameEvent.event_command (s : GameState) (ev : GameEvent) :
    ev.command.event (ev.seat s) ev.time = ev := by
  cases ev <;> rfl

theorem Command.event_time (seat : Color) (t : Instant) (cmd : Command) :
    (cmd.event seat t).time = t := by
  cases cmd <;> rfl

theorem Command.event_command (seat : Color) (t : Instant) (cmd : Command) :
    (cmd.event seat t).command = cmd := by
  cases cmd <;> rfl

inductive Refusal where
  /-- The game already has an ending. -/
  | ended
  /-- The instant is before the running clock started. -/
  | beforeClock
  /-- A play, an offer, or a claim by the seat not to move. -/
  | notYourTurn
  /-- The fold leaves the game as it was. -/
  | notAdmitted
  deriving Repr, DecidableEq

inductive Outcome where
  | accepted (event : GameEvent) (after : GameState)
  | refused (why : Refusal)
  | flagged (ending : Ending) (after : GameState)
  deriving Repr, DecidableEq

/-- The log after an outcome: one more event, or the same log. -/
def Outcome.append (events : List GameEvent) : Outcome → List GameEvent
  | .accepted ev _ => events ++ [ev]
  | _ => events

/-- The fold after an outcome. -/
def Outcome.next (s : GameState) : Outcome → GameState
  | .accepted _ after => after
  | _ => s

/-- Admission of `cmd` for `seat` at `now`, against the fold `s`.
    Precedence: an ending, then an instant before the clock, then the
    flag, then the turn, then the fold. -/
def admit (s : GameState) (seat : Color) (cmd : Command) (now : Instant) : Outcome :=
  if s.ending.isSome then .refused .ended
  else if now.ms < s.runningSince.ms then .refused .beforeClock
  else if expired s now then .flagged (flagEnding s) (freezeFlag s)
  else if cmd.needsTurn && seat != s.position.side then .refused .notYourTurn
  else if applyEvent s (cmd.event seat now) = s then .refused .notAdmitted
  else .accepted (cmd.event seat now) (applyEvent s (cmd.event seat now))

/- ====================================================================
   What an accepted outcome is
   ==================================================================== -/

theorem accepted_event {s : GameState} {seat : Color} {cmd : Command} {now : Instant}
    {ev : GameEvent} {after : GameState}
    (h : admit s seat cmd now = .accepted ev after) :
    ev = cmd.event seat now ∧ after = applyEvent s ev ∧ after ≠ s := by
  unfold admit at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  · rename_i hne
    simp only [Outcome.accepted.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, hne⟩

/-- The accepted event carries the server's instant. -/
theorem accepted_time {s : GameState} {seat : Color} {cmd : Command} {now : Instant}
    {ev : GameEvent} {after : GameState}
    (h : admit s seat cmd now = .accepted ev after) : ev.time = now := by
  rw [(accepted_event h).1]
  exact Command.event_time seat now cmd

/-- The accepted event is this command. -/
theorem accepted_command {s : GameState} {seat : Color} {cmd : Command} {now : Instant}
    {ev : GameEvent} {after : GameState}
    (h : admit s seat cmd now = .accepted ev after) : ev.command = cmd := by
  rw [(accepted_event h).1]
  exact Command.event_command seat now cmd

theorem accepted_open {s : GameState} {seat : Color} {cmd : Command} {now : Instant}
    {ev : GameEvent} {after : GameState}
    (h : admit s seat cmd now = .accepted ev after) :
    s.ending = none ∧ s.runningSince.ms ≤ now.ms ∧ expired s now = false := by
  unfold admit at h
  split at h
  · simp at h
  · rename_i h1
    split at h
    · simp at h
    · rename_i h2
      split at h
      · simp at h
      · rename_i h3
        refine ⟨?_, ?_, ?_⟩
        · cases he : s.ending with
          | none => rfl
          | some e => simp [he] at h1
        · omega
        · simpa using h3

/-- A play, an offer, or a claim was accepted for the side to move. -/
theorem accepted_turn {s : GameState} {seat : Color} {cmd : Command} {now : Instant}
    {ev : GameEvent} {after : GameState}
    (h : admit s seat cmd now = .accepted ev after) (ht : cmd.needsTurn = true) :
    seat = s.position.side := by
  unfold admit at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  · rename_i h4
    simp [ht] at h4
    exact h4

/-- The accepted event is for the seat that proposed it. -/
theorem accepted_seat {s : GameState} {seat : Color} {cmd : Command} {now : Instant}
    {ev : GameEvent} {after : GameState}
    (h : admit s seat cmd now = .accepted ev after) : ev.seat s = seat := by
  have hev := (accepted_event h).1
  cases cmd with
  | play m =>
    rw [hev]
    exact (accepted_turn h rfl).symm
  | _ => rw [hev]; rfl

theorem guardTime_open {s : GameState} {t : Instant} {k : GameState → GameState}
    (h1 : s.ending = none) (h2 : ¬ t.ms < s.runningSince.ms) (h3 : expired s t = false) :
    guardTime s t k = k s := by
  simp [guardTime, h1, h2, h3]

theorem finishPlay_position (s : GameState) (c : Color) :
    (finishPlay s c).position = s.position := by
  unfold finishPlay addIncrement
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem finishPlay_ply (s : GameState) (c : Color) : (finishPlay s c).ply = s.ply := by
  unfold finishPlay addIncrement
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem finishPlay_history (s : GameState) (c : Color) :
    (finishPlay s c).history = s.history := by
  unfold finishPlay addIncrement
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem playMove_some {s : GameState} {m : Move} {t : Instant} {s' : GameState}
    (h : playMove s m t = some s') :
    ∃ p, applyMove s.position m = some p ∧ s'.position = p ∧ s'.ply = s.ply + 1 ∧
      s'.history = s.history ++ [posKey p] ∧ s'.claim = none := by
  unfold playMove at h
  cases hm : applyMove s.position m with
  | none => simp [hm] at h
  | some p =>
    simp only [hm, Option.some.injEq] at h
    subst h
    exact ⟨p, rfl, rfl, rfl, rfl, rfl⟩

/-- An accepted play is a legal move by the side to move, at the server's
    instant, and the fold after it is that move played: the turn handed
    over, the ply one more, the position the move's. -/
theorem accepted_play {s : GameState} {seat : Color} {m : Move} {now : Instant}
    {ev : GameEvent} {after : GameState}
    (h : admit s seat (.play m) now = .accepted ev after) :
    seat = s.position.side ∧ ev = .moved m now ∧
      ∃ p, applyMove s.position m = some p ∧ after.position = p ∧
        after.ply = s.ply + 1 ∧ after.history = s.history ++ [posKey p] := by
  obtain ⟨hev, hafter, hne⟩ := accepted_event h
  obtain ⟨hend, hclk, hexp⟩ := accepted_open h
  refine ⟨accepted_turn h rfl, hev, ?_⟩
  subst hev
  have hce : applyEvent s (Command.event seat now (.play m)) = commitMove s m now := by
    simp only [Command.event, applyEvent]
    exact guardTime_open hend (by omega) hexp
  rw [hce] at hafter
  unfold commitMove at hafter
  cases hp : playMove s m now with
  | none =>
    rw [hp] at hafter
    exact absurd hafter hne
  | some s' =>
    rw [hp] at hafter
    obtain ⟨p, hm, hpos, hply, hhist, _⟩ := playMove_some hp
    refine ⟨p, hm, ?_, ?_, ?_⟩
    · rw [hafter, finishPlay_position, hpos]
    · rw [hafter, finishPlay_ply, hply]
    · rw [hafter, finishPlay_history, hhist]

/- ====================================================================
   What a flag and a refusal are
   ==================================================================== -/

theorem flagged_frame {s : GameState} {seat : Color} {cmd : Command} {now : Instant}
    {e : Ending} {after : GameState}
    (h : admit s seat cmd now = .flagged e after) :
    e = flagEnding s ∧ after = freezeFlag s ∧ expired s now = true := by
  unfold admit at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · rename_i h3
    simp only [Outcome.flagged.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, h3⟩
  split at h
  · simp at h
  split at h <;> simp at h

/-- A flag is what a look at that instant already shows. -/
theorem flagged_look {s : GameState} {seat : Color} {cmd : Command} {now : Instant}
    {e : Ending} {after : GameState}
    (h : admit s seat cmd now = .flagged e after) : resultAt s now = some e := by
  obtain ⟨he, _, hexp⟩ := flagged_frame h
  have hend : s.ending = none := by
    unfold expired at hexp
    cases he' : s.ending with
    | none => rfl
    | some e => simp [he'] at hexp
  simp [resultAt, hend, hexp, he]

theorem freezeFlag_ply (s : GameState) : (freezeFlag s).ply = s.ply := by
  unfold freezeFlag; split <;> rfl

theorem freezeFlag_position (s : GameState) : (freezeFlag s).position = s.position := by
  unfold freezeFlag; split <;> rfl

/-- A refusal or a flag carries no event. The log is what it was. -/
theorem not_accepted_append {s : GameState} {seat : Color} {cmd : Command} {now : Instant}
    (events : List GameEvent)
    (h : ∀ ev after, admit s seat cmd now ≠ .accepted ev after) :
    (admit s seat cmd now).append events = events := by
  cases ho : admit s seat cmd now with
  | accepted ev after => exact absurd ho (h ev after)
  | refused _ => rfl
  | flagged _ _ => rfl

set_option linter.unusedSimpArgs false in
/-- A second delivery of an accepted act is not accepted, once applying it
    again changes nothing. Which commands satisfy that premise is checked
    below, one constructor at a time. -/
theorem retry_not_accepted {s : GameState} {seat : Color} {cmd : Command} {now now' : Instant}
    {ev : GameEvent} {after : GameState}
    (_h : admit s seat cmd now = .accepted ev after)
    (hid : applyEvent after (cmd.event seat now') = after) :
    ∀ ev' after', admit after seat cmd now' ≠ .accepted ev' after' := by
  intro ev' after' hc
  unfold admit at hc
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  split at hc
  · simp at hc
  · simp [hid] at hc

/- ====================================================================
   A stored log is a history of admitted acts
   ==================================================================== -/

/-- Every event, in order, is the accepted event of its own admission. -/
def admittedFrom (s : GameState) : List GameEvent → Bool
  | [] => true
  | ev :: rest =>
    match admit s (ev.seat s) ev.command ev.time with
    | .accepted _ after => admittedFrom after rest
    | _ => false

def admittedLog (a : Agreement) (log : List GameEvent) : Bool :=
  admittedFrom (initial a) log

/-- Instants do not go backwards along the log. -/
def orderedFrom (t : Instant) : List GameEvent → Bool
  | [] => true
  | ev :: rest => t.ms ≤ ev.time.ms && orderedFrom ev.time rest

def orderedLog (a : Agreement) (log : List GameEvent) : Bool :=
  orderedFrom a.start log

/-- A log the server could have written. -/
def validLog (a : Agreement) (log : List GameEvent) : Bool :=
  admittedLog a log && orderedLog a log

theorem admittedFrom_cons_iff (s : GameState) (ev : GameEvent) (rest : List GameEvent) :
    admittedFrom s (ev :: rest) = true ↔
      ∃ ev' after, admit s (ev.seat s) ev.command ev.time = .accepted ev' after ∧
        admittedFrom after rest = true := by
  simp only [admittedFrom]
  constructor
  · intro h
    split at h
    · rename_i ev' after ho
      exact ⟨ev', after, ho, h⟩
    · simp at h
  · rintro ⟨ev', after, ho, h⟩
    rw [ho]
    exact h

theorem admitted_accepted_is_event {s : GameState} {ev ev' : GameEvent} {after : GameState}
    (h : admit s (ev.seat s) ev.command ev.time = .accepted ev' after) :
    ev' = ev ∧ after = applyEvent s ev := by
  obtain ⟨h1, h2, _⟩ := accepted_event h
  rw [GameEvent.event_command] at h1
  subst h1
  exact ⟨rfl, h2⟩

theorem admittedFrom_snoc (s : GameState) (log : List GameEvent) (ev : GameEvent) :
    admittedFrom s (log ++ [ev]) = true ↔
      admittedFrom s log = true ∧
        ∃ ev' after, admit (applyEvents s log) (ev.seat (applyEvents s log)) ev.command ev.time
          = .accepted ev' after := by
  induction log generalizing s with
  | nil =>
    simp only [List.nil_append, applyEvents, admittedFrom, true_and]
    constructor
    · intro h
      split at h
      · rename_i ev' after ho
        exact ⟨ev', after, ho⟩
      · simp at h
    · rintro ⟨ev', after, ho⟩
      rw [ho]
  | cons x xs ih =>
    rw [List.cons_append, admittedFrom_cons_iff, admittedFrom_cons_iff]
    constructor
    · rintro ⟨ev', after, ho, h⟩
      obtain ⟨rfl, rfl⟩ := admitted_accepted_is_event ho
      obtain ⟨h1, h2⟩ := (ih _).mp h
      exact ⟨⟨_, _, ho, h1⟩, h2⟩
    · rintro ⟨⟨ev', after, ho, h1⟩, h2⟩
      obtain ⟨rfl, rfl⟩ := admitted_accepted_is_event ho
      exact ⟨_, _, ho, (ih _).mpr ⟨h1, h2⟩⟩

theorem admittedLog_snoc (a : Agreement) (log : List GameEvent) (ev : GameEvent) :
    admittedLog a (log ++ [ev]) = true ↔
      admittedLog a log = true ∧
        ∃ ev' after, admit (fold a log) (ev.seat (fold a log)) ev.command ev.time
          = .accepted ev' after :=
  admittedFrom_snoc (initial a) log ev

/- ====================================================================
   Checks. Each constructor, accepted once and not twice.
   ==================================================================== -/

private def e4 : Move := mv .e .r2 .e .r4
private def e5 : Move := mv .e .r7 .e .r5

private def isAccepted : Outcome → Bool
  | .accepted _ _ => true
  | _ => false

/-- Accept once at `t`, then offer the same again at `t + 1`. -/
private def twice (s : GameState) (seat : Color) (cmd : Command) (t : Nat) : Bool × Bool :=
  match admit s seat cmd ⟨t⟩ with
  | .accepted _ after => (true, isAccepted (admit after seat cmd ⟨t + 1⟩))
  | _ => (false, false)

private def begun : GameState :=
  applyEvent (applyEvent (initial sample) (.moved e4 ⟨1000⟩)) (.moved e5 ⟨2000⟩)

private def offeredW : GameState := applyEvent begun (.drawOffered .white ⟨3000⟩)

#guard twice (initial sample) .white (.play e4) 500 == (true, false)
#guard twice begun .white .offer 3000 == (true, false)
#guard twice offeredW .black .accept 4000 == (true, false)
#guard twice offeredW .black .decline 4000 == (true, false)
#guard twice begun .white .resign 3000 == (true, false)
#guard twice (initial sample) .black .abort 500 == (true, false)
#guard twice begun .white (.claimThreefold none) 3000 == (true, false)
#guard twice begun .white (.claimFifty none) 3000 == (true, false)
#guard twice begun .white (.claimThreefold (some (mv .g .r1 .f .r3))) 3000 == (true, false)
#guard twice begun .white (.claimFifty (some (mv .g .r1 .f .r3))) 3000 == (true, false)

#guard admit (initial sample) .black (.play e4) ⟨0⟩ == .refused .notYourTurn
#guard admit (initial sample) .black .offer ⟨0⟩ == .refused .notYourTurn
#guard admit (initial sample) .white (.play (mv .e .r2 .e .r5)) ⟨0⟩ == .refused .notAdmitted
#guard admit begun .white .abort ⟨3000⟩ == .refused .notAdmitted
#guard admit begun .black .accept ⟨3000⟩ == .refused .notAdmitted
#guard (match admit (initial sample) .white (.play e4) ⟨300000⟩ with
  | .flagged (.flag .black) after => after.ply == 0 && after.whiteMs == 0
  | _ => false)
#guard admit (initial sample) .white (.play e4) ⟨0⟩ ==
  .accepted (.moved e4 ⟨0⟩) (applyEvent (initial sample) (.moved e4 ⟨0⟩))
#guard (match admit (applyEvent begun (.resigned .white ⟨3000⟩)) .black (.play e4) ⟨4000⟩ with
  | .refused .ended => true
  | _ => false)
#guard (match admit begun .white (.play e4) ⟨1500⟩ with
  | .refused .beforeClock => true
  | _ => false)

#guard admittedLog sample [.moved e4 ⟨1000⟩, .moved e5 ⟨2000⟩]
#guard !admittedLog sample [.moved e5 ⟨1000⟩]
#guard !admittedLog sample [.moved e4 ⟨1000⟩, .moved e4 ⟨2000⟩]
#guard !admittedLog sample [.moved e4 ⟨300000⟩]
#guard validLog sample [.moved e4 ⟨1000⟩, .drawOffered .black ⟨1500⟩, .moved e5 ⟨2000⟩]
#guard !validLog sample [.moved e4 ⟨1000⟩, .drawOffered .black ⟨900⟩]
#guard !orderedLog sample [.moved e4 ⟨1000⟩, .drawOffered .black ⟨900⟩]

end LeanChess
