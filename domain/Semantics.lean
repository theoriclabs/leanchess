/-
  The log, and what the handler is allowed to do to it.

  The stored log is a list of accepted acts. Appending one and folding is
  the same as applying that act to the fold. A step is one admission
  (`domain/Command.lean`): the log grows by the accepted event, or it does
  not grow. Two writes that both read the same log become one of the two
  sequential results. A second delivery of an accepted act does not grow
  the log.

  The older model here appended whenever the fold changed. That counted a
  flag as an appended move, which the server never wrote. `step` is now
  the admission the server runs.
-/

import domain.Command

namespace LeanChess

theorem applyEvents_snoc (s : GameState) (es : List GameEvent) (e : GameEvent) :
    applyEvents s (es ++ [e]) = applyEvent (applyEvents s es) e := by
  induction es generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append]
    simp only [applyEvents]
    rw [ih]

theorem fold_snoc (a : Agreement) (es : List GameEvent) (e : GameEvent) :
    fold a (es ++ [e]) = applyEvent (fold a es) e := by
  simp [fold, applyEvents_snoc]

/-- The pure step the handler takes: admit against the fold of the log,
    and append only an accepted event. -/
structure LogStep where
  events : List GameEvent
  outcome : Outcome

def step (a : Agreement) (events : List GameEvent) (seat : Color) (cmd : Command)
    (now : Instant) : LogStep :=
  let o := admit (fold a events) seat cmd now
  ⟨o.append events, o⟩

theorem step_outcome (a : Agreement) (events : List GameEvent) (seat : Color) (cmd : Command)
    (now : Instant) : (step a events seat cmd now).outcome = admit (fold a events) seat cmd now :=
  rfl

/-- An accepted step appends its event, and the fold of the longer log is
    the state admission promised. -/
theorem step_accepted {a : Agreement} {events : List GameEvent} {seat : Color} {cmd : Command}
    {now : Instant} {ev : GameEvent} {after : GameState}
    (h : (step a events seat cmd now).outcome = .accepted ev after) :
    (step a events seat cmd now).events = events ++ [ev] ∧ fold a (events ++ [ev]) = after := by
  rw [step_outcome] at h
  obtain ⟨_, hafter, _⟩ := accepted_event h
  constructor
  · simp [step, h, Outcome.append]
  · rw [fold_snoc, hafter]

/-- A refused or flagged step leaves the log as it was. -/
theorem step_not_accepted {a : Agreement} {events : List GameEvent} {seat : Color}
    {cmd : Command} {now : Instant}
    (h : ∀ ev after, (step a events seat cmd now).outcome ≠ .accepted ev after) :
    (step a events seat cmd now).events = events := by
  simp only [step]
  exact not_accepted_append events (fun ev after => h ev after)

/-- A flagged step appends nothing, and the flag is what a look at the same
    instant shows of the unchanged log. -/
theorem step_flagged {a : Agreement} {events : List GameEvent} {seat : Color} {cmd : Command}
    {now : Instant} {e : Ending} {after : GameState}
    (h : (step a events seat cmd now).outcome = .flagged e after) :
    (step a events seat cmd now).events = events ∧ resultAt (fold a events) now = some e := by
  rw [step_outcome] at h
  constructor
  · simp [step, h, Outcome.append]
  · exact flagged_look h

/-- A log grown only by accepted steps is an admitted log. -/
theorem step_admitted {a : Agreement} {events : List GameEvent} {seat : Color} {cmd : Command}
    {now : Instant} {ev : GameEvent} {after : GameState}
    (hlog : admittedLog a events = true)
    (h : (step a events seat cmd now).outcome = .accepted ev after) :
    admittedLog a (step a events seat cmd now).events = true := by
  rw [(step_accepted h).1, admittedLog_snoc]
  refine ⟨hlog, ?_⟩
  rw [step_outcome] at h
  have hseat := accepted_seat h
  have hcmd := accepted_command h
  have htime := accepted_time h
  subst hseat hcmd htime
  exact ⟨ev, after, h⟩

/-- Which of two racing writes compare-and-swap keeps. The other observes
    `.stale` and is not in the log. -/
inductive Writer where
  | first
  | second

def cas (events : List GameEvent) (o1 o2 : Outcome) : Writer → List GameEvent
  | .first => o1.append events
  | .second => o2.append events

theorem cas_linear (events : List GameEvent) (o1 o2 : Outcome) (w : Writer) :
    cas events o1 o2 w = events
      ∨ (∃ ev after, o1 = .accepted ev after ∧ cas events o1 o2 w = events ++ [ev])
      ∨ (∃ ev after, o2 = .accepted ev after ∧ cas events o1 o2 w = events ++ [ev]) := by
  cases w with
  | first =>
    cases o1 with
    | accepted ev after => exact Or.inr (Or.inl ⟨ev, after, rfl, rfl⟩)
    | refused _ => exact Or.inl rfl
    | flagged _ _ => exact Or.inl rfl
  | second =>
    cases o2 with
    | accepted ev after => exact Or.inr (Or.inr ⟨ev, after, rfl, rfl⟩)
    | refused _ => exact Or.inl rfl
    | flagged _ _ => exact Or.inl rfl

/-- The fold of what the winner wrote is the state its admission promised. -/
theorem cas_fold (a : Agreement) (events : List GameEvent) (seat1 seat2 : Color)
    (cmd1 cmd2 : Command) (now1 now2 : Instant) (w : Writer) :
    let before := fold a events
    let o1 := admit before seat1 cmd1 now1
    let o2 := admit before seat2 cmd2 now2
    fold a (cas events o1 o2 w) =
      match w with
      | .first => o1.next before
      | .second => o2.next before := by
  intro before o1 o2
  cases w with
  | first =>
    show fold a (o1.append events) = o1.next before
    cases ho : o1 with
    | accepted ev after =>
      simp only [Outcome.append, Outcome.next]
      rw [fold_snoc]
      exact (accepted_event ho).2.1.symm
    | refused _ => rfl
    | flagged _ _ => rfl
  | second =>
    show fold a (o2.append events) = o2.next before
    cases ho : o2 with
    | accepted ev after =>
      simp only [Outcome.append, Outcome.next]
      rw [fold_snoc]
      exact (accepted_event ho).2.1.symm
    | refused _ => rfl
    | flagged _ _ => rfl

/-
  Concrete checks. A play at the instant the clock runs out is a flag:
  the step appends nothing and the look shows the flag. Not a stored move.
-/

private def pair : Agreement where
  white := { id := "ada" }
  black := { id := "bel" }
  rated := true
  time := .realtime 300000 0
  start := ⟨0⟩

private def e4 : Move := mv .e .r2 .e .r4

#guard (step pair [] .white (.play e4) ⟨1000⟩).events == [.moved e4 ⟨1000⟩]
#guard (step pair [] .white (.play e4) ⟨300000⟩).events == []
#guard (match (step pair [] .white (.play e4) ⟨300000⟩).outcome with
  | .flagged (.flag .black) _ => true
  | _ => false)
#guard resultAt (fold pair []) ⟨300000⟩ == some (.flag .black)
#guard (step pair [] .white (.play (mv .e .r7 .e .r5)) ⟨1000⟩).events == []
#guard (step pair [.moved e4 ⟨1000⟩] .white (.play e4) ⟨2000⟩).events == [.moved e4 ⟨1000⟩]

end LeanChess
