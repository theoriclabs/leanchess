/-
  What the handler is allowed to store, and what a race is allowed to become.

  The stored log is a list of acts. Appending one and folding is the same as
  applying that act to the fold. Two writes that both read the same log
  become one of the two sequential results. A retried act is silent when
  applying it twice is the same as applying it once.
-/

import domain.Game

namespace LeanChess

/-- The fields the handler treats as a change. History is not one of them:
    a move that changes history also changes the position and the ply. -/
def changed (before after : GameState) : Bool :=
  !(decide (before.ply = after.ply) && decide (before.ending = after.ending) &&
    decide (before.offer = after.offer) && decide (before.position = after.position) &&
    decide (before.whiteMs = after.whiteMs) && decide (before.blackMs = after.blackMs) &&
    decide (before.runningSince = after.runningSince))

theorem changed_self (s : GameState) : changed s s = false := by
  unfold changed
  simp

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

/-- The pure step the handler takes: append the act only when the fold changes. -/
structure LogStep where
  events : List GameEvent
  admitted : Bool

def step (a : Agreement) (events : List GameEvent) (ev : GameEvent) : LogStep :=
  if changed (fold a events) (applyEvent (fold a events) ev) then
    ⟨events ++ [ev], true⟩
  else
    ⟨events, false⟩

theorem step_fold (a : Agreement) (events : List GameEvent) (ev : GameEvent)
    (h : (step a events ev).admitted = true) :
    fold a (step a events ev).events = applyEvent (fold a events) ev := by
  by_cases hc : changed (fold a events) (applyEvent (fold a events) ev) = true
  · simp [step, hc, fold_snoc] at h ⊢
  · have hf : changed (fold a events) (applyEvent (fold a events) ev) = false := by
      cases hb : changed (fold a events) (applyEvent (fold a events) ev) <;> simp_all
    simp [step, hf] at h

/-- A second delivery of the same act appends nothing, once applying the act
    twice equals applying it once. -/
theorem retry_silent (a : Agreement) (events : List GameEvent) (ev : GameEvent)
    (hid : applyEvent (applyEvent (fold a events) ev) ev = applyEvent (fold a events) ev) :
    (step a (step a events ev).events ev).admitted = false := by
  by_cases hc : changed (fold a events) (applyEvent (fold a events) ev) = true
  · simp [step, hc, fold_snoc, hid, changed_self]
  · have hf : changed (fold a events) (applyEvent (fold a events) ev) = false := by
      cases hb : changed (fold a events) (applyEvent (fold a events) ev) <;> simp_all
    simp [step, hf]

/-- Which of two racing writes compare-and-swap keeps. The other observes
    `.stale` and is not in the log. -/
inductive Writer where
  | first
  | second

def cas (events : List GameEvent) (e1 e2 : GameEvent) (a1 a2 : Bool) : Writer → List GameEvent
  | .first => if a1 then events ++ [e1] else events
  | .second => if a2 then events ++ [e2] else events

theorem cas_linear (events : List GameEvent) (e1 e2 : GameEvent) (a1 a2 : Bool) (w : Writer) :
    cas events e1 e2 a1 a2 w = events
      ∨ cas events e1 e2 a1 a2 w = events ++ [e1]
      ∨ cas events e1 e2 a1 a2 w = events ++ [e2] := by
  cases w <;> cases a1 <;> cases a2 <;> simp [cas]

theorem cas_fold (a : Agreement) (events : List GameEvent) (e1 e2 : GameEvent) (w : Writer) :
    let before := fold a events
    fold a (cas events e1 e2
        (changed before (applyEvent before e1))
        (changed before (applyEvent before e2)) w) =
      match w with
      | .first =>
          if changed before (applyEvent before e1) then applyEvent before e1 else before
      | .second =>
          if changed before (applyEvent before e2) then applyEvent before e2 else before := by
  cases w with
  | first =>
    by_cases h : changed (fold a events) (applyEvent (fold a events) e1) = true
    · simp [cas, h, fold_snoc]
    · have hf : changed (fold a events) (applyEvent (fold a events) e1) = false := by
        cases hb : changed (fold a events) (applyEvent (fold a events) e1) <;> simp_all
      simp [cas, hf]
  | second =>
    by_cases h : changed (fold a events) (applyEvent (fold a events) e2) = true
    · simp [cas, h, fold_snoc]
    · have hf : changed (fold a events) (applyEvent (fold a events) e2) = false := by
        cases hb : changed (fold a events) (applyEvent (fold a events) e2) <;> simp_all
      simp [cas, hf]

/-
  Concrete idempotence. A universal `applyEvent (applyEvent s e) e = applyEvent s e`
  is false for a hand-built state whose opponent already has no time: the first
  play is legal, and the second look at the same instant flags. `initial` does
  not build that state. Both clocks start equal, a successful play leaves a
  positive remainder, and a flag writes the ending, so a fold from a positive
  clock does not reach it. The opening checks below are that fold.
-/

private def pair : Agreement where
  white := { id := "ada" }
  black := { id := "bel" }
  rated := true
  time := .realtime 300000 0
  start := ⟨0⟩

private def at1 (m : Move) : GameEvent := .moved m ⟨1000⟩

theorem opening_e4_idem :
    applyEvent (applyEvent (initial pair) (at1 (mv .e .r2 .e .r4))) (at1 (mv .e .r2 .e .r4))
      = applyEvent (initial pair) (at1 (mv .e .r2 .e .r4)) := by
  native_decide

theorem opening_illegal_idem :
    applyEvent (applyEvent (initial pair) (at1 (mv .e .r7 .e .r5))) (at1 (mv .e .r7 .e .r5))
      = applyEvent (initial pair) (at1 (mv .e .r7 .e .r5)) := by
  native_decide

theorem opening_offer_idem :
    let offer := GameEvent.drawOffered .white ⟨0⟩
    applyEvent (applyEvent (initial pair) offer) offer = applyEvent (initial pair) offer := by
  native_decide

end LeanChess
