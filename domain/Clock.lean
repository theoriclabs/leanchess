/-
  Time. One source, one meaning, and what a look answers about it.

  * The instant of an act is the server's, fixed at admission
    (`domain/Command.lean`). A client's figure is not an input.
  * A current look observes the fold of the whole log at the server's
    instant. A historical look at `d` is the fold of the events at or
    before `d`, observed at `d`: `lookback`. Projecting only the clock of
    the full fold onto an earlier instant is not a historical look, and
    nothing here does that.
  * Time passing is not an event. The flag is derived: `resultAt` reads it
    off the running clock. Once a flag has fallen at `d`, every later look
    sees it. An act after it is refused or flagged, never appended.
  * An act that ends the game charges the running clock up to the act's
    instant and stops it. A look after the ending reads those figures, at
    any instant.

  The boundary. The allowance is used up at exactly `runningSince + allowance`:
  a play at that instant is the flag. One millisecond earlier it is a play.
-/

import domain.Command

namespace LeanChess

/- ====================================================================
   Historical looks
   ==================================================================== -/

/-- The events at or before `d`. On an ordered log, the prefix. -/
def prefixAt (log : List GameEvent) (d : Instant) : List GameEvent :=
  log.takeWhile fun ev => decide (ev.time.ms ≤ d.ms)

/-- A historical look: the fold of the log up to `d`, to be observed at `d`. -/
def lookback (a : Agreement) (log : List GameEvent) (d : Instant) : GameState :=
  fold a (prefixAt log d)

theorem prefixAt_all (d : Instant) : ∀ (log : List GameEvent),
    (∀ ev ∈ log, ev.time.ms ≤ d.ms) → prefixAt log d = log
  | [], _ => rfl
  | ev :: rest, h => by
    have h1 : ev.time.ms ≤ d.ms := h ev (by simp)
    have h2 : prefixAt rest d = rest := prefixAt_all d rest (fun e he => h e (by simp [he]))
    simp only [prefixAt, List.takeWhile] at h2 ⊢
    simp [h1, h2]

/-- A look at or after the last act is the current fold. -/
theorem lookback_current (a : Agreement) (log : List GameEvent) (d : Instant)
    (h : ∀ ev ∈ log, ev.time.ms ≤ d.ms) : lookback a log d = fold a log := by
  simp [lookback, prefixAt_all d log h]

theorem prefixAt_isPrefix (log : List GameEvent) (d : Instant) :
    (prefixAt log d).IsPrefix log :=
  List.takeWhile_prefix _

/-- Nothing after `d` is in the prefix. -/
theorem prefixAt_time (d : Instant) : ∀ (log : List GameEvent),
    ∀ ev ∈ prefixAt log d, ev.time.ms ≤ d.ms
  | [], _, h => by simp [prefixAt] at h
  | x :: rest, ev, h => by
    simp only [prefixAt, List.takeWhile] at h
    by_cases hx : x.time.ms ≤ d.ms
    · simp [hx] at h
      rcases h with rfl | h
      · exact hx
      · exact prefixAt_time d rest ev (by simpa [prefixAt] using h)
    · simp [hx] at h

/- ====================================================================
   The flag
   ==================================================================== -/

theorem resultAt_ended {s : GameState} {e : Ending} (h : s.ending = some e) (d : Instant) :
    resultAt s d = some e := by
  simp [resultAt, h]

theorem expired_mono {s : GameState} {d d' : Instant}
    (h : expired s d = true) (hle : d.ms ≤ d'.ms) : expired s d' = true := by
  unfold expired elapsed at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨h1, by omega⟩, ?_⟩
  split at h3 <;> split <;> omega

/-- Once the flag has fallen, every later look sees it. -/
theorem resultAt_mono {s : GameState} {d d' : Instant} {e : Ending}
    (h : resultAt s d = some e) (hle : d.ms ≤ d'.ms) : resultAt s d' = some e := by
  unfold resultAt at *
  cases he : s.ending with
  | some e' => rw [he] at h; simpa [he] using h
  | none =>
    rw [he] at h
    simp only at h ⊢
    split at h
    · rename_i hx
      rw [if_pos (expired_mono hx hle)]
      exact h
    · simp at h

/-- The side to move has nothing left once the flag has fallen. -/
theorem remaining_at_flag {s : GameState} {d : Instant} (h : expired s d = true) :
    remaining s s.position.side d = 0 := by
  unfold expired at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, _⟩, h3⟩ := h
  have hend : s.ending.isSome = false := by simp [h1]
  simp [remaining, hend, h3]

/- ====================================================================
   The clock after an ending
   ==================================================================== -/

theorem endAt_ending (s : GameState) (t : Instant) (e : Ending) :
    (endAt s t e).ending = some e := by
  unfold endAt spend; split <;> rfl

theorem endAt_side (s : GameState) (t : Instant) (e : Ending) :
    (endAt s t e).position = s.position := by
  unfold endAt spend; split <;> rfl

theorem spend_side (s : GameState) (t : Instant) : (spend s t).position = s.position := by
  unfold spend; split <;> rfl

theorem spend_agreement (s : GameState) (t : Instant) : (spend s t).agreement = s.agreement := by
  unfold spend; split <;> rfl

/-- An ending charges the running clock up to its own instant and stops it.
    A look at any later instant reads what a look at the ending's instant
    read: for the side to move, the other side, in either time control. -/
theorem remaining_endAt (s : GameState) (t : Instant) (e : Ending) (c : Color) (d : Instant)
    (hopen : s.ending = none) :
    remaining (endAt s t e) c d = remaining s c t := by
  unfold remaining endAt spend allowance
  rw [hopen]
  cases hc : c == s.position.side <;> cases hs : s.position.side <;> cases c <;>
    simp_all [elapsed]

/-- A look after an ending does not change with the instant. -/
theorem remaining_frozen {s : GameState} {e : Ending} (h : s.ending = some e) (c : Color)
    (d d' : Instant) : remaining s c d = remaining s c d' := by
  simp [remaining, h]

/- ====================================================================
   Rating eligibility is a reading of the same result
   ==================================================================== -/

theorem counts_iff (s : GameState) (d : Instant) :
    countsForRating s d = true ↔
      s.agreement.effectiveRated = true ∧ 2 ≤ s.ply ∧
        ∃ e, resultAt s d = some e ∧ e ≠ .abort := by
  unfold countsForRating
  cases hr : resultAt s d with
  | none => simp
  | some e => cases e <;> simp

/-- A flag counts once the look reaches it, and not before. -/
theorem counts_mono {s : GameState} {d d' : Instant}
    (h : countsForRating s d = true) (hle : d.ms ≤ d'.ms) : countsForRating s d' = true := by
  rw [counts_iff] at *
  obtain ⟨h1, h2, e, he, hne⟩ := h
  exact ⟨h1, h2, e, resultAt_mono he hle, hne⟩

/- ====================================================================
   Checks. The boundary, the increment, correspondence, the reproductions.
   ==================================================================== -/

private def e4 : Move := mv .e .r2 .e .r4
private def e5 : Move := mv .e .r7 .e .r5

private def begun : GameState :=
  applyEvent (applyEvent (initial sample) (.moved e4 ⟨1000⟩)) (.moved e5 ⟨2000⟩)

/- White has 299000 after e4 at 1000, and is to move from 2000. -/
#guard remaining begun .white ⟨2000⟩ == 299000
#guard remaining begun .white ⟨7000⟩ == 294000
#guard resultAt begun ⟨300999⟩ == none
#guard resultAt begun ⟨301000⟩ == some (.flag .black)
#guard countsForRating begun ⟨300999⟩ == false
#guard countsForRating begun ⟨301000⟩ == true
#guard remaining begun .white ⟨301000⟩ == 0
#guard remaining begun .black ⟨301000⟩ == 299000

/-- Resignation at 7000 stops White's clock at 294000. -/
private def resigned : GameState := applyEvent begun (.resigned .white ⟨7000⟩)
#guard resigned.ending == some (.resign .black)
#guard remaining resigned .white ⟨7000⟩ == 294000
#guard remaining resigned .white ⟨999999⟩ == 294000
#guard remaining resigned .black ⟨999999⟩ == 299000
#guard countsForRating resigned ⟨7000⟩

/- The same instant for an agreed draw and a claim. -/
#guard remaining (applyEvent (applyEvent begun (.drawOffered .white ⟨3000⟩))
  (.drawAccepted .black ⟨7000⟩)) .white ⟨999999⟩ == 294000

/- An abort before both have played stops Black's clock. -/
#guard remaining (applyEvent (applyEvent (initial sample) (.moved e4 ⟨1000⟩))
  (.aborted .white ⟨5000⟩)) .black ⟨999999⟩ == 296000

/-- Increment. 60000 with 1000: e4 at 2500 leaves 58500. -/
private def inc : Agreement := { sample with time := .realtime 60000 1000 }
#guard remaining (applyEvent (initial inc) (.moved e4 ⟨2500⟩)) .white ⟨2500⟩ == 58500
#guard remaining (applyEvent (initial inc) (.moved e4 ⟨2500⟩)) .black ⟨2500⟩ == 60000

/-- Correspondence. One day for the move; a fresh day for the reply. -/
private def postal : Agreement := { sample with time := .correspondence 1 }
private def day : Nat := 24 * 60 * 60 * 1000
#guard remaining (applyEvent (initial postal) (.moved e4 ⟨1000⟩)) .black ⟨6000⟩ == day - 5000
#guard remaining (applyEvent (initial postal) (.moved e4 ⟨1000⟩)) .white ⟨6000⟩ == day
#guard resultAt (applyEvent (initial postal) (.moved e4 ⟨1000⟩)) ⟨1000 + day⟩ == some (.flag .white)
#guard resultAt (applyEvent (initial postal) (.moved e4 ⟨1000⟩)) ⟨999 + day⟩ == none

/-- A historical look is the prefix. At 1500 the log is one move long. -/
private def log2 : List GameEvent := [.moved e4 ⟨1000⟩, .moved e5 ⟨2000⟩]
#guard (lookback sample log2 ⟨1500⟩).ply == 1
#guard (lookback sample log2 ⟨2000⟩).ply == 2
#guard (lookback sample log2 ⟨999⟩).ply == 0
#guard remaining (lookback sample log2 ⟨1500⟩) .black ⟨1500⟩ == 299500
#guard lookback sample log2 ⟨5000⟩ == fold sample log2

/- Repeated terminal observations agree. -/
#guard resultAt resigned ⟨7000⟩ == resultAt resigned ⟨8000⟩
#guard resultAt begun ⟨301000⟩ == resultAt begun ⟨400000⟩

end LeanChess
