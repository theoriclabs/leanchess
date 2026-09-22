/-
  Command admission at the API. The seat and the instant are fixed here,
  before an event is stored. The meaning is `LeanChess.admit` in
  `domain/Command.lean`; this file maps its outcome onto the wire and
  says what each route may append.

  Command time is the server's monotonic clock, sampled inside
  `Server.handle`'s lock after the log has been loaded and immediately
  before this function runs. Waiting for that lock is on the mover's
  clock: the move is not committed, and the opponent's clock does not
  start, until then. The sample is not a durable epoch across restart.
  A client `at` is not an argument. On a command it is ignored when it
  is a whole number and rejected when it is not. It cannot move this
  instant.

  A current look observes that same clock. A historical look is an
  explicit `at` at or before it, and it does not admit an act. A future
  `at` is rejected. A historical look folds the prefix of the log up to
  that instant (`lookback` in `domain/Clock.lean`).

  Host assumptions this file does not discharge:
  * the process mutex around `handle` keeps another command from
    appending between the re-read and the update;
  * `IO.monoMsNow` does not go backwards in one process;
  * a browser token is presented only to the normalized origin that
    issued it (`web/origin.mjs`). A production page uses its own origin.
    A loopback `?api=` override, on a local page, selects a separate
    session and does not receive a token minted for another origin.
    A saved session with no issuer is deleted, not forwarded.
-/

import api.Wire
import domain.Semantics

namespace LeanChess.Api

open Lean LeanChess

inductive AdmitError where
  | notYourTurn
  deriving Repr, DecidableEq

/-- What the requested act did, on the wire. A flag is not a played move. -/
inductive Outcome where
  | played
  | refused
  | flagged
  deriving Repr, DecidableEq

def Outcome.wire : Outcome → String
  | .played => "played"
  | .refused => "refused"
  | .flagged => "flagged"

structure Decision where
  outcome : Outcome
  /-- `some` only when that event is the one to append. -/
  event : Option GameEvent
  deriving Repr, DecidableEq

/-- The domain's answer, on the wire. `notYourTurn` is the one refusal
    the API reports as forbidden rather than as an unchanged game. -/
def admit (before : GameState) (seat : Color) (cmd : Command) (now : Nat) :
    Except AdmitError Decision :=
  match LeanChess.admit before seat cmd ⟨now⟩ with
  | .accepted ev _ => .ok ⟨.played, some ev⟩
  | .refused .notYourTurn => .error .notYourTurn
  | .refused _ => .ok ⟨.refused, none⟩
  | .flagged _ _ => .ok ⟨.flagged, none⟩

/-- A fold read earlier does not authorize. The commit fold does. -/
def admitAtCommit (readFold commitFold : GameState) (seat : Color) (cmd : Command) (now : Nat) :
    Except AdmitError Decision :=
  let _stale := readFold
  admit commitFold seat cmd now

/-- A play by the seat not to move is never appended. An ended game and a
    clock that has run out are reported first; otherwise it is refused as
    not that seat's turn. -/
theorem wrong_seat_never_appends (before : GameState) (seat : Color) (m : Move) (now : Nat)
    (h : seat ≠ before.position.side) :
    ∀ d, admit before seat (.play m) now = .ok d → d.event = none := by
  intro d hd
  unfold admit at hd
  split at hd
  · rename_i ev after ho
    exact absurd (accepted_turn ho rfl) h
  · simp at hd
  · simp only [Except.ok.injEq] at hd; subst hd; rfl
  · simp only [Except.ok.injEq] at hd; subst hd; rfl

theorem wrong_seat_play (before : GameState) (seat : Color) (m : Move) (now : Nat)
    (h : seat ≠ before.position.side) (hopen : before.ending = none)
    (hclk : before.runningSince.ms ≤ now) (hlive : expired before ⟨now⟩ = false) :
    admit before seat (.play m) now = .error .notYourTurn := by
  unfold admit LeanChess.admit
  simp [Command.needsTurn, h, hopen, hlive, Nat.not_lt.mpr hclk]

/-- An appended event is the domain's accepted event: for this seat, this
    command, at the server instant. -/
theorem played_is_accepted {before : GameState} {seat : Color} {cmd : Command} {now : Nat}
    {ev : GameEvent}
    (h : admit before seat cmd now = .ok ⟨.played, some ev⟩) :
    LeanChess.admit before seat cmd ⟨now⟩ = .accepted ev (applyEvent before ev) := by
  unfold admit at h
  split at h
  · rename_i ev' after ho
    simp only [Except.ok.injEq, Decision.mk.injEq, Option.some.injEq, true_and] at h
    subst h
    rw [ho, (accepted_event ho).2.1]
  · simp at h
  · simp at h
  · simp at h

/-- An appended play was authorized for the side to move, at the server
    instant, and is a legal move there. -/
theorem accepted_play_seat {before : GameState} {seat : Color} {m : Move} {now : Nat}
    {ev : GameEvent}
    (h : admit before seat (.play m) now = .ok ⟨.played, some ev⟩) :
    seat = before.position.side ∧ ev = .moved m ⟨now⟩ ∧
      ∃ p, applyMove before.position m = some p := by
  obtain ⟨hseat, hev, p, hp, _⟩ := accepted_play (played_is_accepted h)
  exact ⟨hseat, hev, p, hp⟩

/-- Nothing is appended for a flag, and the flag is what a look at the
    same instant shows. -/
theorem flagged_appends_nothing {before : GameState} {seat : Color} {cmd : Command} {now : Nat}
    {d : Decision}
    (h : admit before seat cmd now = .ok d) (hf : d.outcome = .flagged) :
    d.event = none ∧ ∃ e, resultAt before ⟨now⟩ = some e := by
  unfold admit at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; simp at hf
  · simp at h
  · simp only [Except.ok.injEq] at h; subst h; simp at hf
  · rename_i e after ho
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨rfl, e, flagged_look ho⟩

theorem stale_read_cannot_authorize
    (readFold commitFold : GameState) (seat : Color) (m : Move) (now : Nat)
    (_earlier : seat = readFold.position.side)
    (later : seat ≠ commitFold.position.side) :
    ∀ d, admitAtCommit readFold commitFold seat (.play m) now = .ok d → d.event = none := by
  simp only [admitAtCommit]
  exact wrong_seat_never_appends commitFold seat m now later

/-
  Routes the HTTP match can reach. `routePersist` is what each of them is
  allowed to append. Adding a route means adding a case here.

  A look appends nothing, with one exception this file does not hide:
  when the machine sits the side to move, a current look asks it for a
  move and appends that move through the same `admit`. `machine` is the
  move the machine chose, or `none`. Moving that turn out of GET is #23.
-/
inductive ClientRoute where
  | register
  | openGame
  | look
  | acts
  deriving Repr, DecidableEq

inductive StoredAct where
  | none
  | play (ev : GameEvent)
  deriving Repr, DecidableEq

def routePersist (route : ClientRoute) (before : GameState) (seat : Color)
    (cmd : Command) (now : Nat) (machine : Option Move := none) : Except AdmitError StoredAct :=
  match route with
  | .register | .openGame => .ok .none
  | .look =>
    match machine with
    | Option.none => .ok .none
    | some m =>
      match admit before before.position.side (.play m) now with
      | .ok ⟨.played, some ev⟩ => .ok (.play ev)
      | _ => .ok .none
  | .acts =>
    match admit before seat cmd now with
    | .error e => .error e
    | .ok d =>
      match d.outcome, d.event with
      | .played, some ev => .ok (.play ev)
      | _, _ => .ok .none

theorem inactive_route_appends_nothing
    (route : ClientRoute) (before : GameState) (seat : Color) (cmd : Command) (now : Nat)
    (hinactive : route ≠ .acts ∧ route ≠ .look) :
    routePersist route before seat cmd now = .ok .none := by
  cases route <;> simp_all [routePersist]

/-- A look with no machine move appends nothing. -/
theorem look_appends_nothing (before : GameState) (seat : Color) (cmd : Command) (now : Nat) :
    routePersist .look before seat cmd now none = .ok .none := rfl

/-- What a look may append is a legal play by the machine's own seat. -/
theorem look_appends_machine_play
    {before : GameState} {seat : Color} {cmd : Command} {now : Nat} {m : Move} {ev : GameEvent}
    (h : routePersist .look before seat cmd now (some m) = .ok (.play ev)) :
    ev = .moved m ⟨now⟩ ∧ ∃ p, applyMove before.position m = some p := by
  simp only [routePersist] at h
  split at h
  · rename_i ev' he
    cases h
    obtain ⟨_, hev, hp⟩ := accepted_play_seat he
    exact ⟨hev, hp⟩
  · simp at h

theorem route_play_is_moving_seat
    {before : GameState} {seat : Color} {m : Move} {now : Nat} {ev : GameEvent}
    (h : routePersist .acts before seat (.play m) now = .ok (.play ev)) :
    seat = before.position.side ∧ ev = .moved m ⟨now⟩ := by
  simp only [routePersist] at h
  split at h
  · next e he => injection h
  · next d he =>
    cases d with
    | mk outcome event =>
      cases outcome <;> cases event <;> simp_all
      · next ev' =>
        cases h
        obtain ⟨hs, hev, _⟩ := accepted_play_seat he
        exact ⟨hs, hev⟩

/-- Current observation is the server clock. Historical `at` cannot be later. -/
def observe (now : Nat) (asked : Option Nat) : Except String (Nat × Bool) :=
  match asked with
  | none => .ok (now, false)
  | some t =>
    if t > now then .error "at is in the future"
    else .ok (t, true)

theorem current_look_is_server_time (now : Nat) :
    observe now none = .ok (now, false) := rfl

#guard match observe 1000 none with
  | .ok (1000, false) => true
  | _ => false
#guard match observe 1000 (some 1000) with
  | .ok (1000, true) => true
  | _ => false
#guard match observe 1000 (some 999) with
  | .ok (999, true) => true
  | _ => false
#guard match observe 1000 (some 1001) with
  | .error _ => true
  | _ => false

private def e4 : Move := mv .e .r2 .e .r4

#guard (match parseRequested (Json.mkObj [
    ("kind", .str "play"), ("at", toJson (300000 : Nat)),
    ("from", .str "e2"), ("to", .str "e4")]) with
  | .ok (.play _, none) => true
  | _ => false)

#guard (match parseRequested (Json.mkObj [
    ("kind", .str "play"), ("at", .str "soon"),
    ("from", .str "e2"), ("to", .str "e4")]) with
  | .error _ => true
  | _ => false)

#guard match admit (initial sample) .black (.play e4) 0 with
  | .error .notYourTurn => true
  | _ => false
#guard match admit (initial sample) .white (.play e4) 300000 with
  | .ok ⟨.flagged, none⟩ => true
  | _ => false

#guard (match admit (initial sample) .white (.play e4) 0 with
  | .ok ⟨.played, some (.moved m t)⟩ => m == e4 && t.ms == 0
  | _ => false)

#guard (applyEvent (initial sample) (.moved e4 ⟨300000⟩)).ply == 0
#guard (applyEvent (initial sample) (.moved e4 ⟨0⟩)).ply == 1

private def incAgree : Agreement := { sample with time := .realtime 60000 1000, start := ⟨0⟩ }

#guard (match admit (initial incAgree) .white (.play e4) 2500 with
  | .ok ⟨.played, some ev⟩ => (applyEvent (initial incAgree) ev).whiteMs == 58500
  | _ => false)

private def afterE4 : GameState :=
  applyEvent (initial sample) (.moved e4 ⟨1000⟩)

#guard afterE4.position.side == .black
#guard match admit afterE4 .white (.play e4) 2000 with
  | .error .notYourTurn => true
  | _ => false
#guard match admitAtCommit (initial sample) afterE4 .white (.play (mv .d .r2 .d .r4)) 2000 with
  | .error .notYourTurn => true
  | _ => false
#guard match routePersist .look afterE4 .black .resign 2000 (some (mv .e .r7 .e .r5)) with
  | .ok (.play (.moved m t)) => m == mv .e .r7 .e .r5 && t.ms == 2000
  | _ => false
#guard match routePersist .look afterE4 .black .resign 2000 (some (mv .e .r7 .e .r4)) with
  | .ok .none => true
  | _ => false
/-- An ended game refuses a wrong-seat play as ended, not as forbidden. -/
private def ended : GameState :=
  applyEvent (applyEvent afterE4 (.moved (mv .e .r7 .e .r5) ⟨1500⟩)) (.resigned .black ⟨1600⟩)

#guard ended.ending == some (.resign .white)
#guard match admit ended .black (.play e4) 2000 with
  | .ok ⟨.refused, none⟩ => true
  | _ => false

end LeanChess.Api
