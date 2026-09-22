/-
  Command admission. The seat and the instant are fixed here, before an
  event is stored.

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
  `at` is rejected. Projecting a past instant only changes the clocks
  in the response.

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
  deriving Repr, BEq, DecidableEq

/-- What the requested act did. A flag is not a played move. -/
inductive Outcome where
  | played
  | refused
  | flagged
  deriving Repr, BEq, DecidableEq

def Outcome.wire : Outcome → String
  | .played => "played"
  | .refused => "refused"
  | .flagged => "flagged"

structure Decision where
  outcome : Outcome
  /-- `some` only when that event is the one to append. -/
  event : Option GameEvent
  deriving Repr, DecidableEq

/-- The fold changed because the clock expired, not because the request landed. -/
def timeEnded (before after : GameState) : Bool :=
  before.ending.isNone && after.ply == before.ply &&
    match after.ending with
    | some (.flag _) => true
    | some (.draw .flagOffer) => true
    | some (.draw .flagInsufficient) => true
    | _ => false

/-- A play is built only when `seat` is the side to move in `before`. -/
def admitPlay (before : GameState) (seat : Color) (m : Move) (now : Nat) :
    Except AdmitError Decision :=
  if _h : seat = before.position.side then
    let ev : GameEvent := .moved m ⟨now⟩
    let after := applyEvent before ev
    if timeEnded before after then
      .ok ⟨.flagged, none⟩
    else if after.ply == before.ply + 1 then
      .ok ⟨.played, some ev⟩
    else
      .ok ⟨.refused, none⟩
  else
    .error .notYourTurn

/-- Authorize `req` against the fold at commit, at server instant `now`. -/
def admit (before : GameState) (seat : Color) (req : Requested) (now : Nat) :
    Except AdmitError Decision :=
  match req with
  | .play m => admitPlay before seat m now
  | other =>
    let ev := eventOf seat now other
    let after := applyEvent before ev
    if timeEnded before after then .ok ⟨.flagged, none⟩
    else if changed before after then .ok ⟨.played, some ev⟩
    else .ok ⟨.refused, none⟩

/-- A fold read earlier does not authorize. The commit fold does. -/
def admitAtCommit (readFold commitFold : GameState) (seat : Color) (req : Requested) (now : Nat) :
    Except AdmitError Decision :=
  let _stale := readFold
  admit commitFold seat req now

theorem wrong_seat_play (before : GameState) (seat : Color) (m : Move) (now : Nat)
    (h : seat ≠ before.position.side) :
    admit before seat (.play m) now = .error .notYourTurn := by
  simp only [admit, admitPlay, dif_neg h]

/-- An appended play was authorized for the side to move, at the server instant. -/
theorem accepted_play_seat {before : GameState} {seat : Color} {m : Move} {now : Nat} {ev : GameEvent}
    (h : admit before seat (.play m) now = .ok ⟨.played, some ev⟩) :
    seat = before.position.side ∧ ev = .moved m ⟨now⟩ := by
  simp only [admit, admitPlay] at h
  split at h
  · rename_i hseat
    split at h
    · injection h with heq
      injection heq with ho _
      cases ho
    · split at h
      · injection h with heq
        injection heq with _ hev
        cases hev
        exact ⟨hseat, rfl⟩
      · injection h with heq
        injection heq with ho _
        cases ho
  · injection h

theorem stale_read_cannot_authorize
    (readFold commitFold : GameState) (seat : Color) (m : Move) (now : Nat)
    (_earlier : seat = readFold.position.side)
    (later : seat ≠ commitFold.position.side) :
    admitAtCommit readFold commitFold seat (.play m) now = .error .notYourTurn := by
  simp only [admitAtCommit]
  exact wrong_seat_play commitFold seat m now later

/-
  Routes the HTTP match can reach. `routePersist` is what each of them is
  allowed to append. Adding a route means adding a case here.
-/
inductive ClientRoute where
  | register
  | openGame
  | look
  | acts
  deriving Repr, BEq, DecidableEq

inductive StoredAct where
  | none
  | play (ev : GameEvent)
  deriving Repr, DecidableEq

def routePersist (route : ClientRoute) (before : GameState) (seat : Color)
    (req : Requested) (now : Nat) : Except AdmitError StoredAct :=
  match route with
  | .register | .openGame | .look => .ok .none
  | .acts =>
    match admit before seat req now with
    | .error e => .error e
    | .ok d =>
      match d.outcome, d.event with
      | .played, some ev => .ok (.play ev)
      | _, _ => .ok .none

theorem inactive_route_appends_nothing
    (route : ClientRoute) (before : GameState) (seat : Color) (req : Requested) (now : Nat)
    (hinactive : route ≠ .acts) :
    routePersist route before seat req now = .ok .none := by
  cases route <;> simp_all [routePersist]

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
        exact accepted_play_seat he

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
#guard changed (initial sample)
  (applyEvent (initial sample) (eventOf .white 300000 (.play e4)))

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

end LeanChess.Api
