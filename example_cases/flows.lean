/-
  The flows in `userflows.md`, inhabited.

  A flow is an agreement, a log of attempts, and a look. A look reads the
  fold of that log at an instant. It is not an event, and it does not take
  a seat: both seats are asking the same question.

  Four endings in the prose have no short log from the opening, so they are
  not here: stalemate, a dead position, seventy-five moves, and a
  resignation in a dead position. A flag where the other seat cannot force
  a win is the same gap. From the opening, a flag is a loss for the seat
  whose time ran out. A fifty-move claim that holds is inhabited from a
  state built by hand, and says so.

  The proofs are `native_decide`. `decide` does not reduce `fold`: one play
  goes through `applyMove`, and the kernel does not finish that term.
-/

import domain.Game

namespace LeanChess.Flows

open LeanChess

def ada : Person := { id := "ada" }
def bel : Person := { id := "bel" }

def blitz : Agreement where
  white := ada
  black := bel
  rated := true
  time := .realtime (5 * 60 * 1000) 0
  start := ⟨0⟩

def quick : Agreement := { blitz with time := .realtime 10000 100 }

def bullet : Agreement := { blitz with time := .realtime 1000 0 }

def casual : Agreement := { blitz with rated := false }

def solo : Agreement := { blitz with black := ada }

def auto : Agreement := { blitz with white := { ada with autoClaimThreefold := true } }

def postal : Agreement := { blitz with time := .correspondence 1 }

/-- What either seat sees. The clock figures are the derived ones at `d`. -/
structure Look where
  ending : Option Ending
  turn : Color
  offer : Option Color
  whiteLeft : Nat
  blackLeft : Nat
  ply : Nat
  counts : Bool
  deriving Repr, DecidableEq

def look (a : Agreement) (log : List GameEvent) (d : Instant) : Look :=
  let s := fold a log
  { ending := resultAt s d
    turn := s.position.side
    offer := s.offer
    whiteLeft := remaining s .white d
    blackLeft := remaining s .black d
    ply := s.ply
    counts := countsForRating s d }

def played (step : Nat) (moves : List Move) : List GameEvent :=
  let rec go (i : Nat) : List Move → List GameEvent
    | [] => []
    | m :: ms => .moved m ⟨(i + 1) * step⟩ :: go (i + 1) ms
  go 0 moves

def e4 : Move := mv .e .r2 .e .r4
def e5 : Move := mv .e .r7 .e .r5

/-- Knights out and back. One pass returns the opening; the opening was already there. -/
def shuttle : List Move :=
  [mv .g .r1 .f .r3, mv .g .r8 .f .r6, mv .f .r3 .g .r1, mv .f .r6 .g .r8]

def passes (n : Nat) : List Move :=
  List.range n |>.flatMap fun _ => shuttle

/- ====================================================================
   A play
   ==================================================================== -/

/-- Turn. The play is admitted. The turn is handed over. White's clock has
    stopped; Black's is running, and a later look sees less of it. -/
theorem turn :
    look blitz [.moved e4 ⟨1000⟩] ⟨1000⟩ =
      { ending := none, turn := .black, offer := none
        whiteLeft := 299000, blackLeft := 300000, ply := 1, counts := false } ∧
    (look blitz [.moved e4 ⟨1000⟩] ⟨5000⟩).whiteLeft = 299000 ∧
    (look blitz [.moved e4 ⟨1000⟩] ⟨5000⟩).blackLeft = 296000 := by
  native_decide

/-- Refused. An impossible play leaves the fold as it was. -/
theorem refused :
    fold blitz [.moved (mv .e .r2 .e .r5) ⟨100⟩] = fold blitz [] ∧
    look blitz [.moved (mv .e .r2 .e .r5) ⟨100⟩] ⟨100⟩ =
      look blitz [] ⟨100⟩ := by
  native_decide

/-- Out of turn. A play, an offer, and a claim by White, while it is Black's
    turn, leave the fold as it was. A resignation is not in this group: the
    game admits it from either seat once both have played. -/
theorem outOfTurn :
    let begun := played 1000 [e4]
    fold blitz (begun ++ [.moved (mv .d .r2 .d .r4) ⟨2000⟩]) = fold blitz begun ∧
    fold blitz (begun ++ [.drawOffered .white ⟨2000⟩]) = fold blitz begun ∧
    fold blitz (begun ++ [.claimedThreefold .white none ⟨2000⟩]) = fold blitz begun := by
  native_decide

/-- The play ends the game. Scholar's mate. No resign, no claim, no abort
    in the log. White's clock does not receive the increment on the mating
    play: it finishes at 6300, not 6400. Black's clock stays where the last
    Black play left it. -/
theorem endsItself :
    let s := look quick (played 1000 scholar) ⟨9000⟩
    s.ending = some (.checkmate .white) ∧ s.ply = 7 ∧
      s.whiteLeft = 6300 ∧ s.blackLeft = 7300 ∧ s.counts = true := by
  native_decide

/-- Five times. The fourth return to the opening is the fifth occurrence.
    The play ends it. Nobody claimed. -/
theorem fivefold :
    (look blitz (played 100 (passes 4)) ⟨2000⟩).ending = some (.draw .fivefold) := by
  native_decide

/- ====================================================================
   An offer
   ==================================================================== -/

theorem offer :
    look blitz [.drawOffered .white ⟨0⟩] ⟨0⟩ =
      { ending := none, turn := .white, offer := some .white
        whiteLeft := 300000, blackLeft := 300000, ply := 0, counts := false } := by
  native_decide

def bothPlayed : List GameEvent := played 1000 [e4, e5]

theorem accept :
    let log := bothPlayed ++ [.drawOffered .white ⟨3000⟩, .drawAccepted .black ⟨4000⟩]
    (look blitz log ⟨4000⟩).ending = some (.draw .agreement) ∧
      Score.ofEnding (.draw .agreement) = some ⟨.half, .half⟩ ∧
      (look blitz log ⟨4000⟩).counts = true := by
  native_decide

/-- Accepting before both have played does not end it, and the offer stays. -/
theorem acceptTooSoon :
    fold blitz [.drawOffered .white ⟨0⟩, .drawAccepted .black ⟨10⟩] =
      fold blitz [.drawOffered .white ⟨0⟩] := by
  native_decide

/-- Declining clears the offer. It does not clear what the offer meant for
    White's next play: the fold still remembers who offered this turn. -/
theorem decline :
    let log := bothPlayed ++ [.drawOffered .white ⟨3000⟩, .drawDeclined .black ⟨4000⟩]
    let s := look blitz log ⟨4000⟩
    s.offer = none ∧ s.ending = none ∧ s.ply = 2 ∧
      (fold blitz log).claim = some .white := by
  native_decide

/-- White offers, then plays. The offer is still standing afterwards. -/
theorem offerThenPlay :
    let log := [.drawOffered .white ⟨0⟩, .moved e4 ⟨1000⟩]
    let s := look blitz log ⟨1000⟩
    s.offer = some .white ∧ s.turn = .black ∧ s.ply = 1 ∧ s.ending = none := by
  native_decide

/-- Black's reply play clears the offer White left standing, and the turn
    White offered in is over. -/
theorem clearedByPlay :
    let log := [.drawOffered .white ⟨0⟩, .moved e4 ⟨1000⟩, .moved e5 ⟨2000⟩]
    (look blitz log ⟨2000⟩).offer = none ∧ (look blitz log ⟨2000⟩).ply = 2 ∧
      (fold blitz log).claim = none := by
  native_decide

/-- Black offers, then plays the knight home. That is the third occurrence
    of the opening, so the offer ends the game. Black sent no claim. -/
theorem offerThenThird :
    let front := played 100 (shuttle ++ shuttle.take 3)
    let log := front ++ [.drawOffered .black ⟨700⟩, .moved (mv .f .r6 .g .r8) ⟨800⟩]
    (look blitz log ⟨800⟩).ending = some (.draw .threefold) := by
  native_decide

/-- The same, with White declining in between. The decline clears the
    offer and not the claim it carried: the play that makes the third
    occurrence still ends the game. This is the Lichess reading in
    `facts.md`, and the reading the fold used to miss. -/
theorem declinedThenThird :
    let front := played 100 (shuttle ++ shuttle.take 3)
    let log := front ++ [.drawOffered .black ⟨700⟩, .drawDeclined .white ⟨750⟩,
      .moved (mv .f .r6 .g .r8) ⟨800⟩]
    repetitions (fold blitz log) = 3 ∧
      (look blitz log ⟨800⟩).ending = some (.draw .threefold) ∧
      (look blitz (front ++ [.drawOffered .black ⟨700⟩, .drawDeclined .white ⟨750⟩]) ⟨750⟩).offer
        = none := by
  native_decide

/- ====================================================================
   A claim
   ==================================================================== -/

/-- Two returns: the opening is on the board for the third time, and it is
    White's turn. The claim names no play. -/
theorem claim :
    let log := played 100 (passes 2) ++ [.claimedThreefold .white none ⟨900⟩]
    (look blitz log ⟨900⟩).ending = some (.draw .threefold) := by
  native_decide

/-- A claim naming a play is that play, with a draw offer standing from the
    claimant (FIDE 9.1.2.3). When the play does not make a threefold, the
    fold is exactly the fold of an offer followed by the play: the same
    clock, nothing extra for the failed claim. -/
theorem claimMisses :
    fold quick [.claimedThreefold .white (some e4) ⟨1000⟩] =
      fold quick [.drawOffered .white ⟨1000⟩, .moved e4 ⟨1000⟩] ∧
    fold quick [.claimedFifty .white (some e4) ⟨1000⟩] =
      fold quick [.drawOffered .white ⟨1000⟩, .moved e4 ⟨1000⟩] := by
  native_decide

/-- A claim with no play, which does not hold, is a draw offer. The same for
    a fifty-move claim that does not hold. -/
theorem claimStands :
    fold blitz [.claimedThreefold .white none ⟨0⟩] = fold blitz [.drawOffered .white ⟨0⟩] ∧
    fold blitz [.claimedFifty .white none ⟨0⟩] = fold blitz [.drawOffered .white ⟨0⟩] := by
  native_decide

/-- Because a claim is an offer, the other seat can accept it. -/
theorem claimAccepted :
    let log := bothPlayed ++ [.claimedThreefold .white none ⟨3000⟩, .drawAccepted .black ⟨4000⟩]
    (look blitz log ⟨4000⟩).ending = some (.draw .agreement) := by
  native_decide

/-- A claim naming a play that mates: the mate wins. The claim is not a draw. -/
theorem claimMateWins :
    let front := played 1000 (scholar.take 6)
    let log := front ++ [.claimedThreefold .white (some (mv .h .r5 .f .r7)) ⟨7000⟩]
    (look quick log ⟨7000⟩).ending = some (.checkmate .white) ∧
      (look quick log ⟨7000⟩).offer = none := by
  native_decide

/-- A claim naming a play that is not legal is not admitted at all. -/
theorem claimIllegalPlay :
    fold blitz [.claimedThreefold .white (some (mv .e .r2 .e .r5)) ⟨0⟩] = fold blitz [] ∧
    fold blitz [.claimedFifty .white (some (mv .e .r2 .e .r5)) ⟨0⟩] = fold blitz [] := by
  native_decide

/-- A fifty-move claim that holds. No short log from the opening reaches a
    hundred plies without a pawn move or a capture, so this fold is built
    by hand: the opening, with the count already at 100. With no play named,
    the claim is a draw at once. With a play named, the draw is on the play. -/
def hundredPlies : GameState := { initial blitz with halfmove := 100 }

theorem fiftyHolds :
    (applyEvent hundredPlies (.claimedFifty .white none ⟨0⟩)).ending = some (.draw .fifty) ∧
    (applyEvent hundredPlies (.claimedFifty .white (some (mv .g .r1 .f .r3)) ⟨0⟩)).ending
      = some (.draw .fifty) ∧
    (applyEvent hundredPlies (.claimedFifty .white (some (mv .g .r1 .f .r3)) ⟨0⟩)).ply = 1 ∧
    (applyEvent { hundredPlies with halfmove := 99 }
      (.claimedFifty .white (some (mv .g .r1 .f .r3)) ⟨0⟩)).ending = some (.draw .fifty) ∧
    (applyEvent { hundredPlies with halfmove := 98 }
      (.claimedFifty .white (some (mv .g .r1 .f .r3)) ⟨0⟩)).ending = none := by
  native_decide

/-- White chose beforehand that a threefold be claimed for them.
    The log is only plays. -/
theorem claimedForThem :
    let log := played 100 (passes 2)
    (look auto log ⟨900⟩).ending = some (.draw .threefold) ∧
      log.all (fun e => match e with | .moved _ _ => true | _ => false) = true := by
  native_decide

/- ====================================================================
   Resigning and aborting
   ==================================================================== -/

theorem resign :
    let log := bothPlayed ++ [.resigned .white ⟨3000⟩]
    (look blitz log ⟨3000⟩).ending = some (.resign .black) ∧
      Score.ofEnding (.resign .black) = some ⟨.zero, .one⟩ := by
  native_decide

/-- Once both have played, White may resign on Black's turn. -/
theorem resignOnTheirTurn :
    let log := played 1000 [e4, e5, mv .g .r1 .f .r3] ++ [.resigned .white ⟨4000⟩]
    (look blitz log ⟨4000⟩).ending = some (.resign .black) ∧
      (look blitz log ⟨4000⟩).turn = .black := by
  native_decide

/-- The clock stops where the resignation found it. White had 294000 left
    at 7000; a look after the resignation still says 294000, not the
    299000 the last play left. -/
theorem resignFreezesClock :
    (look blitz bothPlayed ⟨7000⟩).whiteLeft = 294000 ∧
    (look blitz (bothPlayed ++ [.resigned .white ⟨7000⟩]) ⟨7000⟩).whiteLeft = 294000 ∧
    (look blitz (bothPlayed ++ [.resigned .white ⟨7000⟩]) ⟨99000⟩).whiteLeft = 294000 ∧
    (look blitz (bothPlayed ++ [.resigned .white ⟨7000⟩]) ⟨99000⟩).blackLeft = 299000 := by
  native_decide

/-- The same for an agreed draw, a claim, and an abort. -/
theorem endingsFreezeClock :
    (look blitz (bothPlayed ++ [.drawOffered .white ⟨3000⟩, .drawAccepted .black ⟨7000⟩]) ⟨99000⟩).whiteLeft
      = 294000 ∧
    (look blitz (played 100 (passes 2) ++ [.claimedThreefold .white none ⟨1300⟩]) ⟨99000⟩).whiteLeft
      = 299100 ∧
    (look blitz (played 1000 [e4] ++ [.aborted .black ⟨5000⟩]) ⟨99000⟩).blackLeft = 296000 := by
  native_decide

theorem abortAtStart :
    let s := look blitz [.aborted .black ⟨10⟩] ⟨10⟩
    s.ending = some .abort ∧ s.counts = false ∧ Score.ofEnding .abort = none := by
  native_decide

theorem abortAfterOnePlay :
    (look blitz (played 1000 [e4] ++ [.aborted .white ⟨2000⟩]) ⟨2000⟩).ending =
      some .abort := by
  native_decide

theorem abortTooLate :
    fold blitz (bothPlayed ++ [.aborted .white ⟨3000⟩]) = fold blitz bothPlayed := by
  native_decide

/- ====================================================================
   The clock
   ==================================================================== -/

/-- A continuing play adds the increment. 10000 spent 1000, plus 100. -/
theorem incrementContinues :
    let s := look quick [.moved e4 ⟨1000⟩] ⟨1000⟩
    s.whiteLeft = 9100 ∧ s.blackLeft = 10000 ∧ s.ending = none := by
  native_decide

/-- Correspondence: after White plays, Black's period is fresh, and White's
    next period is the full one again. -/
theorem correspondencePeriod :
    let day := (postal.time.initialMs)
    let s0 := look postal [.moved e4 ⟨1000⟩] ⟨1000⟩
    let later := look postal [.moved e4 ⟨1000⟩] ⟨6000⟩
    s0.blackLeft = day ∧ s0.whiteLeft = day ∧
      later.blackLeft = day - 5000 ∧ later.whiteLeft = day := by
  native_decide

/-- Nobody sends a flag. A look past the clock shows it. The boundary is
    the instant the allowance is used up: 999 is play, 1000 is the flag. -/
theorem flagByLooking :
    (look bullet [] ⟨999⟩).ending = none ∧
    (look bullet [] ⟨1000⟩).ending = some (.flag .black) ∧
    (look bullet [] ⟨1000⟩).whiteLeft = 0 := by
  native_decide

/-- The play arrives as the time runs out. It is not in the fold. -/
theorem flagLatePlay :
    let s := fold bullet [.moved e4 ⟨1000⟩]
    s.ply = 0 ∧ s.position = opening ∧ s.ending = some (.flag .black) := by
  native_decide

/-- A flag counts like any other ending. White has 299000 after e4 e5 and
    flags at 301000. Before that instant the game is open and does not
    count; from it on, it is a loss for White and an input to the pool.
    The log gained nothing. -/
theorem flagCounts :
    (look blitz bothPlayed ⟨300999⟩).ending = none ∧
    (look blitz bothPlayed ⟨300999⟩).counts = false ∧
    (look blitz bothPlayed ⟨301000⟩).ending = some (.flag .black) ∧
    (look blitz bothPlayed ⟨301000⟩).counts = true ∧
    (look blitz bothPlayed ⟨999999⟩).ending = some (.flag .black) ∧
    (look blitz bothPlayed ⟨999999⟩).whiteLeft = 0 ∧
    (look blitz bothPlayed ⟨999999⟩).blackLeft = 299000 := by
  native_decide

/-- A flag before both have played does not count. -/
theorem flagBeforeBothPlayedDoesNot :
    (look blitz [] ⟨300000⟩).ending = some (.flag .black) ∧
    (look blitz [] ⟨300000⟩).counts = false := by
  native_decide

/-- White offered, then played, so the offer is still standing on Black's
    turn when Black's time runs out. -/
theorem flagWithOffer :
    let log := [.drawOffered .white ⟨0⟩, .moved e4 ⟨100⟩]
    (look bullet log ⟨1100⟩).ending = some (.draw .flagOffer) ∧
    (fold bullet (log ++ [.moved e5 ⟨1100⟩])).ply = 1 := by
  native_decide

/- ====================================================================
   After it is over
   ==================================================================== -/

theorem alreadyEnded :
    let log := [.aborted .white ⟨10⟩]
    fold blitz (log ++ [.moved e4 ⟨20⟩]) = fold blitz log ∧
      (look blitz log ⟨999999⟩).ending = some .abort := by
  native_decide

/-- The same ending, at every later instant. -/
theorem endingStays :
    let log := bothPlayed ++ [.resigned .white ⟨3000⟩]
    (look blitz log ⟨3000⟩).ending = some (.resign .black) ∧
    (look blitz log ⟨999999⟩).ending = some (.resign .black) ∧
    fold blitz (log ++ [.moved (mv .g .r1 .f .r3) ⟨4000⟩]) = fold blitz log := by
  native_decide

/- ====================================================================
   Whether it counts
   ==================================================================== -/

theorem counts :
    let log := bothPlayed ++ [.resigned .white ⟨3000⟩]
    (look blitz log ⟨3000⟩).counts = true ∧
      Speed.ofControl blitz.time = .blitz := by
  native_decide

theorem casualDoesNot :
    (look casual (bothPlayed ++ [.resigned .white ⟨3000⟩]) ⟨3000⟩).counts = false := by
  native_decide

theorem samePersonDoesNot :
    (look solo (bothPlayed ++ [.resigned .white ⟨3000⟩]) ⟨3000⟩).counts = false := by
  native_decide

theorem abortDoesNot :
    (look blitz [.aborted .white ⟨10⟩] ⟨10⟩).counts = false := by
  native_decide

theorem stillOpenDoesNot :
    (look blitz (played 1000 [e4]) ⟨1000⟩).counts = false := by
  native_decide

end LeanChess.Flows
