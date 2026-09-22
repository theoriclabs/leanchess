# User flows

How a person deals with one game. These are attempts and looks. Which attempt the game admits is inhabited in `example_cases/flows.lean`: one agreement, one log, and the look both seats get.

No board, no pieces, no clock arithmetic in this file. The agreement is already true when a flow starts. How two people came to be paired is not a flow.

## The two things a person does

A person looks, or a person attempts.

A look asks the situation at an instant. It adds nothing to the log. Both seats look at the same log, so they get the same situation. They may look at different instants, and then the clock they each see can differ. A look at an earlier instant is the situation the log had reached by then: the acts up to that instant, and the clock at that instant. It is not today's situation with an older clock.

An attempt names an act, the seat it is made for, and the instant. The instant is the server's, when the attempt reaches it; a figure the person's screen carries is not the instant. It is admitted or it is not.

- Admitted: it is the next entry in the log. Both seats can look and see it. The seat that did not attempt learns it by looking again; nothing is waiting on a reload of a page that was never part of this.
- Not admitted: the log is unchanged. The seat that attempted can tell, and can tell why: the game had ended, it was not their turn, or the situation did not admit that act. The other seat has nothing new to see.
- Flagged: the log is unchanged, and the look shows a flag. The attempt arrived after the clock had run out. The flag was already true; the attempt discovered it.

Time passing is neither a look nor an attempt. A flag is something a look reveals, or something an attempt discovers by arriving too late. Nobody sends one.

A person and a seat stay apart. The agreement says which person sits which seat for this game. The same person may sit either seat in another game, and may sit both seats of this one.

## What an attempt can be

A person attempts one of these, for the seat they sit:

| Attempt | What the person is doing |
|---|---|
| Play | Offering one act that would hand the turn over. |
| Resign | Declaring the game lost for their seat. |
| Offer | Offering a draw, with no condition. |
| Accept | Agreeing to a draw that the other seat offered. |
| Decline | Refusing that offer. |
| Claim | Claiming a draw of a named kind. The claim may carry a play that would make the claim true. |
| Abort | Asking that the game end with no winner. |

A claim is also an offer. A play that the person makes after their own offer does not take the offer back. A play by the other seat does.

Which of these the situation admits, and what the situation is afterwards, is the game. This file only says what the person is trying, and what both seats can then look at.

## What a look can ask

- Whose turn it is, and the situation the admitted plays have reached.
- Whether an offer is standing, and from which seat.
- How much time each seat has at the instant of the look.
- Whether the game has ended, and why.
- Whether this game, as of this look, counts as an input to a rating pool.

A look cannot see the other seat's unsent attempt. A figure the person's own screen has been counting is not an answer to the time question. The answer is derived when they look.

## Flows

Each flow is a sequence of attempts and looks, and what is true at the end that either seat can look at.

### A play

**Turn.** It is this seat's turn. They attempt a play. It is admitted. Both look and see the turn handed over. This seat's clock has stopped. The other clock is running. When the play itself ended the game, both look and see the ending, and the other clock did not start.

**Refused.** They attempt a play. It is not admitted. Both look and see the situation they saw before. The other seat sees no new entry.

**Out of turn.** They attempt a play, a resignation, an offer, or a claim while it is the other seat's turn. It is not admitted. The situation is the one from before the attempt.

**Ends on its own.** They attempt a play. It is admitted, and what both look at is an ending rather than a turn handed over. They sent no separate act to end it. The ending is one of: the other seat is mated; the other seat has no play and is not mated; neither seat can force a win; the same situation has occurred five times; each seat has gone seventy-five moves without a pawn move or a capture. In that last case, a play that mates is a win for the seat that played it.

### An offer

**Offer.** On their turn they attempt an offer. It is admitted. Both look and see it standing from that seat. The turn has not been handed over.

**Accept.** The other seat attempts an accept, and both seats have already played at least once. Both look and see a draw.

**Accept too soon.** The other seat attempts an accept before both have played. It is not admitted. The offer is still standing.

**Decline.** The other seat attempts a decline. Both look and see no offer standing. The game is not over. What the offer meant for the offerer's next play is not undone: see *Offer, then play*.

**Cleared by a play.** The other seat attempts a play and it is admitted. Both look and see no offer standing. The play is in the log.

**Offer, then play.** The seat that offered then attempts a play, and it is admitted. Both look and see the offer still standing, and the turn handed over. When that play is the one that makes the situation occur for the third time, both look and see a draw. The other seat did not have to accept, and a decline in between does not change this: the offer before the repeating play was the claim.

### A claim

**Claim.** On their turn they attempt a claim, of a threefold or of fifty moves. They may name a play that would make it so. The claim holds. Both look and see a draw.

**Claim that does not hold.** They named a play, and the claim does not hold. The play is admitted anyway when the situation admits it, and their draw offer stands. Both look and see the turn handed over, an offer standing from the claimant, and no draw. Nothing is added to the clock for the failed claim: the situation is exactly an offer followed by that play. With no play named, a claim that does not hold is an offer, and the other seat may accept it.

**Claim naming a play that mates.** The play is admitted and it mates. Both look and see the win, not a draw.

**Claim naming a play the situation does not admit.** Nothing is admitted. The situation is the one from before, with no offer standing.

**Claimed for them.** Before the game, this person chose that a threefold be claimed on their behalf. The situation occurs for the third time and it is their turn. Both look and see a draw. This person sent no claim.

### Resigning and aborting

**Resign.** They attempt a resignation, and both seats have already played. Both look and see a loss for the seat that resigned. The clock of the seat to move stopped at the instant of the resignation; a later look shows the same figures.

**Resign where neither can force a win.** The same attempt. Both look and see a draw.

**Abort.** Before the second seat has played, either seat attempts an abort. Both look and see an abort: no winner, and the game is not an input to a rating pool.

**Abort too late.** The second seat has played. Either seat attempts an abort. It is not admitted. The game is still going. Resignation is the attempt that ends it.

### The clock

The agreement already fixed the shape of the clock. Realtime: a running clock, and an increment added to the seat that just played, when the play was admitted and the game is still going. Correspondence: a fresh period for each turn, and no increment. The attempts above are the same in both.

**Flag.** It is this seat's turn. Their time reaches zero. Nobody attempts a flag. Someone looks at a later instant, or this seat attempts a play after the time is gone. Both look and see a loss for this seat. The late play is not in the log. The instant the time reaches zero is the flag: a play at that instant is late, a play one millisecond earlier is a play.

**Flag with an offer standing.** The other seat's offer is standing when the time runs out. Both look and see a draw.

**Flag where the other seat cannot force a win.** Both look and see a draw. Where it cannot be settled whether the other seat can force a win, both look and see a loss for the seat whose time ran out.

**An ending stops the clock.** An agreed draw, a claim that holds, an abort, and a resignation each stop the clock of the seat to move at the instant of the act. A later look shows the same figures, however much later it is.

### After it is over

**Already ended.** The game has an ending. Either seat attempts anything. It is not admitted. A look still shows the ending and why.

### Whether it counts

Counting is a look, not an attempt. The agreement already says whether they asked for a rated game.

**Counts.** They asked for rated, the two people are different, both seats have played, and the look shows an ending that is not an abort. A look says this game is an input to the pool of its speed. The new rating is not something this game stores.

**Counts by the flag.** The same, when the ending the look shows is a flag. A look before the time ran out said the game was still open and did not count; a look after says it counts. The log did not change between the two.

**Does not count.** They did not ask for rated, or one person sits both seats, or the second seat never played, or the ending is an abort, or there is no ending yet. A look says this game is not an input.

## Not these flows

Finding an opponent. Signing in. Chat, messages, and watching. Taking a play back. Sending a play before it is your turn and having it wait. Puzzles, studies, tournaments, and variants. A judgment that someone used an engine. A clock figure announced by a person's own screen.
