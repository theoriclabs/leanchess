/-
  Valid positions, valid states, and what the fold keeps true.

  Three things are kept apart:

  * `Position.structural`: what a position the fold could hold looks like,
    whether or not any game reaches it. Distinct squares, one king each,
    no pawn on an edge rank, a right only while its king and rook are
    home, an en passant square only behind a pawn that just moved two.
    Decidable; a reconstructed value can be checked.
  * `Reachable`: the fold of some log from this agreement. The only way
    a position enters this program is as such a fold; the API never
    reconstructs a position from a diagram (`api/Service.replay` folds a
    checked log). Reachability is not decided here.
  * `validLog` (`domain/Command.lean`): a log every event of which is the
    accepted event of its own admission, in order. A proposed command
    (`Command`) and an accepted fact (`GameEvent`) are different types.

  What is proved, and what is not, is listed at the end under `Spec`.
  A `Spec` entry is a named proposition with no proof. It is not an
  axiom and nothing uses it.
-/

import domain.Command

namespace LeanChess

/- ====================================================================
   Structural validity of a position
   ==================================================================== -/

/-- Strictly ascending by square. Strict, so squares are distinct. -/
def Board.sorted : Board → Bool
  | [] => true
  | [_] => true
  | p :: q :: rest => (compare p.square q.square == .lt) && Board.sorted (q :: rest)

def Board.count (b : Board) (pc : Piece) : Nat :=
  (b.filter fun p => p.piece == pc).length

def Board.pawnsInside (b : Board) : Bool :=
  b.all fun p => p.piece.kind != .pawn || (p.square.rank != .r1 && p.square.rank != .r8)

/-- A right is held only while its king and its rook stand at home. -/
def Rights.consistent (b : Board) (r : Rights) : Bool :=
  (!r.wk || (b.get ⟨.e, .r1⟩ == some ⟨.white, .king⟩ && b.get ⟨.h, .r1⟩ == some ⟨.white, .rook⟩)) &&
  (!r.wq || (b.get ⟨.e, .r1⟩ == some ⟨.white, .king⟩ && b.get ⟨.a, .r1⟩ == some ⟨.white, .rook⟩)) &&
  (!r.bk || (b.get ⟨.e, .r8⟩ == some ⟨.black, .king⟩ && b.get ⟨.h, .r8⟩ == some ⟨.black, .rook⟩)) &&
  (!r.bq || (b.get ⟨.e, .r8⟩ == some ⟨.black, .king⟩ && b.get ⟨.a, .r8⟩ == some ⟨.black, .rook⟩))

/-- An en passant square is the one a pawn of the side that just moved
    passed over: empty, with that pawn one step on, and its origin empty. -/
def Position.epConsistent (p : Position) : Bool :=
  match p.ep with
  | none => true
  | some sq =>
    let mover := p.side.other
    let passed : Rank := match mover with | .white => .r3 | .black => .r6
    let d := pawnDir mover
    sq.rank == passed && p.board.get sq == none &&
      (match sq.offset 0 d with
        | some s => p.board.get s == some ⟨mover, .pawn⟩
        | none => false) &&
      (match sq.offset 0 (-d) with
        | some s => p.board.get s == none
        | none => false)

def Position.structural (p : Position) : Bool :=
  p.board.sorted &&
  p.board.count ⟨.white, .king⟩ == 1 &&
  p.board.count ⟨.black, .king⟩ == 1 &&
  p.board.pawnsInside &&
  Rights.consistent p.board p.rights &&
  p.epConsistent &&
  p.board.length ≤ 32

/-- The side that just moved left its king safe. Every position a legal
    move produces has this (`applyMove_king_safe`); the opening has it. -/
def Position.opponentSafe (p : Position) : Bool :=
  !kingAttacked p p.side.other

theorem opening_structural : opening.structural = true := by decide

theorem opening_opponentSafe : opening.opponentSafe = true := by decide

/- ====================================================================
   Consistency of a state: what the fold keeps in step
   ==================================================================== -/

/-- White moves on even plies. -/
def sideOfPly (n : Nat) : Color :=
  if n % 2 == 0 then .white else .black

theorem sideOfPly_succ (n : Nat) : sideOfPly (n + 1) = (sideOfPly n).other := by
  unfold sideOfPly
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, Nat.add_mod, Color.other]

/-- The fields the fold keeps in step, whatever the log. -/
structure GameState.Consistent (s : GameState) : Prop where
  /-- One key per ply, plus the opening. -/
  history_length : s.history.length = s.ply + 1
  /-- The last key is the position's. -/
  history_last : s.history.getLast? = some (posKey s.position)
  /-- The first key is the opening's. -/
  history_head : s.history.head? = some (posKey opening)
  /-- The side to move is the ply's. -/
  side : s.position.side = sideOfPly s.ply
  /-- A claim is the side to move's, or nobody's. -/
  claim : s.claim = none ∨ s.claim = some s.position.side
  /-- No offer or claim survives an ending. -/
  ended : s.ending.isSome = true → s.offer = none ∧ s.claim = none
  /-- The halfmove count is at most the ply. -/
  halfmove : s.halfmove ≤ s.ply
  /-- The running clock did not start before the agreement. -/
  clock : s.agreement.start.ms ≤ s.runningSince.ms

theorem initial_consistent (a : Agreement) : (initial a).Consistent where
  history_length := rfl
  history_last := rfl
  history_head := rfl
  side := rfl
  claim := Or.inl rfl
  ended := by simp [initial]
  halfmove := Nat.le_refl 0
  clock := Nat.le_refl _

/- Each piece of the fold keeps `Consistent`. -/

theorem spend_consistent {s : GameState} (h : s.Consistent) {t : Instant}
    (ht : s.runningSince.ms ≤ t.ms) : (spend s t).Consistent := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold spend
  split <;> exact ⟨h1, h2, h3, h4, h5, h6, h7, by simp; omega⟩

theorem endAt_consistent {s : GameState} (h : s.Consistent) {t : Instant}
    (ht : s.runningSince.ms ≤ t.ms) (e : Ending) : (endAt s t e).Consistent := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := spend_consistent h ht
  exact ⟨h1, h2, h3, h4, Or.inl rfl, fun _ => ⟨rfl, rfl⟩, h7, h8⟩

theorem freezeFlag_consistent {s : GameState} (h : s.Consistent) : (freezeFlag s).Consistent := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold freezeFlag
  split <;> exact ⟨h1, h2, h3, h4, Or.inl rfl, fun _ => ⟨rfl, rfl⟩, h7, h8⟩

theorem offerNow_consistent {s : GameState} (h : s.Consistent) (hopen : s.ending = none) :
    (offerNow s s.position.side).Consistent := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, Or.inr rfl, by simp [offerNow, hopen], h7, h8⟩

theorem settle_consistent {s : GameState} (h : s.Consistent) (mover : Color)
    (hclaim : s.claim = none) (hoffer : s.offer = none ∨ (settle s mover).ending = none) :
    (settle s mover).Consistent := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, Or.inl hclaim, ?_, h7, h8⟩
  intro he
  rcases hoffer with ho | ho
  · exact ⟨ho, hclaim⟩
  · rw [ho] at he; simp at he

theorem addIncrement_consistent {s : GameState} (h : s.Consistent) (c : Color) :
    (addIncrement s c).Consistent := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold addIncrement
  split
  · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  · split <;> exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem finishPlay_consistent {s : GameState} (h : s.Consistent) (c : Color) :
    (finishPlay s c).Consistent := by
  unfold finishPlay
  split
  · exact h
  · exact addIncrement_consistent h c

theorem spend_history_eq (s : GameState) (t : Instant) : (spend s t).history = s.history := by
  unfold spend; split <;> rfl
theorem spend_position_eq (s : GameState) (t : Instant) : (spend s t).position = s.position := by
  unfold spend; split <;> rfl
theorem spend_ply_eq (s : GameState) (t : Instant) : (spend s t).ply = s.ply := by
  unfold spend; split <;> rfl
theorem spend_halfmove_eq (s : GameState) (t : Instant) : (spend s t).halfmove = s.halfmove := by
  unfold spend; split <;> rfl
theorem spend_agreement_eq (s : GameState) (t : Instant) : (spend s t).agreement = s.agreement := by
  unfold spend; split <;> rfl
theorem spend_running_eq (s : GameState) (t : Instant) : (spend s t).runningSince = t := by
  unfold spend; split <;> rfl

theorem playMove_consistent {s : GameState} (h : s.Consistent) {m : Move} {t : Instant}
    {s' : GameState} (ht : s.runningSince.ms ≤ t.ms) (hp : playMove s m t = some s') :
    s'.Consistent ∧ s'.claim = none := by
  unfold playMove at hp
  cases hm : applyMove s.position m with
  | none => simp [hm] at hp
  | some p =>
    simp only [hm, Option.some.injEq] at hp
    subst hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    have hside := applyMove_side hm
    refine ⟨⟨?_, ?_, ?_, ?_, Or.inl rfl, fun hx => ⟨if_pos hx, rfl⟩, ?_, ?_⟩, rfl⟩
    · simp [settle, h1]
    · simp [settle]
    · simp only [settle]
      rcases hh : s.history with _ | ⟨x, xs⟩
      · rw [hh] at h3; simp at h3
      · rw [hh] at h3; simp at h3; simp [h3]
    · simp only [settle, hside, h4, sideOfPly_succ]
    · simp only [settle]
      split <;> omega
    · simp only [settle, spend_agreement_eq, spend_running_eq]
      omega

theorem commitMove_consistent {s : GameState} (h : s.Consistent) (m : Move) {t : Instant}
    (ht : s.runningSince.ms ≤ t.ms) : (commitMove s m t).Consistent := by
  unfold commitMove
  cases hp : playMove s m t with
  | none => simp only [hp]; exact h
  | some s' =>
    simp only [hp]
    obtain ⟨hc, _⟩ := playMove_consistent h ht hp
    exact finishPlay_consistent hc _

theorem claimWith_consistent {s : GameState} (h : s.Consistent) (hopen : s.ending = none)
    (m : Move) {t : Instant} (ht : s.runningSince.ms ≤ t.ms)
    (holds : GameState → Bool) (reason : DrawReason) :
    (claimWith s s.position.side m t holds reason).Consistent := by
  unfold claimWith
  have ho := offerNow_consistent h hopen
  have hrun : (offerNow s s.position.side).runningSince.ms ≤ t.ms := ht
  cases hp : playMove (offerNow s s.position.side) m t with
  | none => simp only [hp]; exact h
  | some s' =>
    simp only [hp]
    obtain ⟨hc, hclaim⟩ := playMove_consistent ho hrun hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hc
    split
    · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    · split
      · exact ⟨h1, h2, h3, h4, Or.inl hclaim, fun _ => ⟨rfl, hclaim⟩, h7, h8⟩
      · exact addIncrement_consistent ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ _

theorem guardTime_consistent {s : GameState} (h : s.Consistent) (t : Instant)
    (k : GameState → GameState)
    (hk : s.ending = none → s.runningSince.ms ≤ t.ms → (k s).Consistent) :
    (guardTime s t k).Consistent := by
  unfold guardTime
  split
  · exact h
  · rename_i hopen
    split
    · exact h
    · split
      · exact freezeFlag_consistent h
      · rename_i hlt _
        exact hk hopen (by omega)

/-- Every event keeps the state consistent. -/
theorem applyEvent_consistent {s : GameState} (h : s.Consistent) (ev : GameEvent) :
    (applyEvent s ev).Consistent := by
  cases ev with
  | moved m t =>
    simp only [applyEvent]
    exact guardTime_consistent h t _ fun _ ht => commitMove_consistent h m ht
  | resigned c t =>
    simp only [applyEvent]
    refine guardTime_consistent h t _ fun _ ht => ?_
    try simp only []
    split
    · exact h
    · split
      · exact endAt_consistent h ht _
      · exact endAt_consistent h ht _
  | drawOffered c t =>
    simp only [applyEvent]
    refine guardTime_consistent h t _ fun hopen _ => ?_
    try simp only []
    split
    · exact h
    · rename_i hc
      have hc' : s.position.side = c := by simpa using hc
      subst hc'
      exact offerNow_consistent h hopen
  | drawAccepted c t =>
    simp only [applyEvent]
    refine guardTime_consistent h t _ fun _ ht => ?_
    try simp only []
    split
    · exact endAt_consistent h ht _
    · exact h
  | drawDeclined c t =>
    simp only [applyEvent]
    refine guardTime_consistent h t _ fun hopen _ => ?_
    try simp only []
    split
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
      exact ⟨h1, h2, h3, h4, h5, by simp [hopen], h7, h8⟩
    · exact h
  | claimedThreefold c intended t =>
    simp only [applyEvent]
    refine guardTime_consistent h t _ fun hopen ht => ?_
    try simp only []
    split
    · exact h
    · rename_i hc
      have hc' : s.position.side = c := by simpa using hc
      subst hc'
      cases intended with
      | none =>
        try simp only []
        split
        · exact endAt_consistent h ht _
        · exact offerNow_consistent h hopen
      | some m => exact claimWith_consistent h hopen m ht _ _
  | claimedFifty c intended t =>
    simp only [applyEvent]
    refine guardTime_consistent h t _ fun hopen ht => ?_
    try simp only []
    split
    · exact h
    · rename_i hc
      have hc' : s.position.side = c := by simpa using hc
      subst hc'
      cases intended with
      | none =>
        try simp only []
        split
        · exact endAt_consistent h ht _
        · exact offerNow_consistent h hopen
      | some m => exact claimWith_consistent h hopen m ht _ _
  | aborted c t =>
    simp only [applyEvent]
    refine guardTime_consistent h t _ fun _ ht => ?_
    try simp only []
    split
    · exact endAt_consistent h ht _
    · exact h

theorem applyEvents_consistent {s : GameState} (h : s.Consistent) (log : List GameEvent) :
    (applyEvents s log).Consistent := by
  induction log generalizing s with
  | nil => exact h
  | cons ev rest ih => exact ih (applyEvent_consistent h ev)

/-- The fold of some log from this agreement. -/
def Reachable (a : Agreement) (s : GameState) : Prop :=
  ∃ log, fold a log = s

/-- Every reachable state is consistent. -/
theorem reachable_consistent {a : Agreement} {s : GameState} (h : Reachable a s) : s.Consistent := by
  obtain ⟨log, rfl⟩ := h
  exact applyEvents_consistent (initial_consistent a) log

/- ====================================================================
   Stability after an ending
   ==================================================================== -/

/-- Once the game has an ending, no event changes the fold. -/
theorem ended_stable {s : GameState} {e : Ending} (h : s.ending = some e) (ev : GameEvent) :
    applyEvent s ev = s := by
  cases ev <;> simp [applyEvent, guardTime, h]

theorem ended_stable_log {s : GameState} {e : Ending} (h : s.ending = some e)
    (log : List GameEvent) : applyEvents s log = s := by
  induction log with
  | nil => rfl
  | cons ev rest ih => simp [applyEvents, ended_stable h ev, ih]

/- ====================================================================
   Checks. Malformed, and valid but not known reachable.
   ==================================================================== -/

private def wK : Piece := ⟨.white, .king⟩
private def bK : Piece := ⟨.black, .king⟩

/- Two pieces on one square. -/
#guard !(Position.structural ⟨sortBoard [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r1⟩, bK⟩], .white, Rights.none, none⟩)
/- Two white kings. -/
#guard !(Position.structural ⟨sortBoard [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.a, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩], .white, Rights.none, none⟩)
/- No black king. -/
#guard !(Position.structural ⟨[⟨⟨.e, .r1⟩, wK⟩], .white, Rights.none, none⟩)
/- A pawn on the last rank. -/
#guard !(Position.structural ⟨sortBoard [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩, ⟨⟨.a, .r8⟩, ⟨.white, .pawn⟩⟩], .white, Rights.none, none⟩)
/- A right with the king off its square. -/
#guard !(Position.structural ⟨sortBoard [⟨⟨.d, .r1⟩, wK⟩, ⟨⟨.h, .r1⟩, ⟨.white, .rook⟩⟩, ⟨⟨.e, .r8⟩, bK⟩], .white, { wk := true, wq := false, bk := false, bq := false }, none⟩)
/- An en passant square with no pawn behind it. -/
#guard !(Position.structural ⟨sortBoard [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩], .black, Rights.none, some ⟨.e, .r3⟩⟩)
/- Unsorted: the same placements in another order are not a fold's board. -/
#guard !(Position.structural ⟨[⟨⟨.e, .r8⟩, bK⟩, ⟨⟨.e, .r1⟩, wK⟩], .white, Rights.none, none⟩)
/- Structurally valid. Whether a game reaches it is not decided here. -/
#guard Position.structural ⟨sortBoard [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩], .white, Rights.none, none⟩
/- After e4: an en passant square behind the pawn, and the rights intact. -/
#guard (replay [mv .e .r2 .e .r4]).position.structural
#guard (replay [mv .e .r2 .e .r4]).position.ep == some ⟨.e, .r3⟩
#guard (replay scholar).position.structural
#guard (replay castled).position.structural
#guard (replay enPassant).position.structural
#guard (replay scholar).position.opponentSafe
/- The consistency fields, on a fold. -/
#guard (replay scholar).history.length == (replay scholar).ply + 1
#guard (replay scholar).position.side == sideOfPly (replay scholar).ply

/- ====================================================================
   Open. Named, not proved, not assumed.
   ==================================================================== -/

namespace Spec

/-- A legal move from a structurally valid position whose opponent's king
    is safe produces a structurally valid position. Proved above for the
    side to move (`applyMove_side`), the rights' monotonicity
    (`applyMove_rights`), and the mover's king (`applyMove_king_safe`).
    Open for: distinct squares, one king each, no pawn on an edge rank,
    rights consistent, en passant consistent. -/
def structuralPreserved : Prop :=
  ∀ (p : Position) (m : Move) (p' : Position),
    p.structural = true → p.opponentSafe = true → applyMove p m = some p' →
      p'.structural = true

/-- The side that just moved left its king safe: `applyMove_king_safe` says
    it of the mover; this says the fold keeps it as `opponentSafe`. -/
def opponentSafePreserved : Prop :=
  ∀ (p : Position) (m : Move) (p' : Position),
    applyMove p m = some p' → p'.opponentSafe = true

/-- Every reachable position is structurally valid. Follows from the two
    above and `opening_structural`. -/
def reachableStructural : Prop :=
  ∀ (a : Agreement) (s : GameState), Reachable a s → s.position.structural = true

/-- The executable legality decision agrees with the intended rules on
    structural positions. What "intended rules" are, as a Lean proposition
    independent of `applyMove`, is not written yet. -/
def legalityMatchesRules : Prop := True

end Spec

end LeanChess
