/-
  A dead position, and what the material detector establishes.

  The meaning (FIDE 1.5, 5.2.2): a position is dead when no series of
  legal moves lets either side checkmate. `CanMate` and `Dead` say that
  with `Reaches`, the closure of `applyMove`. No solver is required to
  state them.

  Three kinds of evidence, kept apart:

  * `Dead p`, proved. For a position with a finite closure under legal
    moves, `dead_of_closure` checks the closure and proves it. For every
    position with two kings and nothing else, `kings_dead` proves it once.
  * `CanMate p c`, established. `matesWith` plays a line and finds the
    mate; `matesWith_sound` turns that into `CanMate`.
  * Unknown. `Material.mayMate p c = true` says nothing. `Material.dead p
    = true` is the detector's verdict. On two kings it is proved sound
    here. On a lone knight or bishop, and on same-colour bishops, it is
    what the detector asserts and this file has not proved: `Spec` below.

  Completeness is refuted: `blocked` is dead and the detector does not
  say so. The game goes on there until a claim or seventy-five moves.

  How the fold consumes the verdict is site policy, and is named as such
  in `vocabulary.md`: `Material.dead` ends the game (`settle`) and turns a
  resignation into a draw; `Material.mayMate` decides a flag in the
  direction that gives the side with time the win when mate is not ruled
  out (Lichess).
-/

import Std.Data.HashSet
import domain.Valid

namespace LeanChess

/- ====================================================================
   The meaning
   ==================================================================== -/

/-- `q` follows `p` by a series of legal moves. -/
inductive Reaches : Position → Position → Prop
  | refl (p : Position) : Reaches p p
  | step {p q q' : Position} (m : Move) : Reaches p q → applyMove q m = some q' → Reaches p q'

/-- `c` can mate: some continuation ends with the other side to move, in
    check, with no legal move. -/
def CanMate (p : Position) (c : Color) : Prop :=
  ∃ q, Reaches p q ∧ q.side = c.other ∧ isCheckmate q = true

/-- Neither side can mate. -/
def Dead (p : Position) : Prop :=
  ¬ CanMate p .white ∧ ¬ CanMate p .black

theorem dead_iff (p : Position) : Dead p ↔ ∀ q, Reaches p q → isCheckmate q = false := by
  constructor
  · rintro ⟨hw, hb⟩ q hq
    cases hc : isCheckmate q with
    | false => rfl
    | true =>
      exfalso
      cases hs : q.side with
      | black => exact hw ⟨q, hq, hs, hc⟩
      | white => exact hb ⟨q, hq, hs, hc⟩
  · intro h
    constructor
    · rintro ⟨q, hq, _, hc⟩
      rw [h q hq] at hc
      exact Bool.false_ne_true hc
    · rintro ⟨q, hq, _, hc⟩
      rw [h q hq] at hc
      exact Bool.false_ne_true hc

/- ====================================================================
   Proved dead: a closed set with no mate in it
   ==================================================================== -/

/-- If `p` lies in a set closed under legal moves in which no position is
    checkmate, `p` is dead. -/
theorem dead_of_invariant (S : Position → Prop) {p : Position} (hp : S p)
    (closed : ∀ q, S q → ∀ m q', applyMove q m = some q' → S q')
    (safe : ∀ q, S q → isCheckmate q = false) : Dead p := by
  rw [dead_iff]
  intro q hq
  have : S q := by
    induction hq with
    | refl => exact hp
    | step m _ hm ih => exact closed _ ih m _ hm
  exact safe q this

/-- Every legal move from every listed position lands in the list. -/
def closedUnder (visited : List Position) : Bool :=
  visited.all fun q => (legalMoves q).all fun m =>
    match applyMove q m with
    | some q' => visited.contains q'
    | none => true

def noMate (visited : List Position) : Bool :=
  visited.all fun q => !isCheckmate q

/-- The checker's verdict is a proof. The list can come from anywhere. -/
theorem dead_of_closure (visited : List Position) {p : Position}
    (hp : visited.contains p = true) (hc : closedUnder visited = true)
    (hn : noMate visited = true) : Dead p := by
  refine dead_of_invariant (fun q => q ∈ visited) (List.contains_iff_mem.mp hp) ?_ ?_
  · intro q hq m q' hm
    have h1 := (List.all_eq_true.mp hc) q hq
    have hml : m ∈ legalMoves q := mem_legalMoves.mpr ⟨q', hm⟩
    have h2 := (List.all_eq_true.mp h1) m hml
    simp only [hm] at h2
    exact List.contains_iff_mem.mp h2
  · intro q hq
    have h1 := (List.all_eq_true.mp hn) q hq
    simpa using h1

/-- Breadth-first, with fuel. Untrusted: only `dead_of_closure` counts. -/
def explore (fuel : Nat) (frontier : List Position) (seen : Std.HashSet Position) :
    Std.HashSet Position :=
  match fuel, frontier with
  | 0, _ => seen
  | _, [] => seen
  | n + 1, q :: rest =>
    let next := (legalMoves q).filterMap fun m =>
      match applyMove q m with
      | some q' => if seen.contains q' then none else some q'
      | none => none
    let seen := next.foldl (fun acc q' => acc.insert q') seen
    explore n (rest ++ next) seen

def closureOf (p : Position) (fuel : Nat) : List Position :=
  (explore fuel [p] (({} : Std.HashSet Position).insert p)).toList

/-- A dead verdict by exploration: the closure is finite, closed, and holds
    no mate. `false` says nothing. -/
def deadByExploration (p : Position) (fuel : Nat) : Bool :=
  let visited := closureOf p fuel
  visited.contains p && closedUnder visited && noMate visited

theorem deadByExploration_sound {p : Position} {fuel : Nat}
    (h : deadByExploration p fuel = true) : Dead p := by
  unfold deadByExploration at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact dead_of_closure (closureOf p fuel) h1 h2 h3

/- ====================================================================
   Established: a line that mates
   ==================================================================== -/

/-- Play the line. `true` when it is legal throughout and ends in mate. -/
def matesWith (p : Position) : List Move → Bool
  | [] => isCheckmate p
  | m :: ms =>
    match applyMove p m with
    | some p' => matesWith p' ms
    | none => false

/-- A legal move, then a series: a series. -/
theorem Reaches.after {p p' q : Position} {m : Move} (hm : applyMove p m = some p')
    (hq : Reaches p' q) : Reaches p q := by
  induction hq with
  | refl => exact Reaches.step m (Reaches.refl p) hm
  | step m' _ hm' ih => exact Reaches.step m' ih hm'

theorem matesWith_reaches (p : Position) : ∀ (line : List Move), matesWith p line = true →
    ∃ q, Reaches p q ∧ isCheckmate q = true
  | [], h => ⟨p, Reaches.refl p, h⟩
  | m :: ms, h => by
    simp only [matesWith] at h
    cases hm : applyMove p m with
    | none => simp [hm] at h
    | some p' =>
      rw [hm] at h
      obtain ⟨q, hq, hc⟩ := matesWith_reaches p' ms h
      exact ⟨q, Reaches.after hm hq, hc⟩

/-- A line that mates establishes that the side it mates for can mate. -/
theorem matesWith_sound {p : Position} {line : List Move} (h : matesWith p line = true) :
    ∃ c, CanMate p c := by
  obtain ⟨q, hq, hc⟩ := matesWith_reaches p line h
  refine ⟨q.side.other, q, hq, ?_, hc⟩
  cases q.side <;> rfl

/-- A line that mates is not a dead position. -/
theorem not_dead_of_matesWith {p : Position} {line : List Move} (h : matesWith p line = true) :
    ¬ Dead p := by
  intro hd
  obtain ⟨q, hq, hc⟩ := matesWith_reaches p line h
  rw [(dead_iff p).mp hd q hq] at hc
  exact Bool.false_ne_true hc

/- ====================================================================
   Two kings: the detector is sound, once and for all
   ==================================================================== -/

/-- Two kings and nothing else, on a fold's board, with the king of the
    side that just moved not attacked. Kings side by side are not a
    position a game reaches, and from one the mover could take the other. -/
def onlyKings (p : Position) : Bool :=
  (match p.board with
  | [x, y] =>
    p.board.sorted &&
      decide ((x.piece = ⟨.white, .king⟩ ∧ y.piece = ⟨.black, .king⟩) ∨
        (x.piece = ⟨.black, .king⟩ ∧ y.piece = ⟨.white, .king⟩)) &&
      decide (p.rights = Rights.none) && decide (p.ep = none)
  | _ => false) && p.opponentSafe

def kvkBoard (w b : Square) : Board :=
  sortBoard [⟨w, ⟨.white, .king⟩⟩, ⟨b, ⟨.black, .king⟩⟩]

/-- Every placement of two kings, either side to move. -/
def kvkPlacements : List Position :=
  Square.all.flatMap fun w => Square.all.flatMap fun b =>
    if w = b then []
    else [⟨kvkBoard w b, .white, Rights.none, none⟩, ⟨kvkBoard w b, .black, Rights.none, none⟩]

/-- Every position with two kings only. -/
def kvkAll : List Position :=
  kvkPlacements.filter Position.opponentSafe

theorem Square.mem_all (s : Square) : s ∈ Square.all := by
  obtain ⟨fl, r⟩ := s
  cases fl <;> cases r <;> decide

/-- The derived order on squares, checked over every pair. -/
theorem Square.compare_flip : ∀ a ∈ Square.all, ∀ b ∈ Square.all,
    compare a b = .lt → compare b a = .gt := by
  native_decide

theorem Square.compare_lt_ne {a b : Square} (h : compare a b = .lt) : a ≠ b := by
  intro heq
  subst heq
  have := Square.compare_flip a (Square.mem_all a) a (Square.mem_all a) h
  rw [h] at this
  exact Ordering.noConfusion this

theorem onlyKings_mem {p : Position} (h : onlyKings p = true) : p ∈ kvkAll := by
  unfold onlyKings at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h, hsafe⟩ := h
  refine List.mem_filter.mpr ⟨?_, hsafe⟩
  obtain ⟨board, side, rights, ep⟩ := p
  match board, h with
  | [⟨xs, xp⟩, ⟨ys, yp⟩], h =>
    simp only [Board.sorted, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hlt, _⟩, hk⟩, hr⟩, he⟩ := h
    subst hr he
    have hne : xs ≠ ys := Square.compare_lt_ne hlt
    have hgt : compare ys xs = .gt :=
      Square.compare_flip xs (Square.mem_all xs) ys (Square.mem_all ys) hlt
    unfold kvkPlacements
    simp only [List.mem_flatMap, Square.mem_all, true_and]
    rcases hk with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx hy
    · -- white king first, black king second
      refine ⟨xs, ys, ?_⟩
      simp only [hne, if_false, kvkBoard, sortBoard, insertBySquare, hlt, List.mem_cons,
        List.mem_nil_iff, or_false]
      cases side <;> simp
    · -- black king first, white king second
      refine ⟨ys, xs, ?_⟩
      simp only [Ne.symm hne, if_false, kvkBoard, sortBoard, insertBySquare, hgt, List.mem_cons,
        List.mem_nil_iff, or_false]
      cases side <;> simp

/-- The two-king positions are closed under legal moves. Checked once, for
    all of them. -/
theorem kvk_closed :
    (kvkAll.all fun q => (legalMoves q).all fun m =>
      match applyMove q m with
      | some q' => onlyKings q'
      | none => true) = true := by
  native_decide

/-- No two-king position is checkmate. -/
theorem kvk_safe : (kvkAll.all fun q => !isCheckmate q) = true := by
  native_decide

/-- Two kings and nothing else: dead, whatever the squares and the side. -/
theorem kings_dead {p : Position} (h : onlyKings p = true) : Dead p := by
  refine dead_of_invariant (fun q => onlyKings q = true) h ?_ ?_
  · intro q hq m q' hm
    have h1 := (List.all_eq_true.mp kvk_closed) q (onlyKings_mem hq)
    have h2 := (List.all_eq_true.mp h1) m (mem_legalMoves.mpr ⟨q', hm⟩)
    simpa [hm] using h2
  · intro q hq
    have h1 := (List.all_eq_true.mp kvk_safe) q (onlyKings_mem hq)
    simpa using h1

/-- On two kings, the detector says dead, and it is right. -/
theorem material_dead_kings : (kvkAll.all fun q => Material.dead q) = true := by
  native_decide

theorem material_dead_kings_sound {p : Position} (h : onlyKings p = true) :
    Material.dead p = true ∧ Dead p :=
  ⟨by simpa using (List.all_eq_true.mp material_dead_kings) p (onlyKings_mem h), kings_dead h⟩

/- ====================================================================
   Examples. What the detector says, and what is proved.
   ==================================================================== -/

private def wK : Piece := ⟨.white, .king⟩
private def bK : Piece := ⟨.black, .king⟩
private def wP : Piece := ⟨.white, .pawn⟩
private def bP : Piece := ⟨.black, .pawn⟩

private def pos (b : Board) (side : Color := .white) : Position :=
  ⟨sortBoard b, side, Rights.none, none⟩

/-- Sixteen pawns face to face, and the kings cannot get past them. Dead;
    the detector does not say so. -/
def blocked : Position := pos [
  ⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩,
  ⟨⟨.a, .r4⟩, wP⟩, ⟨⟨.b, .r5⟩, wP⟩, ⟨⟨.c, .r4⟩, wP⟩, ⟨⟨.d, .r5⟩, wP⟩,
  ⟨⟨.e, .r4⟩, wP⟩, ⟨⟨.f, .r5⟩, wP⟩, ⟨⟨.g, .r4⟩, wP⟩, ⟨⟨.h, .r5⟩, wP⟩,
  ⟨⟨.a, .r5⟩, bP⟩, ⟨⟨.b, .r6⟩, bP⟩, ⟨⟨.c, .r5⟩, bP⟩, ⟨⟨.d, .r6⟩, bP⟩,
  ⟨⟨.e, .r5⟩, bP⟩, ⟨⟨.f, .r6⟩, bP⟩, ⟨⟨.g, .r5⟩, bP⟩, ⟨⟨.h, .r6⟩, bP⟩]

#guard blocked.structural
#guard !Material.dead blocked
#guard Material.mayMate blocked .white

theorem blocked_dead : Dead blocked :=
  deadByExploration_sound (fuel := 2000) (by native_decide)

/-- Completeness of the detector is refuted: a dead position it reports as
    not dead. -/
theorem material_incomplete : ∃ p, Dead p ∧ Material.dead p = false :=
  ⟨blocked, blocked_dead, by decide⟩

/-- The scholar's mate line establishes that White can mate from the opening. -/
theorem opening_white_can_mate : ∃ c, CanMate opening c :=
  matesWith_sound (line := scholar) (by native_decide)

theorem opening_not_dead : ¬ Dead opening :=
  not_dead_of_matesWith (line := scholar) (by native_decide)

/- A lone knight, a lone bishop, same-colour bishops: the detector says
   dead. Proved here for none of them; see `Spec`. Opposite-colour bishops,
   knight against knight, and a rook: the detector says nothing. -/
private def kNk : Position := pos [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩, ⟨⟨.b, .r1⟩, ⟨.white, .knight⟩⟩]
private def kBk : Position := pos [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩, ⟨⟨.c, .r1⟩, ⟨.white, .bishop⟩⟩]
private def kBkBsame : Position := pos [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩,
  ⟨⟨.c, .r1⟩, ⟨.white, .bishop⟩⟩, ⟨⟨.f, .r8⟩, ⟨.black, .bishop⟩⟩]
private def kBkBopp : Position := pos [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩,
  ⟨⟨.c, .r1⟩, ⟨.white, .bishop⟩⟩, ⟨⟨.c, .r8⟩, ⟨.black, .bishop⟩⟩]
private def kNkN : Position := pos [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩,
  ⟨⟨.b, .r1⟩, ⟨.white, .knight⟩⟩, ⟨⟨.b, .r8⟩, ⟨.black, .knight⟩⟩]
private def kRk : Position := pos [⟨⟨.e, .r1⟩, wK⟩, ⟨⟨.e, .r8⟩, bK⟩, ⟨⟨.a, .r1⟩, ⟨.white, .rook⟩⟩]

#guard Material.dead kNk
#guard Material.dead kBk
#guard Material.dead kBkBsame
#guard !Material.dead kBkBopp
#guard !Material.dead kNkN
#guard !Material.dead kRk
#guard Material.mayMate kRk .white && !Material.mayMate kRk .black

/-- King and rook mate: a line that shows it. -/
private def krkMate : Position := pos [⟨⟨.a, .r6⟩, wK⟩, ⟨⟨.a, .r8⟩, bK⟩, ⟨⟨.h, .r1⟩, ⟨.white, .rook⟩⟩]
theorem krk_can_mate : ∃ c, CanMate krkMate c :=
  matesWith_sound (line := [mv .h .r1 .h .r8]) (by native_decide)

/- ====================================================================
   Open. Named, not proved, not assumed.
   ==================================================================== -/

namespace Spec

/-- The detector's dead verdict is sound on structural positions. Proved
    for two kings only (`kings_dead`). Open for a lone knight, a lone
    bishop, and bishops on one colour. -/
def materialDeadSound : Prop :=
  ∀ p : Position, p.structural = true → Material.dead p = true → Dead p

/-- A side the detector clears cannot mate: what `flagInsufficient` relies
    on. Open on the same cases. -/
def mayMateSound : Prop :=
  ∀ (p : Position) (c : Color), p.structural = true → Material.mayMate p c = false →
    ¬ CanMate p c

end Spec

end LeanChess
