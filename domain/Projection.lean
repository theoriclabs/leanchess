/-
  A stored projection of the fold.

  The prior world and the admitted log govern the answer. A projection
  is a stored copy of the fold at a revision of the log, kept for speed.
  It is not a fact: it is right only when it is the fold, and this file
  says what evidence that takes.

  A projection names the log it projects, the revision it reached, and
  the rules it folded with. Two projections of the same log at the same
  rules are the same state. A projection whose revision or rules do not
  match the log is stale and is rebuilt; nothing reads it as the fold.

  Observation time is not part of a projection. Two looks at one revision
  can differ in the clocks and in whether the flag has fallen.

  This game holds no private data, so no policy identity is carried.
  A projection of private data would carry the policy version that
  decides who may see it, for the same reason it carries the rules.

  What the store has to do with this — write the projection in the same
  transaction as the event, or rebuild on read — is an adapter obligation
  named at the end. It is not discharged here.
-/

import domain.Semantics

namespace LeanChess

/-- Which fold this is. The fold's meaning changed when claims became
    offers and endings started charging the clock (#32, #35); a projection
    folded before that is not this fold. -/
def rulesVersion : Nat := 2

structure Projection where
  /-- The log this projects. -/
  game : String
  /-- How many events were folded. -/
  revision : Nat
  /-- Which fold folded them. -/
  rules : Nat
  state : GameState
  deriving Repr, DecidableEq

/-- What a projection claims: the fold of exactly this log, by this fold. -/
def Projection.Represents (a : Agreement) (game : String) (log : List GameEvent)
    (p : Projection) : Prop :=
  p.game = game ∧ p.rules = rulesVersion ∧ p.revision = log.length ∧ p.state = fold a log

def Projection.init (a : Agreement) (game : String) : Projection :=
  ⟨game, 0, rulesVersion, initial a⟩

/-- One more event, incrementally. -/
def Projection.step (p : Projection) (ev : GameEvent) : Projection :=
  { p with revision := p.revision + 1, state := applyEvent p.state ev }

/-- From the log, by replay. -/
def Projection.rebuild (a : Agreement) (game : String) (log : List GameEvent) : Projection :=
  ⟨game, log.length, rulesVersion, fold a log⟩

theorem init_represents (a : Agreement) (game : String) :
    (Projection.init a game).Represents a game [] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem rebuild_represents (a : Agreement) (game : String) (log : List GameEvent) :
    (Projection.rebuild a game log).Represents a game log :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The incremental update of a projection of `log` is a projection of
    `log ++ [ev]`. This is `fold_snoc`. -/
theorem step_represents {a : Agreement} {game : String} {log : List GameEvent} {p : Projection}
    (h : p.Represents a game log) (ev : GameEvent) :
    (p.step ev).Represents a game (log ++ [ev]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · simp [Projection.step, h3]
  · simp [Projection.step, h4, fold_snoc]

/-- Incremental and replayed agree. -/
theorem represents_unique {a : Agreement} {game : String} {log : List GameEvent}
    {p q : Projection} (hp : p.Represents a game log) (hq : q.Represents a game log) : p = q := by
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  cases p; cases q
  simp_all

/-- A projection the store hands back is used only when it names this
    log's revision and rules. Otherwise it is rebuilt. A matching revision
    with a wrong state is not detected here: that needs the adapter's
    atomicity, or a rebuild. -/
def Projection.refresh (a : Agreement) (game : String) (log : List GameEvent)
    (p : Projection) : Projection :=
  if p.game = game ∧ p.revision = log.length ∧ p.rules = rulesVersion then p
  else Projection.rebuild a game log

/-- `refresh` represents the log, given that a projection at a matching
    revision and rules holds the fold. That premise is what the adapter
    owes. -/
theorem refresh_represents {a : Agreement} {game : String} {log : List GameEvent}
    {p : Projection}
    (trusted : p.game = game → p.revision = log.length → p.rules = rulesVersion →
      p.state = fold a log) :
    (p.refresh a game log).Represents a game log := by
  unfold Projection.refresh
  split
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, h3, h2, trusted h1 h2 h3⟩
  · exact rebuild_represents a game log

/-- A stale revision is rebuilt, whatever its state. -/
theorem refresh_stale {a : Agreement} {game : String} {log : List GameEvent} {p : Projection}
    (h : p.revision ≠ log.length) : p.refresh a game log = Projection.rebuild a game log := by
  unfold Projection.refresh
  rw [if_neg]
  intro ⟨_, h2, _⟩
  exact h h2

/-- Other rules are rebuilt, whatever the revision. -/
theorem refresh_other_rules {a : Agreement} {game : String} {log : List GameEvent}
    {p : Projection} (h : p.rules ≠ rulesVersion) :
    p.refresh a game log = Projection.rebuild a game log := by
  unfold Projection.refresh
  rw [if_neg]
  intro ⟨_, _, h3⟩
  exact h h3

/- ====================================================================
   A projection that carries its evidence
   ==================================================================== -/

/-- A projection with the proof that it is the fold. There is no way to
    build one without that proof, so an implementation without the
    evidence cannot be selected as this. -/
structure Verified (a : Agreement) (game : String) (log : List GameEvent) where
  proj : Projection
  represents : proj.Represents a game log

def Verified.init (a : Agreement) (game : String) : Verified a game [] :=
  ⟨Projection.init a game, init_represents a game⟩

def Verified.step {a : Agreement} {game : String} {log : List GameEvent}
    (v : Verified a game log) (ev : GameEvent) : Verified a game (log ++ [ev]) :=
  ⟨v.proj.step ev, step_represents v.represents ev⟩

def Verified.rebuild (a : Agreement) (game : String) (log : List GameEvent) : Verified a game log :=
  ⟨Projection.rebuild a game log, rebuild_represents a game log⟩

/-- Admission against a verified projection: the same outcome as against
    the fold, and on acceptance a verified projection of the longer log. -/
def Verified.admit {a : Agreement} {game : String} {log : List GameEvent}
    (v : Verified a game log) (seat : Color) (cmd : Command) (now : Instant) :
    (o : Outcome) × Verified a game (o.append log) :=
  match LeanChess.admit v.proj.state seat cmd now with
  | .accepted ev after => ⟨.accepted ev after, v.step ev⟩
  | .refused why => ⟨.refused why, v⟩
  | .flagged e after => ⟨.flagged e after, v⟩

theorem Verified.admit_outcome {a : Agreement} {game : String} {log : List GameEvent}
    (v : Verified a game log) (seat : Color) (cmd : Command) (now : Instant) :
    (v.admit seat cmd now).1 = LeanChess.admit (fold a log) seat cmd now := by
  have hs : v.proj.state = fold a log := v.represents.2.2.2
  unfold Verified.admit
  rw [← hs]
  split <;> rename_i ho <;> simp only [ho]

/-- Clock-dependent answers read the projection's state at an instant of
    the look's choosing. Equal revision does not mean equal clocks. -/
theorem observe_verified {a : Agreement} {game : String} {log : List GameEvent}
    (v : Verified a game log) (d : Instant) :
    resultAt v.proj.state d = resultAt (fold a log) d ∧
      (∀ c, remaining v.proj.state c d = remaining (fold a log) c d) := by
  have hs : v.proj.state = fold a log := v.represents.2.2.2
  rw [hs]
  exact ⟨rfl, fun _ => rfl⟩

/- ====================================================================
   Checks
   ==================================================================== -/

private def e4 : Move := mv .e .r2 .e .r4
private def e5 : Move := mv .e .r7 .e .r5
private def log2 : List GameEvent := [.moved e4 ⟨1000⟩, .moved e5 ⟨2000⟩]

/- Incremental equals replay. -/
#guard ((Projection.init sample "g").step (.moved e4 ⟨1000⟩)).step (.moved e5 ⟨2000⟩)
  == Projection.rebuild sample "g" log2

/- A stale projection is rebuilt; a current one is kept. -/
#guard (Projection.rebuild sample "g" [.moved e4 ⟨1000⟩]).refresh sample "g" log2
  == Projection.rebuild sample "g" log2
#guard (Projection.rebuild sample "g" log2).refresh sample "g" log2 == Projection.rebuild sample "g" log2
#guard ({ Projection.rebuild sample "g" log2 with rules := 1 }).refresh sample "g" log2
  == Projection.rebuild sample "g" log2

/- One revision, two instants, two clocks. -/
#guard remaining (Projection.rebuild sample "g" log2).state .white ⟨2000⟩ == 299000
#guard remaining (Projection.rebuild sample "g" log2).state .white ⟨7000⟩ == 294000
#guard resultAt (Projection.rebuild sample "g" log2).state ⟨301000⟩ == some (.flag .black)

/- A verified projection admits what the fold admits. -/
#guard ((Verified.rebuild sample "g" log2).admit .white (.play (mv .g .r1 .f .r3)) ⟨3000⟩).1
  == LeanChess.admit (fold sample log2) .white (.play (mv .g .r1 .f .r3)) ⟨3000⟩

end LeanChess
