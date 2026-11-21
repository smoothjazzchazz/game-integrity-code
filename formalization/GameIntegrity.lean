/-!
Game Integrity — exploratory Lean 4 formalization
Reference: paper/draft-v0.2.md

This file contains ONLY definitions, the Tic-Tac-Toe example, and statements
of results already developed in the manuscript. `sorry` marks proof work that
has not yet been mechanically established.

The mathematical transition function is partial over S × P × A. In Lean, an
`Option S` models this as a total function returning `none` on illegal inputs.
This is not Lean's `partial def` (which concerns recursive computation).
-/

namespace GameIntegrity

/-! ## 1. Our general game definition -/

/-- The tuple G = (P, S, A, s₀, L, δ, T, u).
    The carrier types P, S, A and the payoff carrier U are parameters. -/
structure Game (P S A U : Type) where
  initial : S
  legal : S → P → A → Prop                      -- L ⊆ S × P × A
  step? : S → P → A → Option S                 -- δ : S × P × A ⇀ S
  terminal : S → Prop                         -- T ⊆ S
  payoff : {s : S // terminal s} → P → U      -- u, on terminal states
  domain_eq_legal : ∀ s p a,
    (∃ s', step? s p a = some s') ↔ legal s p a
  terminal_closed : ∀ s p a,
    terminal s → ¬ legal s p a

namespace Game

variable {P S A U : Type} (G : Game P S A U)

/-- Definition 2: A_p(s) = { a ∈ A | (s,p,a) ∈ L }. -/
def AdmissibleActions (s : S) (p : P) : Set A :=
  {a | G.legal s p a}

/-- A concrete step in a legal history: s --(p,a)--> s'. -/
def Transition (s : S) (p : P) (a : A) (s' : S) : Prop :=
  G.legal s p a ∧ G.step? s p a = some s'

/-- Definition 3: a legal history from the initial state to s.
    The constructors retain the derivation, not just its endpoint. -/
inductive LegalHistory : S → Type where
  | initial : LegalHistory G.initial
  | extend {s s' : S} (h : LegalHistory s)
      (p : P) (a : A) (ht : G.Transition s p a s') : LegalHistory s'

/-- Definition 3: R is the set of endpoints of legal histories. -/
def Reachable (s : S) : Prop :=
  Nonempty (G.LegalHistory s)

/-- Proposition 3: reachability-invariant schema.
    The proof is postponed; the theorem is not yet verified. -/
theorem invariant_preservation
    (I : S → Prop)
    (h_initial : I G.initial)
    (h_step : ∀ s p a s', G.Transition s p a s' → I s → I s') :
    ∀ s, G.Reachable s → I s := by
  sorry

end Game

/-! ## 2. Tic-Tac-Toe: concrete state representation -/

namespace TicTacToe

inductive Player where
  | X
  | O
  deriving DecidableEq, Repr

open Player

def opponent : Player → Player
  | .X => .O
  | .O => .X

/-- C = {1,...,9}, indexed as 0,...,8 in Lean. -/
abbrev Cell := Fin 9

/-- V = {empty, X, O}; `none` is an empty cell. -/
abbrev Mark := Option Player

/-- b : C → V. -/
abbrev Board := Cell → Mark

/-- s = (b,t), with t the designated next player. -/
structure State where
  board : Board
  turn : Player

/-- b₀ is the empty board; X moves first. -/
def emptyBoard : Board := fun _ => none

def initial : State := ⟨emptyBoard, .X⟩

/-- W consists of the eight winning cell triples.
    Numerals in this definition use zero-based indexing. -/
def winningLines : List (Cell × Cell × Cell) :=
  [(0, 1, 2), (3, 4, 5), (6, 7, 8),
   (0, 3, 6), (1, 4, 7), (2, 5, 8),
   (0, 4, 8), (2, 4, 6)]

/-- Win_p(b): a winning line is entirely marked by p. -/
def wins (p : Player) (b : Board) : Prop :=
  ∃ line ∈ winningLines,
    let (c₁, c₂, c₃) := line
    b c₁ = some p ∧ b c₂ = some p ∧ b c₃ = some p

/-- Full(b): no empty cells remain. -/
def full (b : Board) : Prop :=
  ∀ c : Cell, b c ≠ none

/-- Definition of terminal states T. -/
def terminal (s : State) : Prop :=
  wins .X s.board ∨ wins .O s.board ∨ full s.board

/-- A = C. The move is legal exactly on the admissibility relation L. -/
def legal (s : State) (p : Player) (a : Cell) : Prop :=
  s.turn = p ∧ s.board a = none ∧ ¬ terminal s

/-- Board update b[a ↦ p]. -/
def place (b : Board) (a : Cell) (p : Player) : Board :=
  fun c => if c = a then some p else b c

/-- The mathematical successor for an admissible move. -/
def successor (s : State) (p : Player) (a : Cell) : State :=
  ⟨place s.board a p, opponent s.turn⟩

/-- The partial δ encoded as Option State.
    `none` means no game-state successor is defined. -/
def step? (s : State) (p : Player) (a : Cell) : Option State :=
  if legal s p a then some (successor s p a) else none

/-- The payoff convention in the draft: +1 for a win, -1 for a loss, 0 draw. -/
def payoff (s : {s : State // terminal s}) (p : Player) : Int :=
  if wins p s.val.board then 1
  else if wins (opponent p) s.val.board then -1
  else 0

/-- Our concrete G instantiates the general tuple. -/
def game : Game Player State Cell Int where
  initial := initial
  legal := legal
  step? := step?
  terminal := terminal
  payoff := payoff
  domain_eq_legal := by
    intro s p a
    simp [step?, legal]
  terminal_closed := by
    intro s p a ht
    simp [legal, ht]

/-- R, the concrete reachable set. -/
def reachable (s : State) : Prop :=
  game.Reachable s

/-! ## 3. Outcome classes used in our abstract FSM -/

/-- N_X: reachable, nonterminal states with X to move. -/
def N_X (s : State) : Prop :=
  reachable s ∧ ¬ terminal s ∧ s.turn = .X

/-- N_O: reachable, nonterminal states with O to move. -/
def N_O (s : State) : Prop :=
  reachable s ∧ ¬ terminal s ∧ s.turn = .O

/-- T_X: reachable states in which X wins. -/
def T_X (s : State) : Prop :=
  reachable s ∧ wins .X s.board

/-- T_O: reachable states in which O wins. -/
def T_O (s : State) : Prop :=
  reachable s ∧ wins .O s.board

/-- T_D: reachable full-board states without either winner. -/
def T_D (s : State) : Prop :=
  reachable s ∧ full s.board ∧ ¬ wins .X s.board ∧ ¬ wins .O s.board

/-- The initial state belongs to N_X (as shown in Figure 1). -/
theorem initial_in_N_X : N_X initial := by
  sorry

/-- The five classes exhaust R (Definition in Section 5). -/
theorem outcome_classes_cover_reachable (s : State) :
    reachable s → N_X s ∨ N_O s ∨ T_X s ∨ T_O s ∨ T_D s := by
  sorry

/-- Proposition 1: after X moves, the successor is in N_O, T_X, or T_D. -/
theorem x_transition_classes (s s' : State) (a : Cell)
    (hs : N_X s) (hstep : game.Transition s .X a s') :
    N_O s' ∨ T_X s' ∨ T_D s' := by
  sorry

/-- Proposition 1: after O moves, the successor is in N_X or T_O. -/
theorem o_transition_classes (s s' : State) (a : Cell)
    (hs : N_O s) (hstep : game.Transition s .O a s') :
    N_X s' ∨ T_O s' := by
  sorry

/-- Proposition 1: terminal states do not admit actions. -/
theorem terminal_closure (s : State) (p : Player) (a : Cell)
    (hterm : T_X s ∨ T_O s ∨ T_D s) :
    step? s p a = none := by
  sorry

/-! ## 4. Finite play (Proposition 2) -/

/-- A legal history of exactly n transitions, ending in state s. -/
inductive LegalTrace : Nat → State → Prop where
  | initial : LegalTrace 0 initial
  | extend {n : Nat} {s s' : State} (h : LegalTrace n s)
      (p : Player) (a : Cell)
      (hstep : game.Transition s p a s') : LegalTrace (n + 1) s'

/-- Every legal history contains at most nine transitions. -/
theorem history_length_bound (n : Nat) (s : State)
    (h : LegalTrace n s) : n ≤ 9 := by
  sorry

/-- Maximal means no further legal action is defined at the endpoint. -/
def maximal (s : State) : Prop :=
  ∀ p : Player, ∀ a : Cell, ¬ legal s p a

/-- Proposition 2: a maximal history must end in exactly one outcome class.
    Uniqueness is represented by asserting each class excludes the other two. -/
theorem maximal_history_terminates (n : Nat) (s : State)
    (h : LegalTrace n s) (hm : maximal s) :
    (T_X s ∧ ¬ T_O s ∧ ¬ T_D s) ∨
    (T_O s ∧ ¬ T_X s ∧ ¬ T_D s) ∨
    (T_D s ∧ ¬ T_X s ∧ ¬ T_O s) := by
  sorry

/-! ## 5. Proposition 3 applied to Tic-Tac-Toe -/

/-- Any invariant true initially and preserved by every legal transition
    holds at every reachable Tic-Tac-Toe state. -/
theorem reachable_invariant
    (I : State → Prop)
    (h_initial : I initial)
    (h_step : ∀ s p a s', game.Transition s p a s' → I s → I s') :
    ∀ s, reachable s → I s := by
  exact game.invariant_preservation I h_initial h_step

end TicTacToe
end GameIntegrity
