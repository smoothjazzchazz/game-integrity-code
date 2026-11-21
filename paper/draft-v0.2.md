# Game Integrity: Notes Toward an Intrinsically Secure Game Model

**Working draft — Version 0.2 (November 2026)**  
**Author:** Michael Lorenzo Lamiman  
**Status:** Early research draft. The core definitions and small-game results are established in this note, but the broader adversarial integrity claims are still a research goal rather than a finished theorem.

---

## Abstract

This project starts from a simple question: **can a game be designed so that invalid state transitions are excluded by the formal structure of the game itself, instead of being handled only by external anti-cheat mechanisms?** In other words, rather than asking whether a system can detect cheating after the fact, I want to ask whether we can define a game and its execution rules so that unauthorized transitions never become valid game transitions in the first place.

To begin answering that question, this draft builds a small mathematical framework for finite deterministic games using admissibility relations, partially defined transition functions, and reachable-state reasoning. Tic-Tac-Toe is used as the first worked example because it is simple enough to formalize completely while still illustrating the distinction between representable states, reachable states, and terminal outcomes. The goal of this draft is not yet to prove a full distributed security theorem. The goal is to build the first layer of the foundation clearly enough that it can later be formalized in Lean 4 and extended to adversarial execution models.

---

## 1. Motivation and research direction

What motivated this project is the gap between **game rules** and **actual execution**.

In ordinary game theory, a game is defined by legal moves, outcomes, and payoffs. In software, though, those rules only matter if the implementation actually enforces them. A real multiplayer game runs on machines, across networks, with potentially modified clients and adversarial participants. So even if the mathematical game says an action is illegal, that does not automatically mean an implementation cannot be manipulated into accepting it.

That leads to two different questions:

1. **Semantic legality:** what states and histories are actually allowed by the rules of the game?
2. **Execution integrity:** under what assumptions can an implementation be guaranteed to accept only those legal histories?

This draft is mostly about the first question. I want to define the mathematical game carefully enough that the second question can later be asked in a rigorous way.

The longer-term research objective is something like this:

> Can we build an authoritative execution model whose committed game histories are always refinements of the legal histories of the underlying formal game, even when some participants or components are adversarial?

I am **not** claiming that result yet. At this stage I am trying to formalize the first layer: what the game is, what a legal transition is, and what it means for a state to be reachable.

---

## 2. Scope of this draft

To keep the first formalization manageable, I restrict attention to:

- finite games,
- deterministic games,
- turn-based games,
- two-player games,
- perfect-information games.

That means this draft does **not** yet handle randomness, simultaneous actions, hidden information, network timing, Byzantine agreement, or cryptographic commitments. Those belong to a later phase.

The reason for starting this small is not because those issues are unimportant. It is because I want to make sure the foundations are mathematically clean before trying to generalize them.

---

## 3. Core definitions

### Definition 1. Finite deterministic game

I define a game as a tuple

\[
\mathcal G = (P,S,A,s_0,\mathcal L,\delta,T,u)
\]

where:

- \(P\) is a finite nonempty set of players,
- \(S\) is the set of **representable** states,
- \(A\) is the set of representable actions,
- \(s_0 \in S\) is the initial state,
- \(\mathcal L \subseteq S \times P \times A\) is the admissibility relation,
- \(\delta : S \times P \times A \rightharpoonup S\) is a **partially defined** transition function,
- \(T \subseteq S\) is the set of terminal states,
- \(u : T \to \mathbb R^{|P|}\) is a terminal payoff function.

This is not meant to be a universal definition of all games. It is the starting class of games I want to study in this project.

The most important feature here is that the transition function is **partial**. Not every state-player-action triple is valid. In fact,

\[
\operatorname{dom}(\delta)=\mathcal L.
\]

So if \((s,p,a)\notin \mathcal L\), then \(\delta(s,p,a)\) is undefined. In this model, an illegal action does not transition to an “error state.” It simply does not correspond to a game transition at all.

---

### Definition 2. Admissible actions

Given a state \(s\in S\) and player \(p\in P\), define the set of admissible actions for that player at that state by

\[
A_p(s)=\{a\in A \mid (s,p,a)\in \mathcal L\}.
\]

This makes action availability explicitly state-dependent.

That matters because it captures one of the main ideas behind this paper: the set of meaningful actions is not fixed globally. It depends on the current game configuration.

---

### Definition 3. Legal histories and reachability

A **legal history** is a sequence

\[
h=(s_0,p_0,a_0,s_1,\dots,p_{n-1},a_{n-1},s_n)
\]

such that for every \(0\leq i<n\),

\[
(s_i,p_i,a_i)\in \mathcal L
\quad\text{and}\quad
s_{i+1}=\delta(s_i,p_i,a_i).
\]

Let \(H_{\mathcal G}\) be the set of all such legal histories beginning at \(s_0\).

A state is **reachable** if it occurs as the final state of some legal history. The set of reachable states is denoted by \(R\subseteq S\).

This distinction between \(S\) and \(R\) is central:

- \(S\) contains all states that can be represented,
- \(R\) contains only states that can actually arise through legal play.

That is already important for the broader research direction. A machine may be able to store a state in memory even if that state has no legal justification inside the game.

---

## 4. Tic-Tac-Toe as the first case study

Tic-Tac-Toe is a good starting point because it is small enough to formalize clearly while still exposing the basic issues I care about.

### 4.1 State space

Let

\[
P=\{X,O\}, \qquad C=\{1,2,\dots,9\}, \qquad V=\{\varnothing,X,O\}.
\]

A board is a function

\[
b:C\to V.
\]

A game state is a pair

\[
s=(b,t)\in S=V^C\times P,
\]

where \(b\) is the board and \(t\) is the player whose turn it is to move.

The initial state is

\[
s_0=(b_0,X)
\]

where \(b_0(c)=\varnothing\) for every cell \(c\in C\).

---

### 4.2 Terminal states

Let \(\mathcal W\) be the set of eight winning lines in Tic-Tac-Toe:

\[
\mathcal W=
\{\{1,2,3\},\{4,5,6\},\{7,8,9\},\{1,4,7\},\{2,5,8\},\{3,6,9\},\{1,5,9\},\{3,5,7\}\}.
\]

Define

\[
\operatorname{Win}_p(b)
\iff
\exists w\in\mathcal W\;\forall c\in w,\; b(c)=p.
\]

Also define

\[
\operatorname{Full}(b)
\iff
\forall c\in C,\; b(c)\neq\varnothing.
\]

Then the terminal states are

\[
T=\{(b,t)\in S\mid \operatorname{Win}_X(b)\lor \operatorname{Win}_O(b)\lor \operatorname{Full}(b)\}.
\]

---

### 4.3 Admissibility and transition function

An action is just a selected cell, so \(A=C\).

A move is admissible exactly when it is that player’s turn, the chosen cell is empty, and the current state is not already terminal:

\[
((b,t),p,a)\in \mathcal L
\iff
t=p \;\land\; b(a)=\varnothing \;\land\; (b,t)\notin T.
\]

If a move is legal, then the transition function updates the board and switches the turn:

\[
\delta((b,t),p,a)=(b[a\mapsto p],\operatorname{opp}(t)).
\]

If the move is not admissible, then the transition is undefined.

This is exactly the kind of partiality I want to capture. The model does not ask, “what should happen if a player tries an invalid move?” It says that such a move simply has no successor in the game semantics.

---

## 5. Abstract outcome classes for Tic-Tac-Toe

To keep the state machine readable, I do not draw every concrete board configuration. Instead I group reachable states into five classes:

\[
N_X = \{(b,X)\in R\mid (b,X)\notin T\}
\]

\[
N_O = \{(b,O)\in R\mid (b,O)\notin T\}
\]

\[
T_X = \{(b,t)\in R\mid \operatorname{Win}_X(b)\}
\]

\[
T_O = \{(b,t)\in R\mid \operatorname{Win}_O(b)\}
\]

\[
T_D = \{(b,t)\in R\mid \operatorname{Full}(b) \land \neg\operatorname{Win}_X(b) \land \neg\operatorname{Win}_O(b)\}.
\]

These classes partition the reachable state space:

\[
R = N_X\; \dot\cup\; N_O\; \dot\cup\; T_X\; \dot\cup\; T_O\; \dot\cup\; T_D.
\]

### Figure 1. Abstract FSM for Tic-Tac-Toe termination structure

![Abstract FSM for Tic-Tac-Toe](assets/tictactoe-fsm.png)

This diagram is not the full state graph of Tic-Tac-Toe. It is an **abstracted finite state machine over classes of reachable states**.

The arrows should be read as **there exists at least one legal concrete transition of that type**. For example,

- from \(N_X\), X may move to another nonterminal state in \(N_O\),
- from \(N_X\), X may also move into \(T_X\) by completing a winning line,
- from \(N_X\), X may move into \(T_D\) by making the final non-winning move,
- from \(N_O\), O may move to \(N_X\) or \(T_O\).

A useful detail here is that **O cannot move directly to a draw state**. Since X moves first, the ninth and final move belongs to X. So a draw can only happen immediately after X’s move.

---

## 6. First propositions

At this point, I am not trying to prove anything deep yet. I just want the framework to be stable enough that stronger questions can later be asked on top of it.

### Proposition 1. Transition-class restriction

For any admissible move in a reachable state,

\[
s\in N_X \implies \delta(s,X,a)\in N_O\cup T_X\cup T_D,
\]

and

\[
s\in N_O \implies \delta(s,O,a)\in N_X\cup T_O.
\]

Also,

\[
s\in T_X\cup T_O\cup T_D
\implies
\forall p\in P,\forall a\in A,\; \delta(s,p,a)\text{ is undefined}.
\]

#### Proof sketch

If X moves in a nonterminal state, then one of three things happens: X wins, the board becomes full without a winner, or the game remains nonterminal and it becomes O’s turn. Likewise, if O moves in a nonterminal state, then either O wins or the game remains nonterminal and it becomes X’s turn. Since O never makes the ninth move, O cannot move directly into a draw. Terminal closure follows immediately from the definition of \(\mathcal L\). \(\square\)

---

### Proposition 2. Finite termination of maximal play

Every maximal legal history beginning at \(s_0\) reaches exactly one of the terminal classes \(T_X\), \(T_O\), or \(T_D\) in at most nine moves.

#### Proof sketch

The board starts with nine empty cells. Every legal move fills exactly one empty cell, and no move ever removes a mark. So a legal history cannot contain more than nine moves. If play is maximal, it cannot stop before a terminal state, because any nonterminal reachable board still has a legal move available to the player whose turn it is. Therefore maximal play always ends in a terminal state, and because the game ends immediately upon a legal win, exactly one of the three terminal outcomes occurs. \(\square\)

---

### Proposition 3. Reachability invariant schema

Let \(I:S\to \mathsf{Prop}\) be an invariant such that:

1. \(I(s_0)\) holds, and
2. whenever \((s,p,a)\in \mathcal L\), if \(I(s)\) holds then \(I(\delta(s,p,a))\) also holds.

Then

\[
\forall s\in R,\; I(s).
\]

#### Proof sketch

Induct on the length of a legal history from \(s_0\) to \(s\). The base case is the initial state. The induction step follows from closure of the invariant under legal transitions. \(\square\)

This proposition is simple, but it is important because it gives me a clear first target for Lean 4.

---

## 7. What this framework does and does not yet prove

So far, this framework does prove some basic structural facts about the **mathematical game**. In particular, it distinguishes:

- representable states from reachable states,
- legal transitions from undefined ones,
- terminal states from nonterminal ones.

What it does **not** yet prove is the stronger claim I ultimately care about:

> that a real implementation running in an adversarial environment can only commit state histories that belong to the formal game.

That stronger claim will require more than these definitions. It will need:

- a model of messages or actions submitted to an authority,
- some notion of authorization or authenticated provenance,
- some notion of finality or commitment,
- an explicit adversary model,
- and a proof that the implementation refines the mathematical game.

A target statement for the future might look like

\[
\operatorname{CommittedHistories}(\Pi,\mathcal A)\subseteq H_{\mathcal G},
\]

for some protocol \(\Pi\) and adversary class \(\mathcal A\).

But at this point that is still a **research target**, not a theorem.

---

## 8. Why this is different from standard game theory

Traditional game theory already talks about legal actions, histories, and outcomes. So I do **not** want to pretend that defining state-dependent legal moves is itself novel.

What I think is interesting here is the shift in emphasis.

Traditional game theory asks questions like:

- what are the players’ strategies?
- what outcomes are possible?
- what equilibria exist?

This project asks a different kind of question:

- what transitions are structurally valid?
- what states can be reached through legal derivation?
- what would it take for an implementation to guarantee that no other transitions ever become authoritative?

So the novelty, if there is one, would not come from defining partial transition functions alone. It would come from whether these semantics can be connected in a meaningful and provable way to adversarial execution integrity.

---

## 9. Lean 4 direction

Right now, my Lean plan is to keep it simple.

1. Define the core types: players, actions, states.
2. Define the legality predicate.
3. Define a computable step function like `step? : State → Player → Action → Option State`.
4. Define reachability inductively.
5. Prove terminal closure and invariant preservation.
6. Then formalize the Tic-Tac-Toe case.

I think this is the right order because it separates the abstract theory from the implementation details and gives me small proofs to aim for first.

---

## 10. Open questions and next steps

At this point, the most important open questions are not about polishing the prose. They are about deciding what the eventual theory is really trying to prove.

The next steps I see are:

1. **Formalize the current framework in Lean 4.**  
   The first real milestone is a machine-checked reachability or invariant theorem.

2. **Clarify what counts as an authoritative transition.**  
   Right now, the model only knows what a legal transition is inside the abstract game. It does not yet know what a protocol would have to certify.

3. **Separate syntax, semantics, and security.**  
   Representability, legality, and authoritativeness should probably be kept conceptually distinct.

4. **Compare this directly against existing frameworks.**  
   Especially extensive-form games, transition systems, dependent type formulations, and verified distributed systems.

5. **Decide what the smallest nontrivial new theorem might be.**  
   That is probably the real turning point between an interesting idea and an actual paper.

---

## Conclusion

This draft lays out the first piece of the project: a game model based on admissibility relations, partially defined transition functions, and reachable-state reasoning. Tic-Tac-Toe serves as a small but useful case study because it makes the difference between representable states, reachable states, and terminal outcomes concrete.

The main value of this draft is not that it solves the full integrity problem. It does not. Its value is that it gives a clean mathematical starting point for asking the larger question in a serious way: whether game integrity can be made intrinsic to the formal execution structure of the system, rather than delegated entirely to external detection and enforcement.
