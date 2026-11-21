# Game Integrity

**Early-stage undergraduate research in formal game semantics and adversarially resilient execution.**

This repository investigates the separation between a game's **legal state transitions** and the ability of a real implementation to **commit only legal histories** despite adversarial behavior.

## Research status

Exploratory (v0.1). The current work defines finite deterministic games using a state-dependent admissibility relation and a partial transition function, and develops Tic-Tac-Toe as a first case study. **No end-to-end security theorem is yet claimed.**

## Start here

- [Initial paper draft](paper/draft-v0.1.md)
- [Lean formalization notes](formalization/README.md)
- [Worked examples](examples/README.md)
- [Reading and references](references/README.md)

## Central research question

Can an authoritative game implementation be shown to accept only histories belonging to the legal histories of its abstract state-transition specification, even under a stated adversarial model?

## Contributing

The definitions and proofs are in progress and may change. Corrections, counterexamples, and related literature are welcome. Please avoid presenting candidate principles as established security theorems.

## License and manuscript

Source code and associated software documentation are covered by the [MIT License](LICENSE). The research manuscript in `paper/` is **excluded from this software license** and has a separate [rights notice](paper/LICENSE.md), pending an explicit publication license.
