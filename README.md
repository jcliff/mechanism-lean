# mechanism-lean

Machine-checked proofs of two classic mechanism-design results, in core Lean 4 (no Mathlib).

| Theorem | Statement |
| --- | --- |
| `MechDesign.revelation_principle` | If strategies `s` form a dominant-strategy equilibrium of a mechanism `g`, the direct mechanism `θ ↦ g (s θ)` is dominant-strategy incentive compatible and produces the same outcomes. Holds for arbitrary agents, type spaces, message spaces, outcomes, and any `LE` utility scale. |
| `MechDesign.vickrey_truthful` | In a sealed-bid second-price auction, bidding your true value is weakly dominant, for **every** tie-breaking rule that picks a highest bidder. |

## Sanity checks

Lean proves exactly what a statement says, so two extra theorems guard against bad definitions:

- `highest_valid` / `vickrey_truthful_concrete`: an actual winner rule (highest bid, ties go to the lowest index) satisfies the Vickrey hypothesis, so the theorem is not vacuous.
- `first_price_not_truthful`: the same truthfulness claim is **false** for a first-price auction. With a value of 10 against a rival bid of 4, bidding 5 earns 5 and bidding 10 earns 0. The definitions can tell a truthful auction from one that isn't.

## Verify

```sh
bash scripts/audit.sh
```

The script:
1. builds the library with `lake build`;
2. checks that every headline theorem uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and that there is no `sorry`;
3. replays the whole environment through the kernel with `leanchecker --fresh`.

CI runs the same script on every push and pull request.

## Modeling scope

Bids and values are natural numbers. There is a single item, no reserve price, and utilities are quasilinear. Mechanisms are deterministic. The revelation principle is the dominant-strategy version, not the Bayesian–Nash one. Its "same outcomes" half holds by definition; the incentive-compatibility half is the real content.

## Possible next steps

- Myerson's lemma (monotone allocation rule ⇔ implementable, plus the payment identity)
- Gibbard–Satterthwaite
- A Bayesian revelation principle
