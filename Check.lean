import Mechanism

/-! Audit script: run with `lake env lean Check.lean`.
`scripts/audit.sh` fails unless every headline theorem depends only on
Lean's standard axioms (propext, Classical.choice, Quot.sound). -/

#print axioms MechDesign.revelation_principle
#print axioms MechDesign.vickrey_truthful
#print axioms MechDesign.vickrey_truthful_concrete
#print axioms MechDesign.highest_valid
#print axioms MechDesign.first_price_not_truthful

-- Demo: three bidders bid 7, 12, 9. Bidder 1 wins and pays 9.
def demoBids : Fin 3 → Nat := fun j => #[7, 12, 9][j.val]!
#eval MechDesign.highest demoBids
#eval MechDesign.price (MechDesign.highest demoBids) demoBids
