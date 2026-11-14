import StakingPool
open StakingPool
-- headline
#print axioms exit_guarantee
-- the two calls of the exit, and liquidity
#print axioms unstake_all_ok
#print axioms withdraw_all_ok
#print axioms liquid_covers
#print axioms solvency
-- global invariant of reachable worlds
#print axioms Reach.inv
-- safety: other accounts, the owner
#print axioms others_call
#print axioms others_preserve
#print axioms owner_methods
#print axioms updateFee_shape
-- share price never decreases; rounding paid by the fund
#print axioms exec_price
#print axioms step_price
#print axioms exec_rounding
-- money in: a deposit raises the depositor's claim by at least the deposit
#print axioms deposit_claim
