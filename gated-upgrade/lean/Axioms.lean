import GatedUpgrade
open UpgradeWindow GatedUpgrade
-- the gate
#print axioms gated_code_change
#print axioms gated_no_deploy_before
#print axioms uncertified_never_installed
#print axioms uncertified_never_current
#print axioms code_change_origin
-- access control and the delay
#print axioms aclInv_apply
#print axioms aclInv_run
#print axioms external_not_allowed
#print axioms dur_run
-- the projection onto the plugin model, and where deployments and answers come from
#print axioms grun_sys
#print axioms projTrace_split
#print axioms inflight_origin_g
#print axioms answers_origin
#print axioms certified_of_accepts
#print axioms init_fresh
-- the plugin theorems used
#print axioms deploy_origin
#print axioms W3_no_deploy_before
#print axioms W3a_duration_change
-- the examples
#print axioms Examples.s0_fresh
#print axioms Examples.certified_batch
#print axioms Examples.certified_deployed
#print axioms Examples.certified_code_changes
#print axioms Examples.certified_mono
#print axioms Examples.certified_external
#print axioms Examples.early_call_does_nothing
#print axioms Examples.uncertified_asked
#print axioms Examples.uncertified_refused
#print axioms Examples.uncertified_external
#print axioms Examples.uncertified_no_certificate
#print axioms Examples.foreign_certificates_refused
#print axioms Examples.revoked_before_call_refused
#print axioms Examples.revoked_after_call_still_deployed
#print axioms Examples.restaged_other_code_not_deployed
#print axioms Examples.restaged_same_code_not_deployed
#print axioms Examples.restaged_after_callback_installs_checked_code
#print axioms Examples.direct_deploy_refused
#print axioms Examples.contract_key_bypasses_gate
