/-
  GatedUpgrade.Examples — the hypotheses of the theorems are satisfiable, and the gate does what
  the statements say on concrete runs of the model.

  Runs of the model on concrete data (staging duration 1 h): certified code is deployed at
  exactly staging + 1 h and the main theorem applies to that run; staged code without a
  certificate is refused; a certificate revoked before the registry call does not count, one
  revoked after it does not stop the deployment; `deploy_certified` one nanosecond early does
  nothing; code re-staged between the registry call and the callback is not deployed; a direct
  `up_deploy_code` is refused for the stager and for a stranger — and accepted for the contract
  account itself, which is why the theorems assume that no such receipt exists. Nothing here is
  needed by the theorems.
-/
import GatedUpgrade.Theorems

namespace GatedUpgrade.Examples
open UpgradeWindow

/-- A stand-in hash: enough to run the model on concrete data. -/
def H (c : String) : String := c

/-- One hour, in nanoseconds. -/
def D : Nat := 3600000000000

/-- A block timestamp (2026-11-12). -/
def t : Nat := 1794441620000000000

def cfg : Cfg :=
  { self := "vault", registry := "registry", kind := "upgrade-window", attestors := ["attestor"] }

/-- A valid certificate for `"v2"` from the accepted attestor. -/
def certV2 : Cert :=
  { codeHash := "v2", kind := "upgrade-window", attestor := "attestor", revoked := false }

/-- Right after `new`: the vault runs `"v1"`, `"gov"` may stage code, the registry is empty. -/
def s0 : GSys String := GSys.init cfg D "v1" ["gov"] []

theorem s0_fresh : Fresh cfg D s0 := init_fresh cfg D "v1" ["gov"] []

def stage (c : String) : Nat × GEv String := (t, .plugin "gov" (.stageCode (some c)))

/-! ### Certified code is deployed -/

/-- The attestor's certificate appears, `"gov"` stages `"v2"`; exactly one hour later somebody
    calls `deploy_certified`, the registry answers, the callback runs. -/
def certifiedRun : GTrace String :=
  [(t, .regSet [certV2]), stage "v2", (t + D, .deployCertified), (t + D, .regAnswer 0 true),
   (t + D, .callback 0 true)]

/-- The callback created the deploy batch for `"v2"`. -/
theorem certified_batch :
    (grun cfg H s0 certifiedRun).sys.inflight = [⟨"v2", none, t + D⟩] := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.deployCode, Up.stagedCodeHash,
    Acl.allowed, Acl.hasRole, roleFor, accepts, Reg.answer, Cert.accepted, s0, GSys.init, cfg,
    certV2, stage, certifiedRun, satAdd, H, D, t, U64_MAX]

/-- The batch replaces `"v1"` by `"v2"`. -/
theorem certified_deployed :
    (grun cfg H s0 certifiedRun).sys.current = "v1" ∧
    (grun cfg H s0 (certifiedRun ++ [(t + D, .batch 0 true)])).sys.current = "v2" := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.deployCode, Up.stagedCodeHash,
    Acl.allowed, Acl.hasRole, roleFor, accepts, Reg.answer, Cert.accepted, s0, GSys.init, cfg,
    certV2, stage, certifiedRun, satAdd, H, D, t, U64_MAX]

theorem certified_code_changes :
    (grun cfg H s0 (certifiedRun ++ [(t + D, .batch 0 true)])).sys.current
      ≠ (grun cfg H s0 certifiedRun).sys.current := by
  rw [certified_deployed.1, certified_deployed.2]; decide

theorem certified_mono : GMono t (certifiedRun ++ [(t + D, .batch 0 true)]) := by
  simp [GMono, certifiedRun, stage]

theorem certified_external : External cfg (certifiedRun ++ [(t + D, .batch 0 true)]) := by
  intro x hx
  simp only [certifiedRun, stage, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ExternalEv, cfg]

/-- The main theorem on this run: all its hypotheses hold. -/
example :=
  gated_code_change cfg H s0 t D certifiedRun (t + D) (.batch 0 true) s0_fresh certified_mono
    certified_external certified_code_changes

/-- ... and so do those of the variant with `safeUntil`, which here is `t + D`. -/
example : safeUntil s0.sys.up t = t + D := by
  simp [safeUntil, satAdd, s0, GSys.init, D, t, U64_MAX]

example :=
  gated_no_deploy_before cfg H s0 t certifiedRun (t + D) (.batch 0 true) s0_fresh.acl
    s0_fresh.noBatch s0_fresh.noAnswer certified_mono certified_external certified_code_changes

/-- One nanosecond before staging + 1 h, `deploy_certified` creates no registry call; at
    staging + 1 h it creates the call for the staged hash. -/
theorem early_call_does_nothing :
    (grun cfg H s0 [(t, .regSet [certV2]), stage "v2", (t + D - 1, .deployCertified)]).queries = [] ∧
    (grun cfg H s0 [(t, .regSet [certV2]), stage "v2", (t + D, .deployCertified)]).queries = ["v2"] := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.stagedCodeHash,
    Acl.allowed, Acl.hasRole, roleFor, s0, GSys.init, cfg, certV2, stage, satAdd, H, D, t,
    U64_MAX]

/-! ### Uncertified code is refused -/

/-- `"gov"` stages `"v3"`, for which the registry holds nothing; one hour later
    `deploy_certified`, the registry's (empty) answer, the callback. -/
def uncertifiedRun : GTrace String :=
  [stage "v3", (t + D, .deployCertified), (t + D, .regAnswer 0 true), (t + D, .callback 0 true)]

/-- The registry was asked about `"v3"` and answered with no certificate. -/
theorem uncertified_asked :
    (grun cfg H s0 [stage "v3", (t + D, .deployCertified), (t + D, .regAnswer 0 true)]).answers
      = [("v3", some [])] := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.stagedCodeHash,
    Acl.allowed, Acl.hasRole, roleFor, Reg.answer, s0, GSys.init, cfg, stage, satAdd, H, D, t,
    U64_MAX]

/-- The callback created no deploy batch and the code is still `"v1"`; nothing is left pending. -/
theorem uncertified_refused :
    (grun cfg H s0 uncertifiedRun).sys.inflight = [] ∧
    (grun cfg H s0 uncertifiedRun).sys.current = "v1" ∧
    (grun cfg H s0 uncertifiedRun).answers = [] ∧
    (grun cfg H s0 uncertifiedRun).queries = [] := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.stagedCodeHash, Acl.allowed, Acl.hasRole, roleFor, accepts, Reg.answer, Cert.accepted, s0,
    GSys.init, cfg, stage, uncertifiedRun, satAdd, H, D, t, U64_MAX]

theorem uncertified_external : External cfg uncertifiedRun := by
  intro x hx
  simp only [uncertifiedRun, stage, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [ExternalEv, cfg]

theorem uncertified_no_certificate :
    ∀ p q, uncertifiedRun = p ++ q → ¬ Certified cfg (grun cfg H s0 p).reg "v3" := by
  intro p q hpq hc
  have hreg : (grun cfg H s0 p).reg = [] := by
    rw [reg_run cfg H p s0]
    · rfl
    · intro x hx r hr
      have hx' : x ∈ uncertifiedRun := by rw [hpq]; exact List.mem_append_left _ hx
      simp only [uncertifiedRun, stage, List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl | rfl | rfl <;> cases hr
  rw [hreg] at hc
  obtain ⟨c, hc, _⟩ := hc
  cases hc

/-- G3 on this run: its hypotheses hold, so at no moment of the run the account runs `"v3"`. -/
example : ∀ p q, uncertifiedRun = p ++ q → H (grun cfg H s0 p).sys.current ≠ "v3" :=
  uncertified_never_current cfg H s0 uncertifiedRun "v3" s0_fresh.acl s0_fresh.noBatch
    s0_fresh.noAnswer uncertified_external uncertified_no_certificate (by decide)

/-- A certificate from an attestor the vault does not accept, or of another kind, does not
    count either. -/
theorem foreign_certificates_refused :
    (grun cfg H s0 ((t, .regSet [{ certV2 with attestor := "somebody" },
        { certV2 with kind := "exit" }, { certV2 with codeHash := "v3" }]) :: stage "v2" ::
      [(t + D, .deployCertified), (t + D, .regAnswer 0 true), (t + D, .callback 0 true)])).sys.inflight
      = [] := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.stagedCodeHash, Acl.allowed, Acl.hasRole, roleFor, accepts, Reg.answer, Cert.accepted, s0,
    GSys.init, cfg, certV2, stage, satAdd, H, D, t, U64_MAX]

/-! ### Revocation -/

def revokedV2 : Cert := { certV2 with revoked := true }

/-- The certificate is revoked before the registry executes the call: refused. -/
theorem revoked_before_call_refused :
    (grun cfg H s0 [(t, .regSet [certV2]), stage "v2", (t + D, .deployCertified),
      (t + D, .regSet [revokedV2]), (t + D, .regAnswer 0 true), (t + D, .callback 0 true)]).sys.inflight
      = [] := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.stagedCodeHash, Acl.allowed, Acl.hasRole, roleFor, accepts, Reg.answer, Cert.accepted, s0,
    GSys.init, cfg, certV2, revokedV2, stage, satAdd, H, D, t, U64_MAX]

/-- The limit of the guarantee: a certificate revoked after the registry executed the call, and
    before the callback, does not stop the deployment. The statement is about the registry at
    the moment of the call. -/
theorem revoked_after_call_still_deployed :
    (grun cfg H s0 [(t, .regSet [certV2]), stage "v2", (t + D, .deployCertified),
      (t + D, .regAnswer 0 true), (t + D, .regSet [revokedV2]), (t + D, .callback 0 true),
      (t + D, .batch 0 true)]).sys.current = "v2" := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.deployCode, Up.stagedCodeHash,
    Acl.allowed, Acl.hasRole, roleFor, accepts, Reg.answer, Cert.accepted, s0, GSys.init, cfg,
    certV2, revokedV2, stage, satAdd, H, D, t, U64_MAX]

/-! ### Between the check and the deployment -/

/-- Other code is staged between the registry call and the callback: the callback's deploy
    call is for the hash that was asked about, the plugin refuses it (wrong hash). -/
theorem restaged_other_code_not_deployed :
    (grun cfg H s0 [(t, .regSet [certV2]), stage "v2", (t + D, .deployCertified),
      (t + D, .regAnswer 0 true), (t + D, .plugin "gov" (.stageCode (some "v3"))),
      (t + D, .callback 0 true)]).sys.inflight = [] := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.deployCode,
    Up.stagedCodeHash, Acl.allowed, Acl.hasRole, roleFor, accepts, Reg.answer, Cert.accepted, s0,
    GSys.init, cfg, certV2, stage, satAdd, H, D, t, U64_MAX]

/-- The same code is staged again in between: its delay starts again, the plugin refuses the
    deploy call (too early). -/
theorem restaged_same_code_not_deployed :
    (grun cfg H s0 [(t, .regSet [certV2]), stage "v2", (t + D, .deployCertified),
      (t + D, .regAnswer 0 true), (t + D, .plugin "gov" (.stageCode (some "v2"))),
      (t + D, .callback 0 true)]).sys.inflight = [] := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.deployCode,
    Up.stagedCodeHash, Acl.allowed, Acl.hasRole, roleFor, accepts, Reg.answer, Cert.accepted, s0,
    GSys.init, cfg, certV2, stage, satAdd, H, D, t, U64_MAX]

/-- Other code staged after the callback, before the batch: the batch still installs the code
    the callback read, `"v2"`. -/
theorem restaged_after_callback_installs_checked_code :
    (grun cfg H s0 (certifiedRun ++ [(t + D, .plugin "gov" (.stageCode (some "v3"))),
      (t + D, .batch 0 true)])).sys.current = "v2" := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.deployCode, Up.stagedCodeHash,
    Acl.allowed, Acl.hasRole, roleFor, accepts, Reg.answer, Cert.accepted, s0, GSys.init, cfg,
    certV2, stage, certifiedRun, satAdd, H, D, t, U64_MAX]

/-! ### No way around the gate -/

/-- A direct `up_deploy_code` after the delay, with a valid certificate in the registry, by the
    stager and by a stranger; and a stranger trying to grant itself the role first: no deploy
    batch. -/
theorem direct_deploy_refused :
    (grun cfg H s0 [(t, .regSet [certV2]), stage "v2",
      (t + D, .plugin "gov" (.deployCode "v2" none)),
      (t + D, .acl "mallory" (.grantRole .codeDeployer "mallory")),
      (t + D, .acl "mallory" (.addSuperAdmin "mallory")),
      (t + D, .plugin "mallory" (.deployCode "v2" none))]).sys.inflight = [] := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Acl.allowed, Acl.hasRole, Acl.apply, Acl.isAdmin, Acl.isSuperAdmin, roleFor, s0, GSys.init,
    cfg, certV2, stage, satAdd, D, t, U64_MAX]

/-- Why the hypothesis `External` is there: a receipt calling `up_deploy_code` with the contract
    account itself as predecessor — a transaction signed with an access key of that account —
    passes the access-control check and deploys staged code that has no certificate. The
    contract account must have no access keys. -/
theorem contract_key_bypasses_gate :
    (grun cfg H s0 [stage "v3", (t + D, .plugin "vault" (.deployCode "v3" none)),
      (t + D, .batch 0 true)]).sys.current = "v3" := by
  simp [grun, GSys.step, Sys.step, Up.call, Up.stageCode, Up.deployCode,
    Acl.allowed, Acl.hasRole, roleFor, s0, GSys.init, cfg, stage, satAdd, H, D, t, U64_MAX]

end GatedUpgrade.Examples
