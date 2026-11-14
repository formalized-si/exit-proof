/-
  UpgradeWindow.Examples — the hypotheses of the theorems are satisfiable.

  One concrete run of the model (duration 1 h, code staged, deployed exactly one hour later) on
  which the hypotheses of W1, W2, W3 and W5 all hold, and the theorems applied to it. Nothing
  here is needed by the theorems; it guards against statements that are true only vacuously.
-/
import UpgradeWindow.Theorems
import UpgradeWindow.Unchecked

namespace UpgradeWindow.Examples

/-- A stand-in hash: enough to run the model on concrete data. -/
def H (c : String) : String := c

/-- One hour, in nanoseconds. -/
def D : Nat := 3600000000000

/-- A block timestamp (2026-11-12). -/
def t : Nat := 1794441620000000000

/-- Duration set, nothing staged, nothing in flight. -/
def s0 : Sys String := { up := { dur := some D }, current := "v1" }

def stage : Nat × Ev String := (t, Ev.call true (.stageCode (some "v2")))

/-- The deploy call at `t + D` succeeds. -/
theorem deploy_succeeds :
    (run H s0 [stage]).up.call H (t + D) true (.deployCode "v2" none)
      = .ok ((run H s0 [stage]).up, some ⟨"v2", none, t + D⟩) := by
  simp [run, Sys.step, Up.call, Up.stageCode, Up.deployCode, s0, stage, satAdd, H, D, t, U64_MAX]

/-- One nanosecond earlier it is refused. -/
theorem deploy_refused_early :
    (run H s0 [stage]).up.call H (t + D - 1) true (.deployCode "v2" none)
      = .error (.tooEarly (t + D)) := by
  simp [run, Sys.step, Up.call, Up.stageCode, Up.deployCode, s0, stage, satAdd, D, t, U64_MAX]

theorem starts_quiet : s0.up.dur = some D ∧ alarm s0.up = false ∧ s0.up.stagingTs = none := by
  simp [s0, alarm]

theorem timestamps_ok :
    Mono t ([stage] ++ (t + D, Ev.call true (.deployCode "v2" none)) :: []) := by
  simp [Mono, stage]

/-- W1 on this run: the deployed code is the staged `"v2"`, no earlier than `t + D`. -/
example : ∃ pre post ts c,
    [stage] = pre ++ (ts, Ev.call true (.stageCode (some c))) :: post ∧
    (∀ x ∈ post, ¬ IsStage x) ∧ (⟨"v2", none, t + D⟩ : Deploy String).code = c ∧
    (∀ D', (run H s0 pre).up.dur = some D' → min (ts + D') U64_MAX ≤ t + D) :=
  W1_delay H s0 [stage] starts_quiet.2.2 deploy_succeeds

/-- W3 on this run: `safeUntil` at the start is `t + D`, and the deploy is not before it. -/
example : safeUntil s0.up t = t + D ∧ safeUntil s0.up t ≤ t + D :=
  ⟨by simp [safeUntil, satAdd, s0, D, t, U64_MAX],
   W3_no_deploy_before H s0 t [stage] [] timestamps_ok deploy_succeeds⟩

/-- W5 on this run, with an exit that takes at most half an hour: the alarm is raised by the
    staging event and the exit is over before the deploy call. -/
example : ∃ p1 ta e p2, [stage] = p1 ++ (ta, e) :: p2 ∧
    (∀ q r, p1 = q ++ r → alarm (run H s0 q).up = false) ∧
    alarm (run H s0 (p1 ++ [(ta, e)])).up = true ∧
    ∀ exitDone, exitDone ≤ ta + D / 2 → ta + D ≤ U64_MAX → exitDone ≤ t + D :=
  W5_exit_window H s0 t D (D / 2) [stage] [] timestamps_ok starts_quiet.1 starts_quiet.2.1
    (Nat.div_le_self _ _) deploy_succeeds

def deploy : Nat × Ev String := (t + D, Ev.call true (.deployCode "v2" none))

/-- The deploy batch, executed at `t + D`, replaces the code `"v1"` by `"v2"`. -/
theorem code_changes :
    (run H s0 ([stage, deploy] ++ [(t + D, Ev.batch 0 true)])).current
      ≠ (run H s0 [stage, deploy]).current := by
  simp [run, Sys.step, Up.call, Up.stageCode, Up.deployCode, s0, stage, deploy, satAdd, H, D, t, U64_MAX]

/-- W5 for the code itself, on this run: the alarm was raised `D` before the code changed. -/
example : ∃ p1 ta ea p2, [stage, deploy] = p1 ++ (ta, ea) :: p2 ∧
    (∀ q r, p1 = q ++ r → alarm (run H s0 q).up = false) ∧
    alarm (run H s0 (p1 ++ [(ta, ea)])).up = true ∧
    satAdd ta D ≤ t + D :=
  W5_code_change H s0 t D [stage, deploy] (t + D) (Ev.batch 0 true)
    (by simp [Mono, stage, deploy]) rfl starts_quiet.1 starts_quiet.2.1 code_changes

/-- W5_polling on this run: a second reading within a quarter of an hour, an exit of at most
    half an hour. -/
example : ∀ start done, start ≤ t + D / 4 → done ≤ start + D / 2 → done ≤ t + D :=
  fun start done h1 h2 =>
    W5_polling H s0 t D (D / 4) (D / 2) [stage, deploy] (t + D) (Ev.batch 0 true)
      (by simp [Mono, stage, deploy]) rfl starts_quiet.1 starts_quiet.2.1 (by decide)
      code_changes start done h1 h2 (by decide)

/-- The threshold used by the checker for builds without overflow checks: 2^63. -/
def B : Nat := 9223372036854775808

/-- The same deploy call on the model of a build without overflow checks. -/
theorem deployU_succeeds :
    (runU H s0 [stage]).up.callU H (t + D) true (.deployCode "v2" none)
      = .ok ((runU H s0 [stage]).up, some ⟨"v2", none, t + D⟩) := by
  simp [runU, Sys.stepU, Up.callU, Up.call, Up.stageCode, Up.deployCode, s0, stage, satAdd, H, D, t, U64_MAX]

/-- W5U_quiet_reading on this run: the hypotheses hold (the duration is below `B`, the block
    timestamp is below `u64::MAX - B`, no warning sign), and the deploy is not before `t + D`. -/
example : satAdd t D ≤ t + D :=
  W5U_quiet_reading H B s0 t D [stage] [] timestamps_ok
    (by intro x hx; simp [stage] at hx; subst hx; decide)
    starts_quiet.1 (by simp [alarmU, alarm, s0, B, D]) deployU_succeeds

/-- W3_tight on this run: a deploy can succeed at exactly `safeUntil`. -/
example : CanDeployAt H s0 t (max t (safeUntil s0.up t)) :=
  W3_tight H s0 t "v2" (by simp [t, U64_MAX]) (wf_empty _)

end UpgradeWindow.Examples
