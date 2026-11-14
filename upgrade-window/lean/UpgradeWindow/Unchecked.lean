/-
  UpgradeWindow.Unchecked — the plugin as it behaves in a build WITHOUT overflow checks
  (cargo's default release profile; `cargo near build` uses the release profile).

  The only difference from `Model.lean` is `up_stage_update_staging_duration`: the `+` of l. 250
  wraps modulo 2^64 instead of panicking (`Up.stageDurUnchecked`). If `block_timestamp + D`
  overflows, an update staged now carries a timestamp in the past and can be applied at once
  (`W3_unchecked_shortcut`): a staging duration that large is no delay.

  The corrected bound counts such durations as zero. For a threshold `B`, `safeUntilU B` is
  `safeUntil` with every duration above `B` replaced by 0; on every trace whose block timestamps
  stay at or below `u64::MAX - B`, no `up_deploy_code` call succeeds before it
  (`W3U_no_deploy_before`). With `B = 2^63` the condition on timestamps holds until the year
  2262, and durations above `B` exceed 292 years.
-/
import UpgradeWindow.Theorems

namespace UpgradeWindow

variable {Code : Type} (H : Code → String)

/-- One call of a protected method on a build without overflow checks. -/
def Up.callU (H : Code → String) (now : Nat) (allowed : Bool) (s : Up Code) (c : Call Code) :
    Except Err (Up Code × Option (Deploy Code)) :=
  match c with
  | .stageDur d =>
    if allowed = false then .error .noPermission
    else match s.stageDurUnchecked now d with
      | .error e => .error e
      | .ok s' => .ok (s', none)
  | .stageCode x => s.call H now allowed (.stageCode x)
  | .deployCode h fc => s.call H now allowed (.deployCode h fc)
  | .initDur d => s.call H now allowed (.initDur d)
  | .applyDur => s.call H now allowed .applyDur

/-- One event on a build without overflow checks. -/
def Sys.stepU (H : Code → String) (now : Nat) (s : Sys Code) : Ev Code → Sys Code
  | .call a c =>
    match s.up.callU H now a c with
    | .error _ => s
    | .ok (u, none) => { s with up := u }
    | .ok (u, some d) => { s with up := u, inflight := s.inflight ++ [d] }
  | .batch i ok =>
    match s.inflight[i]? with
    | none => s
    | some d => { s with inflight := s.inflight.eraseIdx i,
                         current := if ok then d.code else s.current }
  | .other => s

def runU (H : Code → String) : Sys Code → Trace Code → Sys Code
  | s, [] => s
  | s, (t, e) :: rest => runU H (s.stepU H t e) rest

/-- The delay a duration is worth on a build without overflow checks: nothing above `B`. -/
def effDur (B d : Nat) : Nat := if d ≤ B then d else 0

/-- `safeUntil` for a build without overflow checks: durations above `B` count as 0. -/
def safeUntilU (B : Nat) (u : Up Code) (now : Nat) : Nat :=
  let a := satAdd now (effDur B (u.dur.getD 0))
  let b := match u.stagingTs with
    | some ts => min a ts
    | none => a
  match u.newDur, u.newDurTs with
  | some nd, some ndt => min b (satAdd (max now ndt) (effDur B nd))
  | _, _ => b

/-- The warning signs on a build without overflow checks: the alarm of the checked build, or a
    current or staged duration above `B`. -/
def alarmU (B : Nat) (u : Up Code) : Bool :=
  alarm u ||
  (match u.dur with
   | some d => decide (B < d)
   | none => false) ||
  (match u.newDur, u.newDurTs with
   | some nd, some _ => decide (B < nd)
   | _, _ => false)

/-- Where no `block_timestamp + duration` overflows, the two builds make the same call. -/
theorem callU_eq_call (now : Nat) (a : Bool) (s : Up Code) (c : Call Code)
    (hfit : ∀ cur, s.dur = some cur → now + cur ≤ U64_MAX) :
    s.callU H now a c = s.call H now a c := by
  cases c with
  | stageDur d =>
    cases a with
    | false => simp [Up.callU, Up.call]
    | true =>
      simp only [Up.callU, Up.call, stageDurUnchecked_eq now s d hfit]
      cases s.stageDur now d <;> rfl
  | stageCode x => rfl
  | deployCode h fc => rfl
  | initDur d => rfl
  | applyDur => rfl

/-- Inversion of a successful call on the unchecked build. -/
theorem callU_inv {now : Nat} {a : Bool} {s s' : Up Code} {c : Call Code}
    {eff : Option (Deploy Code)} (hc : s.callU H now a c = .ok (s', eff)) :
    (∃ d cur, c = .stageDur d ∧ s.dur = some cur ∧
        s' = { s with newDur := some d, newDurTs := some ((now + cur) % (U64_MAX + 1)) } ∧
        eff = none)
    ∨ ((∀ d, c ≠ .stageDur d) ∧ s.call H now a c = .ok (s', eff)) := by
  cases c with
  | stageDur d =>
    refine Or.inl ?_
    simp only [Up.callU] at hc
    cases a with
    | false => simp at hc
    | true =>
      simp only [Bool.true_eq_false, ite_false] at hc
      unfold Up.stageDurUnchecked at hc
      cases hd : s.dur with
      | none => simp [hd] at hc
      | some cur =>
        simp only [hd, Except.ok.injEq, Prod.mk.injEq] at hc
        exact ⟨d, cur, rfl, rfl, hc.1.symm, hc.2.symm⟩
  | stageCode x => exact Or.inr ⟨fun d h => (by cases h), hc⟩
  | deployCode h fc => exact Or.inr ⟨fun d h => (by cases h), hc⟩
  | initDur d => exact Or.inr ⟨fun d h => (by cases h), hc⟩
  | applyDur => exact Or.inr ⟨fun d h => (by cases h), hc⟩

theorem safeUntilU_time (B : Nat) (u : Up Code) {now now' : Nat} (h : now ≤ now') :
    safeUntilU B u now ≤ safeUntilU B u now' := by
  obtain ⟨code, sts, dur, nd, ndt⟩ := u
  cases sts <;> cases dur <;> cases nd <;> cases ndt <;>
    simp only [safeUntilU, satAdd, Option.getD] <;> omega

theorem effDur_le (B d : Nat) : effDur B d ≤ d := by
  unfold effDur; split <;> omega

theorem effDur_le_bound (B d : Nat) : effDur B d ≤ B := by
  unfold effDur; split <;> omega

/-- No successful call lowers `safeUntilU`, as long as the block timestamp is at most
    `u64::MAX - B`. -/
theorem safeUntilU_call (B : Nat) {now : Nat} {a : Bool} {s s' : Up Code} {c : Call Code}
    {eff : Option (Deploy Code)} (hnow : now + B ≤ U64_MAX)
    (hc : s.callU H now a c = .ok (s', eff)) :
    safeUntilU B s now ≤ safeUntilU B s' now := by
  rcases callU_inv H hc with ⟨d, cur, _, hd, hs, _⟩ | ⟨hns, hc'⟩
  · -- the unchecked `up_stage_update_staging_duration`
    subst hs
    obtain ⟨code, sts, dur, nd, ndt⟩ := s
    simp only at hd
    subst hd
    by_cases hcb : cur ≤ B
    · have hw : (now + cur) % (U64_MAX + 1) = now + cur := Nat.mod_eq_of_lt (by omega)
      have he : effDur B cur = cur := by simp [effDur, hcb]
      cases sts <;> cases nd <;> cases ndt <;>
        simp only [safeUntilU, satAdd, Option.getD, hw, he] <;> omega
    · have he : effDur B cur = 0 := by simp [effDur, hcb]
      cases sts <;> cases nd <;> cases ndt <;>
        simp only [safeUntilU, satAdd, Option.getD, he] <;> omega
  · rcases call_inv H hc' with ⟨_, h1 | h1 | h1 | h1 | h1⟩
    · rcases h1 with ⟨x, _, hs, _⟩
      subst hs
      obtain ⟨code, sts, dur, nd, ndt⟩ := s
      have h0 : effDur B 0 = 0 := by simp [effDur]
      cases dur with
      | none =>
        cases x <;> cases sts <;> cases nd <;> cases ndt <;>
          simp only [safeUntilU, satAdd, Up.stageCode, Option.getD, h0] <;> omega
      | some cur =>
        have hle := effDur_le B cur
        cases x <;> cases sts <;> cases nd <;> cases ndt <;>
          simp only [safeUntilU, satAdd, Up.stageCode, Option.getD] <;> omega
    · rcases h1 with ⟨_, _, _, _, _, hs, _⟩
      subst hs; exact Nat.le_refl _
    · rcases h1 with ⟨d, _, hd, hs, _⟩
      subst hs
      obtain ⟨code, sts, dur, nd, ndt⟩ := s
      simp only at hd
      subst hd
      have h0 : effDur B 0 = 0 := by simp [effDur]
      cases sts <;> cases nd <;> cases ndt <;>
        simp only [safeUntilU, satAdd, Option.getD, h0] <;> omega
    · rcases h1 with ⟨d, _, hx, _⟩
      exact absurd hx (hns d)
    · rcases h1 with ⟨t, nd', _, ht, hle, hn, hs, _⟩
      subst hs
      obtain ⟨code, sts, dur, nd, ndt⟩ := s
      simp only at ht hn
      subst ht hn
      cases sts <;> cases dur <;>
        simp only [safeUntilU, satAdd, Option.getD] <;> omega

theorem deployU_after_safeUntilU (B : Nat) {now : Nat} {a : Bool} {s s' : Up Code} {h : String}
    {fc : Option FnCall} {eff : Option (Deploy Code)}
    (hc : s.callU H now a (.deployCode h fc) = .ok (s', eff)) : safeUntilU B s now ≤ now := by
  have hc' : s.call H now a (.deployCode h fc) = .ok (s', eff) := hc
  obtain ⟨_, ts, code, hts, hle, _, _, _⟩ := deploy_ok H hc'
  obtain ⟨code', sts, dur, nd, ndt⟩ := s
  simp only at hts
  subst hts
  cases dur <;> cases nd <;> cases ndt <;>
    simp only [safeUntilU, satAdd, Option.getD] <;> omega

theorem stepU_up (s : Sys Code) (t : Nat) (e : Ev Code) :
    (s.stepU H t e).up = s.up ∨
    ∃ a c eff, e = .call a c ∧ s.up.callU H t a c = .ok ((s.stepU H t e).up, eff) := by
  cases e with
  | call a c =>
    cases hr : s.up.callU H t a c with
    | error err => exact Or.inl (by simp [Sys.stepU, hr])
    | ok r =>
      obtain ⟨u, eff⟩ := r
      refine Or.inr ⟨a, c, eff, rfl, ?_⟩
      cases eff <;> simp [Sys.stepU, hr]
  | batch i ok =>
    refine Or.inl ?_
    simp only [Sys.stepU]
    cases s.inflight[i]? <;> rfl
  | other => exact Or.inl rfl

/-- Every event of the trace has a block timestamp at most `u64::MAX - B`. -/
def Before (B : Nat) (tr : Trace Code) : Prop := ∀ x ∈ tr, x.1 + B ≤ U64_MAX

theorem safeUntilU_run (B : Nat) : ∀ (tr : Trace Code) (s0 : Sys Code) (t0 : Nat), Mono t0 tr →
    Before B tr → safeUntilU B s0.up t0 ≤ safeUntilU B (runU H s0 tr).up (endTime t0 tr)
  | [], _, _, _, _ => Nat.le_refl _
  | (t, e) :: rest, s0, _, hm, hb => by
    have hstep : safeUntilU B s0.up t ≤ safeUntilU B (s0.stepU H t e).up t := by
      rcases stepU_up H s0 t e with h | ⟨a, c, eff, _, hc⟩
      · rw [h]; exact Nat.le_refl _
      · exact safeUntilU_call H B (hb (t, e) (List.mem_cons_self ..)) hc
    exact Nat.le_trans (safeUntilU_time B _ hm.1)
      (Nat.le_trans hstep
        (safeUntilU_run B rest (s0.stepU H t e) t hm.2
          (fun x hx => hb x (List.mem_cons_of_mem _ hx))))

/-- **W3 for a build without overflow checks.** From any state `s0` at block timestamp `t0`,
    along any trace with non-decreasing block timestamps that stay at or below `u64::MAX - B`,
    an `up_deploy_code` call succeeds only at a block timestamp `≥ safeUntilU B s0.up t0`:
    the bound of `W3_no_deploy_before` with every duration above `B` counted as 0. -/
theorem W3U_no_deploy_before (B : Nat) (s0 : Sys Code) (t0 : Nat) (pre post : Trace Code)
    {now : Nat} {a : Bool} {h : String} {fc : Option FnCall}
    (hm : Mono t0 (pre ++ (now, Ev.call a (.deployCode h fc)) :: post))
    (hb : Before B pre)
    {u' : Up Code} {eff : Option (Deploy Code)}
    (hdep : (runU H s0 pre).up.callU H now a (.deployCode h fc) = .ok (u', eff)) :
    safeUntilU B s0.up t0 ≤ now := by
  obtain ⟨hm1, hle, _⟩ := mono_append pre t0 _ post hm
  exact Nat.le_trans (safeUntilU_run H B pre s0 t0 hm1 hb)
    (Nat.le_trans (safeUntilU_time B _ hle) (deployU_after_safeUntilU H B hdep))

/-- With no warning sign and duration `D`, `safeUntilU` is `now + D`. -/
theorem quietU_safeUntilU (B : Nat) {u : Up Code} {D : Nat} (hq : alarmU B u = false)
    (hD : u.dur = some D) (now : Nat) : safeUntilU B u now = satAdd now D := by
  obtain ⟨code, sts, dur, nd, ndt⟩ := u
  simp only at hD
  subst hD
  cases sts <;> cases nd <;> cases ndt <;>
    simp [alarmU, alarm] at hq <;>
    simp only [safeUntilU, satAdd, Option.getD, effDur] <;>
    (repeat' split) <;> omega

/-- **W5 for a build without overflow checks (a quiet reading).** If at block timestamp `t0`
    the plugin's state shows staging duration `D` and none of the warning signs — nothing
    staged, no staged duration update below `D`, no current or staged duration above `B` — then
    no `up_deploy_code` call succeeds before `t0 + D` (saturating at `u64::MAX`), on any trace
    whose block timestamps stay at or below `u64::MAX - B`. -/
theorem W5U_quiet_reading (B : Nat) (s0 : Sys Code) (t0 D : Nat) (pre post : Trace Code)
    {now : Nat} {a : Bool} {h : String} {fc : Option FnCall}
    (hm : Mono t0 (pre ++ (now, Ev.call a (.deployCode h fc)) :: post))
    (hb : Before B pre)
    (hD : s0.up.dur = some D) (hq : alarmU B s0.up = false)
    {u' : Up Code} {eff : Option (Deploy Code)}
    (hdep : (runU H s0 pre).up.callU H now a (.deployCode h fc) = .ok (u', eff)) :
    satAdd t0 D ≤ now := by
  rw [← quietU_safeUntilU B hq hD t0]
  exact W3U_no_deploy_before H B s0 t0 pre post hm hb hdep

/-- Staging an update of the duration to `u64::MAX`, from a state with duration `D` and nothing
    else: the alarm of the checked build stays off (the duration grows), `alarmU` is on. -/
theorem alarmU_flags_huge_update (B D now : Nat) (hB : B < U64_MAX) :
    ∃ u1 : Up Code, ({ dur := some D } : Up Code).stageDurUnchecked now U64_MAX = .ok u1 ∧
      (D ≤ U64_MAX → alarm u1 = false) ∧ alarmU B u1 = true := by
  refine ⟨{ dur := some D, newDur := some U64_MAX,
            newDurTs := some ((now + D) % (U64_MAX + 1)) }, by simp [Up.stageDurUnchecked], ?_, ?_⟩
  · intro hD
    simp [alarm]
    omega
  · simp [alarmU, alarm, hB]

/-- **W3 (shortcut 3, the whole path).** On a build without overflow checks, from a state with
    an ordinary duration `D` and nothing staged: stage an update of the duration to `u64::MAX`
    at `t0` — a longer duration, so no alarm of the checked build —, apply it at `t0 + D`, and
    then, at that same block timestamp, stage an update to 0 (its timestamp wraps into the
    past), apply it, stage code `c` and have its deployment accepted: the deploy batch in flight
    carries `c`, created at `t0 + D`. -/
theorem W3U_grow_then_remove (D t0 : Nat) (hpos : 1 ≤ t0 + D) (hfit : t0 + D ≤ U64_MAX)
    (c c0 : Code) :
    let s0 : Sys Code := { up := { dur := some D }, current := c0 }
    let tr : Trace Code :=
      [(t0, Ev.call true (.stageDur U64_MAX)),
       (t0 + D, Ev.call true .applyDur),
       (t0 + D, Ev.call true (.stageDur 0)),
       (t0 + D, Ev.call true .applyDur),
       (t0 + D, Ev.call true (.stageCode (some c))),
       (t0 + D, Ev.call true (.deployCode (H c) none))]
    Mono t0 tr ∧
      alarm (runU H s0 [(t0, Ev.call true (.stageDur U64_MAX))]).up = false ∧
      (runU H s0 tr).inflight = [⟨c, none, t0 + D⟩] := by
  have h1 : (t0 + D) % (U64_MAX + 1) = t0 + D := Nat.mod_eq_of_lt (by omega)
  have h2 : (t0 + D + U64_MAX) % (U64_MAX + 1) = t0 + D - 1 := by
    simp only [U64_MAX] at *
    omega
  have h3 : ¬ (t0 + D < t0 + D - 1) := by omega
  have h4 : ¬ (t0 + D < satAdd (t0 + D) 0) := by unfold satAdd; omega
  have h5 : ¬ (U64_MAX < D) := by omega
  simp [Mono, runU, Sys.stepU, Up.callU, Up.call, Up.stageDurUnchecked, Up.applyDur,
    Up.stageCode, Up.deployCode, alarm, h1, h2, h3, h4, h5]

end UpgradeWindow
