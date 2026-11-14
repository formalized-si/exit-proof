/-
  UpgradeWindow.Theorems — the exit-window theorems W1–W5 about the model in `Model.lean`.

  Every theorem holds for every value of the `allowed` flags in a trace, i.e. whoever holds the
  roles and however the roles change: an adversary holding every role is included.
-/
import UpgradeWindow.Model

namespace UpgradeWindow

variable {Code : Type} (H : Code → String)

/-! ## Arithmetic -/

theorem satAdd_mono {a a' b b' : Nat} (ha : a ≤ a') (hb : b ≤ b') : satAdd a b ≤ satAdd a' b' := by
  unfold satAdd; omega

theorem satAdd_le (a b : Nat) : satAdd a b ≤ U64_MAX := by
  unfold satAdd; omega

theorem satAdd_exact {a b : Nat} (h : a + b ≤ U64_MAX) : satAdd a b = a + b := by
  unfold satAdd; omega

/-! ## One call -/

/-- Inversion of a successful call: which method ran, what it required and what it wrote. -/
theorem call_inv {now : Nat} {a : Bool} {s s' : Up Code} {c : Call Code} {eff : Option (Deploy Code)}
    (hc : s.call H now a c = .ok (s', eff)) :
    a = true ∧
    ( (∃ x, c = .stageCode x ∧ s' = s.stageCode now x ∧ eff = none)
    ∨ (∃ h fc ts code, c = .deployCode h fc ∧ s' = s ∧ s.stagingTs = some ts ∧ ts ≤ now ∧
        s.code = some code ∧ h = H code ∧ eff = some ⟨code, fc, now⟩)
    ∨ (∃ d, c = .initDur d ∧ s.dur = none ∧ s' = { s with dur := some d } ∧ eff = none)
    ∨ (∃ d cur, c = .stageDur d ∧ s.dur = some cur ∧ now + cur ≤ U64_MAX ∧
        s' = { s with newDur := some d, newDurTs := some (now + cur) } ∧ eff = none)
    ∨ (∃ t nd, c = .applyDur ∧ s.newDurTs = some t ∧ t ≤ now ∧ s.newDur = some nd ∧
        s' = { s with dur := some nd } ∧ eff = none) ) := by
  unfold Up.call at hc
  cases a with
  | false => simp at hc
  | true =>
    refine ⟨rfl, ?_⟩
    simp only [Bool.true_eq_false, ite_false] at hc
    cases c with
    | stageCode x =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hc
      exact Or.inl ⟨x, rfl, hc.1.symm, hc.2.symm⟩
    | deployCode h fc =>
      refine Or.inr (Or.inl ?_)
      simp only at hc
      unfold Up.deployCode at hc
      cases hts : s.stagingTs with
      | none => simp [hts] at hc
      | some ts =>
        simp only [hts] at hc
        by_cases hlt : now < ts
        · simp [hlt] at hc
        · simp only [hlt, ite_false] at hc
          cases hcode : s.code with
          | none => simp [hcode] at hc
          | some code =>
            simp only [hcode] at hc
            by_cases hh : h = H code
            · simp only [hh, ite_true, Except.ok.injEq, Prod.mk.injEq] at hc
              exact ⟨h, fc, ts, code, rfl, hc.1.symm, rfl, by omega, rfl, hh, hc.2.symm⟩
            · simp [hh] at hc
    | initDur d =>
      refine Or.inr (Or.inr (Or.inl ?_))
      simp only at hc
      unfold Up.initDur at hc
      cases hd : s.dur with
      | some x => simp [hd] at hc
      | none =>
        simp only [hd, Except.ok.injEq, Prod.mk.injEq] at hc
        exact ⟨d, rfl, rfl, hc.1.symm, hc.2.symm⟩
    | stageDur d =>
      refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      simp only at hc
      unfold Up.stageDur at hc
      cases hd : s.dur with
      | none => simp [hd] at hc
      | some cur =>
        simp only [hd] at hc
        by_cases ho : U64_MAX < now + cur
        · simp [ho] at hc
        · simp only [ho, ite_false, Except.ok.injEq, Prod.mk.injEq] at hc
          exact ⟨d, cur, rfl, rfl, by omega, hc.1.symm, hc.2.symm⟩
    | applyDur =>
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      simp only at hc
      unfold Up.applyDur at hc
      cases ht : s.newDurTs with
      | none => simp [ht] at hc
      | some t =>
        simp only [ht] at hc
        by_cases hlt : now < t
        · simp [hlt] at hc
        · simp only [hlt, ite_false] at hc
          cases hn : s.newDur with
          | none => simp [hn] at hc
          | some nd =>
            simp only [hn, Except.ok.injEq, Prod.mk.injEq] at hc
            exact ⟨t, nd, rfl, rfl, by omega, rfl, hc.1.symm, hc.2.symm⟩

/-- A call without permission fails, whatever the method and the state. -/
theorem call_not_allowed (now : Nat) (s : Up Code) (c : Call Code) :
    s.call H now false c = .error .noPermission := by
  simp [Up.call]

/-- A successful `up_deploy_code`: the storage is untouched, the staging timestamp has passed,
    and the promise carries the staged code, whose hash is the `hash` argument. -/
theorem deploy_ok {now : Nat} {a : Bool} {s s' : Up Code} {h : String} {fc : Option FnCall}
    {eff : Option (Deploy Code)} (hc : s.call H now a (.deployCode h fc) = .ok (s', eff)) :
    s' = s ∧ ∃ ts code, s.stagingTs = some ts ∧ ts ≤ now ∧ s.code = some code ∧ h = H code ∧
      eff = some ⟨code, fc, now⟩ := by
  rcases call_inv H hc with ⟨_, h1 | h1 | h1 | h1 | h1⟩
  · rcases h1 with ⟨x, hx, _⟩; cases hx
  · rcases h1 with ⟨h', fc', ts, code, hx, hs, hts, hle, hcode, hh, he⟩
    cases hx
    exact ⟨hs, ts, code, hts, hle, hcode, hh, he⟩
  · rcases h1 with ⟨d, hx, _⟩; cases hx
  · rcases h1 with ⟨d, cur, hx, _⟩; cases hx
  · rcases h1 with ⟨t, nd, hx, _⟩; cases hx

/-! ## W3 (local): how the duration can change -/

/-- **W3a.** A call changes the staging duration only in two ways: `up_init_staging_duration`
    when no duration is set, or `up_apply_update_staging_duration`, which installs the staged
    value and requires the block timestamp to have reached the staged update's timestamp. -/
theorem W3a_duration_change {now : Nat} {a : Bool} {s s' : Up Code} {c : Call Code}
    {eff : Option (Deploy Code)} (hc : s.call H now a c = .ok (s', eff)) (hne : s'.dur ≠ s.dur) :
    (∃ d, c = .initDur d ∧ s.dur = none ∧ s'.dur = some d) ∨
    (∃ t nd, c = .applyDur ∧ s.newDurTs = some t ∧ t ≤ now ∧ s.newDur = some nd ∧ s'.dur = some nd) := by
  rcases call_inv H hc with ⟨_, h1 | h1 | h1 | h1 | h1⟩
  · rcases h1 with ⟨x, _, hs, _⟩
    subst hs; cases x <;> simp [Up.stageCode] at hne
  · rcases h1 with ⟨_, _, _, _, _, hs, _⟩
    subst hs; exact absurd rfl hne
  · rcases h1 with ⟨d, hx, hd, hs, _⟩
    subst hs; exact Or.inl ⟨d, hx, hd, rfl⟩
  · rcases h1 with ⟨d, cur, _, _, _, hs, _⟩
    subst hs; exact absurd rfl hne
  · rcases h1 with ⟨t, nd, hx, ht, hle, hn, hs, _⟩
    subst hs; exact Or.inr ⟨t, nd, hx, ht, hle, hn, rfl⟩

/-- **W3b.** A staged duration update is written only by `up_stage_update_staging_duration`,
    and its timestamp is the block timestamp of that call plus the duration in force then. -/
theorem W3b_update_staged {now : Nat} {a : Bool} {s s' : Up Code} {c : Call Code}
    {eff : Option (Deploy Code)} (hc : s.call H now a c = .ok (s', eff))
    (hne : s'.newDur ≠ s.newDur ∨ s'.newDurTs ≠ s.newDurTs) :
    ∃ d cur, c = .stageDur d ∧ s.dur = some cur ∧ s'.dur = some cur ∧ s'.newDur = some d ∧
      s'.newDurTs = some (now + cur) ∧ now + cur ≤ U64_MAX := by
  rcases call_inv H hc with ⟨_, h1 | h1 | h1 | h1 | h1⟩
  · rcases h1 with ⟨x, _, hs, _⟩
    subst hs; cases x <;> simp [Up.stageCode] at hne
  · rcases h1 with ⟨_, _, _, _, _, hs, _⟩
    subst hs; simp at hne
  · rcases h1 with ⟨d, _, _, hs, _⟩
    subst hs; simp at hne
  · rcases h1 with ⟨d, cur, hx, hd, hfit, hs, _⟩
    subst hs; exact ⟨d, cur, hx, hd, hd, rfl, rfl, hfit⟩
  · rcases h1 with ⟨t, nd, _, _, _, _, hs, _⟩
    subst hs; simp at hne

/-! ## W3: `safeUntil` never decreases, and no deploy succeeds before it -/

/-- Waiting does not lower `safeUntil`. -/
theorem safeUntil_time (u : Up Code) {now now' : Nat} (h : now ≤ now') :
    safeUntil u now ≤ safeUntil u now' := by
  obtain ⟨code, sts, dur, nd, ndt⟩ := u
  cases sts <;> cases dur <;> cases nd <;> cases ndt <;>
    simp only [safeUntil, satAdd, Option.getD] <;> omega

/-- No successful call lowers `safeUntil`. -/
theorem safeUntil_call {now : Nat} {a : Bool} {s s' : Up Code} {c : Call Code}
    {eff : Option (Deploy Code)} (hc : s.call H now a c = .ok (s', eff)) :
    safeUntil s now ≤ safeUntil s' now := by
  rcases call_inv H hc with ⟨_, h1 | h1 | h1 | h1 | h1⟩
  · rcases h1 with ⟨x, _, hs, _⟩
    subst hs
    obtain ⟨code, sts, dur, nd, ndt⟩ := s
    cases x <;> cases sts <;> cases dur <;> cases nd <;> cases ndt <;>
      simp only [safeUntil, satAdd, Option.getD, Up.stageCode] <;> omega
  · rcases h1 with ⟨_, _, _, _, _, hs, _⟩
    subst hs; exact Nat.le_refl _
  · rcases h1 with ⟨d, _, hd, hs, _⟩
    subst hs
    obtain ⟨code, sts, dur, nd, ndt⟩ := s
    simp only at hd
    subst hd
    cases sts <;> cases nd <;> cases ndt <;>
      simp only [safeUntil, satAdd, Option.getD] <;> omega
  · rcases h1 with ⟨d, cur, _, hd, hfit, hs, _⟩
    subst hs
    obtain ⟨code, sts, dur, nd, ndt⟩ := s
    simp only at hd
    subst hd
    cases sts <;> cases nd <;> cases ndt <;>
      simp only [safeUntil, satAdd, Option.getD] <;> omega
  · rcases h1 with ⟨t, nd', _, ht, hle, hn, hs, _⟩
    subst hs
    obtain ⟨code, sts, dur, nd, ndt⟩ := s
    simp only at ht hn
    subst ht hn
    cases sts <;> cases dur <;>
      simp only [safeUntil, satAdd, Option.getD] <;> omega

/-- A deploy call succeeds only at or after `safeUntil`. -/
theorem deploy_after_safeUntil {now : Nat} {a : Bool} {s s' : Up Code} {h : String}
    {fc : Option FnCall} {eff : Option (Deploy Code)}
    (hc : s.call H now a (.deployCode h fc) = .ok (s', eff)) : safeUntil s now ≤ now := by
  obtain ⟨_, ts, code, hts, hle, _, _, _⟩ := deploy_ok H hc
  obtain ⟨code', sts, dur, nd, ndt⟩ := s
  simp only at hts
  subst hts
  cases dur <;> cases nd <;> cases ndt <;>
    simp only [safeUntil, satAdd, Option.getD] <;> omega

/-! ## Traces -/

theorem run_append (s : Sys Code) (p q : Trace Code) : run H s (p ++ q) = run H (run H s p) q := by
  induction p generalizing s with
  | nil => rfl
  | cons x p ih => obtain ⟨t, e⟩ := x; exact ih _

theorem mono_append : ∀ (p : Trace Code) (t0 : Nat) (x : Nat × Ev Code) (q : Trace Code),
    Mono t0 (p ++ x :: q) → Mono t0 p ∧ endTime t0 p ≤ x.1 ∧ Mono x.1 q
  | [], _, (_, _), _, hm => ⟨trivial, hm.1, hm.2⟩
  | (t1, _) :: p, _, x, q, hm =>
    have ih := mono_append p t1 x q hm.2
    ⟨⟨hm.1, ih.1⟩, ih.2.1, ih.2.2⟩

/-- The plugin storage after an event is the old one, or the result of a successful call. -/
theorem step_up (s : Sys Code) (t : Nat) (e : Ev Code) :
    (s.step H t e).up = s.up ∨
    ∃ a c eff, e = .call a c ∧ s.up.call H t a c = .ok ((s.step H t e).up, eff) := by
  cases e with
  | call a c =>
    cases hr : s.up.call H t a c with
    | error err => exact Or.inl (by simp [Sys.step, hr])
    | ok r =>
      obtain ⟨u, eff⟩ := r
      refine Or.inr ⟨a, c, eff, rfl, ?_⟩
      cases eff <;> simp [Sys.step, hr]
  | batch i ok =>
    refine Or.inl ?_
    simp only [Sys.step]
    cases s.inflight[i]? <;> rfl
  | other => exact Or.inl rfl

theorem safeUntil_step (s : Sys Code) (t : Nat) (e : Ev Code) :
    safeUntil s.up t ≤ safeUntil (s.step H t e).up t := by
  rcases step_up H s t e with h | ⟨a, c, eff, _, hc⟩
  · rw [h]; exact Nat.le_refl _
  · exact safeUntil_call H hc

/-- Along any trace with non-decreasing block timestamps `safeUntil` never decreases. -/
theorem safeUntil_run : ∀ (tr : Trace Code) (s0 : Sys Code) (t0 : Nat), Mono t0 tr →
    safeUntil s0.up t0 ≤ safeUntil (run H s0 tr).up (endTime t0 tr)
  | [], _, _, _ => Nat.le_refl _
  | (t, e) :: rest, s0, _, hm =>
    Nat.le_trans (safeUntil_time _ hm.1)
      (Nat.le_trans (safeUntil_step H s0 t e) (safeUntil_run rest (s0.step H t e) t hm.2))

/-- **W3 (no deploy before `safeUntil`).** Start from any state `s0` at block timestamp `t0`.
    Along any trace with non-decreasing block timestamps — any calls, by anyone, with any
    permissions — an `up_deploy_code` call can succeed only at a block timestamp
    `≥ safeUntil s0.up t0`. -/
theorem W3_no_deploy_before (s0 : Sys Code) (t0 : Nat) (pre post : Trace Code)
    {now : Nat} {a : Bool} {h : String} {fc : Option FnCall}
    (hm : Mono t0 (pre ++ (now, Ev.call a (.deployCode h fc)) :: post))
    {u' : Up Code} {eff : Option (Deploy Code)}
    (hdep : (run H s0 pre).up.call H now a (.deployCode h fc) = .ok (u', eff)) :
    safeUntil s0.up t0 ≤ now := by
  obtain ⟨hm1, hle, _⟩ := mono_append pre t0 _ post hm
  exact Nat.le_trans (safeUntil_run H pre s0 t0 hm1)
    (Nat.le_trans (safeUntil_time _ hle) (deploy_after_safeUntil H hdep))

/-- Every deploy batch in flight was created by a call made at or after `lo ≤ safeUntil`, and
    not after the current block timestamp. -/
theorem inflight_bounds : ∀ (tr : Trace Code) (s0 : Sys Code) (t0 lo : Nat), Mono t0 tr →
    lo ≤ safeUntil s0.up t0 →
    (∀ d ∈ s0.inflight, lo ≤ d.calledAt ∧ d.calledAt ≤ t0) →
    ∀ d ∈ (run H s0 tr).inflight, lo ≤ d.calledAt ∧ d.calledAt ≤ endTime t0 tr
  | [], _, _, _, _, _, h0 => h0
  | (t, e) :: rest, s0, t0, lo, hm, hlo, h0 => by
    have hlo' : lo ≤ safeUntil s0.up t := Nat.le_trans hlo (safeUntil_time _ hm.1)
    apply inflight_bounds rest (s0.step H t e) t lo hm.2
      (Nat.le_trans hlo' (safeUntil_step H s0 t e))
    intro d hd
    have hold : ∀ d ∈ s0.inflight, lo ≤ d.calledAt ∧ d.calledAt ≤ t :=
      fun d hd => ⟨(h0 d hd).1, Nat.le_trans (h0 d hd).2 hm.1⟩
    cases e with
    | call a c =>
      cases hr : s0.up.call H t a c with
      | error err => simp only [Sys.step, hr] at hd; exact hold d hd
      | ok r =>
        obtain ⟨u, eff⟩ := r
        cases eff with
        | none => simp only [Sys.step, hr] at hd; exact hold d hd
        | some d' =>
          simp only [Sys.step, hr, List.mem_append, List.mem_singleton] at hd
          rcases hd with hd | hd
          · exact hold d hd
          · subst hd
            rcases call_inv H hr with ⟨_, h1 | h1 | h1 | h1 | h1⟩
            · rcases h1 with ⟨_, _, _, he⟩; cases he
            · rcases h1 with ⟨h', fc', ts, code, hx, _, _, _, _, _, he⟩
              cases he
              subst hx
              exact ⟨Nat.le_trans hlo' (deploy_after_safeUntil H hr), Nat.le_refl _⟩
            · rcases h1 with ⟨_, _, _, _, he⟩; cases he
            · rcases h1 with ⟨_, _, _, _, _, _, he⟩; cases he
            · rcases h1 with ⟨_, _, _, _, _, _, _, he⟩; cases he
    | batch i ok =>
      cases hi : s0.inflight[i]? with
      | none => simp only [Sys.step, hi] at hd; exact hold d hd
      | some d' =>
        simp only [Sys.step, hi] at hd
        exact hold d (List.mem_of_mem_eraseIdx hd)
    | other => exact hold d hd

/-- **W3 (no code replacement before `safeUntil`).** Start from any state `s0` at block
    timestamp `t0` with no deploy batch in flight. If an event at block timestamp `t` changes
    the code on the account, that event is the successful execution of a deploy batch, the new
    code is the batch's code, and the batch was created by an `up_deploy_code` call made at a
    block timestamp in `[safeUntil s0.up t0, t]`. -/
theorem W3_code_change (s0 : Sys Code) (t0 : Nat) (tr : Trace Code) (t : Nat) (e : Ev Code)
    (hm : Mono t0 (tr ++ [(t, e)])) (h0 : s0.inflight = [])
    (hne : (run H s0 (tr ++ [(t, e)])).current ≠ (run H s0 tr).current) :
    ∃ i d, e = .batch i true ∧ (run H s0 tr).inflight[i]? = some d ∧
      (run H s0 (tr ++ [(t, e)])).current = d.code ∧
      safeUntil s0.up t0 ≤ d.calledAt ∧ d.calledAt ≤ t := by
  obtain ⟨hm1, hle, _⟩ := mono_append tr t0 (t, e) [] hm
  have hb := inflight_bounds H tr s0 t0 (safeUntil s0.up t0) hm1 (Nat.le_refl _)
    (by intro d hd; rw [h0] at hd; cases hd)
  rw [run_append] at hne ⊢
  simp only [run] at hne ⊢
  cases e with
  | call a c =>
    exfalso; apply hne
    cases hr : (run H s0 tr).up.call H t a c with
    | error err => simp [Sys.step, hr]
    | ok r => obtain ⟨u, eff⟩ := r; cases eff <;> simp [Sys.step, hr]
  | other => exact absurd rfl hne
  | batch i ok =>
    cases hi : (run H s0 tr).inflight[i]? with
    | none => simp [Sys.step, hi] at hne
    | some d =>
      cases ok with
      | false => simp [Sys.step, hi] at hne
      | true =>
        have hmem : d ∈ (run H s0 tr).inflight := List.mem_of_getElem? hi
        refine ⟨i, d, rfl, hi, ?_, (hb d hmem).1, Nat.le_trans (hb d hmem).2 hle⟩
        simp [Sys.step, hi]

theorem le_endTime : ∀ (tr : Trace Code) (t0 : Nat), Mono t0 tr → t0 ≤ endTime t0 tr
  | [], _, _ => Nat.le_refl _
  | (t, _) :: rest, _, hm => Nat.le_trans hm.1 (le_endTime rest t hm.2)

/-- Every deploy batch in flight after a trace either was already in flight at the start, or
    was created by a call made at or after `lo ≤ safeUntil` and not after the last block
    timestamp. -/
theorem inflight_origin : ∀ (tr : Trace Code) (s0 : Sys Code) (t0 lo : Nat), Mono t0 tr →
    lo ≤ safeUntil s0.up t0 →
    ∀ d ∈ (run H s0 tr).inflight,
      d ∈ s0.inflight ∨ (lo ≤ d.calledAt ∧ d.calledAt ≤ endTime t0 tr)
  | [], _, _, _, _, _, _, hd => Or.inl hd
  | (t, e) :: rest, s0, t0, lo, hm, hlo, d, hd => by
    have hlo' : lo ≤ safeUntil s0.up t := Nat.le_trans hlo (safeUntil_time _ hm.1)
    have hend : t ≤ endTime t rest := le_endTime rest t hm.2
    rcases inflight_origin rest (s0.step H t e) t lo hm.2
      (Nat.le_trans hlo' (safeUntil_step H s0 t e)) d hd with h1 | h1
    · cases e with
      | call a c =>
        cases hr : s0.up.call H t a c with
        | error err => simp only [Sys.step, hr] at h1; exact Or.inl h1
        | ok r =>
          obtain ⟨u, eff⟩ := r
          cases eff with
          | none => simp only [Sys.step, hr] at h1; exact Or.inl h1
          | some d' =>
            simp only [Sys.step, hr, List.mem_append, List.mem_singleton] at h1
            rcases h1 with h1 | h1
            · exact Or.inl h1
            · subst h1
              rcases call_inv H hr with ⟨_, h2 | h2 | h2 | h2 | h2⟩
              · rcases h2 with ⟨_, _, _, he⟩; cases he
              · rcases h2 with ⟨h', fc', ts, code, hx, _, _, _, _, _, he⟩
                cases he
                subst hx
                exact Or.inr ⟨Nat.le_trans hlo' (deploy_after_safeUntil H hr), hend⟩
              · rcases h2 with ⟨_, _, _, _, he⟩; cases he
              · rcases h2 with ⟨_, _, _, _, _, _, he⟩; cases he
              · rcases h2 with ⟨_, _, _, _, _, _, _, he⟩; cases he
      | batch i ok =>
        cases hi : s0.inflight[i]? with
        | none => simp only [Sys.step, hi] at h1; exact Or.inl h1
        | some d' =>
          simp only [Sys.step, hi] at h1
          exact Or.inl (List.mem_of_mem_eraseIdx h1)
      | other => exact Or.inl h1
    · exact Or.inr h1

/-- **W3 (code replacement, from any state).** If an event at block timestamp `t` changes the
    code on the account, it is the successful execution of a deploy batch, and that batch
    either was already in flight at the start, or was created by an `up_deploy_code` call made
    at a block timestamp in `[safeUntil s0.up t0, t]`. -/
theorem W3_code_change_any (s0 : Sys Code) (t0 : Nat) (tr : Trace Code) (t : Nat) (e : Ev Code)
    (hm : Mono t0 (tr ++ [(t, e)]))
    (hne : (run H s0 (tr ++ [(t, e)])).current ≠ (run H s0 tr).current) :
    ∃ i d, e = .batch i true ∧ (run H s0 tr).inflight[i]? = some d ∧
      (run H s0 (tr ++ [(t, e)])).current = d.code ∧
      (d ∈ s0.inflight ∨ (safeUntil s0.up t0 ≤ d.calledAt ∧ d.calledAt ≤ t)) := by
  obtain ⟨hm1, hle, _⟩ := mono_append tr t0 (t, e) [] hm
  have hb := inflight_origin H tr s0 t0 (safeUntil s0.up t0) hm1 (Nat.le_refl _)
  rw [run_append] at hne ⊢
  simp only [run] at hne ⊢
  cases e with
  | call a c =>
    exfalso; apply hne
    cases hr : (run H s0 tr).up.call H t a c with
    | error err => simp [Sys.step, hr]
    | ok r => obtain ⟨u, eff⟩ := r; cases eff <;> simp [Sys.step, hr]
  | other => exact absurd rfl hne
  | batch i ok =>
    cases hi : (run H s0 tr).inflight[i]? with
    | none => simp [Sys.step, hi] at hne
    | some d =>
      cases ok with
      | false => simp [Sys.step, hi] at hne
      | true =>
        have hmem : d ∈ (run H s0 tr).inflight := List.mem_of_getElem? hi
        refine ⟨i, d, rfl, hi, ?_, ?_⟩
        · simp [Sys.step, hi]
        · rcases hb d hmem with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨h1.1, Nat.le_trans h1.2 hle⟩

/-! ## W1, W2: what is deployed, and when -/

/-- A permitted `up_stage_code` call: the only event that changes the staged code or its
    timestamp (`up_stage_code` has no failure other than the permission check). -/
def IsStage : Nat × Ev Code → Prop
  | (_, .call true (.stageCode _)) => True
  | _ => False

theorem step_not_stage (s : Sys Code) (t : Nat) (e : Ev Code) (hn : ¬ IsStage (t, e)) :
    (s.step H t e).up.code = s.up.code ∧ (s.step H t e).up.stagingTs = s.up.stagingTs := by
  rcases step_up H s t e with h | ⟨a, c, eff, he, hc⟩
  · rw [h]; exact ⟨rfl, rfl⟩
  · rcases call_inv H hc with ⟨ha, h1 | h1 | h1 | h1 | h1⟩
    · rcases h1 with ⟨x, hx, _⟩
      subst he ha hx
      exact absurd trivial hn
    · rcases h1 with ⟨_, _, _, _, _, hs, _⟩; rw [hs]; exact ⟨rfl, rfl⟩
    · rcases h1 with ⟨_, _, _, hs, _⟩; rw [hs]; exact ⟨rfl, rfl⟩
    · rcases h1 with ⟨_, _, _, _, _, hs, _⟩; rw [hs]; exact ⟨rfl, rfl⟩
    · rcases h1 with ⟨_, _, _, _, _, _, hs, _⟩; rw [hs]; exact ⟨rfl, rfl⟩

theorem run_no_stage : ∀ (tr : Trace Code) (s : Sys Code), (∀ x ∈ tr, ¬ IsStage x) →
    (run H s tr).up.code = s.up.code ∧ (run H s tr).up.stagingTs = s.up.stagingTs
  | [], _, _ => ⟨rfl, rfl⟩
  | (t, e) :: rest, s, hn => by
    have h1 := step_not_stage H s t e (hn (t, e) (List.mem_cons_self ..))
    have h2 := run_no_stage rest (s.step H t e) (fun x hx => hn x (List.mem_cons_of_mem _ hx))
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- Where the staged code and its timestamp come from: untouched since the start, removed, or
    written by the last permitted `up_stage_code` call of the trace. -/
theorem staged_origin : ∀ (tr : Trace Code) (s0 : Sys Code),
    ((∀ x ∈ tr, ¬ IsStage x) ∧ (run H s0 tr).up.stagingTs = s0.up.stagingTs ∧
        (run H s0 tr).up.code = s0.up.code)
    ∨ (run H s0 tr).up.stagingTs = none
    ∨ (∃ pre post t c, tr = pre ++ (t, Ev.call true (.stageCode (some c))) :: post ∧
        (∀ x ∈ post, ¬ IsStage x) ∧
        (run H s0 tr).up.code = some c ∧
        (run H s0 tr).up.stagingTs = some (satAdd t ((run H s0 pre).up.dur.getD 0)))
  | [], _ => Or.inl ⟨fun _ hx => (by cases hx), rfl, rfl⟩
  | (t, e) :: rest, s0 => by
    rcases staged_origin rest (s0.step H t e) with ⟨hns, hts, hcode⟩ | hnone | ⟨pre, post, t', c, hsplit, hns, hcode, hts⟩
    · by_cases hst : IsStage (t, e)
      · -- the first event is the last permitted stage call
        cases e with
        | call a c =>
          cases a with
          | false => exact absurd hst (by simp [IsStage])
          | true =>
            cases c with
            | stageCode x =>
              cases x with
              | none =>
                refine Or.inr (Or.inl ?_)
                show (run H (s0.step H t _) rest).up.stagingTs = none
                rw [hts]; simp [Sys.step, Up.call, Up.stageCode]
              | some c =>
                refine Or.inr (Or.inr ⟨[], rest, t, c, rfl, hns, ?_, ?_⟩)
                · show (run H (s0.step H t _) rest).up.code = some c
                  rw [hcode]; simp [Sys.step, Up.call, Up.stageCode]
                · show (run H (s0.step H t _) rest).up.stagingTs = _
                  rw [hts]; simp [Sys.step, Up.call, Up.stageCode, run]
            | deployCode h fc => exact absurd hst (by simp [IsStage])
            | initDur d => exact absurd hst (by simp [IsStage])
            | stageDur d => exact absurd hst (by simp [IsStage])
            | applyDur => exact absurd hst (by simp [IsStage])
        | batch i ok => exact absurd hst (by simp [IsStage])
        | other => exact absurd hst (by simp [IsStage])
      · have h1 := step_not_stage H s0 t e hst
        refine Or.inl ⟨?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with hx | hx
          · rw [hx]; exact hst
          · exact hns x hx
        · exact hts.trans h1.2
        · exact hcode.trans h1.1
    · exact Or.inr (Or.inl hnone)
    · refine Or.inr (Or.inr ⟨(t, e) :: pre, post, t', c, ?_, hns, hcode, hts⟩)
      rw [hsplit]; rfl

/-- **W1 + W2 (origin of a deployment).** Start from a state with nothing staged. If an
    `up_deploy_code(hash, ..)` call succeeds after the trace `tr`, then `tr` contains a permitted
    `up_stage_code(c)` call at some block timestamp `t` with no permitted `up_stage_code` call
    after it, and
    * (W1) the promise deploys exactly that `c`, and the deploy call's block timestamp is at
      least `t + D` (saturating at `u64::MAX`), `D` being the staging duration when `c` was
      staged (0 if none was set);
    * (W2) `hash` is the hash of `c`, and at every moment between that staging and the deploy
      the view `up_staged_code_hash` returned this same hash. -/
theorem deploy_origin (s0 : Sys Code) (tr : Trace Code) (hinit : s0.up.stagingTs = none)
    {now : Nat} {a : Bool} {h : String} {fc : Option FnCall} {u' : Up Code} {d : Deploy Code}
    (hdep : (run H s0 tr).up.call H now a (.deployCode h fc) = .ok (u', some d)) :
    ∃ pre post t c,
      tr = pre ++ (t, Ev.call true (.stageCode (some c))) :: post ∧
      (∀ x ∈ post, ¬ IsStage x) ∧
      d.code = c ∧ d.calledAt = now ∧ h = H c ∧
      satAdd t ((run H s0 pre).up.dur.getD 0) ≤ now ∧
      (∀ p q, post = p ++ q →
        (run H s0 (pre ++ (t, Ev.call true (.stageCode (some c))) :: p)).up.stagedCodeHash H
          = some (H c)) := by
  obtain ⟨_, ts, code, hts, hle, hcode, hh, he⟩ := deploy_ok H hdep
  rcases staged_origin H tr s0 with ⟨_, hts', _⟩ | hnone | ⟨pre, post, t, c, hsplit, hns, hcode', hts'⟩
  · rw [hts', hinit] at hts; cases hts
  · rw [hnone] at hts; cases hts
  · have hd : d = ⟨code, fc, now⟩ := Option.some.inj he
    have hc1 : code = c := by rw [hcode'] at hcode; exact (Option.some.inj hcode).symm
    have hts1 : satAdd t ((run H s0 pre).up.dur.getD 0) = ts := by
      rw [hts'] at hts; exact Option.some.inj hts
    refine ⟨pre, post, t, c, hsplit, hns, by rw [hd]; exact hc1, by rw [hd], by rw [hh, hc1],
      by rw [hts1]; exact hle, ?_⟩
    intro p q hpq
    have hnp : ∀ x ∈ p, ¬ IsStage x := fun x hx => hns x (by rw [hpq]; exact List.mem_append_left _ hx)
    rw [run_append]
    simp only [run]
    have h2 := (run_no_stage H p ((run H s0 pre).step H t (Ev.call true (.stageCode (some c)))) hnp).1
    unfold Up.stagedCodeHash
    rw [h2]
    simp [Sys.step, Up.call, Up.stageCode]

/-- **W1 (delay).** If the staging duration is `some D` when code is staged at block timestamp
    `t`, any later successful `up_deploy_code` of it deploys exactly that code, at a block
    timestamp `≥ t + D` (when `t + D` fits in u64; otherwise never before `u64::MAX`). -/
theorem W1_delay (s0 : Sys Code) (tr : Trace Code) (hinit : s0.up.stagingTs = none)
    {now : Nat} {a : Bool} {h : String} {fc : Option FnCall} {u' : Up Code} {d : Deploy Code}
    (hdep : (run H s0 tr).up.call H now a (.deployCode h fc) = .ok (u', some d)) :
    ∃ pre post t c,
      tr = pre ++ (t, Ev.call true (.stageCode (some c))) :: post ∧
      (∀ x ∈ post, ¬ IsStage x) ∧
      d.code = c ∧
      (∀ D, (run H s0 pre).up.dur = some D → min (t + D) U64_MAX ≤ now) := by
  obtain ⟨pre, post, t, c, hsplit, hns, hc, _, _, hle, _⟩ := deploy_origin H s0 tr hinit hdep
  refine ⟨pre, post, t, c, hsplit, hns, hc, ?_⟩
  intro D hD
  rw [hD] at hle
  exact hle

/-- **W2 (visibility).** Between the staging of code `c` and a successful
    `up_deploy_code(hash, ..)`, the view `up_staged_code_hash` returns `some (H c)` at every
    moment, and the deploy succeeds only with `hash = H c`, deploying `c`. -/
theorem W2_visibility (s0 : Sys Code) (tr : Trace Code) (hinit : s0.up.stagingTs = none)
    {now : Nat} {a : Bool} {h : String} {fc : Option FnCall} {u' : Up Code} {d : Deploy Code}
    (hdep : (run H s0 tr).up.call H now a (.deployCode h fc) = .ok (u', some d)) :
    ∃ pre post t c,
      tr = pre ++ (t, Ev.call true (.stageCode (some c))) :: post ∧
      d.code = c ∧ h = H c ∧
      (∀ p q, post = p ++ q →
        (run H s0 (pre ++ (t, Ev.call true (.stageCode (some c))) :: p)).up.stagedCodeHash H
          = some h) := by
  obtain ⟨pre, post, t, c, hsplit, _, hc, _, hh, _, hvis⟩ := deploy_origin H s0 tr hinit hdep
  exact ⟨pre, post, t, c, hsplit, hc, hh, by rw [hh]; exact hvis⟩

/-! ## W4: no duration, no window -/

/-- **W4 (the null case).** With no staging duration set, any code can be staged and its
    deployment accepted at the same block timestamp. -/
theorem W4_no_window (u : Up Code) (hd : u.dur = none) (now : Nat) (c : Code) (fc : Option FnCall) :
    ∃ u1, u.call H now true (.stageCode (some c)) = .ok (u1, none) ∧
      u1.call H now true (.deployCode (H c) fc) = .ok (u1, some ⟨c, fc, now⟩) := by
  refine ⟨u.stageCode now (some c), by simp [Up.call], ?_⟩
  have : ¬ (now < satAdd now 0) := by unfold satAdd; omega
  simp [Up.call, Up.deployCode, Up.stageCode, hd, this]

/-- **W4 (witness trace).** From a state with no staging duration and nothing in flight, three
    events carrying the same block timestamp replace the code on the account with any `c`. -/
theorem W4_witness (s0 : Sys Code) (hd : s0.up.dur = none) (h0 : s0.inflight = []) (now : Nat)
    (c : Code) :
    (run H s0 [(now, Ev.call true (.stageCode (some c))),
               (now, Ev.call true (.deployCode (H c) none)),
               (now, Ev.batch 0 true)]).current = c := by
  have : ¬ (now < satAdd now 0) := by unfold satAdd; omega
  simp [run, Sys.step, Up.call, Up.deployCode, Up.stageCode, hd, h0, this]

/-! ## W3: the shortcuts the naive statement misses -/

/-- **W3 (shortcut 1: code staged before the duration was initialised).** Code staged while no
    duration is set keeps its staging timestamp: after `up_init_staging_duration(D)` the state
    shows `staging_duration = D`, yet that code is deployable at once. -/
theorem W3_prestaged_shortcut (D now : Nat) (c : Code) (fc : Option FnCall) :
    ∃ u1 u2 : Up Code,
      ({} : Up Code).call H now true (.stageCode (some c)) = .ok (u1, none) ∧
      u1.call H now true (.initDur D) = .ok (u2, none) ∧
      u2.dur = some D ∧
      u2.call H now true (.deployCode (H c) fc) = .ok (u2, some ⟨c, fc, now⟩) := by
  have : ¬ (now < satAdd now 0) := by unfold satAdd; omega
  refine ⟨({} : Up Code).stageCode now (some c),
    { (({} : Up Code).stageCode now (some c)) with dur := some D }, by simp [Up.call],
    by simp [Up.call, Up.initDur, Up.stageCode], rfl, ?_⟩
  simp [Up.call, Up.deployCode, Up.stageCode, this]

/-- **W3 (shortcut 2: shrink the duration first).** From a state with duration `D` and nothing
    staged: stage an update of the duration to 0 at `t0`, apply it at `t0 + D`, then stage code
    `c` and have its deployment accepted, both at block timestamp `t0 + D`: the deploy batch in
    flight carries exactly `c`, created at `t0 + D`. The code was visible for no time at all;
    what was visible for `D` is the staged duration update. -/
theorem W3_shrink_shortcut (D t0 : Nat) (hfit : t0 + D ≤ U64_MAX) (c c0 : Code) :
    let s0 : Sys Code := { up := { dur := some D }, current := c0 }
    let tr : Trace Code :=
      [(t0, Ev.call true (.stageDur 0)),
       (t0 + D, Ev.call true .applyDur),
       (t0 + D, Ev.call true (.stageCode (some c))),
       (t0 + D, Ev.call true (.deployCode (H c) none))]
    Mono t0 tr ∧ (run H s0 tr).inflight = [⟨c, none, t0 + D⟩] ∧
      (run H s0 tr).up.code = some c := by
  have h1 : ¬ (U64_MAX < t0 + D) := by omega
  have h2 : ¬ (t0 + D < satAdd (t0 + D) 0) := by unfold satAdd; omega
  simp [Mono, run, Sys.step, Up.call, Up.stageDur, Up.applyDur, Up.stageCode, Up.deployCode, h1, h2]

/-! ## W3: the bound is exact -/

/-- Well-formed plugin storage; holds in every state reachable from an empty storage
    (`wf_empty`, `wf_run`): a staging timestamp comes with staged code, and the timestamp of a
    staged duration update fits in u64. -/
def WF (u : Up Code) : Prop :=
  (∀ ts, u.stagingTs = some ts → ∃ c, u.code = some c) ∧
  (∀ ndt, u.newDurTs = some ndt → ndt ≤ U64_MAX)

theorem wf_empty (d : Option Nat) : WF ({ dur := d } : Up Code) :=
  ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem wf_call {now : Nat} {a : Bool} {s s' : Up Code} {c : Call Code}
    {eff : Option (Deploy Code)} (hc : s.call H now a c = .ok (s', eff)) (hwf : WF s) : WF s' := by
  rcases call_inv H hc with ⟨_, h1 | h1 | h1 | h1 | h1⟩
  · rcases h1 with ⟨x, _, hs, _⟩
    subst hs
    cases x with
    | none => exact ⟨fun _ h => (by cases h), hwf.2⟩
    | some c => exact ⟨fun _ _ => ⟨c, rfl⟩, hwf.2⟩
  · rcases h1 with ⟨_, _, _, _, _, hs, _⟩; rw [hs]; exact hwf
  · rcases h1 with ⟨_, _, _, hs, _⟩; rw [hs]; exact hwf
  · rcases h1 with ⟨d, cur, _, _, hfit, hs, _⟩
    rw [hs]
    refine ⟨hwf.1, ?_⟩
    intro ndt h
    cases h
    exact hfit
  · rcases h1 with ⟨_, _, _, _, _, _, hs, _⟩; rw [hs]; exact hwf

theorem wf_run : ∀ (tr : Trace Code) (s0 : Sys Code), WF s0.up → WF (run H s0 tr).up
  | [], _, h => h
  | (t, e) :: rest, s0, h => by
    apply wf_run rest (s0.step H t e)
    rcases step_up H s0 t e with h1 | ⟨a, c, eff, _, hc⟩
    · rw [h1]; exact h
    · exact wf_call H hc h

/-- Some trace starting at `t0` ends with a successful `up_deploy_code` at block timestamp `X`. -/
def CanDeployAt (s0 : Sys Code) (t0 X : Nat) : Prop :=
  ∃ (pre : Trace Code) (h : String) (u' : Up Code) (d : Deploy Code),
    Mono t0 (pre ++ [(X, Ev.call true (.deployCode h none))]) ∧
    (run H s0 pre).up.call H X true (.deployCode h none) = .ok (u', some d)

/-- Stage new code now, deploy it when its timestamp is reached. -/
theorem canDeploy_new (s0 : Sys Code) (t0 : Nat) (c : Code) (ht0 : t0 ≤ U64_MAX) :
    CanDeployAt H s0 t0 (satAdd t0 (s0.up.dur.getD 0)) := by
  have hle : t0 ≤ satAdd t0 (s0.up.dur.getD 0) := by unfold satAdd; omega
  refine ⟨[(t0, Ev.call true (.stageCode (some c)))], H c,
    (run H s0 [(t0, Ev.call true (.stageCode (some c)))]).up,
    ⟨c, none, satAdd t0 (s0.up.dur.getD 0)⟩, ?_, ?_⟩
  · exact ⟨Nat.le_refl _, hle, trivial⟩
  · simp [run, Sys.step, Up.call, Up.stageCode, Up.deployCode]

/-- Deploy the code that is already staged. -/
theorem canDeploy_staged (s0 : Sys Code) (t0 ts : Nat) (c : Code)
    (hts : s0.up.stagingTs = some ts) (hcode : s0.up.code = some c) :
    CanDeployAt H s0 t0 (max t0 ts) := by
  have h1 : ¬ (max t0 ts < ts) := by omega
  refine ⟨[], H c, s0.up, ⟨c, none, max t0 ts⟩, ?_, ?_⟩
  · exact ⟨by omega, trivial⟩
  · simp [run, Up.call, Up.deployCode, hts, hcode, h1]

/-- Apply the staged duration update when it becomes applicable, stage new code at once, deploy
    it after the new duration. -/
theorem canDeploy_after_update (s0 : Sys Code) (t0 nd ndt : Nat) (c : Code) (ht0 : t0 ≤ U64_MAX)
    (hnd : s0.up.newDur = some nd) (hndt : s0.up.newDurTs = some ndt) (hfit : ndt ≤ U64_MAX) :
    CanDeployAt H s0 t0 (satAdd (max t0 ndt) nd) := by
  have h1 : ¬ (max t0 ndt < ndt) := by omega
  have hle : max t0 ndt ≤ satAdd (max t0 ndt) nd := by unfold satAdd; omega
  refine ⟨[(max t0 ndt, Ev.call true .applyDur), (max t0 ndt, Ev.call true (.stageCode (some c)))],
    H c,
    (run H s0 [(max t0 ndt, Ev.call true .applyDur), (max t0 ndt, Ev.call true (.stageCode (some c)))]).up,
    ⟨c, none, satAdd (max t0 ndt) nd⟩, ?_, ?_⟩
  · exact ⟨by omega, Nat.le_refl _, hle, trivial⟩
  · simp [run, Sys.step, Up.call, Up.applyDur, Up.stageCode, Up.deployCode, hnd, hndt, h1]

/-- **W3 (the bound is exact).** From any well-formed state at block timestamp `t0`, an
    adversary holding every role can have an `up_deploy_code` call succeed at block timestamp
    exactly `max t0 (safeUntil s0.up t0)`: by deploying what is staged, by staging new code now,
    or by applying the staged duration update first. With `W3_no_deploy_before` this makes
    `safeUntil` the exact earliest time of a successful deploy. -/
theorem W3_tight (s0 : Sys Code) (t0 : Nat) (c : Code) (ht0 : t0 ≤ U64_MAX) (hwf : WF s0.up) :
    CanDeployAt H s0 t0 (max t0 (safeUntil s0.up t0)) := by
  have hnew := canDeploy_new H s0 t0 c ht0
  have hupd := fun nd ndt h1 h2 h3 => canDeploy_after_update H s0 t0 nd ndt c ht0 h1 h2 h3
  have hstg := fun ts c' h1 h2 => canDeploy_staged H s0 t0 ts c' h1 h2
  obtain ⟨hwf1, hwf2⟩ := hwf
  obtain ⟨⟨code, sts, dur, nd, ndt⟩, cur, infl⟩ := s0
  simp only at hnew hupd hstg hwf1 hwf2 ⊢
  have ha : t0 ≤ satAdd t0 (dur.getD 0) := by unfold satAdd; omega
  cases sts with
  | none =>
    cases nd with
    | none =>
      have : max t0 (safeUntil ⟨code, none, dur, none, ndt⟩ t0) = satAdd t0 (dur.getD 0) := by
        simp only [safeUntil]; omega
      rw [this]; exact hnew
    | some nd =>
      cases ndt with
      | none =>
        have : max t0 (safeUntil ⟨code, none, dur, some nd, none⟩ t0) = satAdd t0 (dur.getD 0) := by
          simp only [safeUntil]; omega
        rw [this]; exact hnew
      | some ndt =>
        have hfit := hwf2 ndt rfl
        have hc : max t0 ndt ≤ satAdd (max t0 ndt) nd := by unfold satAdd; omega
        by_cases hmin : satAdd t0 (dur.getD 0) ≤ satAdd (max t0 ndt) nd
        · have : max t0 (safeUntil ⟨code, none, dur, some nd, some ndt⟩ t0) = satAdd t0 (dur.getD 0) := by
            simp only [safeUntil]; omega
          rw [this]; exact hnew
        · have : max t0 (safeUntil ⟨code, none, dur, some nd, some ndt⟩ t0) = satAdd (max t0 ndt) nd := by
            simp only [safeUntil]; omega
          rw [this]; exact hupd nd ndt rfl rfl hfit
  | some ts =>
    obtain ⟨c', hc'⟩ := hwf1 ts rfl
    cases nd with
    | none =>
      by_cases hmin : ts ≤ satAdd t0 (dur.getD 0)
      · have : max t0 (safeUntil ⟨code, some ts, dur, none, ndt⟩ t0) = max t0 ts := by
          simp only [safeUntil]; omega
        rw [this]; exact hstg ts c' rfl hc'
      · have : max t0 (safeUntil ⟨code, some ts, dur, none, ndt⟩ t0) = satAdd t0 (dur.getD 0) := by
          simp only [safeUntil]; omega
        rw [this]; exact hnew
    | some nd =>
      cases ndt with
      | none =>
        by_cases hmin : ts ≤ satAdd t0 (dur.getD 0)
        · have : max t0 (safeUntil ⟨code, some ts, dur, some nd, none⟩ t0) = max t0 ts := by
            simp only [safeUntil]; omega
          rw [this]; exact hstg ts c' rfl hc'
        · have : max t0 (safeUntil ⟨code, some ts, dur, some nd, none⟩ t0) = satAdd t0 (dur.getD 0) := by
            simp only [safeUntil]; omega
          rw [this]; exact hnew
      | some ndt =>
        have hfit := hwf2 ndt rfl
        have hc : max t0 ndt ≤ satAdd (max t0 ndt) nd := by unfold satAdd; omega
        by_cases h1 : ts ≤ satAdd t0 (dur.getD 0) ∧ ts ≤ satAdd (max t0 ndt) nd
        · have : max t0 (safeUntil ⟨code, some ts, dur, some nd, some ndt⟩ t0) = max t0 ts := by
            simp only [safeUntil]; omega
          rw [this]; exact hstg ts c' rfl hc'
        · by_cases h2 : satAdd t0 (dur.getD 0) ≤ satAdd (max t0 ndt) nd
          · have : max t0 (safeUntil ⟨code, some ts, dur, some nd, some ndt⟩ t0) = satAdd t0 (dur.getD 0) := by
              simp only [safeUntil]; omega
            rw [this]; exact hnew
          · have : max t0 (safeUntil ⟨code, some ts, dur, some nd, some ndt⟩ t0) = satAdd (max t0 ndt) nd := by
              simp only [safeUntil]; omega
            rw [this]; exact hupd nd ndt rfl rfl hfit

/-! ## W3: a build without overflow checks -/

/-- A build without overflow checks behaves like the model on every
    `up_stage_update_staging_duration` call whose `block_timestamp + staging_duration` fits in
    u64: on traces without such an overflow all theorems above apply to it unchanged. -/
theorem stageDurUnchecked_eq (now : Nat) (s : Up Code) (d : Nat)
    (hfit : ∀ cur, s.dur = some cur → now + cur ≤ U64_MAX) :
    s.stageDurUnchecked now d = s.stageDur now d := by
  unfold Up.stageDurUnchecked Up.stageDur
  cases hd : s.dur with
  | none => rfl
  | some cur =>
    have h := hfit cur hd
    have h1 : ¬ (U64_MAX < now + cur) := by omega
    have h2 : (now + cur) % (U64_MAX + 1) = now + cur := Nat.mod_eq_of_lt (by omega)
    simp [h1, h2]

/-- **W3 (shortcut 3: a build without overflow checks).** If `block_timestamp + D` exceeds
    u64, a build without overflow checks lets the duration be changed at once: stage an update to
    0 (its timestamp wraps into the past), apply it, stage code and have its deployment accepted,
    all at the same block timestamp. An absurdly long staging duration is no protection there. -/
theorem W3_unchecked_shortcut (D now : Nat) (hnow : now ≤ U64_MAX) (hD : D ≤ U64_MAX)
    (hov : U64_MAX < now + D) (c : Code) :
    ∃ u1 u2 u3 : Up Code,
      ({ dur := some D } : Up Code).stageDurUnchecked now 0 = .ok u1 ∧
      u1.call H now true .applyDur = .ok (u2, none) ∧
      u2.dur = some 0 ∧
      u2.call H now true (.stageCode (some c)) = .ok (u3, none) ∧
      u3.call H now true (.deployCode (H c) none) = .ok (u3, some ⟨c, none, now⟩) := by
  have h1 : ¬ (now < (now + D) % (U64_MAX + 1)) := by
    simp only [U64_MAX] at *
    omega
  have h2 : ¬ (now < satAdd now 0) := by unfold satAdd; omega
  refine ⟨{ dur := some D, newDur := some 0, newDurTs := some ((now + D) % (U64_MAX + 1)) },
    { dur := some 0, newDur := some 0, newDurTs := some ((now + D) % (U64_MAX + 1)) },
    { code := some c, stagingTs := some (satAdd now 0), dur := some 0, newDur := some 0,
      newDurTs := some ((now + D) % (U64_MAX + 1)) }, ?_, ?_, rfl, ?_, ?_⟩
  · simp [Up.stageDurUnchecked]
  · simp [Up.call, Up.applyDur, h1]
  · simp [Up.call, Up.stageCode]
  · simp [Up.call, Up.deployCode, h2]

/-! ## W5: the exit window -/

/-- In a state without alarm and with duration `D`, `safeUntil` is `now + D`. -/
theorem quiet_safeUntil {u : Up Code} {D : Nat} (hq : alarm u = false) (hD : u.dur = some D)
    (now : Nat) : safeUntil u now = satAdd now D := by
  obtain ⟨code, sts, dur, nd, ndt⟩ := u
  simp only at hD
  subst hD
  cases sts <;> cases nd <;> cases ndt <;>
    simp [alarm] at hq <;> simp only [safeUntil, satAdd, Option.getD] <;> omega

/-- A successful call in a state without alarm does not lower the duration. -/
theorem quiet_call {now : Nat} {a : Bool} {s s' : Up Code} {c : Call Code}
    {eff : Option (Deploy Code)} (hc : s.call H now a c = .ok (s', eff)) {D : Nat}
    (hD : s.dur = some D) (hq : alarm s = false) : ∃ D', s'.dur = some D' ∧ D ≤ D' := by
  rcases call_inv H hc with ⟨_, h1 | h1 | h1 | h1 | h1⟩
  · rcases h1 with ⟨x, _, hs, _⟩
    rw [hs]; cases x <;> exact ⟨D, hD, Nat.le_refl _⟩
  · rcases h1 with ⟨_, _, _, _, _, hs, _⟩; rw [hs]; exact ⟨D, hD, Nat.le_refl _⟩
  · rcases h1 with ⟨d, _, hd, _⟩; rw [hd] at hD; cases hD
  · rcases h1 with ⟨_, _, _, _, _, hs, _⟩; rw [hs]; exact ⟨D, hD, Nat.le_refl _⟩
  · rcases h1 with ⟨t', nd, _, ht, _, hn, hs, _⟩
    rw [hs]
    refine ⟨nd, rfl, ?_⟩
    obtain ⟨code, sts, dur, nd', ndt⟩ := s
    simp only at hD ht hn
    subst hD ht hn
    cases sts <;> simp [alarm] at hq <;> omega

/-- A step from a state without alarm does not lower the duration. -/
theorem quiet_step (s : Sys Code) (t : Nat) (e : Ev Code) {D : Nat} (hD : s.up.dur = some D)
    (hq : alarm s.up = false) : ∃ D', (s.step H t e).up.dur = some D' ∧ D ≤ D' := by
  rcases step_up H s t e with h | ⟨a, c, eff, _, hc⟩
  · rw [h]; exact ⟨D, hD, Nat.le_refl _⟩
  · exact quiet_call H hc hD hq

/-- The first event that raises the alarm. -/
theorem first_alarm : ∀ (tr : Trace Code) (s0 : Sys Code), alarm s0.up = false →
    alarm (run H s0 tr).up = true →
    ∃ p1 x p2, tr = p1 ++ x :: p2 ∧ alarm (run H s0 (p1 ++ [x])).up = true ∧
      ∀ q r, p1 = q ++ r → alarm (run H s0 q).up = false
  | [], s0, h0, h1 => by simp [run] at h1; rw [h0] at h1; cases h1
  | (t, e) :: rest, s0, h0, h1 => by
    by_cases hs : alarm (s0.step H t e).up = true
    · refine ⟨[], (t, e), rest, rfl, hs, ?_⟩
      intro q r hqr
      have : q = [] := by
        cases q with
        | nil => rfl
        | cons _ _ => cases hqr
      rw [this]; exact h0
    · have hs' : alarm (s0.step H t e).up = false := by
        cases hb : alarm (s0.step H t e).up with
        | false => rfl
        | true => exact absurd hb hs
      obtain ⟨p1, x, p2, hsplit, ha, hq⟩ := first_alarm rest (s0.step H t e) hs' h1
      refine ⟨(t, e) :: p1, x, p2, by rw [hsplit]; rfl, ha, ?_⟩
      intro q r hqr
      cases q with
      | nil => exact h0
      | cons y q' =>
        simp only [List.cons_append, List.cons.injEq] at hqr
        obtain ⟨hy, hrest⟩ := hqr
        subst hy
        exact hq q' r hrest

/-- Along a prefix on which no state shows the alarm, the duration never goes down. -/
theorem quiet_prefix_dur : ∀ (p : Trace Code) (s0 : Sys Code) (D : Nat), s0.up.dur = some D →
    (∀ q r, p = q ++ r → alarm (run H s0 q).up = false) →
    ∃ D', (run H s0 p).up.dur = some D' ∧ D ≤ D'
  | [], _, D, hD, _ => ⟨D, hD, Nat.le_refl _⟩
  | (t, e) :: rest, s0, D, hD, hq => by
    have h0 : alarm s0.up = false := hq [] _ rfl
    obtain ⟨D1, hD1, hle1⟩ := quiet_step H s0 t e hD h0
    obtain ⟨D2, hD2, hle2⟩ := quiet_prefix_dur rest (s0.step H t e) D1 hD1
      (fun q r hqr => hq ((t, e) :: q) r (by rw [hqr]; rfl))
    exact ⟨D2, hD2, Nat.le_trans hle1 hle2⟩

/-- **W5 (notice).** Start at block timestamp `t0` from a state with staging duration `D` and
    no alarm (nothing staged, no staged duration update below `D`). If an `up_deploy_code` call
    succeeds at block timestamp `now`, then some earlier event, at block timestamp `ta`, was the
    first to raise the alarm — every state before it showed no alarm — and
    `now ≥ ta + D` (saturating at `u64::MAX`).

    The alarm is a function of `up_get_delay_status`, and it holds in the state right after
    that event. A watcher who sees every state has `D` from `ta`; one who polls may miss the
    event and relies on `W5_quiet_reading` instead. -/
theorem W5_notice (s0 : Sys Code) (t0 D : Nat) (pre post : Trace Code)
    {now : Nat} {a : Bool} {h : String} {fc : Option FnCall}
    (hm : Mono t0 (pre ++ (now, Ev.call a (.deployCode h fc)) :: post))
    (hD : s0.up.dur = some D) (hq : alarm s0.up = false)
    {u' : Up Code} {eff : Option (Deploy Code)}
    (hdep : (run H s0 pre).up.call H now a (.deployCode h fc) = .ok (u', eff)) :
    ∃ p1 ta e p2, pre = p1 ++ (ta, e) :: p2 ∧
      (∀ q r, p1 = q ++ r → alarm (run H s0 q).up = false) ∧
      alarm (run H s0 (p1 ++ [(ta, e)])).up = true ∧
      satAdd ta D ≤ now := by
  obtain ⟨_, ts, code, hts, _, _, _, _⟩ := deploy_ok H hdep
  have halarm : alarm (run H s0 pre).up = true := by simp [alarm, hts]
  obtain ⟨p1, ⟨ta, e⟩, p2, hsplit, ha, hquiet⟩ := first_alarm H pre s0 hq halarm
  refine ⟨p1, ta, e, p2, hsplit, hquiet, ha, ?_⟩
  obtain ⟨D1, hD1, hle1⟩ := quiet_prefix_dur H p1 s0 D hD hquiet
  have hq1 : alarm (run H s0 p1).up = false := hquiet p1 [] (by simp)
  -- timestamps
  rw [hsplit, List.append_assoc] at hm
  obtain ⟨_, _, hm2⟩ := mono_append p1 t0 (ta, e) _ hm
  obtain ⟨hm3, hle3, _⟩ := mono_append p2 ta _ post hm2
  -- the state the deploy call ran in
  have hrun : run H s0 pre = run H ((run H s0 p1).step H ta e) p2 := by
    rw [hsplit, run_append]; rfl
  rw [hrun] at hdep
  calc satAdd ta D ≤ satAdd ta D1 := satAdd_mono (Nat.le_refl _) hle1
    _ = safeUntil (run H s0 p1).up ta := (quiet_safeUntil hq1 hD1 ta).symm
    _ ≤ safeUntil ((run H s0 p1).step H ta e).up ta := safeUntil_step H _ ta e
    _ ≤ safeUntil (run H ((run H s0 p1).step H ta e) p2).up (endTime ta p2) :=
        safeUntil_run H p2 _ ta hm3
    _ ≤ safeUntil (run H ((run H s0 p1).step H ta e) p2).up now := safeUntil_time _ hle3
    _ ≤ now := deploy_after_safeUntil H hdep

/-- From a state without alarm and with no deploy batch in flight, an event creates none: a
    deploy call cannot succeed while nothing is staged. -/
theorem quiet_step_inflight (s : Sys Code) (t : Nat) (e : Ev Code) (h0 : s.inflight = [])
    (hq : alarm s.up = false) : (s.step H t e).inflight = [] := by
  cases e with
  | call a c =>
    cases hr : s.up.call H t a c with
    | error err => simp [Sys.step, hr, h0]
    | ok r =>
      obtain ⟨u, eff⟩ := r
      cases eff with
      | none => simp [Sys.step, hr, h0]
      | some d =>
        exfalso
        rcases call_inv H hr with ⟨_, h1 | h1 | h1 | h1 | h1⟩
        · rcases h1 with ⟨_, _, _, he⟩; cases he
        · rcases h1 with ⟨_, _, ts, _, _, _, hts, _⟩
          simp [alarm, hts] at hq
        · rcases h1 with ⟨_, _, _, _, he⟩; cases he
        · rcases h1 with ⟨_, _, _, _, _, _, he⟩; cases he
        · rcases h1 with ⟨_, _, _, _, _, _, _, he⟩; cases he
  | batch i ok => simp [Sys.step, h0]
  | other => exact h0

/-- Either no deploy batch is in flight after the trace, or some event raised the alarm. -/
theorem inflight_or_alarm : ∀ (tr : Trace Code) (s0 : Sys Code), s0.inflight = [] →
    alarm s0.up = false →
    ((run H s0 tr).inflight = [] ∧ ∀ q r, tr = q ++ r → alarm (run H s0 q).up = false) ∨
    ∃ p1 x p2, tr = p1 ++ x :: p2 ∧ alarm (run H s0 (p1 ++ [x])).up = true ∧
      (run H s0 p1).inflight = [] ∧ ∀ q r, p1 = q ++ r → alarm (run H s0 q).up = false
  | [], s0, h0, hq => Or.inl ⟨h0, fun q r hqr => by
      have : q = [] := by
        cases q with
        | nil => rfl
        | cons _ _ => cases hqr
      rw [this]; exact hq⟩
  | (t, e) :: rest, s0, h0, hq => by
    have h1 := quiet_step_inflight H s0 t e h0 hq
    by_cases hs : alarm (s0.step H t e).up = true
    · refine Or.inr ⟨[], (t, e), rest, rfl, hs, h0, ?_⟩
      intro q r hqr
      have : q = [] := by
        cases q with
        | nil => rfl
        | cons _ _ => cases hqr
      rw [this]; exact hq
    · have hs' : alarm (s0.step H t e).up = false := by
        cases hb : alarm (s0.step H t e).up with
        | false => rfl
        | true => exact absurd hb hs
      rcases inflight_or_alarm rest (s0.step H t e) h1 hs' with ⟨hi, hall⟩ | ⟨p1, x, p2, hsplit, ha, hi, hall⟩
      · refine Or.inl ⟨hi, ?_⟩
        intro q r hqr
        cases q with
        | nil => exact hq
        | cons y q' =>
          simp only [List.cons_append, List.cons.injEq] at hqr
          obtain ⟨hy, hrest⟩ := hqr
          subst hy
          exact hall q' r hrest
      · refine Or.inr ⟨(t, e) :: p1, x, p2, by rw [hsplit]; rfl, ha, hi, ?_⟩
        intro q r hqr
        cases q with
        | nil => exact hq
        | cons y q' =>
          simp only [List.cons_append, List.cons.injEq] at hqr
          obtain ⟨hy, hrest⟩ := hqr
          subst hy
          exact hall q' r hrest

/-- **W5 (the code itself).** Start at block timestamp `t0` from a state with staging duration
    `D`, no alarm and no deploy batch in flight. If an event at block timestamp `t` changes the
    code on the account, then some earlier event, at block timestamp `ta`, was the first to raise
    the alarm, and `t ≥ ta + D` (saturating at `u64::MAX`): the code cannot change earlier than
    `D` after the first event that raised the alarm. -/
theorem W5_code_change (s0 : Sys Code) (t0 D : Nat) (tr : Trace Code) (t : Nat) (e : Ev Code)
    (hm : Mono t0 (tr ++ [(t, e)])) (h0 : s0.inflight = [])
    (hD : s0.up.dur = some D) (hq : alarm s0.up = false)
    (hne : (run H s0 (tr ++ [(t, e)])).current ≠ (run H s0 tr).current) :
    ∃ p1 ta ea p2, tr = p1 ++ (ta, ea) :: p2 ∧
      (∀ q r, p1 = q ++ r → alarm (run H s0 q).up = false) ∧
      alarm (run H s0 (p1 ++ [(ta, ea)])).up = true ∧
      satAdd ta D ≤ t := by
  rcases inflight_or_alarm H tr s0 h0 hq with ⟨hi, _⟩ | ⟨p1, ⟨ta, ea⟩, p2, hsplit, ha, hi1, hquiet⟩
  · -- nothing in flight: the last event cannot change the code
    exfalso
    obtain ⟨i, d, _, hget, _⟩ := W3_code_change H s0 t0 tr t e hm h0 hne
    rw [hi] at hget
    simp at hget
  · refine ⟨p1, ta, ea, p2, hsplit, hquiet, ha, ?_⟩
    obtain ⟨D1, hD1, hle1⟩ := quiet_prefix_dur H p1 s0 D hD hquiet
    have hq1 : alarm (run H s0 p1).up = false := hquiet p1 [] (by simp)
    have hia : ((run H s0 p1).step H ta ea).inflight = [] :=
      quiet_step_inflight H _ ta ea hi1 hq1
    -- timestamps of the part after the alarm
    have hm' : Mono t0 (p1 ++ (ta, ea) :: (p2 ++ [(t, e)])) := by
      rw [hsplit] at hm
      simpa [List.append_assoc] using hm
    obtain ⟨_, _, hm2⟩ := mono_append p1 t0 (ta, ea) _ hm'
    -- the same run, seen from the state right after the alarm
    have hrun1 : run H s0 tr = run H ((run H s0 p1).step H ta ea) p2 := by
      rw [hsplit, run_append]; rfl
    have hrun2 : run H s0 (tr ++ [(t, e)]) = run H ((run H s0 p1).step H ta ea) (p2 ++ [(t, e)]) := by
      rw [hsplit, List.append_assoc, run_append]; rfl
    rw [hrun1, hrun2] at hne
    obtain ⟨i, d, _, _, _, hlo, hhi⟩ :=
      W3_code_change H ((run H s0 p1).step H ta ea) ta p2 t e hm2 hia hne
    calc satAdd ta D ≤ satAdd ta D1 := satAdd_mono (Nat.le_refl _) hle1
      _ = safeUntil (run H s0 p1).up ta := (quiet_safeUntil hq1 hD1 ta).symm
      _ ≤ safeUntil ((run H s0 p1).step H ta ea).up ta := safeUntil_step H _ ta ea
      _ ≤ d.calledAt := hlo
      _ ≤ t := hhi

/-- **W5 (a quiet reading).** What a watcher who polls can rely on. If at block timestamp `t0`
    the plugin's state shows staging duration `D` and no alarm, then no `up_deploy_code` call
    succeeds before `t0 + D` (saturating at `u64::MAX`), whatever is called in between, visible
    to the watcher or not. -/
theorem W5_quiet_reading (s0 : Sys Code) (t0 D : Nat) (pre post : Trace Code)
    {now : Nat} {a : Bool} {h : String} {fc : Option FnCall}
    (hm : Mono t0 (pre ++ (now, Ev.call a (.deployCode h fc)) :: post))
    (hD : s0.up.dur = some D) (hq : alarm s0.up = false)
    {u' : Up Code} {eff : Option (Deploy Code)}
    (hdep : (run H s0 pre).up.call H now a (.deployCode h fc) = .ok (u', eff)) :
    satAdd t0 D ≤ now := by
  rw [← quiet_safeUntil hq hD t0]
  exact W3_no_deploy_before H s0 t0 pre post hm hdep

/-- **W5 (a quiet reading, the code itself).** If in addition no deploy batch is in flight at
    `t0`, the code on the account does not change before `t0 + D` (saturating at `u64::MAX`). -/
theorem W5_quiet_reading_code (s0 : Sys Code) (t0 D : Nat) (tr : Trace Code) (t : Nat) (e : Ev Code)
    (hm : Mono t0 (tr ++ [(t, e)])) (h0 : s0.inflight = [])
    (hD : s0.up.dur = some D) (hq : alarm s0.up = false)
    (hne : (run H s0 (tr ++ [(t, e)])).current ≠ (run H s0 tr).current) :
    satAdd t0 D ≤ t := by
  obtain ⟨_, d, _, _, _, hlo, hhi⟩ := W3_code_change H s0 t0 tr t e hm h0 hne
  rw [← quiet_safeUntil hq hD t0]
  exact Nat.le_trans hlo hhi

/-- **W5 (a quiet reading, the code itself, from any state).** Without the assumption that
    nothing is in flight: if the code on the account changes before `t0 + D`, the deploy batch
    that changed it was already in flight at `t0` — created by an `up_deploy_code` call made
    before the reading. -/
theorem W5_quiet_reading_code_any (s0 : Sys Code) (t0 D : Nat) (tr : Trace Code) (t : Nat)
    (e : Ev Code) (hm : Mono t0 (tr ++ [(t, e)]))
    (hD : s0.up.dur = some D) (hq : alarm s0.up = false)
    (hne : (run H s0 (tr ++ [(t, e)])).current ≠ (run H s0 tr).current) :
    ∃ i d, e = .batch i true ∧ (run H s0 tr).inflight[i]? = some d ∧
      (d ∈ s0.inflight ∨ satAdd t0 D ≤ t) := by
  obtain ⟨i, d, he, hget, _, hor⟩ := W3_code_change_any H s0 t0 tr t e hm hne
  refine ⟨i, d, he, hget, ?_⟩
  rcases hor with h1 | ⟨hlo, hhi⟩
  · exact Or.inl h1
  · rw [quiet_safeUntil hq hD t0] at hlo
    exact Or.inr (Nat.le_trans hlo hhi)

/-- **W5 (polling, the deploy call).** A watcher reads a quiet state with duration `D` at `t0`
    and reads again no later than `P` after; an exit takes at most `T`; `P + T ≤ D` and
    `t0 + D` fits in u64. Then an exit started at the second reading at the latest is over no
    later than any successful `up_deploy_code` call — whatever that second reading shows and
    whatever happened between the readings. The premises on `start` and `done` are the
    assumption about the watcher and the host contract; nothing about them is proved here. -/
theorem W5_polling_call (s0 : Sys Code) (t0 D P T : Nat) (pre post : Trace Code)
    {now : Nat} {a : Bool} {h : String} {fc : Option FnCall}
    (hm : Mono t0 (pre ++ (now, Ev.call a (.deployCode h fc)) :: post))
    (hD : s0.up.dur = some D) (hq : alarm s0.up = false) (hPT : P + T ≤ D)
    {u' : Up Code} {eff : Option (Deploy Code)}
    (hdep : (run H s0 pre).up.call H now a (.deployCode h fc) = .ok (u', eff))
    (start done : Nat) (hstart : start ≤ t0 + P) (hdone : done ≤ start + T)
    (hfit : t0 + D ≤ U64_MAX) : done ≤ now := by
  have h1 := W5_quiet_reading H s0 t0 D pre post hm hD hq hdep
  rw [satAdd_exact hfit] at h1
  omega

/-- **W5 (polling, the code itself).** The same for the event that changes the code, under the
    additional hypothesis that no deploy batch is in flight at the first reading (`h0`; the
    views do not show one, see `W5_quiet_reading_code_any`), and with `t0 + D` fitting in u64.
    The premises on `start` and `done` are assumed, not proved. -/
theorem W5_polling (s0 : Sys Code) (t0 D P T : Nat) (tr : Trace Code) (t : Nat) (e : Ev Code)
    (hm : Mono t0 (tr ++ [(t, e)])) (h0 : s0.inflight = [])
    (hD : s0.up.dur = some D) (hq : alarm s0.up = false) (hPT : P + T ≤ D)
    (hne : (run H s0 (tr ++ [(t, e)])).current ≠ (run H s0 tr).current)
    (start done : Nat) (hstart : start ≤ t0 + P) (hdone : done ≤ start + T)
    (hfit : t0 + D ≤ U64_MAX) : done ≤ t := by
  have h := W5_quiet_reading_code H s0 t0 D tr t e hm h0 hD hq hne
  rw [satAdd_exact hfit] at h
  omega

/-- **W5 (exit window).** `W5_notice` with the arithmetic of an exit added. The conclusion is
    conditional on `exitDone ≤ ta + T`: an exit started when the alarm is raised (at `ta`) is
    complete by `ta + T`. That premise is an assumption about the host contract and about the
    watcher (who must see the alarm at `ta`); it is not derived from anything in the model.
    With it and `T ≤ D`, the exit is over no later than the block timestamp of any successful
    `up_deploy_code` call. -/
theorem W5_exit_window (s0 : Sys Code) (t0 D T : Nat) (pre post : Trace Code)
    {now : Nat} {a : Bool} {h : String} {fc : Option FnCall}
    (hm : Mono t0 (pre ++ (now, Ev.call a (.deployCode h fc)) :: post))
    (hD : s0.up.dur = some D) (hq : alarm s0.up = false) (hT : T ≤ D)
    {u' : Up Code} {eff : Option (Deploy Code)}
    (hdep : (run H s0 pre).up.call H now a (.deployCode h fc) = .ok (u', eff)) :
    ∃ p1 ta e p2, pre = p1 ++ (ta, e) :: p2 ∧
      (∀ q r, p1 = q ++ r → alarm (run H s0 q).up = false) ∧
      alarm (run H s0 (p1 ++ [(ta, e)])).up = true ∧
      ∀ exitDone, exitDone ≤ ta + T → ta + D ≤ U64_MAX → exitDone ≤ now := by
  obtain ⟨p1, ta, e, p2, hsplit, hquiet, ha, hle⟩ := W5_notice H s0 t0 D pre post hm hD hq hdep
  refine ⟨p1, ta, e, p2, hsplit, hquiet, ha, ?_⟩
  intro exitDone hexit hfit
  rw [satAdd_exact hfit] at hle
  omega

/-- **W5 (exit before the code changes).** `W5_code_change` with the same conditional premise
    as `W5_exit_window` (an exit started at the alarm takes at most `T ≤ D`; assumed, not
    proved): the exit is over no later than the block timestamp of the event that changes the
    code. -/
theorem W5_exit_before_code_change (s0 : Sys Code) (t0 D T : Nat) (tr : Trace Code) (t : Nat)
    (e : Ev Code) (hm : Mono t0 (tr ++ [(t, e)])) (h0 : s0.inflight = [])
    (hD : s0.up.dur = some D) (hq : alarm s0.up = false) (hT : T ≤ D)
    (hne : (run H s0 (tr ++ [(t, e)])).current ≠ (run H s0 tr).current) :
    ∃ p1 ta ea p2, tr = p1 ++ (ta, ea) :: p2 ∧
      (∀ q r, p1 = q ++ r → alarm (run H s0 q).up = false) ∧
      alarm (run H s0 (p1 ++ [(ta, ea)])).up = true ∧
      ∀ exitDone, exitDone ≤ ta + T → ta + D ≤ U64_MAX → exitDone ≤ t := by
  obtain ⟨p1, ta, ea, p2, hsplit, hquiet, ha, hle⟩ := W5_code_change H s0 t0 D tr t e hm h0 hD hq hne
  refine ⟨p1, ta, ea, p2, hsplit, hquiet, ha, ?_⟩
  intro exitDone hexit hfit
  rw [satAdd_exact hfit] at hle
  omega

end UpgradeWindow
