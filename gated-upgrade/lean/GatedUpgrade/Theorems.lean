/-
  GatedUpgrade.Theorems — what the gate guarantees, about the model in `Model.lean`.

  Main statement (`gated_code_change`): from a quiet state, along any trace in which no receipt
  calling a plugin or `acl_*` method has the contract account as predecessor, every change of
  the code on the account
  * is the successful execution of a deploy batch,
  * created by a callback `on_certificates`,
  * for a registry call the registry executed earlier, at a moment when it held a certificate
    for the hash of the new code that was not revoked, of the accepted kind, from an accepted
    attestor,
  * and the new code was staged at least the staging duration before the callback's deploy call
    and was the staged code, under its hash, at every moment in between.

  The kit's theorems (`UpgradeWindow.Theorems`) are used through the projection of a run onto
  the plugin-level trace (`projTrace`, `grun_sys`).
-/
import UpgradeWindow.Theorems
import GatedUpgrade.Model

namespace GatedUpgrade
open UpgradeWindow

variable {Code : Type} (cfg : Cfg) (H : Code → String)

/-! ## Sets -/

theorem mem_addTo {l : List String} {x y : String} (h : y ∈ addTo l x) : y ∈ l ∨ y = x := by
  unfold addTo at h
  split at h
  · exact Or.inl h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)

theorem mem_removeFrom {l : List String} {x y : String} (h : y ∈ removeFrom l x) : y ∈ l :=
  (List.mem_filter.mp h).1

/-! ## Access control -/

theorem not_superAdmin {a : Acl} {caller : String} (hinv : AclInv cfg a) (hne : caller ≠ cfg.self) :
    a.isSuperAdmin caller = false := by
  unfold Acl.isSuperAdmin
  exact decide_eq_false (fun h => hne (hinv.1 caller h))

theorem not_admin {a : Acl} {caller : String} (hinv : AclInv cfg a) (hne : caller ≠ cfg.self)
    (r : Role) : a.isAdmin r caller = false := by
  unfold Acl.isAdmin
  exact decide_eq_false (fun h => hne (h.elim (hinv.1 caller) (hinv.2.1 r caller)))

/-- An `acl_*` call by anybody but the contract account keeps the invariant: the calls that
    need a permission are refused, and the two that do not only remove the caller's own. -/
theorem aclInv_apply {a : Acl} {caller : String} (op : AclOp) (hinv : AclInv cfg a)
    (hne : caller ≠ cfg.self) : AclInv cfg (a.apply cfg.self caller op) := by
  have hsa := not_superAdmin cfg hinv hne
  have had := fun r => not_admin cfg hinv hne r
  cases op with
  | initSuperAdmin x =>
    have : ¬ (caller = cfg.self ∧ a.superAdmins = []) := fun h => hne h.1
    simp only [Acl.apply, this, ite_false]; exact hinv
  | addSuperAdmin x => simp only [Acl.apply, hsa]; exact hinv
  | revokeSuperAdmin x => simp only [Acl.apply, hsa]; exact hinv
  | transferSuperAdmin x => simp only [Acl.apply, hsa]; exact hinv
  | addAdmin r x => simp only [Acl.apply, had r]; exact hinv
  | revokeAdmin r x => simp only [Acl.apply, had r]; exact hinv
  | grantRole r x => simp only [Acl.apply, had r]; exact hinv
  | revokeRole r x => simp only [Acl.apply, had r]; exact hinv
  | renounceAdmin r =>
    refine ⟨hinv.1, ?_, hinv.2.2.1, hinv.2.2.2⟩
    intro r' x hx
    simp only [Acl.apply, setRole] at hx
    split at hx
    · exact hinv.2.1 r x (mem_removeFrom hx)
    · exact hinv.2.1 r' x hx
  | renounceRole r =>
    refine ⟨hinv.1, hinv.2.1, ?_, ?_⟩
    · intro x hx
      simp only [Acl.apply, setRole] at hx
      split at hx
      · rename_i heq
        subst heq
        exact hinv.2.2.1 x (mem_removeFrom hx)
      · exact hinv.2.2.1 x hx
    · intro x hx
      simp only [Acl.apply, setRole] at hx
      split at hx
      · rename_i heq
        subst heq
        exact hinv.2.2.2 x (mem_removeFrom hx)
      · exact hinv.2.2.2 x hx

/-- Under the invariant, the access-control check of every protected method other than
    `up_stage_code` fails for every account but the contract's own. -/
theorem not_allowed {a : Acl} {caller : String} (hinv : AclInv cfg a) (hne : caller ≠ cfg.self)
    (c : Call Code) (hc : roleFor c ≠ .codeStager) : a.allowed caller c = false := by
  unfold Acl.allowed Acl.hasRole
  apply decide_eq_false
  intro h
  cases hr : roleFor c with
  | codeStager => exact hc hr
  | codeDeployer => rw [hr] at h; exact hne (hinv.2.2.1 caller h)
  | durationManager => rw [hr] at h; exact hne (hinv.2.2.2 caller h)

/-! ## One event -/

/-- The plugin part of a step is the kit's step on the projected event. -/
theorem step_sys (s : GSys Code) (t : Nat) (e : GEv Code) :
    (s.step cfg H t e).sys = s.sys.step H t (s.evOf cfg e) := by
  cases e with
  | plugin caller c => rfl
  | acl caller op => rfl
  | deployCertified =>
    simp only [GSys.step, GSys.evOf, Sys.step]
    split
    · split <;> rfl
    · rfl
  | regAnswer i ok =>
    simp only [GSys.step, GSys.evOf, Sys.step]
    split <;> rfl
  | callback j ok =>
    simp only [GSys.step, GSys.evOf]
    cases s.answers[j]? with
    | none => rfl
    | some a =>
      obtain ⟨h, res⟩ := a
      simp only []
      split <;> rfl
  | batch i ok => rfl
  | regSet r => rfl
  | other => rfl

/-- Only `acl_*` calls change the access-control state. -/
theorem step_acl (s : GSys Code) (t : Nat) (e : GEv Code) :
    (s.step cfg H t e).acl = s.acl ∨
    ∃ caller op, e = .acl caller op ∧ (s.step cfg H t e).acl = s.acl.apply cfg.self caller op := by
  cases e with
  | plugin caller c => exact Or.inl rfl
  | acl caller op => exact Or.inr ⟨caller, op, rfl, rfl⟩
  | deployCertified =>
    refine Or.inl ?_
    simp only [GSys.step]
    split
    · split <;> rfl
    · rfl
  | regAnswer i ok =>
    refine Or.inl ?_
    simp only [GSys.step]
    split <;> rfl
  | callback j ok =>
    refine Or.inl ?_
    simp only [GSys.step]
    cases s.answers[j]? with
    | none => rfl
    | some a =>
      obtain ⟨h, res⟩ := a
      simp only []
      split <;> rfl
  | batch i ok => exact Or.inl rfl
  | regSet r => exact Or.inl rfl
  | other => exact Or.inl rfl

theorem aclInv_step {s : GSys Code} {t : Nat} {e : GEv Code} (hinv : AclInv cfg s.acl)
    (hext : ExternalEv cfg e) : AclInv cfg (s.step cfg H t e).acl := by
  rcases step_acl cfg H s t e with h | ⟨caller, op, he, h⟩
  · rw [h]; exact hinv
  · rw [h]; subst he; exact aclInv_apply cfg op hinv hext

/-- Only a registry event changes the registry's certificates. -/
theorem step_reg (s : GSys Code) (t : Nat) (e : GEv Code) (hn : ∀ r, e ≠ .regSet r) :
    (s.step cfg H t e).reg = s.reg := by
  cases e with
  | plugin caller c => rfl
  | acl caller op => rfl
  | deployCertified =>
    simp only [GSys.step]
    split
    · split <;> rfl
    · rfl
  | regAnswer i ok =>
    simp only [GSys.step]
    split <;> rfl
  | callback j ok =>
    simp only [GSys.step]
    cases s.answers[j]? with
    | none => rfl
    | some a =>
      obtain ⟨h, res⟩ := a
      simp only []
      split <;> rfl
  | batch i ok => rfl
  | regSet r => exact absurd rfl (hn r)
  | other => rfl

/-- Where an answer on its way to the callback comes from: it was there before the event, or the
    event is the registry executing a call in flight, and the answer is what the registry holds
    at that moment for the hash asked about (or a failure). -/
theorem step_answers_mem (s : GSys Code) (t : Nat) (e : GEv Code)
    (a : String × Option (List Cert)) (ha : a ∈ (s.step cfg H t e).answers) :
    a ∈ s.answers ∨
    ∃ i ok h, e = .regAnswer i ok ∧ s.queries[i]? = some h ∧
      a = (h, if ok = true then some (Reg.answer s.reg h cfg.kind) else none) := by
  cases e with
  | plugin caller c => exact Or.inl ha
  | acl caller op => exact Or.inl ha
  | deployCertified =>
    refine Or.inl ?_
    simp only [GSys.step] at ha
    split at ha
    · split at ha <;> exact ha
    · exact ha
  | regAnswer i ok =>
    simp only [GSys.step] at ha
    cases hq : s.queries[i]? with
    | none => rw [hq] at ha; exact Or.inl ha
    | some h =>
      rw [hq] at ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr ⟨i, ok, h, rfl, hq, ha⟩
  | callback j ok =>
    refine Or.inl ?_
    simp only [GSys.step] at ha
    cases hj : s.answers[j]? with
    | none => rw [hj] at ha; exact ha
    | some b =>
      obtain ⟨h, res⟩ := b
      rw [hj] at ha
      simp only [] at ha
      split at ha <;> exact List.mem_of_mem_eraseIdx ha
  | batch i ok => exact Or.inl ha
  | regSet r => exact Or.inl ha
  | other => exact Or.inl ha

/-- Which events the plugin sees as a call of a protected method: an external call of that
    method — permitted only if the method is `up_stage_code` — or a successful callback on an
    accepted answer, which is `up_deploy_code(hash, None)` for the hash asked about. -/
theorem evOf_call {s : GSys Code} {e : GEv Code} {a : Bool} {c : Call Code}
    (hinv : AclInv cfg s.acl) (hext : ExternalEv cfg e) (hev : s.evOf cfg e = .call a c) :
    (∃ who, e = .plugin who c ∧ a = s.acl.allowed who c ∧ (a = true → roleFor c = .codeStager)) ∨
    (∃ j h res, e = .callback j true ∧ c = .deployCode h none ∧
      s.answers[j]? = some (h, res) ∧ accepts cfg h res = true) := by
  cases e with
  | plugin who c' =>
    simp only [GSys.evOf, Ev.call.injEq] at hev
    obtain ⟨ha, hc⟩ := hev
    subst hc
    refine Or.inl ⟨who, rfl, ha.symm, ?_⟩
    intro hat
    cases hr : roleFor c' with
    | codeStager => rfl
    | codeDeployer =>
      rw [not_allowed cfg hinv hext c' (by rw [hr]; exact fun h => by cases h)] at ha
      rw [hat] at ha; cases ha
    | durationManager =>
      rw [not_allowed cfg hinv hext c' (by rw [hr]; exact fun h => by cases h)] at ha
      rw [hat] at ha; cases ha
  | acl caller op => simp [GSys.evOf] at hev
  | deployCertified => simp [GSys.evOf] at hev
  | regAnswer i ok => simp [GSys.evOf] at hev
  | callback j ok =>
    simp only [GSys.evOf] at hev
    cases hj : s.answers[j]? with
    | none => rw [hj] at hev; cases hev
    | some b =>
      obtain ⟨h, res⟩ := b
      rw [hj] at hev
      simp only [] at hev
      split at hev
      · rename_i hcond
        simp only [Ev.call.injEq] at hev
        obtain ⟨hok, hacc⟩ := hcond
        subst hok
        exact Or.inr ⟨j, h, res, rfl, hev.2.symm, hj, hacc⟩
      · cases hev
  | batch i ok => simp [GSys.evOf] at hev
  | regSet r => simp [GSys.evOf] at hev
  | other => simp [GSys.evOf] at hev

/-- The plugin sees a deploy batch only when the event is that batch. -/
theorem evOf_batch {s : GSys Code} {e : GEv Code} {i : Nat} {ok : Bool}
    (hev : s.evOf cfg e = .batch i ok) : e = .batch i ok := by
  cases e with
  | plugin who c => simp [GSys.evOf] at hev
  | acl caller op => simp [GSys.evOf] at hev
  | deployCertified => simp [GSys.evOf] at hev
  | regAnswer i ok => simp [GSys.evOf] at hev
  | callback j ok' =>
    simp only [GSys.evOf] at hev
    cases hj : s.answers[j]? with
    | none => rw [hj] at hev; cases hev
    | some b =>
      obtain ⟨h, res⟩ := b
      rw [hj] at hev
      simp only [] at hev
      split at hev <;> cases hev
  | batch i' ok' =>
    simp only [GSys.evOf, Ev.batch.injEq] at hev
    rw [hev.1, hev.2]
  | regSet r => simp [GSys.evOf] at hev
  | other => simp [GSys.evOf] at hev

/-- A permitted `up_deploy_code` is never an external call: it is a successful callback on an
    accepted answer, for the hash that answer is about, with no function call attached. -/
theorem evOf_deploy {s : GSys Code} {e : GEv Code} {h : String} {fc : Option FnCall}
    (hinv : AclInv cfg s.acl) (hext : ExternalEv cfg e)
    (hev : s.evOf cfg e = .call true (.deployCode h fc)) :
    fc = none ∧ ∃ j res, e = .callback j true ∧ s.answers[j]? = some (h, res) ∧
      accepts cfg h res = true := by
  rcases evOf_call cfg hinv hext hev with ⟨who, _, _, hrole⟩ | ⟨j, h', res, he, hc, hans, hacc⟩
  · have := hrole rfl
    simp [roleFor] at this
  · simp only [Call.deployCode.injEq] at hc
    obtain ⟨hh, hfc⟩ := hc
    subst hh hfc
    exact ⟨rfl, j, res, he, hans, hacc⟩

/-- A permitted `up_stage_code` is an external call by an account that passes the check. -/
theorem evOf_stage {s : GSys Code} {e : GEv Code} {x : Option Code}
    (hinv : AclInv cfg s.acl) (hext : ExternalEv cfg e)
    (hev : s.evOf cfg e = .call true (.stageCode x)) :
    ∃ who, e = .plugin who (.stageCode x) ∧ s.acl.allowed who (.stageCode x : Call Code) = true := by
  rcases evOf_call cfg hinv hext hev with ⟨who, he, ha, _⟩ | ⟨j, h', res, _, hc, _, _⟩
  · exact ⟨who, he, ha.symm⟩
  · cases hc

/-- No event changes the staging duration: the three duration methods are refused for everybody
    who can call them. -/
theorem dur_step {s : GSys Code} {t : Nat} {e : GEv Code} (hinv : AclInv cfg s.acl)
    (hext : ExternalEv cfg e) : (s.step cfg H t e).sys.up.dur = s.sys.up.dur := by
  rw [step_sys]
  rcases step_up H s.sys t (s.evOf cfg e) with h | ⟨a, c, eff, hev, hc⟩
  · rw [h]
  · apply Classical.byContradiction
    intro hne
    have hat : a = true := (call_inv H hc).1
    subst hat
    rcases evOf_call cfg hinv hext hev with ⟨who, _, _, hrole⟩ | ⟨j, h', res, _, hc', _, _⟩
    · have hr := hrole rfl
      rcases W3a_duration_change H hc hne with ⟨d, hcd, _⟩ | ⟨t', nd, hcd, _⟩
      · subst hcd; simp [roleFor] at hr
      · subst hcd; simp [roleFor] at hr
    · rcases W3a_duration_change H hc hne with ⟨d, hcd, _⟩ | ⟨t', nd, hcd, _⟩
      · rw [hcd] at hc'; cases hc'
      · rw [hcd] at hc'; cases hc'

/-! ## Traces -/

theorem grun_append (s : GSys Code) (p q : GTrace Code) :
    grun cfg H s (p ++ q) = grun cfg H (grun cfg H s p) q := by
  induction p generalizing s with
  | nil => rfl
  | cons x p ih => obtain ⟨t, e⟩ := x; exact ih _

theorem projTrace_append (s : GSys Code) (p q : GTrace Code) :
    projTrace cfg H s (p ++ q) = projTrace cfg H s p ++ projTrace cfg H (grun cfg H s p) q := by
  induction p generalizing s with
  | nil => rfl
  | cons x p ih =>
    obtain ⟨t, e⟩ := x
    show (t, s.evOf cfg e) :: projTrace cfg H (s.step cfg H t e) (p ++ q) = _
    rw [ih]; rfl

/-- **Projection.** The plugin part of a run of the gated vault is the kit's run on the
    plugin-level trace. -/
theorem grun_sys (s : GSys Code) (tr : GTrace Code) :
    (grun cfg H s tr).sys = run H s.sys (projTrace cfg H s tr) := by
  induction tr generalizing s with
  | nil => rfl
  | cons x tr ih =>
    obtain ⟨t, e⟩ := x
    show (grun cfg H (s.step cfg H t e) tr).sys = run H (s.sys.step H t (s.evOf cfg e)) _
    rw [ih, step_sys]

/-- Splitting the plugin-level trace splits the trace. -/
theorem projTrace_split : ∀ (pre : Trace Code) (s : GSys Code) (tr : GTrace Code)
    (x : Nat × Ev Code) (post : Trace Code),
    projTrace cfg H s tr = pre ++ x :: post →
    ∃ ps t e pt, tr = ps ++ (t, e) :: pt ∧ projTrace cfg H s ps = pre ∧
      x = (t, (grun cfg H s ps).evOf cfg e) ∧
      projTrace cfg H ((grun cfg H s ps).step cfg H t e) pt = post
  | [], s, tr, x, post, h => by
    cases tr with
    | nil => simp [projTrace] at h
    | cons y rest =>
      obtain ⟨t, e⟩ := y
      simp only [projTrace, List.nil_append, List.cons.injEq] at h
      exact ⟨[], t, e, rest, rfl, rfl, h.1.symm, h.2⟩
  | z :: pre, s, tr, x, post, h => by
    cases tr with
    | nil => simp [projTrace] at h
    | cons y rest =>
      obtain ⟨t, e⟩ := y
      simp only [projTrace, List.cons_append, List.cons.injEq] at h
      obtain ⟨ps, t', e', pt, h1, h2, h3, h4⟩ :=
        projTrace_split pre (s.step cfg H t e) rest x post h.2
      refine ⟨(t, e) :: ps, t', e', pt, by rw [h1]; rfl, ?_, h3, h4⟩
      show (t, s.evOf cfg e) :: projTrace cfg H (s.step cfg H t e) ps = z :: pre
      rw [h2, h.1]

theorem gmono_start : ∀ (tr : GTrace Code) (t0 : Nat), GMono t0 tr → ∀ x ∈ tr, t0 ≤ x.1
  | [], _, _, _, hx => by cases hx
  | (t, _) :: rest, _, hm, x, hx => by
    rcases List.mem_cons.mp hx with hx | hx
    · rw [hx]; exact hm.1
    · exact Nat.le_trans hm.1 (gmono_start rest t hm.2 x hx)

/-- In a trace with non-decreasing block timestamps, everything before an event is not later
    and everything after it is not earlier. -/
theorem gmono_split : ∀ (p : GTrace Code) (t0 : Nat) (x : Nat × GEv Code) (q : GTrace Code),
    GMono t0 (p ++ x :: q) → (∀ y ∈ p, y.1 ≤ x.1) ∧ t0 ≤ x.1 ∧ (∀ y ∈ q, x.1 ≤ y.1)
  | [], _, (t, _), q, hm => ⟨fun _ hy => (nomatch hy), hm.1, gmono_start q t hm.2⟩
  | (t1, _) :: p, _, x, q, hm => by
    obtain ⟨h1, h2, h3⟩ := gmono_split p t1 x q hm.2
    refine ⟨?_, Nat.le_trans hm.1 h2, h3⟩
    intro y hy
    rcases List.mem_cons.mp hy with hy | hy
    · rw [hy]; exact h2
    · exact h1 y hy

/-- The plugin-level trace up to an event has non-decreasing block timestamps too. -/
theorem mono_proj_snoc : ∀ (pa : GTrace Code) (s : GSys Code) (t0 tc : Nat) (e' : GEv Code)
    (rest : GTrace Code) (ev : Ev Code),
    GMono t0 (pa ++ (tc, e') :: rest) → Mono t0 (projTrace cfg H s pa ++ [(tc, ev)])
  | [], _, _, _, _, _, _, hm => ⟨hm.1, trivial⟩
  | (t1, e1) :: pa, s, _, tc, e', rest, ev, hm =>
    ⟨hm.1, mono_proj_snoc pa (s.step cfg H t1 e1) t1 tc e' rest ev hm.2⟩

/-- **The access-control invariant is preserved** along any trace in which no receipt calling a
    plugin or `acl_*` method has the contract account as predecessor. -/
theorem aclInv_run : ∀ (tr : GTrace Code) (s0 : GSys Code), AclInv cfg s0.acl → External cfg tr →
    AclInv cfg (grun cfg H s0 tr).acl
  | [], _, hinv, _ => hinv
  | (t, e) :: rest, s0, hinv, hext =>
    aclInv_run rest (s0.step cfg H t e)
      (aclInv_step cfg H hinv (hext (t, e) (List.mem_cons_self ..)))
      (fun x hx => hext x (List.mem_cons_of_mem _ hx))

/-- **No direct deployment, no change of the delay, by anybody.** After any such trace, the
    access-control check of `up_deploy_code` and of the three duration methods fails for every
    account other than the contract's own. -/
theorem external_not_allowed (s0 : GSys Code) (tr : GTrace Code) (hinv : AclInv cfg s0.acl)
    (hext : External cfg tr) (caller : String) (hne : caller ≠ cfg.self) (c : Call Code)
    (hc : roleFor c ≠ .codeStager) : (grun cfg H s0 tr).acl.allowed caller c = false :=
  not_allowed cfg (aclInv_run cfg H tr s0 hinv hext) hne c hc

/-- **The staging duration never changes** along such a trace. -/
theorem dur_run : ∀ (tr : GTrace Code) (s0 : GSys Code), AclInv cfg s0.acl → External cfg tr →
    (grun cfg H s0 tr).sys.up.dur = s0.sys.up.dur
  | [], _, _, _ => rfl
  | (t, e) :: rest, s0, hinv, hext => by
    have h1 : ExternalEv cfg e := hext (t, e) (List.mem_cons_self ..)
    have h2 := dur_run rest (s0.step cfg H t e) (aclInv_step cfg H hinv h1)
      (fun x hx => hext x (List.mem_cons_of_mem _ hx))
    exact h2.trans (dur_step cfg H hinv h1)

/-- Without registry events the registry's certificates stay as they were. -/
theorem reg_run : ∀ (tr : GTrace Code) (s0 : GSys Code), (∀ x ∈ tr, ∀ r, x.2 ≠ GEv.regSet r) →
    (grun cfg H s0 tr).reg = s0.reg
  | [], _, _ => rfl
  | (t, e) :: rest, s0, hn => by
    have h1 := step_reg cfg H s0 t e (hn (t, e) (List.mem_cons_self ..))
    have h2 := reg_run rest (s0.step cfg H t e) (fun x hx => hn x (List.mem_cons_of_mem _ hx))
    exact h2.trans h1

/-! ## Where a deployment comes from -/

/-- (Plugin model.) A deploy batch in flight after an event was in flight before it, or the
    event is a successful `up_deploy_code` call that created it. -/
theorem sys_step_inflight (s : Sys Code) (t : Nat) (ev : Ev Code) (d : Deploy Code)
    (hd : d ∈ (s.step H t ev).inflight) :
    d ∈ s.inflight ∨ ∃ a h fc u', ev = .call a (.deployCode h fc) ∧
      s.up.call H t a (.deployCode h fc) = .ok (u', some d) := by
  cases ev with
  | call a c =>
    cases hr : s.up.call H t a c with
    | error err => simp only [Sys.step, hr] at hd; exact Or.inl hd
    | ok r =>
      obtain ⟨u, eff⟩ := r
      cases eff with
      | none => simp only [Sys.step, hr] at hd; exact Or.inl hd
      | some d' =>
        simp only [Sys.step, hr, List.mem_append, List.mem_singleton] at hd
        rcases hd with hd | hd
        · exact Or.inl hd
        · subst hd
          rcases call_inv H hr with ⟨_, h1 | h1 | h1 | h1 | h1⟩
          · rcases h1 with ⟨_, _, _, he⟩; cases he
          · rcases h1 with ⟨h', fc', ts, code, hx, _, _, _, _, _, _⟩
            subst hx
            exact Or.inr ⟨a, h', fc', u, rfl, hr⟩
          · rcases h1 with ⟨_, _, _, _, he⟩; cases he
          · rcases h1 with ⟨_, _, _, _, _, _, he⟩; cases he
          · rcases h1 with ⟨_, _, _, _, _, _, _, he⟩; cases he
  | batch i ok =>
    cases hi : s.inflight[i]? with
    | none => simp only [Sys.step, hi] at hd; exact Or.inl hd
    | some d' =>
      simp only [Sys.step, hi] at hd
      exact Or.inl (List.mem_of_mem_eraseIdx hd)
  | other => exact Or.inl hd

/-- (Plugin model.) An event that changes the code on the account is a deploy batch in flight
    executing successfully, and the new code is the batch's. -/
theorem sys_step_current (s : Sys Code) (t : Nat) (ev : Ev Code)
    (hne : (s.step H t ev).current ≠ s.current) :
    ∃ i d, ev = .batch i true ∧ s.inflight[i]? = some d ∧ (s.step H t ev).current = d.code := by
  cases ev with
  | call a c =>
    exfalso; apply hne
    cases hr : s.up.call H t a c with
    | error err => simp [Sys.step, hr]
    | ok r => obtain ⟨u, eff⟩ := r; cases eff <;> simp [Sys.step, hr]
  | other => exact absurd rfl hne
  | batch i ok =>
    cases hi : s.inflight[i]? with
    | none => simp [Sys.step, hi] at hne
    | some d =>
      cases ok with
      | false => simp [Sys.step, hi] at hne
      | true => exact ⟨i, d, rfl, hi, by simp [Sys.step, hi]⟩

/-- **Every deploy batch comes from a callback.** A deploy batch in flight after a trace was in
    flight at the start, or was created by a successful callback on an accepted answer: the
    plugin's `up_deploy_code(hash, None)` for the hash that answer is about. -/
theorem inflight_origin_g : ∀ (tr : GTrace Code) (s0 : GSys Code), AclInv cfg s0.acl →
    External cfg tr → ∀ d ∈ (grun cfg H s0 tr).sys.inflight,
      d ∈ s0.sys.inflight ∨
      ∃ pa pb tc j h res u', tr = pa ++ (tc, GEv.callback j true) :: pb ∧
        (grun cfg H s0 pa).answers[j]? = some (h, res) ∧ accepts cfg h res = true ∧
        (grun cfg H s0 pa).sys.up.call H tc true (.deployCode h none) = .ok (u', some d)
  | [], _, _, _, _, hd => Or.inl hd
  | (t, e) :: rest, s0, hinv, hext, d, hd => by
    have hext1 : ExternalEv cfg e := hext (t, e) (List.mem_cons_self ..)
    have hext2 : External cfg rest := fun x hx => hext x (List.mem_cons_of_mem _ hx)
    rcases inflight_origin_g rest (s0.step cfg H t e) (aclInv_step cfg H hinv hext1) hext2 d hd
      with h1 | ⟨pa, pb, tc, j, h, res, u', hsplit, hans, hacc, hcall⟩
    · rw [step_sys] at h1
      rcases sys_step_inflight H s0.sys t _ d h1 with h2 | ⟨a, h, fc, u', hev, hcall⟩
      · exact Or.inl h2
      · have ha : a = true := (call_inv H hcall).1
        subst ha
        obtain ⟨hfc, j, res, he, hans, hacc⟩ := evOf_deploy cfg hinv hext1 hev
        subst hfc he
        exact Or.inr ⟨[], rest, t, j, h, res, u', rfl, hans, hacc, hcall⟩
    · exact Or.inr ⟨(t, e) :: pa, pb, tc, j, h, res, u', by rw [hsplit]; rfl, hans, hacc, hcall⟩

/-- **Every answer comes from the registry.** An answer on its way to the callback after a trace
    was there at the start, or was produced by the registry executing a call in flight for that
    hash: it is what the registry held at that moment (or a failure). -/
theorem answers_origin : ∀ (tr : GTrace Code) (s0 : GSys Code),
    ∀ a ∈ (grun cfg H s0 tr).answers,
      a ∈ s0.answers ∨
      ∃ pq pr tq i ok h, tr = pq ++ (tq, GEv.regAnswer i ok) :: pr ∧
        (grun cfg H s0 pq).queries[i]? = some h ∧
        a = (h, if ok = true then some (Reg.answer (grun cfg H s0 pq).reg h cfg.kind) else none)
  | [], _, _, ha => Or.inl ha
  | (t, e) :: rest, s0, a, ha => by
    rcases answers_origin rest (s0.step cfg H t e) a ha
      with h1 | ⟨pq, pr, tq, i, ok, h, hsplit, hq, hpair⟩
    · rcases step_answers_mem cfg H s0 t e a h1 with h2 | ⟨i, ok, h, he, hq, hpair⟩
      · exact Or.inl h2
      · subst he
        exact Or.inr ⟨[], rest, t, i, ok, h, rfl, hq, hpair⟩
    · exact Or.inr ⟨(t, e) :: pq, pr, tq, i, ok, h, by rw [hsplit]; rfl, hq, hpair⟩

/-- What the callback accepts was in the registry: an accepted answer of the registry's view
    means the registry held an accepted certificate for that hash. -/
theorem certified_of_accepts {reg : List Cert} {h : String}
    (hacc : accepts cfg h (some (Reg.answer reg h cfg.kind)) = true) : Certified cfg reg h := by
  simp only [accepts, List.any_eq_true, decide_eq_true_eq] at hacc
  obtain ⟨c, hc, hrev, hhash, hkind, hatt⟩ := hacc
  exact ⟨c, (List.mem_filter.mp hc).1, hhash, hkind, hrev, hatt⟩

/-- **The gate (without time).** From a state with the access-control invariant, no deploy batch
    in flight and no registry answer on its way: an event that changes the code on the account
    is the successful execution of a deploy batch `d`; that batch was created by a successful
    callback, whose `up_deploy_code(H d.code, None)` call succeeded and read `d.code`; and the
    answer that callback consumed was produced by the registry executing a call for `H d.code`
    at a moment when it held an accepted certificate for that hash. -/
theorem code_change_origin (s0 : GSys Code) (tr : GTrace Code) (t : Nat) (e : GEv Code)
    (hacl : AclInv cfg s0.acl) (h0 : s0.sys.inflight = []) (ha0 : s0.answers = [])
    (hext : External cfg tr)
    (hne : (grun cfg H s0 (tr ++ [(t, e)])).sys.current ≠ (grun cfg H s0 tr).sys.current) :
    ∃ i d, e = .batch i true ∧ (grun cfg H s0 tr).sys.inflight[i]? = some d ∧
      (grun cfg H s0 (tr ++ [(t, e)])).sys.current = d.code ∧
      ∃ pa pb tc j u', tr = pa ++ (tc, GEv.callback j true) :: pb ∧
        (grun cfg H s0 pa).sys.up.call H tc true (.deployCode (H d.code) none) = .ok (u', some d) ∧
        d = ⟨d.code, none, tc⟩ ∧
        ∃ pq pr tq i', pa = pq ++ (tq, GEv.regAnswer i' true) :: pr ∧
          (grun cfg H s0 pq).queries[i']? = some (H d.code) ∧
          (grun cfg H s0 pa).answers[j]? =
            some (H d.code, some (Reg.answer (grun cfg H s0 pq).reg (H d.code) cfg.kind)) ∧
          Certified cfg (grun cfg H s0 pq).reg (H d.code) := by
  rw [grun_append] at hne ⊢
  simp only [grun] at hne ⊢
  rw [step_sys] at hne ⊢
  obtain ⟨i, d, hev, hi, hcur⟩ := sys_step_current H _ t _ hne
  have he := evOf_batch cfg hev
  have hmem : d ∈ (grun cfg H s0 tr).sys.inflight := List.mem_of_getElem? hi
  rcases inflight_origin_g cfg H tr s0 hacl hext d hmem
    with h1 | ⟨pa, pb, tc, j, h, res, u', hsplit, hans, hacc, hcall⟩
  · rw [h0] at h1; cases h1
  · obtain ⟨_, ts, code, _, _, _, hh, heff⟩ := deploy_ok H hcall
    have hd : d = ⟨code, none, tc⟩ := Option.some.inj heff
    have hmema : (h, res) ∈ (grun cfg H s0 pa).answers := List.mem_of_getElem? hans
    rcases answers_origin cfg H pa s0 _ hmema with h2 | ⟨pq, pr, tq, i', ok, h', hsplit2, hq, hpair⟩
    · rw [ha0] at h2; cases h2
    · have hcode : d.code = code := by rw [hd]
      have hh' : h = H d.code := by rw [hcode]; exact hh
      subst hh'
      simp only [Prod.mk.injEq] at hpair
      obtain ⟨hh2, hres⟩ := hpair
      subst hh2
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hres
        subst hres
        simp [accepts] at hacc
      | true =>
        simp only [ite_true] at hres
        subst hres
        refine ⟨i, d, he, hi, hcur, pa, pb, tc, j, u', hsplit, hcall, ?_, pq, pr, tq, i', hsplit2,
          hq, hans, certified_of_accepts cfg hacc⟩
        rw [hd]

/-! ## The main statements -/

/-- **G1 — every code change is a certified, announced deployment.**

    Start at block timestamp `t0` from a quiet state `s0` with staging duration `D` (`Fresh`: the
    access-control invariant, no deploy batch in flight, no registry answer on its way, nothing
    staged). Take any trace with non-decreasing block timestamps in which no receipt calling a
    plugin or `acl_*` method has the contract account as predecessor — otherwise any event, by
    anyone, in any order, with any receipt failing, and the registry changing arbitrarily.

    If the event `e` at block timestamp `t` changes the code on the account to `new`, then
    * `e` is the successful execution of a deploy batch;
    * the trace before it contains a successful callback at block timestamp `tc ≤ t`, whose
      `up_deploy_code(H new, None)` call succeeded and created that batch with the code `new`;
    * before that callback the registry executed, at `tq ≤ tc`, a call about `H new`; the answer
      the callback consumed is what the registry held at that moment; and at that moment the
      registry held a certificate for `H new` that was not revoked, of the accepted kind, from
      an accepted attestor;
    * before that callback, at `ts`, an account that passed the access-control check staged
      `new`, with `ts + D ≤ tc` (saturating at `u64::MAX`), and from that staging to the
      callback the view `up_staged_code_hash` showed `H new` at every moment;
    * `t0 + D ≤ tc`. -/
theorem gated_code_change (s0 : GSys Code) (t0 D : Nat) (tr : GTrace Code) (t : Nat)
    (e : GEv Code) (hfresh : Fresh cfg D s0)
    (hm : GMono t0 (tr ++ [(t, e)]))
    (hext : External cfg (tr ++ [(t, e)]))
    (hne : (grun cfg H s0 (tr ++ [(t, e)])).sys.current ≠ (grun cfg H s0 tr).sys.current) :
    ∃ new : Code, (grun cfg H s0 (tr ++ [(t, e)])).sys.current = new ∧
      (∃ i, e = GEv.batch i true) ∧
      ∃ pa pb tc j, tr = pa ++ (tc, GEv.callback j true) :: pb ∧ tc ≤ t ∧ satAdd t0 D ≤ tc ∧
        (∃ u', (grun cfg H s0 pa).sys.up.call H tc true (.deployCode (H new) none)
                = .ok (u', some ⟨new, none, tc⟩)) ∧
        (∃ pq pr tq i', pa = pq ++ (tq, GEv.regAnswer i' true) :: pr ∧ tq ≤ tc ∧
          (grun cfg H s0 pq).queries[i']? = some (H new) ∧
          (grun cfg H s0 pa).answers[j]? =
            some (H new, some (Reg.answer (grun cfg H s0 pq).reg (H new) cfg.kind)) ∧
          Certified cfg (grun cfg H s0 pq).reg (H new)) ∧
        (∃ ps pt ts who, pa = ps ++ (ts, GEv.plugin who (.stageCode (some new))) :: pt ∧
          (grun cfg H s0 ps).acl.allowed who (.stageCode (some new) : Call Code) = true ∧
          satAdd ts D ≤ tc ∧
          ∀ p q, pt = p ++ q →
            (grun cfg H s0 (ps ++ (ts, GEv.plugin who (.stageCode (some new))) :: p)).sys.up.stagedCodeHash H
              = some (H new)) := by
  have hext' : External cfg tr := fun x hx => hext x (List.mem_append_left _ hx)
  obtain ⟨i, d, he, _, hcur, pa, pb, tc, j, u', hsplit, hcall, hd, pq, pr, tq, i', hsplit2, hq,
    hans, hcert⟩ := code_change_origin cfg H s0 tr t e hfresh.acl hfresh.noBatch hfresh.noAnswer
      hext' hne
  -- time
  have hm' : GMono t0 (pa ++ (tc, GEv.callback j true) :: (pb ++ [(t, e)])) := by
    rw [hsplit] at hm; simpa using hm
  obtain ⟨hbefore, _, hafter⟩ := gmono_split pa t0 _ _ hm'
  have htc : tc ≤ t := hafter (t, e) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have htq : tq ≤ tc := hbefore (tq, GEv.regAnswer i' true) (by rw [hsplit2]; simp)
  -- the staging, through the kit's theorem on the plugin-level trace
  have hcall' : (run H s0.sys (projTrace cfg H s0 pa)).up.call H tc true
      (.deployCode (H d.code) none) = .ok (u', some d) := by rw [← grun_sys]; exact hcall
  obtain ⟨pre, post, ts, c, hsp, _, hdc, _, _, hdelay, hvis⟩ :=
    deploy_origin H s0.sys (projTrace cfg H s0 pa) hfresh.nothingStaged hcall'
  obtain ⟨ps, ts', ev, pt, hpa, hpre, hx, hpost⟩ := projTrace_split cfg H pre s0 pa _ post hsp
  simp only [Prod.mk.injEq] at hx
  obtain ⟨hts, hev⟩ := hx
  subst hts
  have hextpa : External cfg pa := fun x hx => hext' x (by rw [hsplit]; exact List.mem_append_left _ hx)
  have hextps : External cfg ps := fun x hx => hextpa x (by rw [hpa]; exact List.mem_append_left _ hx)
  have hinvps := aclInv_run cfg H ps s0 hfresh.acl hextps
  have hextev : ExternalEv cfg ev := hextpa (ts, ev) (by rw [hpa]; simp)
  obtain ⟨who, hevp, hallowed⟩ := evOf_stage cfg hinvps hextev hev.symm
  subst hevp
  have hdur : (run H s0.sys pre).up.dur = some D := by
    rw [← hpre, ← grun_sys, dur_run cfg H ps s0 hfresh.acl hextps]; exact hfresh.dur
  rw [hdur] at hdelay
  have hts0 : t0 ≤ ts := by
    have := gmono_start (tr ++ [(t, e)]) t0 hm (ts, GEv.plugin who (.stageCode (some c)))
      (by rw [hsplit, hpa]; simp)
    exact this
  subst hdc
  refine ⟨d.code, hcur, ⟨i, he⟩, pa, pb, tc, j, hsplit, htc,
    Nat.le_trans (satAdd_mono hts0 (Nat.le_refl D)) hdelay, ⟨u', by rw [← hd]; exact hcall⟩,
    ⟨pq, pr, tq, i', hsplit2, htq, hq, hans, hcert⟩,
    ⟨ps, pt, ts, who, hpa, hallowed, hdelay, ?_⟩⟩
  intro p q hpq
  have h1 := hvis (projTrace cfg H ((grun cfg H s0 ps).step cfg H ts
      (GEv.plugin who (.stageCode (some d.code)))) p)
    (projTrace cfg H (grun cfg H ((grun cfg H s0 ps).step cfg H ts
      (GEv.plugin who (.stageCode (some d.code)))) p) q)
    (by rw [← hpost, hpq, projTrace_append])
  rw [grun_sys, projTrace_append, hpre]
  show (run H s0.sys (pre ++ (ts, (grun cfg H s0 ps).evOf cfg
    (GEv.plugin who (.stageCode (some d.code)))) :: _)).up.stagedCodeHash H = _
  rw [← hev]
  exact h1

/-- **G2 — no certified deployment before `safeUntil` either.** The same from any state with
    the access-control invariant, no deploy batch in flight and no registry answer on its way —
    code may already be staged, and nothing is assumed about the staging duration. A change of
    the code is the successful execution of a deploy batch created by a successful callback at a
    block timestamp `tc` with `safeUntil s0 t0 ≤ tc ≤ t`, on a registry answer produced when the
    registry held an accepted certificate for the hash of the new code. -/
theorem gated_no_deploy_before (s0 : GSys Code) (t0 : Nat) (tr : GTrace Code) (t : Nat)
    (e : GEv Code) (hacl : AclInv cfg s0.acl) (h0 : s0.sys.inflight = []) (ha0 : s0.answers = [])
    (hm : GMono t0 (tr ++ [(t, e)]))
    (hext : External cfg (tr ++ [(t, e)]))
    (hne : (grun cfg H s0 (tr ++ [(t, e)])).sys.current ≠ (grun cfg H s0 tr).sys.current) :
    ∃ new : Code, (grun cfg H s0 (tr ++ [(t, e)])).sys.current = new ∧
      (∃ i, e = GEv.batch i true) ∧
      ∃ pa pb tc j, tr = pa ++ (tc, GEv.callback j true) :: pb ∧
        safeUntil s0.sys.up t0 ≤ tc ∧ tc ≤ t ∧
        (∃ u', (grun cfg H s0 pa).sys.up.call H tc true (.deployCode (H new) none)
                = .ok (u', some ⟨new, none, tc⟩)) ∧
        (∃ pq pr tq i', pa = pq ++ (tq, GEv.regAnswer i' true) :: pr ∧ tq ≤ tc ∧
          (grun cfg H s0 pq).queries[i']? = some (H new) ∧
          (grun cfg H s0 pa).answers[j]? =
            some (H new, some (Reg.answer (grun cfg H s0 pq).reg (H new) cfg.kind)) ∧
          Certified cfg (grun cfg H s0 pq).reg (H new)) := by
  have hext' : External cfg tr := fun x hx => hext x (List.mem_append_left _ hx)
  obtain ⟨i, d, he, _, hcur, pa, pb, tc, j, u', hsplit, hcall, hd, pq, pr, tq, i', hsplit2, hq,
    hans, hcert⟩ := code_change_origin cfg H s0 tr t e hacl h0 ha0 hext' hne
  have hm' : GMono t0 (pa ++ (tc, GEv.callback j true) :: (pb ++ [(t, e)])) := by
    rw [hsplit] at hm; simpa using hm
  obtain ⟨hbefore, _, hafter⟩ := gmono_split pa t0 _ _ hm'
  have htc : tc ≤ t := hafter (t, e) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have htq : tq ≤ tc := hbefore (tq, GEv.regAnswer i' true) (by rw [hsplit2]; simp)
  have hcall' : (run H s0.sys (projTrace cfg H s0 pa)).up.call H tc true
      (.deployCode (H d.code) none) = .ok (u', some d) := by rw [← grun_sys]; exact hcall
  have hsafe : safeUntil s0.sys.up t0 ≤ tc :=
    W3_no_deploy_before H s0.sys t0 (projTrace cfg H s0 pa) []
      (mono_proj_snoc cfg H pa s0 t0 tc _ _ _ hm') hcall'
  exact ⟨d.code, hcur, ⟨i, he⟩, pa, pb, tc, j, hsplit, hsafe, htc,
    ⟨u', by rw [← hd]; exact hcall⟩, ⟨pq, pr, tq, i', hsplit2, htq, hq, hans, hcert⟩⟩

/-- **G3 — uncertified code is never installed.** From a state with the access-control
    invariant, no deploy batch in flight and no registry answer on its way, along any trace in
    which no receipt calling a plugin or `acl_*` method has the contract account as predecessor:
    if at no moment of the trace the registry holds an accepted certificate for the hash `h`,
    then no event of the trace changes the code on the account to code with hash `h`. -/
theorem uncertified_never_installed (s0 : GSys Code) (tr : GTrace Code) (h : String)
    (hacl : AclInv cfg s0.acl) (h0 : s0.sys.inflight = []) (ha0 : s0.answers = [])
    (hext : External cfg tr)
    (hno : ∀ p q, tr = p ++ q → ¬ Certified cfg (grun cfg H s0 p).reg h) :
    ∀ p t e q, tr = p ++ (t, e) :: q →
      (grun cfg H s0 (p ++ [(t, e)])).sys.current ≠ (grun cfg H s0 p).sys.current →
      H (grun cfg H s0 (p ++ [(t, e)])).sys.current ≠ h := by
  intro p t e q hsplit hne heq
  have hextp : External cfg p := fun x hx => hext x (by rw [hsplit]; exact List.mem_append_left _ hx)
  obtain ⟨i, d, _, _, hcur, pa, pb, tc, j, u', hsplit1, _, _, pq, pr, tq, i', hsplit2, _, _,
    hcert⟩ := code_change_origin cfg H s0 p t e hacl h0 ha0 hextp hne
  rw [hcur] at heq
  rw [heq] at hcert
  exact hno pq ((tq, GEv.regAnswer i' true) :: pr ++ (tc, GEv.callback j true) :: pb ++ (t, e) :: q)
    (by rw [hsplit, hsplit1, hsplit2]; simp) hcert

/-- **G3, as a statement about the account.** Under the same hypotheses, if the code on the
    account does not have hash `h` at the start, it does not have hash `h` at any moment of the
    trace. -/
theorem uncertified_never_current (s0 : GSys Code) (tr : GTrace Code) (h : String)
    (hacl : AclInv cfg s0.acl) (h0 : s0.sys.inflight = []) (ha0 : s0.answers = [])
    (hext : External cfg tr)
    (hno : ∀ p q, tr = p ++ q → ¬ Certified cfg (grun cfg H s0 p).reg h)
    (hstart : H s0.sys.current ≠ h) :
    ∀ p q, tr = p ++ q → H (grun cfg H s0 p).sys.current ≠ h := by
  have key : ∀ (n : Nat) (p q : GTrace Code), p.length = n → tr = p ++ q →
      H (grun cfg H s0 p).sys.current ≠ h := by
    intro n
    induction n with
    | zero =>
      intro p q hlen _
      have hp : p = [] := List.eq_nil_of_length_eq_zero hlen
      subst hp; exact hstart
    | succ n ih =>
      intro p q hlen hsplit
      have hne : p ≠ [] := by intro hp; rw [hp] at hlen; cases hlen
      obtain ⟨p', x, rfl⟩ : ∃ p' x, p = p' ++ [x] :=
        ⟨p.dropLast, p.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
      obtain ⟨t, e⟩ := x
      have hlen' : p'.length = n := by simpa using hlen
      have hsplit' : tr = p' ++ (t, e) :: q := by rw [hsplit]; simp
      have ih' := ih p' ((t, e) :: q) hlen' hsplit'
      by_cases hch : (grun cfg H s0 (p' ++ [(t, e)])).sys.current = (grun cfg H s0 p').sys.current
      · rw [hch]; exact ih'
      · exact uncertified_never_installed cfg H s0 tr h hacl h0 ha0 hext hno p' t e q hsplit' hch
  intro p q hsplit
  exact key p.length p q rfl hsplit

/-- The state right after `new` is quiet. -/
theorem init_fresh (D : Nat) (code : Code) (stagers : List String) (reg : List Cert) :
    Fresh cfg D (GSys.init cfg D code stagers reg) where
  acl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx; simpa [GSys.init] using hx
    · intro r x hx; simp [GSys.init] at hx
    · intro x hx; simpa [GSys.init] using hx
    · intro x hx; simp [GSys.init] at hx
  noBatch := rfl
  noAnswer := rfl
  nothingStaged := rfl
  dur := rfl

end GatedUpgrade
