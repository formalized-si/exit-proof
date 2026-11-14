/-
  Statements about the strict world (`Intents/Strict.lean`).

  * refinement         `strict_refines`, `strict_reach`: every strict step is zero or more steps
                       of the world of `Intents/World.lean`, so T1–T3 hold in the strict world
                       (`strict_T1_backing`, `strict_T1_ledger_covered`)
  * T4 who can lower   `T4_authorised` (the six ways, with the authorisation of each),
                       `T4_calls` (where a pending refund comes from and that it is used once),
                       `T4_nonce_kept`, `T4_signed_by_holder` (with the assumption `Unforgeable`)
  * T4 the role table  `T4_role_power`, `T4_admin_power`, `T4_super_power`, `T4_role_change`,
                       `T4_roles_from_initial`, `T4_force_from_initial`,
                       `T4_super_admin_can_take_any_role`
  * T4 the auth flag   `T4_auth_flag_power`
  * two guards of the ledger functions that follow from the invariant in every reachable state:
                       `startWithdraw_amount_guard_redundant`, `moveBal_destination_guard_redundant`
-/
import Intents.Theorems
import Intents.Strict

namespace Intents
open ProvedFT

/-! ## Facts about the functions of `Intents/Auth.lean` -/

theorem ff_tt {P : Prop} {b : Bool} (h0 : b = false) (h1 : b = true) : P := by
  rw [h0] at h1; cases h1

theorem refund_le_amount (L : Ledger) (x : Xc) (req : Nat) : x.refund L req ≤ x.amount :=
  Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_right _ _)

theorem refund_le_bal (L : Ledger) (x : Xc) (req : Nat) : x.refund L req ≤ bal L.bals x.receiver :=
  Nat.min_le_right _ _

theorem refund_le_req (L : Ledger) (x : Xc) (req : Nat) : x.refund L req ≤ req :=
  Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_left _ _)

theorem resolveTransfer_some {L L' : Ledger} {x : Xc} {req : Nat}
    (h : resolveTransfer L x req = some L') :
    (x.refund L req = 0 ∧ L' = L) ∨
    (x.refund L req ≠ 0 ∧ moveBal L .refund x.receiver x.sender (x.refund L req) = some L') := by
  unfold resolveTransfer at h
  by_cases h0 : x.refund L req = 0
  · rw [ifP h0] at h; exact Or.inl ⟨h0, (Option.some.inj h).symm⟩
  · rw [ifN h0] at h; exact Or.inr ⟨h0, h⟩

/-- Only the source of an internal move loses, and at most the amount moved. -/
theorem moveBal_lower {L L' : Ledger} {auth : MoveAuth} {src dst u : Acct} {amt : Nat}
    (h : moveBal L auth src dst amt = some L') (hlt : bal L'.bals u < bal L.bals u) :
    u = src ∧ auth.ok L.ctl src = true ∧ bal L.bals u ≤ bal L'.bals u + amt := by
  obtain ⟨hne, _, hauth, hle, _, rfl⟩ := moveBal_some h
  by_cases hsu : src = u
  · subst hsu
    refine ⟨rfl, hauth, ?_⟩
    show bal L.bals src ≤ bal (set (set L.bals src (bal L.bals src - amt)) dst (bal L.bals dst + amt)) src + amt
    rw [bal_set_ne _ _ (Ne.symm hne), bal_set_self]
    omega
  · exfalso
    have hlt' : bal (set (set L.bals src (bal L.bals src - amt)) dst (bal L.bals dst + amt)) u
        < bal L.bals u := hlt
    by_cases hdu : dst = u
    · subst hdu; rw [bal_set_self] at hlt'; omega
    · rw [bal_set_ne _ _ hdu, bal_set_ne _ _ hsu] at hlt'; omega

theorem admit_spec {implicit : Key → Acct} {me : Acct} {now : Nat} {c : Ctl} {A : AuthSt}
    {p : Payload} (h : admit implicit me now c A p = true) :
    p.contract = me ∧ now ≤ p.deadline ∧ hasKey implicit A p.signer p.key = true ∧
    A.nonces.contains (p.signer, p.nonce) = false ∧ c.locked.contains p.signer = false := by
  unfold admit at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_false_iff_not,
    Nat.not_lt] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem addKey_nonces {implicit : Key → Acct} {c : Ctl} {A A' : AuthSt} {a : Acct} {k : Key}
    (h : addKey implicit c A a k = some A') : A'.nonces = A.nonces := by
  unfold addKey at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · obtain rfl := Option.some.inj h; rfl
      · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · obtain rfl := Option.some.inj h; rfl

theorem removeKey_nonces {implicit : Key → Acct} {c : Ctl} {A A' : AuthSt} {a : Acct} {k : Key}
    (h : removeKey implicit c A a k = some A') : A'.nonces = A.nonces := by
  unfold removeKey at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · exact absurd h (by simp)
      · obtain rfl := Option.some.inj h; rfl
    · split at h
      · obtain rfl := Option.some.inj h; rfl
      · exact absurd h (by simp)

theorem adminStep_roles (c : Ctl) (a : Admin) (h : ∀ r, a ≠ .acl r) :
    (adminStep c a).roles = c.roles := by
  cases a with
  | pause who key => simp only [adminStep]; split <;> rfl
  | unpause who key => simp only [adminStep]; split <;> rfl
  | lock who x => simp only [adminStep]; split <;> rfl
  | unlock who x => simp only [adminStep]; split <;> rfl
  | authOffSelf x => simp only [adminStep, setAuth]; (repeat' split) <;> rfl
  | authIntent x en => simp only [adminStep, setAuth]; (repeat' split) <;> rfl
  | authForce who x en => simp only [adminStep, setAuth]; (repeat' split) <;> rfl
  | acl r => exact absurd rfl (h r)

/-- A step of the world of `Intents/World.lean` other than a free change of the role table
    leaves the grantees as they are. -/
theorem step_roles (K : Cfg) (S : World) (st : Step) (h : ∀ r, st ≠ .admin (.acl r)) :
    (stdStep K S st).L.ctl.roles = S.L.ctl.roles := by
  by_cases ha : ∃ a, st = .admin a
  · obtain ⟨a, rfl⟩ := ha
    show (adminStep S.L.ctl a).roles = S.L.ctl.roles
    exact adminStep_roles _ _ (fun r e => h r (by rw [e]))
  · rw [T4_switches K S st (fun a e => ha ⟨a, e⟩)]

/-! ## The strict world refines the world of `Intents/World.lean` -/

theorem runOp_refines (G : SCfg) (ex : St → Rcpt → Option Out) (signer : Acct) (S S' : SWorld)
    (o : Op) (h : runOp G ex signer S o = some S') :
    S'.w = S.w ∨ ∃ st, S'.w = step G.base ex S.w st := by
  cases o with
  | withdraw w =>
    simp only [runOp] at h
    split at h
    · obtain rfl := Option.some.inj h; exact Or.inr ⟨.ftWithdraw .intent w, rfl⟩
    · exact absurd h (by simp)
  | move dst amt call =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i L' hm
      obtain rfl := Option.some.inj h
      refine Or.inr ⟨.move .owner signer dst amt, ?_⟩
      show _ = step G.base ex S.w (.move .owner signer dst amt)
      simp only [step, hm]
  | addKey k =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h; exact Or.inl rfl
  | removeKey k =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h; exact Or.inl rfl
  | setAuth en =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h; exact Or.inr ⟨.admin (.authIntent signer en), rfl⟩

theorem runOps_refines (G : SCfg) (ex : St → Rcpt → Option Out) (signer : Acct) :
    ∀ (ops : List Op) (S S' : SWorld), runOps G ex signer S ops = some S' →
      ∃ l, S'.w = run G.base ex S.w l := by
  intro ops
  induction ops with
  | nil =>
    intro S S' h
    have e : S = S' := by simpa [runOps] using h
    subst e
    exact ⟨[], rfl⟩
  | cons o t ih =>
    intro S S' h
    simp only [runOps] at h
    split at h
    · exact absurd h (by simp)
    · rename_i S1 h1
      obtain ⟨l, hl⟩ := ih S1 S' h
      rcases runOp_refines G ex signer S S1 o h1 with he | ⟨st, he⟩
      · exact ⟨l, by rw [hl, he]⟩
      · exact ⟨st :: l, by rw [hl, he]; rfl⟩

/-- **Refinement.** On the token, the ledger and everything in flight between them, a step of
    the strict world is zero or more steps of the world of `Intents/World.lean`. -/
theorem strict_refines (G : SCfg) (ex : St → Rcpt → Option Out) (S : SWorld) (st : SStep) :
    ∃ l, (sstep G ex S st).w = run G.base ex S.w l := by
  cases st with
  | base st0 =>
    simp only [sstep]
    split
    · exact ⟨[st0], rfl⟩
    · exact ⟨[], rfl⟩
  | transfer src dst amt call =>
    simp only [sstep]
    split
    · split
      · exact ⟨[], rfl⟩
      · rename_i L' hm
        refine ⟨[.move .owner src dst amt], ?_⟩
        show _ = step G.base ex S.w (.move .owner src dst amt)
        simp only [step, hm]
    · exact ⟨[], rfl⟩
  | forceTransfer who src dst amt call =>
    simp only [sstep]
    split
    · exact ⟨[], rfl⟩
    · rename_i L' hm
      refine ⟨[.move (.force who) src dst amt], ?_⟩
      show _ = step G.base ex S.w (.move (.force who) src dst amt)
      simp only [step, hm]
  | resolveTransfer k req =>
    simp only [sstep]
    split
    · exact ⟨[], rfl⟩
    · rename_i x hk
      split
      · exact ⟨[], rfl⟩
      · rename_i L' hr
        rcases resolveTransfer_some hr with ⟨_, rfl⟩ | ⟨_, hm⟩
        · exact ⟨[], rfl⟩
        · refine ⟨[.move .refund x.receiver x.sender (x.refund S.w.L req)], ?_⟩
          show _ = step G.base ex S.w (.move .refund x.receiver x.sender (x.refund S.w.L req))
          simp only [step, hm]
  | resolveTransferFails k => exact ⟨[], rfl⟩
  | payload now p sig =>
    simp only [sstep]
    split
    · split
      · exact ⟨[], rfl⟩
      · rename_i S' hr
        have hx := runOps_refines G ex p.signer p.ops { S with auth := commitNonce S.auth p } S' hr
        exact hx
    · exact ⟨[], rfl⟩
  | addKey a k =>
    simp only [sstep]
    split
    · exact ⟨[], rfl⟩
    · split <;> exact ⟨[], rfl⟩
  | removeKey a k =>
    simp only [sstep]
    split
    · exact ⟨[], rfl⟩
    · split <;> exact ⟨[], rfl⟩
  | acl c => exact ⟨[.admin (.acl (aclStep S.acl c).roles)], rfl⟩

/-- **Every reachable state of the strict world is a reachable state of the world of
    `Intents/World.lean`** on the part they share. So T1–T3 and everything else proved for
    `Reach` hold in the strict world. -/
theorem strict_reach {G : SCfg} {S0 S : SWorld} (h : SReach G S0 S) : Reach G.base S.w := by
  induction h with
  | init h => exact Reach.init _ h.base
  | step st _ ih =>
    obtain ⟨l, hl⟩ := strict_refines G (exec G.base.tok) _ st
    show Reach G.base (sstep G (exec G.base.tok) _ st).w
    rw [hl]
    exact reach_run ih l

theorem sreach_run {G : SCfg} {S0 S : SWorld} (h : SReach G S0 S) (l : List SStep) :
    SReach G S0 (srun G (exec G.base.tok) S l) := by
  induction l generalizing S with
  | nil => exact h
  | cons st t ih => exact ih (SReach.step st h)

/-- T1 in the strict world. -/
theorem strict_T1_backing {G : SCfg} {S0 S : SWorld} (h : SReach G S0 S) :
    total S.w.L.bals + debitedInFlight S.w + uncredited S.w ≤
      bal S.w.c.accts G.base.me + movedOut S.w :=
  T1_backing G.base S.w (strict_reach h)

/-- T1, the plain reading, in the strict world. -/
theorem strict_T1_ledger_covered {G : SCfg} {S0 S : SWorld} (h : SReach G S0 S) :
    total S.w.L.bals ≤ bal S.w.c.accts G.base.me :=
  T1_ledger_covered G.base S.w (strict_reach h)

/-! ## What the intents of one payload can do -/

/-- What running intents of `signer` can change: no other balance falls, the signer's balance
    falls by at most `taken`, and the nonces and the role table stay. -/
structure OpOK (signer : Acct) (taken : Nat) (S S' : SWorld) : Prop where
  others : ∀ a, a ≠ signer → bal S.w.L.bals a ≤ bal S'.w.L.bals a
  own : bal S.w.L.bals signer ≤ bal S'.w.L.bals signer + taken
  nonces : S'.auth.nonces = S.auth.nonces
  supers : S'.supers = S.supers
  admins : S'.admins = S.admins
  roles : S'.w.L.ctl.roles = S.w.L.ctl.roles

theorem runOp_ok (G : SCfg) (ex : St → Rcpt → Option Out) (signer : Acct) (S S' : SWorld) (o : Op)
    (h : runOp G ex signer S o = some S') : OpOK signer o.takes S S' := by
  cases o with
  | withdraw w =>
    simp only [runOp] at h
    split at h
    · rename_i hg
      obtain rfl := Option.some.inj h
      obtain ⟨hown, hsw⟩ := hg
      subst hown
      cases hs : startWithdraw S.w.L .intent w with
      | none => rw [hs] at hsw; simp at hsw
      | some L' =>
        have hL : (step G.base ex S.w (.ftWithdraw .intent w)).L = L' := by
          simp only [step, hs]; split <;> rfl
        obtain ⟨h1, h2, _, h4⟩ := T2_debit S.w.L L' .intent w hs
        refine ⟨fun a ha => ?_, ?_, rfl, rfl, rfl, ?_⟩
        · have e := h2 a ha
          show bal S.w.L.bals a ≤ bal (step G.base ex S.w (.ftWithdraw .intent w)).L.bals a
          rw [hL]; omega
        · show bal S.w.L.bals w.owner ≤
            bal (step G.base ex S.w (.ftWithdraw .intent w)).L.bals w.owner + w.amount
          rw [hL]; omega
        · show (step G.base ex S.w (.ftWithdraw .intent w)).L.ctl.roles = S.w.L.ctl.roles
          rw [hL, h4]
    · exact absurd h (by simp)
  | move dst amt call =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i L' hm
      obtain rfl := Option.some.inj h
      obtain ⟨hne, _, _, hle, _, rfl⟩ := moveBal_some hm
      refine ⟨fun a ha => ?_, ?_, rfl, rfl, rfl, rfl⟩
      · show bal S.w.L.bals a ≤ bal (set (set S.w.L.bals signer (bal S.w.L.bals signer - amt)) dst
            (bal S.w.L.bals dst + amt)) a
        by_cases hd : dst = a
        · subst hd; rw [bal_set_self]; omega
        · exact Nat.le_of_eq (by rw [bal_set_ne _ _ hd, bal_set_ne _ _ (Ne.symm ha)])
      · show bal S.w.L.bals signer ≤ bal (set (set S.w.L.bals signer (bal S.w.L.bals signer - amt))
            dst (bal S.w.L.bals dst + amt)) signer + amt
        rw [bal_set_ne _ _ (Ne.symm hne), bal_set_self]; omega
  | addKey k =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i A ha
      obtain rfl := Option.some.inj h
      exact ⟨fun _ _ => Nat.le_refl _, Nat.le_add_right _ _, addKey_nonces ha, rfl, rfl, rfl⟩
  | removeKey k =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i A ha
      obtain rfl := Option.some.inj h
      exact ⟨fun _ _ => Nat.le_refl _, Nat.le_add_right _ _, removeKey_nonces ha, rfl, rfl, rfl⟩
  | setAuth en =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h
      refine ⟨fun _ _ => Nat.le_refl _, Nat.le_add_right _ _, rfl, rfl, rfl, ?_⟩
      exact adminStep_roles _ _ (fun r e => by cases e)

theorem runOps_ok (G : SCfg) (ex : St → Rcpt → Option Out) (signer : Acct) :
    ∀ (ops : List Op) (S S' : SWorld), runOps G ex signer S ops = some S' →
      OpOK signer (sumBy Op.takes ops) S S' := by
  intro ops
  induction ops with
  | nil =>
    intro S S' h
    have e : S = S' := by simpa [runOps] using h
    subst e
    exact ⟨fun _ _ => Nat.le_refl _, Nat.le_add_right _ _, rfl, rfl, rfl, rfl⟩
  | cons o t ih =>
    intro S S' h
    simp only [runOps] at h
    split at h
    · exact absurd h (by simp)
    · rename_i S1 h1
      have a := runOp_ok G ex signer S S1 o h1
      have b := ih S1 S' h
      refine ⟨fun x hx => Nat.le_trans (a.others x hx) (b.others x hx), ?_, ?_, ?_, ?_, ?_⟩
      · have h2 := a.own
        have h3 := b.own
        simp only [sumBy]; omega
      · rw [b.nonces, a.nonces]
      · rw [b.supers, a.supers]
      · rw [b.admins, a.admins]
      · rw [b.roles, a.roles]

theorem runOp_calls (G : SCfg) (ex : St → Rcpt → Option Out) (signer : Acct) (S S' : SWorld)
    (o : Op) (h : runOp G ex signer S o = some S') :
    S'.calls = S.calls ∨
    ∃ dst amt, o = .move dst amt true ∧ S'.calls = S.calls ++ [⟨signer, dst, amt⟩] := by
  cases o with
  | withdraw w =>
    simp only [runOp] at h
    split at h
    · obtain rfl := Option.some.inj h; exact Or.inl rfl
    · exact absurd h (by simp)
  | move dst amt call =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h
      cases call with
      | false => exact Or.inl rfl
      | true => exact Or.inr ⟨dst, amt, rfl, rfl⟩
  | addKey k =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h; exact Or.inl rfl
  | removeKey k =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h; exact Or.inl rfl
  | setAuth en =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h; exact Or.inl rfl

theorem runOps_calls (G : SCfg) (ex : St → Rcpt → Option Out) (signer : Acct) :
    ∀ (ops : List Op) (S S' : SWorld), runOps G ex signer S ops = some S' →
      ∃ l, S'.calls = S.calls ++ l ∧
        ∀ x ∈ l, x.sender = signer ∧ Op.move x.receiver x.amount true ∈ ops := by
  intro ops
  induction ops with
  | nil =>
    intro S S' h
    have e : S = S' := by simpa [runOps] using h
    subst e
    exact ⟨[], by simp, by simp⟩
  | cons o t ih =>
    intro S S' h
    simp only [runOps] at h
    split at h
    · exact absurd h (by simp)
    · rename_i S1 h1
      obtain ⟨l, hl, hx⟩ := ih S1 S' h
      rcases runOp_calls G ex signer S S1 o h1 with he | ⟨dst, amt, rfl, he⟩
      · refine ⟨l, by rw [hl, he], fun x hxl => ?_⟩
        exact ⟨(hx x hxl).1, List.mem_cons_of_mem _ (hx x hxl).2⟩
      · refine ⟨⟨signer, dst, amt⟩ :: l, by rw [hl, he]; simp, fun x hxl => ?_⟩
        rcases List.mem_cons.mp hxl with rfl | hxl
        · exact ⟨rfl, List.mem_cons.mpr (Or.inl rfl)⟩
        · exact ⟨(hx x hxl).1, List.mem_cons_of_mem _ (hx x hxl).2⟩

/-! ## T4 Who can lower a ledger balance, with the authorisation of each way -/

/-- **T4. Who can lower a ledger balance.** If a step of the strict world lowers `u`'s ledger
    balance for the token, it is one of six:
    1. `ft_withdraw` called by `u` itself: not paused, authentication by predecessor enabled
       for `u`, `u` not locked;
    2. one signed payload whose signer is `u`: its signature verifies under `p.key`, that key is
       registered for `u`, the verifying contract is this contract, the deadline has not
       passed, the nonce was not used, `u` is not locked; the balance falls by at most what
       the intents of the payload name (`p.takes`), and the nonce is used after the step;
    3. `ft_force_withdraw` by a holder of `DAO` or `UnrestrictedWithdrawer`;
    4. `mt_transfer*` called by `u` itself: not paused, authentication by predecessor enabled,
       `u` not locked;
    5. `mt_resolve_transfer` for a transfer call in flight whose receiver is `u`: the balance
       falls by at most the amount of that transfer, and the entry is gone after the step;
    6. `mt_force_transfer*` by a holder of `DAO` or `UnrestrictedWithdrawer`. -/
theorem T4_authorised (G : SCfg) (S : SWorld) (u : Acct) (st : SStep)
    (hlt : bal (sstd G S st).w.L.bals u < bal S.w.L.bals u) :
    (∃ w, st = .base (.ftWithdraw (.method u) w) ∧ w.owner = u ∧
      S.w.L.ctl.isPaused "ft_withdraw" = false ∧ S.w.L.ctl.authOff.contains u = false ∧
      S.w.L.ctl.locked.contains u = false) ∨
    (∃ now p sig, st = .payload now p sig ∧ p.signer = u ∧ G.valid p.key p sig = true ∧
      hasKey G.implicit S.auth u p.key = true ∧ p.contract = G.base.me ∧ now ≤ p.deadline ∧
      S.auth.nonces.contains (u, p.nonce) = false ∧ S.w.L.ctl.locked.contains u = false ∧
      bal S.w.L.bals u ≤ bal (sstd G S st).w.L.bals u + p.takes ∧
      (u, p.nonce) ∈ (sstd G S st).auth.nonces) ∨
    (∃ who w, st = .base (.ftWithdraw (.force who) w) ∧ w.owner = u ∧
      S.w.L.ctl.any who [.DAO, .UnrestrictedWithdrawer] = true) ∨
    (∃ dst amt call, st = .transfer u dst amt call ∧
      S.w.L.ctl.isPaused "mt_transfer" = false ∧ S.w.L.ctl.authOff.contains u = false ∧
      S.w.L.ctl.locked.contains u = false) ∨
    (∃ k req x, st = .resolveTransfer k req ∧ S.calls[k]? = some x ∧ x.receiver = u ∧
      bal S.w.L.bals u ≤ bal (sstd G S st).w.L.bals u + x.amount ∧
      (sstd G S st).calls = S.calls.eraseIdx k) ∨
    (∃ who dst amt call, st = .forceTransfer who u dst amt call ∧
      S.w.L.ctl.any who [.DAO, .UnrestrictedWithdrawer] = true) := by
  cases st with
  | base st0 =>
    simp only [sstd, sstep] at hlt
    by_cases hf : st0.free = true
    · rw [ifP hf] at hlt
      rcases T4_who_can_lower G.base S.w u st0 hlt with ⟨w, rfl, h1, h2, h3, h4⟩ | ⟨w, rfl, _⟩ |
          ⟨who, w, rfl, h1, h2⟩ | ⟨dst, amt, rfl, _⟩ | ⟨dst, amt, rfl⟩ | ⟨who, dst, amt, rfl, _⟩
      · left; exact ⟨w, rfl, h1, h2, h3, h4⟩
      · simp [Step.free] at hf
      · right; right; left; exact ⟨who, w, rfl, h1, h2⟩
      · simp [Step.free] at hf
      · simp [Step.free] at hf
      · simp [Step.free] at hf
    · rw [ifN hf] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  | transfer src dst amt call =>
    simp only [sstd, sstep] at hlt
    by_cases hd : directOk S.w.L.ctl src = true
    · rw [ifP hd] at hlt
      cases hm : moveBal S.w.L .owner src dst amt with
      | none => rw [hm] at hlt; exact absurd hlt (Nat.lt_irrefl _)
      | some L' =>
        rw [hm] at hlt
        obtain ⟨rfl, hok, _⟩ := moveBal_lower hm hlt
        right; right; right; left
        simp only [directOk, Bool.and_eq_true, Bool.not_eq_true'] at hd
        exact ⟨dst, amt, call, rfl, hd.1, hd.2, by simpa [MoveAuth.ok] using hok⟩
    · rw [ifN hd] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  | forceTransfer who src dst amt call =>
    simp only [sstd, sstep] at hlt
    cases hm : moveBal S.w.L (.force who) src dst amt with
    | none => rw [hm] at hlt; exact absurd hlt (Nat.lt_irrefl _)
    | some L' =>
      rw [hm] at hlt
      obtain ⟨rfl, hok, _⟩ := moveBal_lower hm hlt
      right; right; right; right; right
      exact ⟨who, dst, amt, call, rfl, by simpa [MoveAuth.ok] using hok⟩
  | resolveTransfer k req =>
    cases hk : S.calls[k]? with
    | none =>
      have e : sstd G S (.resolveTransfer k req) = S := by simp only [sstd, sstep, hk]
      rw [e] at hlt; exact absurd hlt (Nat.lt_irrefl _)
    | some x =>
      cases hr : resolveTransfer S.w.L x req with
      | none =>
        have e : (sstd G S (.resolveTransfer k req)).w = S.w := by simp only [sstd, sstep, hk, hr]
        rw [e] at hlt; exact absurd hlt (Nat.lt_irrefl _)
      | some L' =>
        have e : sstd G S (.resolveTransfer k req) =
            { S with w := { S.w with L := L' }, calls := S.calls.eraseIdx k } := by
          simp only [sstd, sstep, hk, hr]
        rw [e] at hlt ⊢
        rcases resolveTransfer_some hr with ⟨_, rfl⟩ | ⟨_, hm⟩
        · exact absurd hlt (Nat.lt_irrefl _)
        · obtain ⟨rfl, _, hle⟩ := moveBal_lower hm hlt
          right; right; right; right; left
          have hra := refund_le_amount S.w.L x req
          refine ⟨k, req, x, rfl, hk, rfl, ?_, rfl⟩
          show bal S.w.L.bals x.receiver ≤ bal L'.bals x.receiver + x.amount
          omega
  | resolveTransferFails k => exact absurd hlt (Nat.lt_irrefl _)
  | payload now p sig =>
    by_cases hg : G.valid p.key p sig = true ∧
        admit G.implicit G.base.me now S.w.L.ctl S.auth p = true
    · cases hr : runOps G (exec G.base.tok) p.signer { S with auth := commitNonce S.auth p }
          p.ops with
      | none =>
        have e : sstd G S (.payload now p sig) = S := by simp only [sstd, sstep, ifP hg, hr]
        rw [e] at hlt; exact absurd hlt (Nat.lt_irrefl _)
      | some S' =>
        have e : sstd G S (.payload now p sig) = S' := by simp only [sstd, sstep, ifP hg, hr]
        rw [e] at hlt ⊢
        have ok := runOps_ok G (exec G.base.tok) p.signer p.ops _ S' hr
        have hsu : p.signer = u := by
          by_cases hsu : u = p.signer
          · exact hsu.symm
          · exfalso
            have h' : bal S.w.L.bals u ≤ bal S'.w.L.bals u := ok.others u hsu
            omega
        right; left
        obtain ⟨hv, ha⟩ := hg
        obtain ⟨hc, hdl, hkey, hnon, hlock⟩ := admit_spec ha
        subst hsu
        refine ⟨now, p, sig, rfl, rfl, hv, hkey, hc, hdl, hnon, hlock, ok.own, ?_⟩
        rw [ok.nonces]
        exact List.mem_cons.mpr (Or.inl rfl)
    · have e : sstd G S (.payload now p sig) = S := by simp only [sstd, sstep, ifN hg]
      rw [e] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  | addKey a k =>
    exfalso
    have e : (sstd G S (.addKey a k)).w = S.w := by
      simp only [sstd, sstep]
      split
      · rfl
      · split <;> rfl
    rw [e] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  | removeKey a k =>
    exfalso
    have e : (sstd G S (.removeKey a k)).w = S.w := by
      simp only [sstd, sstep]
      split
      · rfl
      · split <;> rfl
    rw [e] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  | acl c => exact absurd hlt (Nat.lt_irrefl _)

/-- **T4, where a pending refund comes from, and that it is used once.** The list of transfer
    calls in flight changes in three ways only: one entry is removed by its
    `mt_resolve_transfer` (run or failed); one entry `⟨src, dst, amt⟩` is added by a transfer
    call that moved exactly `amt` from `src` to `dst` in the same step (`mt_transfer_call` by
    `src`, or `mt_force_transfer_call`); entries are added by a signed payload of their sender,
    one for each of its transfers with a notification. -/
theorem T4_calls (G : SCfg) (S : SWorld) (st : SStep) :
    (sstd G S st).calls = S.calls ∨
    (∃ k, ((∃ req, st = .resolveTransfer k req) ∨ st = .resolveTransferFails k) ∧
      (sstd G S st).calls = S.calls.eraseIdx k) ∨
    (∃ src dst amt, (st = .transfer src dst amt true ∨ ∃ who, st = .forceTransfer who src dst amt true) ∧
      (sstd G S st).calls = S.calls ++ [⟨src, dst, amt⟩] ∧ src ≠ dst ∧
      bal (sstd G S st).w.L.bals dst = bal S.w.L.bals dst + amt ∧
      bal (sstd G S st).w.L.bals src + amt = bal S.w.L.bals src) ∨
    (∃ now p sig l, st = .payload now p sig ∧ (sstd G S st).calls = S.calls ++ l ∧
      ∀ x ∈ l, x.sender = p.signer ∧ Op.move x.receiver x.amount true ∈ p.ops) := by
  cases st with
  | base st0 =>
    left; simp only [sstd, sstep]; split <;> rfl
  | transfer src dst amt call =>
    by_cases hd : directOk S.w.L.ctl src = true
    · cases hm : moveBal S.w.L .owner src dst amt with
      | none => left; simp only [sstd, sstep, ifP hd, hm]
      | some L' =>
        have e : sstd G S (.transfer src dst amt call) =
            { S with w := { S.w with L := L' }, calls := pushCall S.calls call src dst amt } := by
          simp only [sstd, sstep, ifP hd, hm]
        obtain ⟨hne, _, _, hle, _, rfl⟩ := moveBal_some hm
        rw [e]
        cases call with
        | false => left; rfl
        | true =>
          right; right; left
          refine ⟨src, dst, amt, Or.inl rfl, rfl, hne, ?_, ?_⟩
          · show bal (set (set S.w.L.bals src (bal S.w.L.bals src - amt)) dst
                (bal S.w.L.bals dst + amt)) dst = bal S.w.L.bals dst + amt
            rw [bal_set_self]
          · show bal (set (set S.w.L.bals src (bal S.w.L.bals src - amt)) dst
                (bal S.w.L.bals dst + amt)) src + amt = bal S.w.L.bals src
            rw [bal_set_ne _ _ (Ne.symm hne), bal_set_self]; omega
    · left; simp only [sstd, sstep, ifN hd]
  | forceTransfer who src dst amt call =>
    cases hm : moveBal S.w.L (.force who) src dst amt with
    | none => left; simp only [sstd, sstep, hm]
    | some L' =>
      have e : sstd G S (.forceTransfer who src dst amt call) =
          { S with w := { S.w with L := L' }, calls := pushCall S.calls call src dst amt } := by
        simp only [sstd, sstep, hm]
      obtain ⟨hne, _, _, hle, _, rfl⟩ := moveBal_some hm
      rw [e]
      cases call with
      | false => left; rfl
      | true =>
        right; right; left
        refine ⟨src, dst, amt, Or.inr ⟨who, rfl⟩, rfl, hne, ?_, ?_⟩
        · show bal (set (set S.w.L.bals src (bal S.w.L.bals src - amt)) dst
              (bal S.w.L.bals dst + amt)) dst = bal S.w.L.bals dst + amt
          rw [bal_set_self]
        · show bal (set (set S.w.L.bals src (bal S.w.L.bals src - amt)) dst
              (bal S.w.L.bals dst + amt)) src + amt = bal S.w.L.bals src
          rw [bal_set_ne _ _ (Ne.symm hne), bal_set_self]; omega
  | resolveTransfer k req =>
    cases hk : S.calls[k]? with
    | none => left; simp only [sstd, sstep, hk]
    | some x =>
      right; left
      refine ⟨k, Or.inl ⟨req, rfl⟩, ?_⟩
      simp only [sstd, sstep, hk]
      split <;> rfl
  | resolveTransferFails k => right; left; exact ⟨k, Or.inr rfl, rfl⟩
  | payload now p sig =>
    by_cases hg : G.valid p.key p sig = true ∧
        admit G.implicit G.base.me now S.w.L.ctl S.auth p = true
    · cases hr : runOps G (exec G.base.tok) p.signer { S with auth := commitNonce S.auth p }
          p.ops with
      | none => left; simp only [sstd, sstep, ifP hg, hr]
      | some S' =>
        have e : sstd G S (.payload now p sig) = S' := by simp only [sstd, sstep, ifP hg, hr]
        obtain ⟨l, hl, hx⟩ := runOps_calls G (exec G.base.tok) p.signer p.ops _ S' hr
        right; right; right
        exact ⟨now, p, sig, l, rfl, by rw [e, hl], hx⟩
    · left; simp only [sstd, sstep, ifN hg]
  | addKey a k =>
    left; simp only [sstd, sstep]
    split
    · rfl
    · split <;> rfl
  | removeKey a k =>
    left; simp only [sstd, sstep]
    split
    · rfl
    · split <;> rfl
  | acl c => left; rfl

/-- **T4, a nonce stays used.** No step of the strict world removes a committed nonce, so a
    signed payload is accepted at most once (`T4_authorised`, way 2, needs the nonce unused). -/
theorem T4_nonce_kept (G : SCfg) (S : SWorld) (st : SStep) (e : Acct × Nonce)
    (h : e ∈ S.auth.nonces) : e ∈ (sstd G S st).auth.nonces := by
  cases st with
  | base st0 => simp only [sstd, sstep]; split <;> exact h
  | transfer src dst amt call =>
    simp only [sstd, sstep]
    split
    · split <;> exact h
    · exact h
  | forceTransfer who src dst amt call => simp only [sstd, sstep]; split <;> exact h
  | resolveTransfer k req =>
    simp only [sstd, sstep]
    split
    · exact h
    · split <;> exact h
  | resolveTransferFails k => exact h
  | payload now p sig =>
    simp only [sstd, sstep]
    split
    · split
      · exact h
      · rename_i S' hr
        rw [(runOps_ok G (exec G.base.tok) p.signer p.ops _ S' hr).nonces]
        exact List.mem_cons_of_mem _ h
    · exact h
  | addKey a k =>
    simp only [sstd, sstep]
    split
    · exact h
    · split
      · exact h
      · rename_i A ha; rw [addKey_nonces ha]; exact h
  | removeKey a k =>
    simp only [sstd, sstep]
    split
    · exact h
    · split
      · exact h
      · rename_i A ha; rw [removeKey_nonces ha]; exact h
  | acl c => exact h

/-- **The one assumption about signatures** (label: caller). `made k p` reads "the holder of the
    private key of `k` signed the payload `p`". The assumption: a signature that verifies under
    `k` was made by that holder. Nothing else about the signature scheme is used. -/
def Unforgeable (G : SCfg) (made : Key → Payload → Prop) : Prop :=
  ∀ k p sig, G.valid k p sig = true → made k p

/-- **T4 under that assumption.** If a signed payload lowers `u`'s balance, the holder of a key
    registered for `u` signed exactly that payload. -/
theorem T4_signed_by_holder (G : SCfg) (made : Key → Payload → Prop) (hU : Unforgeable G made)
    (S : SWorld) (u : Acct) (now : Nat) (p : Payload) (sig : Sig)
    (hlt : bal (sstd G S (.payload now p sig)).w.L.bals u < bal S.w.L.bals u) :
    p.signer = u ∧ hasKey G.implicit S.auth u p.key = true ∧ made p.key p := by
  rcases T4_authorised G S u _ hlt with ⟨w, e, _⟩ | ⟨now', p', sig', e, h1, h2, h3, _⟩ |
      ⟨who, w, e, _⟩ | ⟨dst, amt, call, e, _⟩ | ⟨k, req, x, e, _⟩ | ⟨who, dst, amt, call, e, _⟩
  · cases e
  · cases e; exact ⟨h1, h3, hU _ _ _ h2⟩
  · cases e
  · cases e
  · cases e
  · cases e

/-! ## T4 The role table -/

theorem contains_of_filter {α : Type} [BEq α] {l : List α} {p : α → Bool} {e : α}
    (h : (l.filter p).contains e = true) : l.contains e = true := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    simp only [List.filter_cons] at h
    split at h
    · simp only [List.contains_cons, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih h)
    · simp only [List.contains_cons, Bool.or_eq_true]; exact Or.inr (ih h)

/-- **T4, who can make a holder of a role.** An account that does not hold role `r` holds it
    after an `acl_*` call only if the call is `acl_grant_role(r, a)` by a super-admin or an
    admin of `r`. -/
theorem T4_role_power (x : Acl) (c : AclCall) (a : Acct) (r : Role)
    (h0 : x.roles.contains (a, r) = false) (h1 : (aclStep x c).roles.contains (a, r) = true) :
    ∃ g, c = .grantRole g r a ∧ x.isAdmin r g = true := by
  cases c with
  | grantRole who r' a' =>
    simp only [aclStep] at h1
    split at h1
    · rename_i hc
      simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with h2 | h2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
        rw [Bool.and_eq_true] at hc
        exact ⟨who, rfl, hc.1⟩
      · exact ff_tt h0 h2
    · exact ff_tt h0 h1
  | revokeRole who r' a' =>
    simp only [aclStep] at h1
    split at h1
    · exact ff_tt h0 (contains_of_filter h1)
    · exact ff_tt h0 h1
  | renounceRole who r' => exact ff_tt h0 (contains_of_filter h1)
  | addAdmin who r' a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | revokeAdmin who r' a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | renounceAdmin who r' => exact ff_tt h0 h1
  | addSuper who a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | revokeSuper who a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | transferSuper who a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1

/-- **T4, who can make an admin of a role:** `acl_add_admin(r, a)` by a super-admin or an admin
    of `r`. -/
theorem T4_admin_power (x : Acl) (c : AclCall) (a : Acct) (r : Role)
    (h0 : x.admins.contains (a, r) = false) (h1 : (aclStep x c).admins.contains (a, r) = true) :
    ∃ g, c = .addAdmin g r a ∧ x.isAdmin r g = true := by
  cases c with
  | addAdmin who r' a' =>
    simp only [aclStep] at h1
    split at h1
    · rename_i hc
      simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with h2 | h2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
        rw [Bool.and_eq_true] at hc
        exact ⟨who, rfl, hc.1⟩
      · exact ff_tt h0 h2
    · exact ff_tt h0 h1
  | revokeAdmin who r' a' =>
    simp only [aclStep] at h1
    split at h1
    · exact ff_tt h0 (contains_of_filter h1)
    · exact ff_tt h0 h1
  | renounceAdmin who r' => exact ff_tt h0 (contains_of_filter h1)
  | grantRole who r' a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | revokeRole who r' a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | renounceRole who r' => exact ff_tt h0 h1
  | addSuper who a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | revokeSuper who a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | transferSuper who a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1

/-- **T4, who can make a super-admin:** `acl_add_super_admin(a)` or
    `acl_transfer_super_admin(a)` by a super-admin. -/
theorem T4_super_power (x : Acl) (c : AclCall) (a : Acct)
    (h0 : x.supers.contains a = false) (h1 : (aclStep x c).supers.contains a = true) :
    ∃ g, (c = .addSuper g a ∨ c = .transferSuper g a) ∧ x.supers.contains g = true := by
  cases c with
  | addSuper who a' =>
    simp only [aclStep] at h1
    split at h1
    · rename_i hc
      simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with h2 | h2
      · subst h2
        rw [Bool.and_eq_true] at hc
        exact ⟨who, Or.inl rfl, hc.1⟩
      · exact ff_tt h0 h2
    · exact ff_tt h0 h1
  | transferSuper who a' =>
    simp only [aclStep] at h1
    split at h1
    · rename_i hc
      have h3 := contains_of_filter h1
      simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h3
      rcases h3 with h2 | h2
      · subst h2
        rw [Bool.and_eq_true] at hc
        exact ⟨who, Or.inr rfl, hc.1⟩
      · exact ff_tt h0 h2
    · exact ff_tt h0 h1
  | revokeSuper who a' =>
    simp only [aclStep] at h1
    split at h1
    · exact ff_tt h0 (contains_of_filter h1)
    · exact ff_tt h0 h1
  | grantRole who r' a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | revokeRole who r' a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | renounceRole who r' => exact ff_tt h0 h1
  | addAdmin who r' a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | revokeAdmin who r' a' => simp only [aclStep] at h1; split at h1 <;> exact ff_tt h0 h1
  | renounceAdmin who r' => exact ff_tt h0 h1

/-- **The power the statement names.** A super-admin can make itself (or anyone) a holder of
    any role with one call; so can an admin of that role. -/
theorem T4_super_admin_can_take_any_role (x : Acl) (g a : Acct) (r : Role)
    (hg : x.isAdmin r g = true) : (aclStep x (.grantRole g r a)).roles.contains (a, r) = true := by
  simp only [aclStep]
  by_cases hc : x.roles.contains (a, r) = true
  · rw [ifN (by rw [hg, hc]; simp)]; exact hc
  · rw [ifP (by rw [hg]; simpa using hc)]
    simp only [List.contains_cons, beq_self_eq_true, Bool.true_or]

/-- A strict step other than an `acl_*` call leaves the grantees as they are. -/
theorem roles_other (G : SCfg) (S : SWorld) (st : SStep) (h : ∀ c, st ≠ .acl c) :
    (sstd G S st).w.L.ctl.roles = S.w.L.ctl.roles := by
  cases st with
  | base st0 =>
    simp only [sstd, sstep]
    split
    · rename_i hf
      exact step_roles G.base S.w st0 (fun r e => by subst e; simp [Step.free] at hf)
    · rfl
  | transfer src dst amt call =>
    simp only [sstd, sstep]
    split
    · split
      · rfl
      · rename_i L' hm
        obtain ⟨_, _, _, _, _, rfl⟩ := moveBal_some hm
        rfl
    · rfl
  | forceTransfer who src dst amt call =>
    simp only [sstd, sstep]
    split
    · rfl
    · rename_i L' hm
      obtain ⟨_, _, _, _, _, rfl⟩ := moveBal_some hm
      rfl
  | resolveTransfer k req =>
    simp only [sstd, sstep]
    split
    · rfl
    · split
      · rfl
      · rename_i L' hr
        rcases resolveTransfer_some hr with ⟨_, rfl⟩ | ⟨_, hm⟩
        · rfl
        · obtain ⟨_, _, _, _, _, rfl⟩ := moveBal_some hm
          rfl
  | resolveTransferFails k => rfl
  | payload now p sig =>
    simp only [sstd, sstep]
    split
    · split
      · rfl
      · rename_i S' hr
        exact (runOps_ok G (exec G.base.tok) p.signer p.ops _ S' hr).roles
    · rfl
  | addKey a k =>
    simp only [sstd, sstep]
    split
    · rfl
    · split <;> rfl
  | removeKey a k =>
    simp only [sstd, sstep]
    split
    · rfl
    · split <;> rfl
  | acl c => exact absurd rfl (h c)

/-- **T4, how a holder of a role is made, in the strict world.** If `who` does not hold role
    `r` before a step and holds it after, the step is `acl_grant_role(r, who)` called by `g`,
    and `g` is a super-admin or an admin of `r` at that moment. No other step of the world
    makes a holder. -/
theorem T4_role_change (G : SCfg) (S : SWorld) (st : SStep) (who : Acct) (r : Role)
    (h0 : S.w.L.ctl.roles.contains (who, r) = false)
    (h1 : (sstd G S st).w.L.ctl.roles.contains (who, r) = true) :
    ∃ g, st = .acl (.grantRole g r who) ∧ S.acl.isAdmin r g = true := by
  by_cases hacl : ∃ c, st = .acl c
  · obtain ⟨c, rfl⟩ := hacl
    obtain ⟨g, rfl, hg⟩ := T4_role_power S.acl c who r h0 h1
    exact ⟨g, rfl, hg⟩
  · rw [roles_other G S st (fun c e => hacl ⟨c, e⟩)] at h1
    exact ff_tt h0 h1

/-- A strict step other than an `acl_*` call leaves the whole role table as it is. -/
theorem acl_other (G : SCfg) (S : SWorld) (st : SStep) (h : ∀ c, st ≠ .acl c) :
    (sstd G S st).acl = S.acl := by
  have hr := roles_other G S st h
  have hs : (sstd G S st).supers = S.supers ∧ (sstd G S st).admins = S.admins := by
    cases st with
    | base st0 => simp only [sstd, sstep]; split <;> exact ⟨rfl, rfl⟩
    | transfer src dst amt call =>
      simp only [sstd, sstep]
      split
      · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    | forceTransfer who src dst amt call => simp only [sstd, sstep]; split <;> exact ⟨rfl, rfl⟩
    | resolveTransfer k req =>
      simp only [sstd, sstep]
      split
      · exact ⟨rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl⟩
    | resolveTransferFails k => exact ⟨rfl, rfl⟩
    | payload now p sig =>
      simp only [sstd, sstep]
      split
      · split
        · exact ⟨rfl, rfl⟩
        · rename_i S' hr'
          have ok := runOps_ok G (exec G.base.tok) p.signer p.ops _ S' hr'
          exact ⟨ok.supers, ok.admins⟩
      · exact ⟨rfl, rfl⟩
    | addKey a k =>
      simp only [sstd, sstep]
      split
      · exact ⟨rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl⟩
    | removeKey a k =>
      simp only [sstd, sstep]
      split
      · exact ⟨rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl⟩
    | acl c => exact absurd rfl (h c)
  unfold SWorld.acl
  rw [hr, hs.1, hs.2]

/-- Nobody can change who holds role `r`: there is no super-admin and no admin of `r`. -/
def NoAuthority (x : Acl) (r : Role) : Prop :=
  (∀ g, x.supers.contains g = false) ∧ (∀ g, x.admins.contains (g, r) = false)

theorem noAuthority_step {x : Acl} {r : Role} (h : NoAuthority x r) (c : AclCall) :
    NoAuthority (aclStep x c) r ∧
    ∀ a, (aclStep x c).roles.contains (a, r) = true → x.roles.contains (a, r) = true := by
  refine ⟨⟨fun g => ?_, fun g => ?_⟩, fun a ha => ?_⟩
  · cases hb : (aclStep x c).supers.contains g with
    | false => rfl
    | true =>
      obtain ⟨g', _, hg'⟩ := T4_super_power x c g (h.1 g) hb
      exact ff_tt (h.1 g') hg'
  · cases hb : (aclStep x c).admins.contains (g, r) with
    | false => rfl
    | true =>
      obtain ⟨g', _, hg'⟩ := T4_admin_power x c g r (h.2 g) hb
      unfold Acl.isAdmin at hg'
      rw [h.1 g', h.2 g'] at hg'
      exact absurd hg' (by decide)
  · cases hb : x.roles.contains (a, r) with
    | true => rfl
    | false =>
      obtain ⟨g', _, hg'⟩ := T4_role_power x c a r hb ha
      unfold Acl.isAdmin at hg'
      rw [h.1 g', h.2 g'] at hg'
      exact absurd hg' (by decide)

/-- **T4, the holders of a role come from the initial table by the rules.** Along any run of
    the strict world: if at the start there is no super-admin and no admin of `r`, there is
    none later, and every holder of `r` later held `r` at the start. With a super-admin or an
    admin of `r` at the start the set of holders can grow, and `T4_role_change` names the only
    step by which it does. -/
theorem T4_roles_from_initial {G : SCfg} {S0 S : SWorld} (h : SReach G S0 S) (r : Role)
    (hno : NoAuthority S0.acl r) :
    NoAuthority S.acl r ∧
    ∀ a, S.w.L.ctl.roles.contains (a, r) = true → S0.w.L.ctl.roles.contains (a, r) = true := by
  induction h with
  | init h => exact ⟨hno, fun _ ha => ha⟩
  | step st _ ih =>
    rename_i S1 hreach1
    obtain ⟨hn, hsub⟩ := ih
    by_cases hacl : ∃ c, st = .acl c
    · obtain ⟨c, rfl⟩ := hacl
      obtain ⟨hn', hr'⟩ := noAuthority_step hn c
      exact ⟨hn', fun a ha => hsub a (hr' a ha)⟩
    · have e := acl_other G S1 st (fun c e => hacl ⟨c, e⟩)
      have e2 := roles_other G S1 st (fun c e => hacl ⟨c, e⟩)
      refine ⟨by rw [e]; exact hn, fun a ha => hsub a ?_⟩
      rw [e2] at ha; exact ha

/-- **T4, forced operations along a run.** If at the start nobody can change who holds `DAO`
    or `UnrestrictedWithdrawer`, then whoever can force a withdrawal or an internal transfer in
    a reachable state held one of the two roles at the start. -/
theorem T4_force_from_initial {G : SCfg} {S0 S : SWorld} (h : SReach G S0 S)
    (hD : NoAuthority S0.acl .DAO) (hW : NoAuthority S0.acl .UnrestrictedWithdrawer) (who : Acct)
    (hw : S.w.L.ctl.any who [.DAO, .UnrestrictedWithdrawer] = true) :
    S0.w.L.ctl.any who [.DAO, .UnrestrictedWithdrawer] = true := by
  simp only [Ctl.any, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hw ⊢
  rcases hw with h1 | h1
  · exact Or.inl ((T4_roles_from_initial h .DAO hD).2 who h1)
  · exact Or.inr ((T4_roles_from_initial h .UnrestrictedWithdrawer hW).2 who h1)

/-! ## T4 The authentication flag -/

/-- **T4, who can switch authentication by predecessor.** The flag of an account changes only
    by the account's own `disable_auth_by_predecessor_id` (flag on, account not locked), by its
    `SetAuthByPredecessorId` intent (account not locked), or by the forced switch of a holder
    of the listed roles. -/
theorem T4_auth_flag_power (c : Ctl) (a : Admin) (h : (adminStep c a).authOff ≠ c.authOff) :
    (∃ x, a = .authOffSelf x ∧ c.authOff.contains x = false ∧ c.locked.contains x = false) ∨
    (∃ x en, a = .authIntent x en ∧ c.locked.contains x = false) ∨
    (∃ who x en, a = .authForce who x en ∧
      c.any who (if en then [.DAO, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager]
        else [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager]) = true) := by
  cases a with
  | pause who key => exfalso; simp only [adminStep] at h; split at h <;> exact h rfl
  | unpause who key => exfalso; simp only [adminStep] at h; split at h <;> exact h rfl
  | lock who x => exfalso; simp only [adminStep] at h; split at h <;> exact h rfl
  | unlock who x => exfalso; simp only [adminStep] at h; split at h <;> exact h rfl
  | authOffSelf x =>
    left
    by_cases hc : (c.authOff.contains x || c.locked.contains x) = true
    · exfalso; apply h; simp only [adminStep]; rw [ifP hc]
    · have h2 : c.authOff.contains x = false ∧ c.locked.contains x = false := by simpa using hc
      exact ⟨x, rfl, h2.1, h2.2⟩
  | authIntent x en =>
    right; left
    by_cases hc : c.locked.contains x = true
    · exfalso; apply h; simp only [adminStep]; rw [ifP hc]
    · exact ⟨x, en, rfl, by simpa using hc⟩
  | authForce who x en =>
    right; right
    by_cases hr : c.any who (if en then [.DAO, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager]
        else [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager]) = true
    · exact ⟨who, x, en, rfl, hr⟩
    · exfalso; apply h; simp only [adminStep]; rw [ifN hr]
  | acl roles => exact absurd rfl h

/-! ## Two guards that the invariant implies -/

theorem supply_le_max {K : Cfg} {S : World} (h : Reach K S) : S.L.supply ≤ U128_MAX := by
  have h1 := T1_supply K S h
  have h2 := T1_ledger_covered K S h
  have h3 := held_le_max h
  omega

theorem bal_add_le_total (l : Accts) {a b : Acct} (h : a ≠ b) : bal l a + bal l b ≤ total l := by
  have h1 := total_set l a 0
  have h2 := bal_le_total (set l a 0) b
  rw [bal_set_ne _ _ h] at h2
  omega

/-- **The guard `w.amount ≤ U128_MAX` of `startWithdraw` is implied in every reachable state.**
    There the function equals the same function without that guard: a debit needs the amount
    within the total supply, and the supply is at most the tokens the contract holds, a `u128`.
    So no statement about reachable states can tell the two apart. -/
theorem startWithdraw_amount_guard_redundant {K : Cfg} {S : World} (h : Reach K S) (via : Via)
    (w : Wd) :
    startWithdraw S.L via w =
      (if via.ok S.L.ctl w = true then debit S.L w.owner w.amount via.forced else none) := by
  unfold startWithdraw
  by_cases hv : via.ok S.L.ctl w = true
  · rw [ifP hv]
    by_cases ha : w.amount ≤ U128_MAX
    · rw [ifP ⟨hv, ha⟩]
    · rw [ifN (fun hc => ha hc.2)]
      cases hd : debit S.L w.owner w.amount via.forced with
      | none => rfl
      | some L' =>
        exfalso
        obtain ⟨_, _, _, hs, _⟩ := debit_some hd
        have := supply_le_max h
        omega
  · rw [ifN hv, ifN (fun hc => hv hc.1)]

/-- **The guard `bal dst + amt ≤ U128_MAX` of `moveBal` is implied in every reachable state**
    by its other guards: source and destination differ and the amount is within the source
    balance, so the destination balance plus the amount is at most the sum of all balances,
    which is the supply, a `u128`. -/
theorem moveBal_destination_guard_redundant {K : Cfg} {S : World} (h : Reach K S)
    (src dst : Acct) (amt : Nat) (hne : src ≠ dst) (hle : amt ≤ bal S.L.bals src) :
    bal S.L.bals dst + amt ≤ U128_MAX := by
  have h1 := bal_add_le_total S.L.bals hne
  have h2 := T1_supply K S h
  have h3 := supply_le_max h
  omega

end Intents
