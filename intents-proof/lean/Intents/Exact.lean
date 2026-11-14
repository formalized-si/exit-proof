/-
  T1 with equality: where every token is.

  `T1_backing` is an inequality because tokens can end up held by the contract and assigned to
  nobody. `Lossless` lists the four kinds of step in which that happens; `T1_exact` proves that
  without them (and starting with an empty token balance) the books are exact in every state:
  ledger total + everything in flight = tokens held, and `T1_equality` that in a quiet state the
  ledger total equals the tokens held.
-/
import Intents.Theorems

namespace Intents
open ProvedFT

/-! ### Exact token facts -/

/-- A receipt from `p ≠ u` that is not a plain `ft_transfer` to `u` changes `u`'s balance only
    by the amount of an `ft_transfer_call` to `u`, for which it starts the settlement callback. -/
theorem method_third_exact {E : Env} {s : St} {p u : Acct} {d : Nat} {m : Method} {rs : List PR}
    {o : Out} (hpu : p ≠ u) (hres : ∀ sn rc amt, m = .ft_resolve_transfer sn rc amt → False)
    (hgift : ∀ x memo, m ≠ .ft_transfer u x memo)
    (h : method E s ⟨p, d, m, rs⟩ = some o) :
    bal o.st.accts u = bal s.accts u + sumBy depW (annThird u o.calls) := by
  cases m with
  | reinit => simp [method] at h
  | bad => simp [method] at h
  | ft_total_supply | ft_balance_of _ | storage_balance_bounds | storage_balance_of _ =>
    simp only [method, Option.some.injEq] at h; subst h; simp [annThird, sumBy]
  | ft_transfer rc x memo =>
    have hru : rc ≠ u := fun e => hgift x memo (by rw [e])
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, ite_false] at h
      cases hq : iTransfer s.accts s.supply p rc x with
      | none => simp [hq] at h
      | some q =>
        obtain ⟨l', sup'⟩ := q
        simp only [hq, Option.some.injEq] at h; subst h
        obtain ⟨hne, _, bs, br, _, hgr, _, _, _, rfl, rfl⟩ := iTransfer_some hq
        simp only [annThird, List.map_nil, sumBy, Nat.add_zero]
        rw [bal_set_ne _ _ hru, bal_set_ne _ _ hpu]
  | ft_transfer_call rc x memo msg =>
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, ite_false] at h
      cases hq : iTransfer s.accts s.supply p rc x with
      | none => simp [hq] at h
      | some q =>
        obtain ⟨l', sup'⟩ := q
        simp only [hq, Option.some.injEq] at h; subst h
        obtain ⟨hne, _, bs, br, _, hgr, _, _, _, rfl, rfl⟩ := iTransfer_some hq
        simp only [annThird, List.map_cons, List.map_nil, sumBy, Nat.add_zero]
        by_cases hru : rc = u
        · subst hru
          rw [bal_set_self, bal_of_some hgr]
          simp [depW]
        · rw [bal_set_ne _ _ hru, bal_set_ne _ _ hpu]
          simp [depW, hru]
  | ft_resolve_transfer sn rc amt => exact absurd (hres sn rc amt rfl) id
  | storage_deposit acc ro =>
    simp only [method] at h
    cases hg : get s.accts (acc.getD p) with
    | some w => simp only [hg, Option.some.injEq] at h; subst h; simp [annThird, sumBy]
    | none =>
      simp only [hg] at h
      by_cases hm : d < E.minBal
      · simp [hm] at h
      · simp only [hm, ite_false, Option.some.injEq] at h; subst h
        simp only [annThird, List.map_nil, sumBy, Nat.add_zero]
        by_cases hau : acc.getD p = u
        · rw [← hau, bal_set_self, bal_of_none hg]
        · rw [bal_set_ne _ _ hau]
  | storage_withdraw amt =>
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, ite_false] at h
      cases hgp : get s.accts p with
      | none => simp [hgp] at h
      | some w =>
        simp only [hgp] at h
        cases amt with
        | none => simp only [Option.some.injEq] at h; subst h; simp [annThird, sumBy]
        | some a =>
          simp only at h
          by_cases ha : 0 < a
          · simp [ha] at h
          · simp only [ha, ite_false, Option.some.injEq] at h; subst h; simp [annThird, sumBy]
  | storage_unregister f =>
    simp only [method] at h
    by_cases hd : d ≠ 1
    · simp [hd] at h
    · simp only [hd, ite_false] at h
      cases hg : get s.accts p with
      | none => simp only [hg, Option.some.injEq] at h; subst h; simp [annThird, sumBy]
      | some b =>
        simp only [hg] at h
        by_cases hc : b = 0 ∨ f = some true
        · simp only [hc, ite_true] at h
          by_cases hc2 : b ≤ s.supply
          · simp only [hc2, ite_true, Option.some.injEq] at h; subst h
            simp only [annThird, List.map_nil, sumBy, Nat.add_zero]
            rw [bal_erase_ne _ hpu]
          · simp only [hc2, ite_false] at h; exact absurd h (by simp)
        · simp [hc] at h

theorem third_call_exact {E : Env} {c : St} {p u : Acct} {d : Nat} {m : Method} {rs : List PR}
    {o : Out} (hpu : p ≠ u) (hgift : ∀ x memo, m ≠ .ft_transfer u x memo)
    (h : exec E c ⟨p, d, m, resultsFor E p rs⟩ = some o) :
    bal o.st.accts u = bal c.accts u + sumBy depW (annThird u o.calls) := by
  obtain ⟨o0, hm, ha, _, _, hc, _⟩ := exec_some h
  have hres : ∀ sn rc amt, m = .ft_resolve_transfer sn rc amt → False := by
    intro sn rc amt hmr
    subst hmr
    obtain ⟨hps, _, _, _, _, _, _, _, hrs, _⟩ := method_resolve_some hm
    simp [resultsFor, hps] at hrs
  rw [ha, hc]
  exact method_third_exact hpu hres hgift hm

/-- The settlement callback touches nobody but the sender and the receiver. -/
theorem resolve_bystander {E : Env} {c : St} {sn rc : Acct} {amt : Nat} {res : PR} {o : Out}
    (hne : sn ≠ rc) (h : exec E c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [res]⟩ = some o)
    (u : Acct) (h1 : u ≠ sn) (h2 : u ≠ rc) : bal o.st.accts u = bal c.accts u := by
  obtain ⟨o0, hm, ha, _⟩ := exec_some h
  obtain ⟨_, _, _, _, h5, _⟩ := P2_settlement_call E c sn rc amt res o0 hne hm
  rw [ha]
  unfold bal
  rw [h5 u h1 h2]

/-- After a failed `ft_on_transfer` the settlement callback takes the whole amount back from
    the receiver, when the receiver still holds it. -/
theorem resolve_failed_receiver {E : Env} {c : St} {sn rc : Acct} {amt : Nat} {o : Out}
    (hne : sn ≠ rc) (hle : amt ≤ bal c.accts rc)
    (h : exec E c ⟨E.self, 0, .ft_resolve_transfer sn rc amt, [PR.failed]⟩ = some o) :
    bal o.st.accts rc + amt = bal c.accts rc := by
  obtain ⟨o0, hm, ha, _⟩ := exec_some h
  obtain ⟨_, _, _, h4, _⟩ := P2_settlement_call E c sn rc amt .failed o0 hne hm
  rw [ha]
  have hf : refundOf c.accts rc amt .failed = amt := by
    have hu : unusedOf amt PR.failed = amt := rfl
    unfold refundOf
    rw [hu]
    by_cases h0 : 0 < amt ∧ 0 < bal c.accts rc
    · rw [ifP h0]; exact Nat.min_eq_right hle
    · rw [ifN h0]; omega
  rw [hf] at h4
  exact h4

/-! ### Steps that lose track of nothing -/

/-- The steps after which every token the contract holds is still accounted for. The four
    excluded kinds are exactly how tokens become held and unassigned:
    * a plain `ft_transfer` to the contract (a gift: no `ft_on_transfer`, no credit);
    * the token's refund callback of a *failed* deposit is dropped: the sender is not refunded
      and was not credited;
    * `ft_resolve_withdraw` for an `ft_transfer_call` withdrawal whose token receipt failed:
      nothing left the contract, nothing is refunded;
    * `ft_resolve_withdraw` is dropped while a refund was due. -/
def Lossless (K : Cfg) (S : World) : Step → Prop
  | .tokCall _ _ m _ => ∀ x memo, m ≠ .ft_transfer K.me x memo
  | .tokResolveFails i => ∀ e, S.pend[i]? = some e → e.ann ≠ .dep (some false)
  | .resolveWd k =>
    ∀ r, S.resolves[k]? = some r → ¬(r.isCall = true ∧ r.res = PR.failed ∧ r.left = 0)
  | .resolveWdFails k => ∀ r, S.resolves[k]? = some r → r.unsettled = 0
  | _ => True

/-- States reachable from a contract that holds no tokens of `T` through lossless steps. -/
inductive ReachExact (K : Cfg) : World → Prop
  | init (S : World) (h : Init K S) (h0 : bal S.c.accts K.me = 0) : ReachExact K S
  | step {S : World} (st : Step) (hl : Lossless K S st) :
      ReachExact K S → ReachExact K (stdStep K S st)

theorem reachExact_reach {K : Cfg} {S : World} (h : ReachExact K S) : Reach K S := by
  induction h with
  | init S h _ => exact Reach.init S h
  | step st _ _ ih => exact Reach.step st ih

/-- Put the goal `supply + owed = held` of a concrete next state into the form of sums. -/
local macro "books" : tactic => `(tactic| ((try dsimp only); unfold owed; (try dsimp only)))

/-- One lossless step keeps the books exact. -/
theorem exact_step (K : Cfg) (hE : K.tok.Sane) {S : World} (hR : Reach K S)
    (heq : S.L.supply + owed S = bal S.c.accts K.me) (st : Step) (hl : Lossless K S st) :
    (stdStep K S st).L.supply + owed (stdStep K S st) = bal (stdStep K S st).c.accts K.me := by
  have hI := inv_reach hR
  have hT := ProvedFT.inv_reach (tok_reach hR)
  obtain ⟨hb, hc, hp, ho, hu, hr⟩ := hI
  have hq := heq
  unfold owed at hq hb
  -- every callback in flight on the token is between two different accounts
  have hpne : ∀ e ∈ S.pend, e.sender ≠ e.receiver := by
    intro e he
    have := hT.pend e.raw (by simp only [toSys]; exact List.mem_map_of_mem he)
    exact this.1
  -- the token's settlement callback never fails for arithmetic reasons
  have hnf : ∀ (e : Pend) (r : PR),
      exec K.tok S.c ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [r]⟩ ≠ none := by
    intro e r hn
    obtain ⟨o, ho⟩ := P2_settlement_never_fails K.tok hE (toSys S) hT e.sender e.receiver e.amount r
    simp only [toSys] at ho
    rw [hn] at ho; cases ho
  cases st with
  | tokCall p d m rs =>
    simp only [stdStep, step]
    by_cases hpm : p = K.me
    · rw [ifP hpm]; exact heq
    · rw [ifN hpm]
      cases he : exec K.tok S.c ⟨p, d, m, resultsFor K.tok p rs⟩ with
      | none => exact heq
      | some o =>
        have hx := third_call_exact (u := K.me) hpm hl he
        books
        rw [sumBy_append]; omega
  | tokResolve i res =>
    simp only [stdStep, step]
    cases hpi : S.pend[i]? with
    | none => exact heq
    | some e =>
      dsimp only
      have hmem := List.mem_of_getElem? hpi
      have hpe := hp e hmem
      have hne := hpne e hmem
      have hsum := sumBy_eraseIdx depW hpi
      unfold PendOK at hpe
      cases hann : e.ann with
      | other =>
        rw [hann] at hpe
        simp only [resOf_other res hann, wdDone_other _ _ hann, List.append_nil]
        have hw := depW_other hann
        cases he : exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [res]⟩ with
        | none => exact absurd he (hnf e res)
        | some o =>
          obtain ⟨hcalls, _⟩ := resolve_exec he
          have hbal := resolve_bystander hne he K.me (Ne.symm hpe.1) (Ne.symm hpe.2)
          books
          rw [hcalls, hbal]; simp only [annThird, List.map_nil, List.append_nil]; omega
      | dep s =>
        rw [hann] at hpe
        cases s with
        | none => simp only [resOf_dep_none res hann]; exact heq
        | some b =>
          simp only [resOf_dep_some res hann, wdDone_dep _ _ hann, List.append_nil]
          cases he : exec K.tok S.c
              ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [depRes b]⟩ with
          | none => exact absurd he (hnf e (depRes b))
          | some o =>
            cases b with
            | true =>
              obtain ⟨hacc, hcalls⟩ := resolve_credited he
              have hw := depW_credited hann
              books
              rw [hcalls, hacc]; simp only [annThird, List.map_nil, List.append_nil]; omega
            | false =>
              obtain ⟨hcalls, _⟩ := resolve_exec he
              have hw := depW_failed hann
              have hle := le_sumBy depW hmem
              have hrecv : bal o.st.accts K.me + e.amount = bal S.c.accts K.me := by
                have := resolve_failed_receiver (rc := e.receiver) hne (by rw [hpe]; omega) he
                rw [hpe] at this; exact this
              books
              rw [hcalls]; simp only [annThird, List.map_nil, List.append_nil]; omega
      | wd owner =>
        rw [hann] at hpe
        obtain ⟨hsn, hrc, hmax⟩ := hpe
        have hw := depW_wd hann
        simp only [resOf_wd res hann]
        cases he : exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [res]⟩ with
        | none => exact absurd he (hnf e res)
        | some o =>
          obtain ⟨hcalls, f, hf, hcase⟩ := resolve_sender hne he
          rw [hsn] at hcase
          simp only [wdDone_wd _ _ hann]
          books
          rw [hcalls]
          simp only [annThird, List.map_nil, List.append_nil, sumBy_append, sumBy_one,
            Rs.unsettled]
          rcases hcase with ⟨hbal, _⟩ | ⟨hbal, _⟩ <;> omega
  | tokResolveFails i =>
    simp only [stdStep, step]
    cases hpi : S.pend[i]? with
    | none => exact heq
    | some e =>
      dsimp only
      have hsum := sumBy_eraseIdx depW hpi
      have hl' := hl e hpi
      cases hann : e.ann with
      | other =>
        simp only [resOf_other _ hann, wdDone_other _ _ hann, List.append_nil]
        have hw := depW_other hann
        books; omega
      | dep s =>
        cases s with
        | none => simp only [resOf_dep_none _ hann]; exact heq
        | some b =>
          cases b with
          | false => exact absurd hann hl'
          | true =>
            simp only [resOf_dep_some _ hann, wdDone_dep _ _ hann, List.append_nil]
            have hw := depW_credited hann
            books; omega
      | wd owner =>
        simp only [resOf_wd _ hann, wdDone_wd _ _ hann]
        have hw := depW_wd hann
        books
        simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
  | tokNearIn x =>
    simp only [stdStep, step]
    by_cases hx : S.c.near + x ≤ K.tok.cap
    · rw [ifP hx]; books; exact hq
    · rw [ifN hx]; exact heq
  | onTransfer i recv ok =>
    simp only [stdStep, step]
    cases hpi : S.pend[i]? with
    | none => exact heq
    | some e =>
      dsimp only
      by_cases hg : e.receiver = K.me ∧ e.ann = .dep none
      · rw [ifP hg]
        have hw := depW_fresh hg.2
        cases hcr : (if ok = true ∧ S.L.ctl.isPaused "ft_on_transfer" = false then
            credit S.L recv e.amount else none) with
        | none =>
          have hsum := sumBy_set depW hpi { e with ann := .dep (some false) }
          have hw' : depW { e with ann := .dep (some false) } = e.amount := rfl
          books; omega
        | some L' =>
          have hcr' : credit S.L recv e.amount = some L' := by
            by_cases hcond : ok = true ∧ S.L.ctl.isPaused "ft_on_transfer" = false
            · rw [ifP hcond] at hcr; exact hcr
            · rw [ifN hcond] at hcr; exact absurd hcr (by simp)
          obtain ⟨_, _, _, rfl⟩ := credit_some hcr'
          have hsum := sumBy_set depW hpi { e with ann := .dep (some true) }
          have hw' : depW { e with ann := .dep (some true) } = 0 := rfl
          have hle := le_sumBy depW (List.mem_of_getElem? hpi)
          books; omega
      · rw [ifN hg]; exact heq
  | ftWithdraw via w =>
    simp only [stdStep, step]
    cases hs : startWithdraw S.L via w with
    | none => exact heq
    | some L' =>
      obtain ⟨_, _, hd⟩ := startWithdraw_some hs
      obtain ⟨_, _, _, hles, rfl⟩ := debit_some hd
      dsimp only
      by_cases hsd : w.sd.isSome = true
      · rw [ifP hsd]
        books
        simp only [sumBy_append, sumBy_one]; omega
      · rw [ifN hsd]
        books
        simp only [sumBy_append, sumBy_one]; omega
  | doFtWithdraw j ok =>
    simp only [stdStep, step]
    cases hj : S.unwrap[j]? with
    | none => exact heq
    | some w =>
      dsimp only
      have hsum := sumBy_eraseIdx Wd.amount hj
      cases ok with
      | true =>
        simp only [ite_true]
        books
        simp only [sumBy_append, sumBy_one]; omega
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        books
        simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
  | tokXfer j =>
    simp only [stdStep, step]
    cases hj : S.outbox[j]? with
    | none => exact heq
    | some w =>
      dsimp only
      have hsum := sumBy_eraseIdx Wd.amount hj
      cases hx : xferBatch (exec K.tok) K.me S.c w with
      | none =>
        books
        simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
      | some o =>
        obtain ⟨hne, hbal, hplain, hcall⟩ := batch_exec hx
        have hle := le_sumBy Wd.amount (List.mem_of_getElem? hj)
        cases hmsg : w.msg with
        | none =>
          obtain ⟨hcalls, hret⟩ := hplain hmsg
          have hleft : bal S.c.accts K.me - bal o.st.accts K.me = w.amount := by omega
          simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
          rw [hcalls, hret, hleft]
          books
          simp only [annWd, List.map_nil, List.append_nil, sumBy_append, sumBy_one, Rs.unsettled,
            retPR]
          omega
        | some msg =>
          have hcalls := hcall (by rw [hmsg]; rfl)
          simp only [Option.isSome_some, ite_true, List.append_nil]
          rw [hcalls]
          books
          simp only [annWd, List.map_cons, List.map_nil, sumBy_append, sumBy_one, depW]
          omega
  | tokXferFails j =>
    simp only [stdStep, step]
    cases hj : S.outbox[j]? with
    | none => exact heq
    | some w =>
      have hsum := sumBy_eraseIdx Wd.amount hj
      books
      simp only [sumBy_append, sumBy_one, Rs.unsettled]; omega
  | meStorageDeposit acc d =>
    simp only [stdStep, step]
    cases he : exec K.tok S.c ⟨K.me, d, .storage_deposit (some acc) none, []⟩ with
    | none => exact heq
    | some o =>
      obtain ⟨hbal, hcalls⟩ := sd_exec he
      books
      rw [hcalls, hbal]; simp only [annThird, List.map_nil, List.append_nil]; omega
  | resolveWd k =>
    simp only [stdStep, step]
    cases hk : S.resolves[k]? with
    | none => exact heq
    | some r =>
      dsimp only
      have hmem := List.mem_of_getElem? hk
      have hsum := sumBy_eraseIdx Rs.unsettled hk
      have hok := hr r hmem
      have hl' := hl r hk
      have hmax := held_le_max hR
      have hbt := bal_le_total S.L.bals r.owner
      have hun : r.refund = r.unsettled := by
        unfold Rs.unsettled
        rcases hok.2 with h' | h'
        · omega
        · exact absurd ⟨h'.1, h'.2.1, h'.2.2.1⟩ hl'
      by_cases h0 : r.refund = 0
      · simp only [resolveWithdraw, ifP h0]
        books; omega
      · have hcr := credit_of (L := S.L) (a := r.owner) (x := r.refund) (by omega) (by omega)
          (by omega)
        simp only [resolveWithdraw, ifN h0, hcr]
        books; omega
  | resolveWdFails k =>
    simp only [stdStep, step]
    by_cases hk : ∃ r, S.resolves[k]? = some r
    · obtain ⟨r, hk⟩ := hk
      have hsum := sumBy_eraseIdx Rs.unsettled hk
      have hl' := hl r hk
      books; omega
    · have hnone : S.resolves[k]? = none := by
        cases h : S.resolves[k]? with
        | none => rfl
        | some r => exact absurd ⟨r, h⟩ hk
      have hlen : S.resolves.length ≤ k := by
        rcases Nat.lt_or_ge k S.resolves.length with h | h
        · rw [List.getElem?_eq_getElem h] at hnone; exact absurd hnone (by simp)
        · exact h
      rw [List.eraseIdx_of_length_le hlen]
      exact heq
  | move auth src dst amt =>
    simp only [stdStep, step]
    cases hm : moveBal S.L auth src dst amt with
    | none => exact heq
    | some L' =>
      obtain ⟨_, _, _, _, _, rfl⟩ := moveBal_some hm
      books; exact hq
  | admin a =>
    simp only [stdStep, step]
    books; exact hq

/-- A run all of whose steps are lossless. -/
def LosslessRun (K : Cfg) : World → List Step → Prop
  | _, [] => True
  | S, st :: t => Lossless K S st ∧ LosslessRun K (stdStep K S st) t

theorem reachExact_run {K : Cfg} {S : World} (h : ReachExact K S) (l : List Step)
    (hl : LosslessRun K S l) : ReachExact K (run K (exec K.tok) S l) := by
  induction l generalizing S with
  | nil => exact h
  | cons st t ih => exact ih (ReachExact.step st hl.1 h) hl.2

/-- **T1 with equality: every token is accounted for.** Starting from a contract that holds no
    tokens, as long as none of the four losing events of `Lossless` happens, in every state:
    ledger total + what is owed in flight = the contract's token balance. -/
theorem T1_exact (K : Cfg) (hE : K.tok.Sane) (S : World) (h : ReachExact K S) :
    S.L.supply + owed S = bal S.c.accts K.me := by
  induction h with
  | init S h h0 =>
    unfold owed
    rw [h.supply, h.unwrap, h.outbox, h.resolves, h.pend, h0]; simp [sumBy]
  | step st hl hprev ih => exact exact_step K hE (reachExact_reach hprev) ih st hl

/-- **T1, equality in a quiet state.** Under the same conditions, when nothing of the contract
    is in flight the sum of the ledger balances *equals* the contract's token balance. -/
theorem T1_equality (K : Cfg) (hE : K.tok.Sane) (S : World) (h : ReachExact K S)
    (hq : Quiet K S) : total S.L.bals = bal S.c.accts K.me := by
  have hR := reachExact_reach h
  have he := T1_exact K hE S h
  obtain ⟨_, hd, _, _⟩ := T1_quiet K S hR hq
  obtain ⟨h1, h2, h3, _⟩ := hq
  have hcons := T1_supply K S hR
  unfold owed at he
  unfold uncredited at hd
  rw [h1, h2, h3, hd] at he
  simp only [sumBy] at he
  omega

end Intents
