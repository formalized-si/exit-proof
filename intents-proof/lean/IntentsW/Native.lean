/-
  The unwrap paths: the contract debits wNEAR from a ledger balance, calls `near_withdraw` on
  wNEAR, and its `do_*` callback sends the NEAR on (`NativeWithdraw`, `StorageDeposit`,
  `AuthCall` with a deposit, any withdrawal with `storage_deposit`).

  * N1 the debit            `N1_debit`, `N1_start`
  * N2 the burn             `N2_burn` (the wNEAR burned is exactly the amount debited, and
                            wNEAR sends back exactly that amount plus the attached yocto),
                            `N2_unwrap_succeeds`, `N2_burn_is_debit` (in a reachable state the
                            receipt cannot fail for a reason of state)
  * N3 the NEAR sent on     `N3_forward` (the callback sends the debited amount, and only after
                            a successful unwrap), `N3_books`, `N3_near_le` (in every reachable
                            state: NEAR sent on ≤ wNEAR burned ≤ NEAR received from wNEAR, and
                            wNEAR burned ≤ wNEAR debited)
  * N4 failures             `N4_unwrap_fails`, `N4_callback_fails`, `N4_no_refund`,
                            `N4_withdrawal_refund` (which receipt failed → what the ledger, the
                            wNEAR held and the NEAR do; the table is in NOTES.md)
-/
import IntentsW.Theorems

namespace IntentsW
open ProvedFT (Acct Accts bal set total U128_MAX bal_set_self bal_set_ne)
open Intents

/-! ## N1 The debit -/

/-- **N1. The debit of an unwrap.** It takes exactly `x > 0` from the owner's ledger balance of
    `nep141:<wNEAR>` and from the total, touches no other balance, and needs: intents not
    paused, the owner not locked. -/
theorem N1_debit (L L' : Ledger) (owner : Acct) (x : Nat) (h : startUnwrap L owner x = some L') :
    0 < x ∧ bal L'.bals owner + x = bal L.bals owner ∧
    (∀ a, a ≠ owner → bal L'.bals a = bal L.bals a) ∧
    L'.supply + x = L.supply ∧ L'.ctl = L.ctl ∧
    L.ctl.isPaused "intents" = false ∧ L.ctl.locked.contains owner = false := by
  obtain ⟨hpz, _, hd⟩ := startUnwrap_some h
  obtain ⟨hpos, hlock, hle, hles, rfl⟩ := debit_some hd
  refine ⟨hpos, ?_, fun a ha => ?_, ?_, rfl, hpz, by simpa using hlock⟩
  · simp only; rw [bal_set_self]; omega
  · simp only; rw [bal_set_ne _ _ (Ne.symm ha)]
  · simp only; omega

/-- **N1, the step.** A successful unwrap intent changes the ledger by that debit and puts
    exactly one `near_withdraw(x)` in flight; wNEAR is not touched yet. -/
theorem N1_start (K : Cfg) (S : World) (owner : Acct) (x : Nat) (f : Fwd) (hf : f.isWd = false)
    (L' : Ledger) (h : startUnwrap S.L owner x = some L') :
    let S' := step K S (.unwrap owner x f)
    S'.L = L' ∧ S'.jobs = S.jobs ++ [⟨owner, x, f⟩] ∧ S'.c = S.c ∧ S'.ready = S.ready ∧
    S'.uDebited = S.uDebited + x := by
  intro S'
  have hf' : ¬ f.isWd = true := by rw [hf]; exact Bool.false_ne_true
  have hS' : S' = { S with
      L := L', jobs := S.jobs ++ [⟨owner, x, f⟩], uDebited := S.uDebited + x } := by
    simp only [S', step, ifN hf', h]
  rw [hS']
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## N2 The burn -/

/-- **N2. The wNEAR burned is exactly what was debited.** When the `near_withdraw` receipt of a
    job executes successfully on wNEAR, the contract's wNEAR balance and wNEAR's total supply
    drop by exactly the job's amount — the amount debited from the ledger when the job
    started — nobody else's wNEAR balance changes, and wNEAR sends the contract exactly one
    NEAR transfer, of that amount plus the 1 yoctoNEAR that was attached. The ledger is not
    touched. -/
theorem N2_burn (K : Cfg) (S : World) (j : Nat) (u : Job) (hj : S.jobs[j]? = some u)
    (o : WNear.Out)
    (he : WNear.exec K.tok S.c ⟨K.me, 1, .near_withdraw u.amount, []⟩ = some o) :
    let S' := step K S (.nearWithdraw j)
    WNear.bal S'.c.accts K.me + u.amount = WNear.bal S.c.accts K.me ∧
    S'.c.supply + u.amount = S.c.supply ∧
    (∀ a, a ≠ K.me → WNear.bal S'.c.accts a = WNear.bal S.c.accts a) ∧
    S'.c.near + u.amount = S.c.near ∧
    S'.paid = S.paid ++ [(K.me, u.amount + 1)] ∧
    S'.jobs = S.jobs.eraseIdx j ∧ S'.ready = S.ready ++ [⟨u, true⟩] ∧ S'.L = S.L ∧
    S'.uBurned = S.uBurned + u.amount ∧ S'.nGot = S.nGot + (u.amount + 1) := by
  intro S'
  obtain ⟨h1, h2, h3, hcalls, htr, _, h7⟩ := nw_exec he
  have hS' : S' = { S with
      c := o.st
      pend := S.pend ++ annThird K.me o.calls
      paid := S.paid ++ o.transfers
      jobs := S.jobs.eraseIdx j
      ready := S.ready ++ [⟨u, true⟩]
      uBurned := S.uBurned + (WNear.bal S.c.accts K.me - WNear.bal o.st.accts K.me)
      nGot := S.nGot + WNear.sumT o.transfers } := by
    simp only [S', step, hj, he]
  rw [hS']
  refine ⟨h1, h2, h3, h7, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · simp only; rw [htr]
  · simp only; omega
  · simp only; rw [htr, WNear.sumT_one]

/-- **N2, the receipt cannot fail for a reason of state.** In a reachable state, for every
    unwrap in flight, `near_withdraw` succeeds when it executes: the contract is registered on
    wNEAR and holds at least the amount (W1), and wNEAR is solvent (the invariant of its model).
    `hE`: the deployment parameters of the wNEAR model; `hcap`: wNEAR's NEAR balance is below the
    bound on any NEAR balance. What is left is a failure before the receipt runs (out of gas),
    which is `Step.nearWithdrawFails`. -/
theorem N2_unwrap_succeeds (K : Cfg) (hE : K.tok.Sane) (S : World) (h : Reach K S)
    (hcap : S.c.near < K.tok.cap) (j : Nat) (u : Job) (hj : S.jobs[j]? = some u) :
    ∃ o, WNear.exec K.tok S.c ⟨K.me, 1, .near_withdraw u.amount, []⟩ = some o := by
  have hT := tok_inv h
  obtain ⟨hcov, hpos⟩ := W1_can_unwrap K S h j u hj
  have hbal : 0 < WNear.bal S.c.accts K.me := by omega
  obtain ⟨b, hb⟩ := WNear.get_of_bal_pos hbal
  have hbb : WNear.bal S.c.accts K.me = b := WNear.bal_of_some hb
  exact nw_succeeds hE hT.pre hT.solvent hcap hb (by omega)

/-- **N2, in a reachable state.** The step that executes the `near_withdraw` of a job burns
    exactly the debited amount and brings back exactly that amount plus one yocto. -/
theorem N2_burn_is_debit (K : Cfg) (hE : K.tok.Sane) (S : World) (h : Reach K S)
    (hcap : S.c.near < K.tok.cap) (j : Nat) (u : Job) (hj : S.jobs[j]? = some u) :
    let S' := step K S (.nearWithdraw j)
    WNear.bal S'.c.accts K.me + u.amount = WNear.bal S.c.accts K.me ∧
    S'.c.supply + u.amount = S.c.supply ∧
    S'.paid = S.paid ++ [(K.me, u.amount + 1)] ∧
    S'.ready = S.ready ++ [⟨u, true⟩] ∧ S'.L = S.L := by
  obtain ⟨o, he⟩ := N2_unwrap_succeeds K hE S h hcap j u hj
  obtain ⟨h1, h2, _, _, h5, _, h7, h8, _⟩ := N2_burn K S j u hj o he
  exact ⟨h1, h2, h5, h7, h8⟩

/-! ## N3 The NEAR sent on -/

/-- **N3. What the callback sends on.** The `do_*` callback of a ready job never touches the
    ledger or wNEAR. If the unwrap succeeded and the callback runs, it sends on exactly the
    job's amount of NEAR — one yocto less than the unwrap brought in — and, for a withdrawal of
    wNEAR itself, releases the token receipt. Otherwise it sends nothing; for a withdrawal of
    wNEAR itself the chained `ft_resolve_withdraw` then reads a failure. -/
theorem N3_forward (K : Cfg) (S : World) (k : Nat) (r : Ready) (hk : S.ready[k]? = some r)
    (ok : Bool) :
    let S' := step K S (.doJob k ok)
    S'.L = S.L ∧ S'.c = S.c ∧ S'.ready = S.ready.eraseIdx k ∧ S'.jobs = S.jobs ∧
    (r.ok = true ∧ ok = true →
      S'.nFwd = S.nFwd + r.job.amount ∧ S'.outbox = S.outbox ++ r.job.fwd.sent ∧
      S'.resolves = S.resolves) ∧
    (¬(r.ok = true ∧ ok = true) →
      S'.nFwd = S.nFwd ∧ S'.outbox = S.outbox ∧
      S'.resolves = S.resolves ++ r.job.fwd.failedRs) := by
  intro S'
  by_cases hgo : r.ok = true ∧ ok = true
  · have hS' : S' = { S with
        ready := S.ready.eraseIdx k
        outbox := S.outbox ++ r.job.fwd.sent
        nFwd := S.nFwd + r.job.amount } := by
      simp only [S', step, hk, ifP hgo]
    rw [hS']
    exact ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun hn => absurd hgo hn⟩
  · have hS' : S' = { S with
        ready := S.ready.eraseIdx k, resolves := S.resolves ++ r.job.fwd.failedRs } := by
      simp only [S', step, hk, ifN hgo]
    rw [hS']
    exact ⟨rfl, rfl, rfl, rfl, fun hy => absurd hy hgo, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- **N3, the books of the unwrap paths, in every reachable state.**
    * every wNEAR debited for unwrapping is burned, or kept because its `near_withdraw` failed,
      or its `near_withdraw` is still in flight;
    * the NEAR sent on, plus what ready callbacks may still send, is at most the wNEAR burned;
    * the wNEAR burned is at most the NEAR wNEAR sent to the contract for it. -/
theorem N3_books (K : Cfg) (S : World) (h : Reach K S) :
    S.uDebited = S.uBurned + S.uKept + sumBy Job.amount S.jobs ∧
    S.nFwd + sumBy Ready.live S.ready ≤ S.uBurned ∧ S.uBurned ≤ S.nGot := by
  have hB := books_reach h
  exact ⟨hB.burn, hB.near, hB.got⟩

/-- **N3, the plain reading.** In every reachable state the NEAR the unwrap paths have sent on
    is at most the wNEAR they burned, which is at most the wNEAR debited from ledger balances
    for them, and at most the NEAR the unwrapping returned. -/
theorem N3_near_le (K : Cfg) (S : World) (h : Reach K S) :
    S.nFwd ≤ S.uBurned ∧ S.uBurned ≤ S.uDebited ∧ S.uBurned ≤ S.nGot ∧ S.nFwd ≤ S.nGot := by
  obtain ⟨h1, h2, h3⟩ := N3_books K S h
  refine ⟨by omega, by omega, h3, by omega⟩

/-! ## N4 Failures -/

/-- **N4, `near_withdraw` fails.** The ledger keeps the debit, wNEAR is not touched (the wNEAR
    stays in the contract's balance; `W1_kept`), and the callback will read a failure. -/
theorem N4_unwrap_fails (K : Cfg) (S : World) (j : Nat) (u : Job) (hj : S.jobs[j]? = some u) :
    let S' := step K S (.nearWithdrawFails j)
    S'.L = S.L ∧ S'.c = S.c ∧ S'.jobs = S.jobs.eraseIdx j ∧ S'.ready = S.ready ++ [⟨u, false⟩] ∧
    S'.uKept = S.uKept + u.amount ∧ S'.uBurned = S.uBurned ∧ S'.nGot = S.nGot ∧
    S'.nFwd = S.nFwd := by
  intro S'
  have hS' : S' = { S with
      jobs := S.jobs.eraseIdx j
      ready := S.ready ++ [⟨u, false⟩]
      uKept := S.uKept + u.amount } := by
    simp only [S', step, hj]
  rw [hS']
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What follows a job that is not a withdrawal of wNEAR itself: nothing. -/
theorem not_wd_nothing {f : Fwd} (h : f.isWd = false) : f.failedRs = [] ∧ f.sent = [] := by
  cases f with
  | ftw w => exact absurd h (by simp [Fwd.isWd])
  | native r => exact ⟨rfl, rfl⟩
  | storage c a => exact ⟨rfl, rfl⟩
  | auth c => exact ⟨rfl, rfl⟩
  | other t r => exact ⟨rfl, rfl⟩

/-- **N4, the callback of a failed or dropped unwrap.** For `NativeWithdraw`, `StorageDeposit`,
    `AuthCall` and the storage deposit of a withdrawal of another token id: whatever the
    outcome of the unwrap and of the callback, the callback changes neither the ledger nor
    wNEAR and leaves nothing behind that could; when the unwrap failed or the callback did not
    run, no NEAR is sent on. Together with `W3_credit_only_on_arrival`: the debit is final. -/
theorem N4_callback_fails (K : Cfg) (S : World) (k : Nat) (r : Ready)
    (hk : S.ready[k]? = some r) (hf : r.job.fwd.isWd = false) (ok : Bool) :
    let S' := step K S (.doJob k ok)
    S'.L = S.L ∧ S'.c = S.c ∧ S'.resolves = S.resolves ∧ S'.outbox = S.outbox ∧
    S'.ready = S.ready.eraseIdx k ∧
    (¬(r.ok = true ∧ ok = true) → S'.nFwd = S.nFwd) := by
  obtain ⟨h1, h2, h3, _, h5, h6⟩ := N3_forward K S k r hk ok
  obtain ⟨e1, e2⟩ := not_wd_nothing hf
  by_cases hgo : r.ok = true ∧ ok = true
  · obtain ⟨_, a2, a3⟩ := h5 hgo
    exact ⟨h1, h2, a3, by rw [a2, e2, List.append_nil], h3, fun hn => absurd hgo hn⟩
  · obtain ⟨a1, a2, a3⟩ := h6 hgo
    exact ⟨h1, h2, by rw [a3, e1, List.append_nil], a2, h3, fun _ => a1⟩

/-- **N4, no step gives the unwrapped amount back.** A step that raises the ledger total is a
    deposit that arrived or the refund of a withdrawal of wNEAR by `ft_resolve_withdraw`
    (`W3_credit_only_on_arrival`); the steps of the unwrap paths themselves never raise it. -/
theorem N4_no_refund (K : Cfg) (S : World) (st : Step)
    (hst : (∃ j, st = .nearWithdraw j) ∨ (∃ j, st = .nearWithdrawFails j) ∨
      (∃ k ok, st = .doJob k ok)) :
    (step K S st).L = S.L := by
  rcases hst with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨k, ok, rfl⟩
  · simp only [step]
    split
    · rfl
    · split <;> rfl
  · simp only [step]
    split <;> rfl
  · simp only [step]
    split
    · rfl
    · split <;> rfl

/-- **N4, a withdrawal of wNEAR with a storage deposit whose unwrap or callback failed.** The
    `ft_resolve_withdraw` that follows reads a failure for the withdrawal's own amount only:
    it gives back that amount when the withdrawal was a plain `ft_transfer`, nothing when it
    was an `ft_transfer_call` (the exception of `W2_settles`). The storage deposit is not part
    of it and stays debited. -/
theorem N4_withdrawal_refund (w : Wd) :
    (Fwd.ftw w).failedRs = [⟨w.owner, w.amount, w.msg.isSome, .failed, 0⟩] ∧
    (Rs.mk w.owner w.amount w.msg.isSome .failed 0).refund =
      (if w.msg.isSome then 0 else w.amount) := by
  refine ⟨rfl, ?_⟩
  cases hm : w.msg.isSome with
  | true => simp [refund_call_failed]
  | false => simp [refund_plain_failed]

end IntentsW
