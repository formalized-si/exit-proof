/-
  The token's side of the two-contract world is the transition system of the proved wNEAR
  model: every step of the world is zero, one or two steps of `WNear.sysStep` on the token's
  state, its callbacks in flight and the NEAR it has sent. So every statement of the wNEAR proof
  that holds along `WNear.sysStep` (conservation, solvency, who can lower a wNEAR balance, the
  exit of any holder) holds inside this world too.
-/
import IntentsW.Theorems

namespace IntentsW
open ProvedFT (Acct)
open Intents

/-- A call by an account other than wNEAR itself, in the wNEAR model and in the world, when it
    adds callbacks `anns` with the right raw content. -/
theorem toSys_call {K : Cfg} {S : World} {p : Acct} {d : Nat} {m : WNear.Method}
    {rs : List WNear.PR} {o : WNear.Out} (hp : p ≠ K.tok.self)
    (he : WNear.exec K.tok S.c ⟨p, d, m, rs⟩ = some o) (anns : List Pend)
    (hraw : anns.map Pend.raw = o.calls) :
    (⟨o.st, S.pend.map Pend.raw ++ anns.map Pend.raw, S.paid ++ o.transfers⟩ : WNear.Sys) =
      WNear.sysStep K.tok (toSys S) (.call p d m rs) := by
  simp only [WNear.sysStep, toSys, ifN hp, he, hraw]

/-- **Every step of the world is zero, one or two steps of the proved wNEAR model on the
    token's side.** `hme`: the Intents contract is not the wNEAR account. -/
theorem tok_step (K : Cfg) (hme : K.me ≠ K.tok.self) (S : World) (st : Step) :
    ∃ l : List WNear.Step, toSys (step K S st) = l.foldl (WNear.sysStep K.tok) (toSys S) := by
  cases st with
  | tokCall p d m rs =>
    simp only [step]
    by_cases hpm : p = K.me ∨ p = K.tok.self
    · rw [ifP hpm]; exact ⟨[], rfl⟩
    · rw [ifN hpm]
      have hp2 : p ≠ K.tok.self := fun h => hpm (Or.inr h)
      cases he : WNear.exec K.tok S.c ⟨p, d, m, rs⟩ with
      | none => exact ⟨[], rfl⟩
      | some o =>
        refine ⟨[.call p d m rs], ?_⟩
        simp only [List.foldl_cons, List.foldl_nil]
        rw [← toSys_call hp2 he (annThird K.me o.calls) (raw_annThird _ _)]
        simp only [toSys, List.map_append]
  | tokResolve i res =>
    simp only [step]
    cases hpi : S.pend[i]? with
    | none => exact ⟨[], rfl⟩
    | some e =>
      dsimp only
      cases hro : resOfW e res with
      | none => exact ⟨[], rfl⟩
      | some r =>
        dsimp only
        refine ⟨[.resolve i r], ?_⟩
        have hraw : (S.pend.map Pend.raw)[i]? = some (e.sender, e.receiver, e.amount) := by
          rw [List.getElem?_map, hpi]; rfl
        simp only [List.foldl_cons, List.foldl_nil, WNear.sysStep, toSys, hraw]
        cases he : WNear.exec K.tok S.c
            ⟨K.tok.self, 0, .ft_resolve_transfer e.sender e.receiver e.amount, [r]⟩ with
        | none => simp only [map_eraseIdx]
        | some o => simp only [List.map_append, map_eraseIdx, raw_annThird]
  | tokResolveFails i =>
    simp only [step]
    cases hpi : S.pend[i]? with
    | none => exact ⟨[], rfl⟩
    | some e =>
      dsimp only
      cases hro : resOfW e .failed with
      | none => exact ⟨[], rfl⟩
      | some r =>
        refine ⟨[.resolveFails i], ?_⟩
        simp only [List.foldl_cons, List.foldl_nil, WNear.sysStep, toSys, map_eraseIdx]
  | tokNearIn x =>
    refine ⟨[.nearIn x], ?_⟩
    simp only [step, List.foldl_cons, List.foldl_nil, WNear.sysStep, toSys]
    by_cases hx : S.c.near + x ≤ K.tok.cap
    · rw [ifP hx, ifP hx]
    · rw [ifN hx, ifN hx]
  | onTransfer i recv ok =>
    refine ⟨[], ?_⟩
    simp only [step, List.foldl_nil]
    cases hpi : S.pend[i]? with
    | none => rfl
    | some e =>
      dsimp only
      by_cases hg : e.receiver = K.me ∧ e.ann = .dep none
      · rw [ifP hg]
        split
        · simp only [toSys]
          rw [map_set_same Pend.raw hpi { e with ann := .dep (some true) } rfl]
        · simp only [toSys]
          rw [map_set_same Pend.raw hpi { e with ann := .dep (some false) } rfl]
      · rw [ifN hg]
  | ftWithdraw via w =>
    refine ⟨[], ?_⟩
    simp only [step, List.foldl_nil]
    split
    · rfl
    · split <;> rfl
  | unwrap owner x f =>
    refine ⟨[], ?_⟩
    simp only [step, List.foldl_nil]
    split
    · rfl
    · split <;> rfl
  | nearWithdraw j =>
    simp only [step]
    cases hjj : S.jobs[j]? with
    | none => exact ⟨[], rfl⟩
    | some u =>
      dsimp only
      cases he : WNear.exec K.tok S.c ⟨K.me, 1, .near_withdraw u.amount, []⟩ with
      | none => exact ⟨[], rfl⟩
      | some o =>
        refine ⟨[.call K.me 1 (.near_withdraw u.amount) []], ?_⟩
        simp only [List.foldl_cons, List.foldl_nil]
        rw [← toSys_call hme he (annThird K.me o.calls) (raw_annThird _ _)]
        simp only [toSys, List.map_append]
  | nearWithdrawFails j =>
    refine ⟨[], ?_⟩
    simp only [step, List.foldl_nil]
    split <;> rfl
  | doJob k ok =>
    refine ⟨[], ?_⟩
    simp only [step, List.foldl_nil]
    split
    · rfl
    · split <;> rfl
  | tokXfer j =>
    simp only [step]
    cases hjj : S.outbox[j]? with
    | none => exact ⟨[], rfl⟩
    | some w =>
      dsimp only
      cases hsd : w.sd with
      | none =>
        have hb : xferBatchW K.tok K.me S.c w =
            WNear.exec K.tok S.c ⟨K.me, 1, xferMethodW w, []⟩ := by
          simp only [xferBatchW, hsd]
        rw [hb]
        cases he : WNear.exec K.tok S.c ⟨K.me, 1, xferMethodW w, []⟩ with
        | none => exact ⟨[], rfl⟩
        | some o =>
          refine ⟨[.call K.me 1 (xferMethodW w) []], ?_⟩
          simp only [List.foldl_cons, List.foldl_nil]
          rw [← toSys_call hme he (annWd w.owner o.calls) (raw_annWd _ _)]
          simp only [toSys, List.map_append]
      | some d =>
        cases h1 : WNear.exec K.tok S.c ⟨K.me, d, .storage_deposit (some w.receiver), []⟩ with
        | none =>
          have hb : xferBatchW K.tok K.me S.c w = none := by
            simp only [xferBatchW, hsd, h1]
          rw [hb]; exact ⟨[], rfl⟩
        | some o1 =>
          cases h2 : WNear.exec K.tok o1.st ⟨K.me, 1, xferMethodW w, []⟩ with
          | none =>
            have hb : xferBatchW K.tok K.me S.c w = none := by
              simp only [xferBatchW, hsd, h1, h2]
            rw [hb]; exact ⟨[], rfl⟩
          | some o2 =>
            have hb : xferBatchW K.tok K.me S.c w =
                some ⟨o2.st, o1.transfers ++ o2.transfers, o1.calls ++ o2.calls, o2.ret⟩ := by
              simp only [xferBatchW, hsd, h1, h2]
            rw [hb]
            refine ⟨[.call K.me d (.storage_deposit (some w.receiver)) [],
              .call K.me 1 (xferMethodW w) []], ?_⟩
            simp only [List.foldl_cons, List.foldl_nil, WNear.sysStep, toSys, ifN hme, h1, h2,
              List.map_append, raw_annWd, List.append_assoc]
  | tokXferFails j =>
    refine ⟨[], ?_⟩
    simp only [step, List.foldl_nil]
    split <;> rfl
  | meStorageDeposit acc d =>
    simp only [step]
    cases he : WNear.exec K.tok S.c ⟨K.me, d, .storage_deposit (some acc), []⟩ with
    | none => exact ⟨[], rfl⟩
    | some o =>
      refine ⟨[.call K.me d (.storage_deposit (some acc)) []], ?_⟩
      simp only [List.foldl_cons, List.foldl_nil]
      rw [← toSys_call hme he (annThird K.me o.calls) (raw_annThird _ _)]
      simp only [toSys, List.map_append]
  | resolveWd k =>
    refine ⟨[], ?_⟩
    simp only [step, List.foldl_nil]
    split
    · rfl
    · split <;> rfl
  | resolveWdFails k => exact ⟨[], rfl⟩
  | move auth src dst amt =>
    refine ⟨[], ?_⟩
    simp only [step, List.foldl_nil]
    split <;> rfl
  | admin a => exact ⟨[], rfl⟩

/-- **The token in the two-contract world is the proved wNEAR model.** The token's side of a
    reachable world is the result of running `WNear.sysStep` from the token's side of a start
    state. -/
theorem tok_run {K : Cfg} (hme : K.me ≠ K.tok.self) {S : World} (h : Reach K S) :
    ∃ (S0 : World) (l : List WNear.Step), Init K S0 ∧
      toSys S = l.foldl (WNear.sysStep K.tok) (toSys S0) := by
  induction h with
  | init S h => exact ⟨S, [], h, rfl⟩
  | step st _ ih =>
    obtain ⟨S0, l, h0, hl⟩ := ih
    obtain ⟨l2, hl2⟩ := tok_step K hme _ st
    exact ⟨S0, l ++ l2, h0, by rw [hl2, hl, List.foldl_append]⟩

theorem reach_foldl {E : WNear.Env} {X : WNear.Sys} (h : WNear.Reach E X) (l : List WNear.Step) :
    WNear.Reach E (l.foldl (WNear.sysStep E) X) := by
  induction l generalizing X with
  | nil => exact h
  | cons st t ih => exact ih (WNear.Reach.step st h)

/-- If the world starts from a token state that wNEAR reaches from its `new()`, the token in
    every reachable world is such a state too, so the theorems of the wNEAR proof stated for
    `WNear.Reach` (`exit_always`, `T_conservation`) apply to it. -/
theorem tok_reach {K : Cfg} (hme : K.me ≠ K.tok.self) {S : World} (h : Reach K S) :
    ∃ S0 : World, Init K S0 ∧
      (WNear.Reach K.tok (toSys S0) → WNear.Reach K.tok (toSys S)) := by
  obtain ⟨S0, l, h0, hl⟩ := tok_run hme h
  exact ⟨S0, h0, fun hr => by rw [hl]; exact reach_foldl hr l⟩

end IntentsW
