"""Adequacy of the replay: one-line changes of the Lean model of the ledger must show up as disagreements
with the receipts recorded from the deployed wasm.

For a mutant only the executable model is rebuilt. The lemmas stated next to the definitions are dropped first:
a mutant makes some of them false (they stop compiling, which is their job), and they are not needed to run
the model.

A change listed with a reason why no receipt can tell it apart (EQUIVALENT) is replayed like the others and must
give no disagreement; for it the theorems are built as well, to see whether the proofs reject what the replay
cannot see.

usage: model_mutants.py <lean dir> <trace file> <work dir> [<result.json>]
environment: MUT_JOBS (default 6) mutants are built and replayed at a time; MUT_ONLY (e.g. "X8,X9") runs the
control and the named changes only.
"""
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys

SRC, TRACE, WORK = (os.path.abspath(a) for a in sys.argv[1:4])
OUT = os.path.abspath(sys.argv[4]) if len(sys.argv) > 4 else os.path.join(WORK, "..", "model_mutants.json")
JOBS = int(os.environ.get("MUT_JOBS", "6"))
NL = chr(10)
LEDGER = "Intents/Ledger.lean"
WORLD_W = "IntentsW/World.lean"
WORLD = "Intents/World.lean"
AUTH = "Intents/Auth.lean"
STRICT = "Intents/Strict.lean"
# (id, what changes, file, old text, new text, None | why no receipt can tell it apart)
MUTANTS = [
    ("M0_control", "no change", LEDGER, None, None, None),
    ("M1_credit_supply_plus_one", "a credit adds one unit too many to the total supply", LEDGER,
     "supply := L.supply + x }", "supply := L.supply + x + 1 }", None),
    ("M2_credit_balance_plus_one", "a credit adds one unit too many to the account", LEDGER,
     "set L.bals a (bal L.bals a + x), supply", "set L.bals a (bal L.bals a + x + 1), supply", None),
    ("M3_debit_ignores_lock", "a locked account can spend", LEDGER,
     "else if L.ctl.locked.contains a = true ∧ force = false then none",
     "else if false = true ∧ force = false then none", None),
    ("M4_debit_keeps_supply", "a debit does not lower the total supply", LEDGER,
     "supply := L.supply - x }", "supply := L.supply }", None),
    ("M5_resolve_refunds_all", "the withdrawal callback credits back the whole amount", LEDGER,
     "if r.refund = 0 then some L else credit L r.owner r.refund",
     "if r.amount = 0 then some L else credit L r.owner r.amount", None),
    ("M6_resolve_never_refunds", "the withdrawal callback never credits back", LEDGER,
     "if r.refund = 0 then some L else credit L r.owner r.refund", "some L", None),
    ("M7_failed_call_refunded", "a failed transfer_call is treated as nothing delivered", LEDGER,
     "| .failed => r.amount" + NL + "    | .ok b =>", "| .failed => 0" + NL + "    | .ok b =>", None),
    ("M8_unparsable_means_used", "an unparsable reply of transfer_call is treated as everything delivered", LEDGER,
     "| none => 0)", "| none => r.amount)", None),
    ("M9_failed_transfer_kept", "a failed plain transfer is treated as delivered", LEDGER,
     "| .ok [] => r.amount" + NL + "    | _ => 0", "| .ok [] => r.amount" + NL + "    | _ => r.amount", None),
    ("M10_pause_ignored", "pause switches are ignored", LEDGER,
     'c.paused.contains key || c.paused.contains "ALL"', "false", None),
    ("M11_long_reply_refunded", "an over-long reply of transfer_call is treated as nothing delivered", LEDGER,
     "| none => 0)" + NL + "      else r.amount", "| none => 0)" + NL + "      else 0", None),
    # written by an independent reviewer
    ("X1_auth_flag_ignored", "ft_withdraw ignores the auth-by-predecessor flag", LEDGER,
     ' && !c.isPaused "ft_withdraw" && !c.authOff.contains p', ' && !c.isPaused "ft_withdraw"', None),
    ("X2_force_by_anyone", "ft_force_withdraw needs no role", LEDGER,
     "| .force who => c.any who [.DAO, .UnrestrictedWithdrawer] && w.sd.isNone",
     "| .force who => (c.any who [.DAO, .UnrestrictedWithdrawer] || true) && w.sd.isNone", None),
    ("X3_force_only_dao", "ft_force_withdraw only for DAO", LEDGER,
     "| .force who => c.any who [.DAO, .UnrestrictedWithdrawer] && w.sd.isNone",
     "| .force who => c.any who [.DAO] && w.sd.isNone", None),
    ("X4_force_not_dao", "ft_force_withdraw refused to DAO", LEDGER,
     "| .force who => c.any who [.DAO, .UnrestrictedWithdrawer] && w.sd.isNone",
     "| .force who => c.any who [.UnrestrictedWithdrawer] && w.sd.isNone", None),
    ("X5_credit_no_overflow_check", "a credit has no overflow guard", LEDGER,
     "else if L.supply + x ≤ U128_MAX ∧ bal L.bals a + x ≤ U128_MAX then", "else if True then", None),
    ("X6_debit_zero_ok", "a zero withdrawal is accepted", LEDGER,
     "(force : Bool) : Option Ledger :=" + NL + "  if x = 0 then none",
     "(force : Bool) : Option Ledger :=" + NL + "  if False then none", None),
    ("X7_credit_zero_ok", "a zero deposit is accepted", LEDGER,
     "(x : Nat) : Option Ledger :=" + NL + "  if x = 0 then none",
     "(x : Nat) : Option Ledger :=" + NL + "  if False then none", None),
    ("X8_json_limit_43", "reply length limit 43 instead of 44", LEDGER,
     "def U128_JSON_MAX : Nat := 44", "def U128_JSON_MAX : Nat := 43", None),
    ("X9_json_limit_45", "reply length limit 45 instead of 44", LEDGER,
     "def U128_JSON_MAX : Nat := 44", "def U128_JSON_MAX : Nat := 45", None),
    ("X10_json_limit_1000", "reply length limit 1000", LEDGER,
     "def U128_JSON_MAX : Nat := 44", "def U128_JSON_MAX : Nat := 1000", None),
    ("X11_used_not_capped", "the used amount reported by the token is not capped by the amount", LEDGER,
     "| some v => min v r.amount", "| some v => v", None),
    ("X12_self_move_ok", "an internal move to oneself is accepted", LEDGER,
     "if src = dst ∨ amt = 0 then none", "if amt = 0 then none", None),
    ("X13_zero_move_ok", "an internal move of zero is accepted", LEDGER,
     "if src = dst ∨ amt = 0 then none", "if src = dst then none", None),
    ("X14_locked_can_move", "a locked account can move its balance", LEDGER,
     "| .owner => !c.locked.contains src", "| .owner => true", None),
    ("X15_intents_pause_ignored", "an FtWithdraw intent ignores the intents pause", LEDGER,
     '| .intent => !c.isPaused "intents"', "| .intent => true", None),
    ("X16_unpauser_can_pause", "UnpauseManager can pause", LEDGER,
     "if c.any who [.DAO, .PauseManager] then", "if c.any who [.DAO, .PauseManager, .UnpauseManager] then", None),
    ("X17_anyone_can_pause", "anyone can pause", LEDGER,
     "if c.any who [.DAO, .PauseManager] then", "if true then", None),
    ("X18_anyone_can_lock", "anyone can lock an account", LEDGER,
     "if c.any who [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager] then" + NL
     + "      { c with locked := a :: c.locked }",
     "if true then" + NL + "      { c with locked := a :: c.locked }", None),
    ("X19_anyone_can_unlock", "anyone can unlock an account", LEDGER,
     "if c.any who [.DAO, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager] then" + NL
     + "      { c with locked := c.locked.filter fun x => x != a }",
     "if true then" + NL + "      { c with locked := c.locked.filter fun x => x != a }", None),
    ("X20_nonempty_ok_is_delivered", "a plain transfer that returns a non-empty value counts as delivered", LEDGER,
     "| .ok [] => r.amount" + NL + "    | _ => 0", "| .ok _ => r.amount" + NL + "    | _ => 0", None),
    ("X21_withdraw_for_others", "ft_withdraw may debit another owner", LEDGER,
     "p == w.owner && w.sd.isNone && !c.isPaused", "w.sd.isNone && !c.isPaused",
     "ft_withdraw(token, receiver_id, amount, memo, msg) has no owner argument: the wasm debits the predecessor, so "
     "every receipt is Via.method p with w.owner = p, and on those inputs the changed guard equals the original"),
    ("X22_force_respects_lock", "a forced withdrawal is stopped by a lock", LEDGER,
     "else if L.ctl.locked.contains a = true ∧ force = false then none",
     "else if L.ctl.locked.contains a = true then none", None),
    ("X23_unlock_roles_narrow", "only DAO can unlock", LEDGER,
     "if c.any who [.DAO, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager] then" + NL
     + "      { c with locked := c.locked.filter fun x => x != a }",
     "if c.any who [.DAO] then" + NL + "      { c with locked := c.locked.filter fun x => x != a }", None),
    # the entry points the traces call since the generator was extended
    ("A1_force_move_by_anyone", "a forced internal transfer needs no role", LEDGER,
     "| .force who => c.any who [.DAO, .UnrestrictedWithdrawer]" + NL + NL, "| .force who => true" + NL + NL, None),
    ("A2_force_move_not_dao", "a forced internal transfer is refused to DAO", LEDGER,
     "| .force who => c.any who [.DAO, .UnrestrictedWithdrawer]" + NL + NL,
     "| .force who => c.any who [.UnrestrictedWithdrawer]" + NL + NL, None),
    ("A3_pauser_can_unpause", "PauseManager can unpause", LEDGER,
     "if c.any who [.DAO, .UnpauseManager] then", "if c.any who [.DAO, .UnpauseManager, .PauseManager] then", None),
    ("A4_unlocker_can_lock", "UnrestrictedAccountUnlocker can lock", LEDGER,
     "if c.any who [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager] then" + NL
     + "      { c with locked := a :: c.locked }",
     "if c.any who [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager] then"
     + NL + "      { c with locked := a :: c.locked }", None),
    ("A5_manager_cannot_lock", "UnrestrictedAccountManager cannot lock", LEDGER,
     "if c.any who [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager] then" + NL
     + "      { c with locked := a :: c.locked }",
     "if c.any who [.DAO, .UnrestrictedAccountLocker] then" + NL + "      { c with locked := a :: c.locked }", None),
    ("A6_self_disable_when_locked", "a locked account can disable its auth-by-predecessor flag", LEDGER,
     "if c.authOff.contains a || c.locked.contains a then c else setAuth c a false",
     "if c.authOff.contains a then c else setAuth c a false", None),
    ("A7_force_disable_by_anyone", "anyone can switch the auth-by-predecessor flag of an account", LEDGER,
     "    if c.any who (if enable then", "    if true || c.any who (if enable then", None),
    ("A8_force_enable_by_locker", "the locker role can force-enable the auth-by-predecessor flag", LEDGER,
     "if enable then [.DAO, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager]",
     "if enable then [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager]", None),
    ("A9_auth_intent_ignored", "a SetAuthByPredecessorId intent changes nothing", LEDGER,
     "| .authIntent a enable => if c.locked.contains a then c else setAuth c a enable",
     "| .authIntent a enable => if c.locked.contains a then c else setAuth c a (c.authOff.contains a == false)", None),
    ("A10_pause_not_dao", "a pause is refused to DAO", LEDGER,
     "if c.any who [.DAO, .PauseManager] then", "if c.any who [.PauseManager] then", None),
    ("A11_unpause_not_dao", "an unpause is refused to DAO", LEDGER,
     "if c.any who [.DAO, .UnpauseManager] then", "if c.any who [.UnpauseManager] then", None),
    ("A12_lock_not_dao", "a lock is refused to DAO", LEDGER,
     "if c.any who [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager] then" + NL
     + "      { c with locked := a :: c.locked }",
     "if c.any who [.UnrestrictedAccountLocker, .UnrestrictedAccountManager] then" + NL
     + "      { c with locked := a :: c.locked }", None),
    ("A13_unlock_not_manager", "an unlock is refused to the account manager", LEDGER,
     "if c.any who [.DAO, .UnrestrictedAccountUnlocker, .UnrestrictedAccountManager] then" + NL
     + "      { c with locked := c.locked.filter fun x => x != a }",
     "if c.any who [.DAO, .UnrestrictedAccountUnlocker] then" + NL
     + "      { c with locked := c.locked.filter fun x => x != a }", None),
    ("A14_force_disable_not_dao", "forcing the auth-by-predecessor flag off is refused to DAO", LEDGER,
     "else [.DAO, .UnrestrictedAccountLocker, .UnrestrictedAccountManager]) then",
     "else [.UnrestrictedAccountLocker, .UnrestrictedAccountManager]) then", None),
    # one change for every guard of the model that had none
    ("B1_debit_unbounded", "a debit is not bounded by the balance", LEDGER,
     "else if x ≤ bal L.bals a ∧ x ≤ L.supply then", "else if True then", None),
    ("B2_withdraw_pause_ignored", "ft_withdraw ignores its own pause key", LEDGER,
     ' && !c.isPaused "ft_withdraw" && !c.authOff.contains p', " && !c.authOff.contains p", None),
    ("B3_move_unbounded", "an internal move is not bounded by the source balance", LEDGER,
     "if auth.ok L.ctl src = true ∧ amt ≤ bal L.bals src ∧ bal L.bals dst + amt ≤ U128_MAX then",
     "if auth.ok L.ctl src = true ∧ bal L.bals dst + amt ≤ U128_MAX then", None),
    ("B4_pause_only_dao", "only DAO can pause", LEDGER,
     "if c.any who [.DAO, .PauseManager] then", "if c.any who [.DAO] then", None),
    ("B5_anyone_can_unpause", "anyone can unpause", LEDGER,
     "if c.any who [.DAO, .UnpauseManager] then", "if true then", None),
    ("B6_self_disable_twice", "an account whose auth flag is off can switch it off again", LEDGER,
     "if c.authOff.contains a || c.locked.contains a then c else setAuth c a false",
     "if c.locked.contains a then c else setAuth c a false", None),
    ("B7_auth_intent_when_locked", "a SetAuthByPredecessorId intent of a locked account is applied", LEDGER,
     "| .authIntent a enable => if c.locked.contains a then c else setAuth c a enable",
     "| .authIntent a enable => setAuth c a enable",
     "a SetAuthByPredecessorId intent exists only inside a signed payload, and the admission of a payload "
     "(Intents.admit, as commit_nonce in the contract) refuses a locked signer before any intent runs; the account "
     "cannot become locked between the two inside one receipt. Before the model had that test the replay noticed "
     "this change"),
    ("B8_all_pauses_nothing", "the key ALL pauses nothing", LEDGER,
     'c.paused.contains key || c.paused.contains "ALL"', "c.paused.contains key", None),
    # guards that no receipt can reach with inputs on which they matter
    ("E1_method_with_storage_deposit", "ft_withdraw accepts a withdrawal with a storage deposit", LEDGER,
     "p == w.owner && w.sd.isNone && !c.isPaused", "p == w.owner && !c.isPaused",
     "ft_withdraw has no storage_deposit argument (withdraw.rs:25-50 builds the FtWithdraw with storage_deposit: None), "
     "so every receipt of the method has w.sd = none"),
    ("E2_force_with_storage_deposit", "ft_force_withdraw accepts a withdrawal with a storage deposit", LEDGER,
     "| .force who => c.any who [.DAO, .UnrestrictedWithdrawer] && w.sd.isNone",
     "| .force who => c.any who [.DAO, .UnrestrictedWithdrawer]",
     "ft_force_withdraw has no storage_deposit argument (withdraw.rs:199-225), so every receipt of it has w.sd = none"),
    ("E3_amount_not_u128", "a withdrawal amount above the u128 range is accepted", LEDGER,
     "if via.ok L.ctl w = true ∧ w.amount ≤ U128_MAX then", "if via.ok L.ctl w = true then",
     "the amount of every receipt is a U128 argument; a larger number fails to deserialize before the model is asked"),
    ("E4_move_overflows_destination", "an internal move may lift the destination above the u128 range", LEDGER,
     "if auth.ok L.ctl src = true ∧ amt ≤ bal L.bals src ∧ bal L.bals dst + amt ≤ U128_MAX then",
     "if auth.ok L.ctl src = true ∧ amt ≤ bal L.bals src then",
     "in every state of a trace the balances of a ledger id sum to its supply, a u128; source and destination "
     "differ and the amount is within the source balance, so the destination balance plus the amount is at most the supply"),
    # the step function of the two-contract world (only the world-level replay runs it)
    ("V1_deposit_while_paused", "a deposit is credited while ft_on_transfer is paused", WORLD,
     'match (if ok = true ∧ S.L.ctl.isPaused "ft_on_transfer" = false then', "match (if ok = true then", None),
    ("V2_failed_deposit_kept", "the token's settlement reads a failed ft_on_transfer as accepted", WORLD,
     "| false => .failed", "| false => .ok [0x22, 0x30, 0x22]", None),
    ("V3_call_result_lost", "ft_resolve_withdraw reads a failure where the token's settlement returned a number", WORLD,
     "wdDone e (retPR o.ret)", "wdDone e .failed", None),
    ("V4_number_read_as_empty", "a number returned by the token reaches the contract as an empty value", WORLD,
     "| .u128 n => .ok (encU128 n)", "| .u128 _ => .ok []", None),
    ("V5_deposit_not_announced", "a transfer to the contract is not treated as a deposit", WORLD,
     "⟨q.1, q.2.1, q.2.2, if q.2.1 = me then .dep none else .other⟩", "⟨q.1, q.2.1, q.2.2, .other⟩", None),
    ("V6_msg_sent_as_plain", "a withdrawal with msg is sent as a plain ft_transfer", WORLD,
     "| some m => .ft_transfer_call w.receiver w.amount w.memo m", "| some _ => .ft_transfer w.receiver w.amount w.memo", None),
    ("V7_delivered_read_as_failed", "ft_resolve_withdraw reads a failure where the plain transfer succeeded", WORLD,
     "else [⟨w.owner, w.amount, false, retPR o.ret,", "else [⟨w.owner, w.amount, false, .failed,", None),
    ("V8_credit_to_sender", "a deposit is credited to the sender, whatever msg names", WORLD,
     "credit S.L recv e.amount else none", "credit S.L e.sender e.amount else none", None),
    # the two ledger functions of the wNEAR world
    ("W1_unwrap_one_more", "an unwrap debits one unit more", WORLD_W,
     "x ≤ U128_MAX then debit L owner x false else none", "x ≤ U128_MAX then debit L owner (x + 1) false else none", None),
    ("W2_wnear_storage_deposit_free", "the storage deposit of a wNEAR withdrawal is not debited", WORLD_W,
     "| some d => if d ≤ U128_MAX then debit L1 w.owner d via.forced else none",
     "| some d => if d ≤ U128_MAX then some L1 else none", None),
    ("W3_unwrap_ignores_pause", "an unwrap ignores the pause of intents", WORLD_W,
     'if L.ctl.isPaused "intents" = false ∧ x ≤ U128_MAX then debit L owner x false else none',
     "if x ≤ U128_MAX then debit L owner x false else none", None),
    ("W4_unwrap_ignores_lock", "an unwrap ignores the account lock", WORLD_W,
     "x ≤ U128_MAX then debit L owner x false else none", "x ≤ U128_MAX then debit L owner x true else none",
     "an unwrap exists only as an intent of a signed payload, and the admission of a payload (Intents.admit, as "
     "commit_nonce in the contract) refuses a locked signer before any intent runs. Before the model had that test "
     "the replay noticed this change"),
    # the refund of a transfer call, the entry guard of mt_transfer*, the admission of a signed payload and the
    # role table: the functions of Intents/Auth.lean
    ("R2_refund_above_balance", "the refund of a transfer call is not capped by the receiver's balance", AUTH,
     "min (min req x.amount) (bal L.bals x.receiver)", "min req x.amount", None),
    ("R3_refund_request_ignored", "mt_resolve_transfer takes back the whole amount, whatever the receiver asked for", AUTH,
     "min (min req x.amount) (bal L.bals x.receiver)", "min x.amount (bal L.bals x.receiver)", None),
    ("R4_refund_never", "mt_resolve_transfer never moves a refund", AUTH,
     "if x.refund L req = 0 then some L else moveBal L .refund x.receiver x.sender (x.refund L req)", "some L", None),
    ("R5_zero_refund_fails", "mt_resolve_transfer with nothing to refund fails", AUTH,
     "if x.refund L req = 0 then some L else moveBal L .refund x.receiver x.sender (x.refund L req)",
     "moveBal L .refund x.receiver x.sender (x.refund L req)", None),
    ("R6_refund_wrong_way", "the refund moves from the sender to the receiver", AUTH,
     "if x.refund L req = 0 then some L else moveBal L .refund x.receiver x.sender (x.refund L req)",
     "if x.refund L req = 0 then some L else moveBal L .refund x.sender x.receiver (x.refund L req)", None),
    ("D1_transfer_while_paused", "mt_transfer ignores the pause of mt_transfer", AUTH,
     '!c.isPaused "mt_transfer" && !c.authOff.contains pred', "!c.authOff.contains pred", None),
    ("D2_transfer_auth_flag_ignored", "mt_transfer ignores the auth-by-predecessor flag of the caller", AUTH,
     '!c.isPaused "mt_transfer" && !c.authOff.contains pred', '!c.isPaused "mt_transfer"', None),
    ("D3_transfer_other_pause_key", "mt_transfer is paused by the key intents instead of mt_transfer", AUTH,
     '!c.isPaused "mt_transfer" && !c.authOff.contains pred', '!c.isPaused "intents" && !c.authOff.contains pred', None),
    ("P1_other_contract_accepted", "a payload for another verifying contract is accepted", AUTH,
     "p.contract == me && !decide (p.deadline < now)", "!decide (p.deadline < now)", None),
    ("P2_deadline_ignored", "a payload whose deadline has passed is accepted", AUTH,
     "p.contract == me && !decide (p.deadline < now) && hasKey", "p.contract == me && hasKey", None),
    ("P3_key_not_tested", "a payload is accepted whatever key signed it", AUTH,
     " && hasKey implicit A p.signer p.key", "", None),
    ("P4_nonce_reused", "a payload with a used nonce is accepted", AUTH,
     "!A.nonces.contains (p.signer, p.nonce) && !c.locked.contains p.signer", "!c.locked.contains p.signer", None),
    ("P6_nonce_not_committed", "an executed payload does not commit its nonce", AUTH,
     "{ A with nonces := (p.signer, p.nonce) :: A.nonces }", "A", None),
    ("K1_registered_key_not_counted", "a key registered for the account is not one of its keys", AUTH,
     "(!A.noImplicit.contains a && implicit k == a) || A.keys.contains (a, k)",
     "(!A.noImplicit.contains a && implicit k == a)", None),
    ("K2_key_of_any_account", "a key registered for any account counts as a key of this one", AUTH,
     "(!A.noImplicit.contains a && implicit k == a) || A.keys.contains (a, k)",
     "(!A.noImplicit.contains a && implicit k == a) || A.keys.any fun e => e.2 == k", None),
    ("C1_grant_by_anyone", "acl_grant_role needs no permission", AUTH,
     "if x.isAdmin r who && !x.roles.contains (a, r) then", "if !x.roles.contains (a, r) then", None),
    ("C2_grant_only_super_admin", "acl_grant_role is refused to an admin of the role", AUTH,
     "if x.isAdmin r who && !x.roles.contains (a, r) then", "if x.supers.contains who && !x.roles.contains (a, r) then", None),
    ("C3_revoke_role_by_anyone", "acl_revoke_role needs no permission", AUTH,
     "if x.isAdmin r who then { x with roles := x.roles.filter fun e => e != (a, r) } else x",
     "{ x with roles := x.roles.filter fun e => e != (a, r) }", None),
    ("C4_renounce_role_keeps", "acl_renounce_role removes nothing", AUTH,
     "| .renounceRole who r => { x with roles := x.roles.filter fun e => e != (who, r) }", "| .renounceRole _ _ => x", None),
    ("C5_add_admin_by_anyone", "acl_add_admin needs no permission", AUTH,
     "if x.isAdmin r who && !x.admins.contains (a, r) then", "if !x.admins.contains (a, r) then", None),
    ("C8_add_super_admin_by_anyone", "acl_add_super_admin needs no permission", AUTH,
     "if x.supers.contains who && !x.supers.contains a then", "if !x.supers.contains a then", None),
    ("C9_revoke_super_admin_by_anyone", "acl_revoke_super_admin needs no permission", AUTH,
     "if x.supers.contains who then { x with supers := x.supers.filter fun y => y != a } else x",
     "{ x with supers := x.supers.filter fun y => y != a }", None),
    ("C11_transfer_super_admin_by_anyone", "acl_transfer_super_admin needs no permission", AUTH,
     "if x.supers.contains who && a != who then", "if a != who then", None),
    ("C12_super_admin_no_role_admin", "a super-admin is not an admin of every role", AUTH,
     "x.supers.contains a || x.admins.contains (a, r)", "x.admins.contains (a, r)", None),
    ("C13_admin_of_any_role", "an admin of one role is an admin of every role", AUTH,
     "x.supers.contains a || x.admins.contains (a, r)", "x.supers.contains a || x.admins.any fun e => e.1 == a", None),
    # the step function of the strict world (only the world-level replay runs it)
    ("S1_call_leaves_no_entry", "a transfer call leaves no mt_resolve_transfer in flight", STRICT,
     "if call then calls ++ [⟨src, dst, amt⟩] else calls", "calls", None),
    ("S2_resolve_keeps_entry", "mt_resolve_transfer leaves its transfer call in flight (it could run again)", STRICT,
     "      | some L' => { S with w := { S.w with L := L' }, calls := S.calls.eraseIdx k }",
     "      | some L' => { S with w := { S.w with L := L' } }", None),
    ("S3_entry_wrong_way", "the entry of a transfer call names the sender as the receiver", STRICT,
     "if call then calls ++ [⟨src, dst, amt⟩] else calls", "if call then calls ++ [⟨dst, src, amt⟩] else calls", None),
    ("S4_plain_transfer_leaves_entry", "a plain transfer leaves an mt_resolve_transfer in flight", STRICT,
     "if call then calls ++ [⟨src, dst, amt⟩] else calls", "calls ++ [⟨src, dst, amt⟩]", None),
    ("S6_super_admins_not_updated", "an acl_* call does not change the super-admins", STRICT,
     "      supers := (aclStep S.acl c).supers", "      supers := S.supers", None),
    ("S7_grantees_not_updated", "an acl_* call does not change the grantees", STRICT,
     "      w := step G.base ex S.w (.admin (.acl (aclStep S.acl c).roles)) }", "      w := S.w }", None),
    ("S8_resolve_moves_nothing", "mt_resolve_transfer removes its entry and moves no refund", STRICT,
     "      | some L' => { S with w := { S.w with L := L' }, calls := S.calls.eraseIdx k }",
     "      | some _ => { S with calls := S.calls.eraseIdx k }", None),
    ("S10_forced_call_leaves_no_entry", "a forced transfer call leaves no mt_resolve_transfer in flight", STRICT,
     "    | some L' => { S with w := { S.w with L := L' }, calls := pushCall S.calls call src dst amt }",
     "    | some L' => { S with w := { S.w with L := L' } }", None),
    ("S11_admins_not_updated", "an acl_* call does not change the admins of a role", STRICT,
     "      admins := (aclStep S.acl c).admins", "      admins := S.admins", None),
    ("S13_transfer_moves_nothing", "a transfer by the owner leaves the balances as they are", STRICT,
     "        { S with w := { S.w with L := L' }, calls := pushCall S.calls call src dst amt }",
     "        { S with calls := pushCall S.calls call src dst amt }", None),
    ("R1_refund_above_amount", "the refund of a transfer call is not capped by the amount of the transfer", AUTH,
     "min (min req x.amount) (bal L.bals x.receiver)", "min req (bal L.bals x.receiver)", None),
    ("P5_locked_signer_accepted", "a payload of a locked signer is accepted", AUTH,
     " && !c.locked.contains p.signer", "", None),
    ("C6_revoke_admin_by_anyone", "acl_revoke_admin needs no permission", AUTH,
     "if x.isAdmin r who then { x with admins := x.admins.filter fun e => e != (a, r) } else x",
     "{ x with admins := x.admins.filter fun e => e != (a, r) }", None),
    ("C7_renounce_admin_keeps", "acl_renounce_admin removes nothing", AUTH,
     "| .renounceAdmin who r => { x with admins := x.admins.filter fun e => e != (who, r) }", "| .renounceAdmin _ _ => x", None),
    ("C10_transfer_keeps_old_super_admin", "acl_transfer_super_admin leaves the caller a super-admin", AUTH,
     "{ x with supers := (a :: x.supers).filter fun y => y != who }", "{ x with supers := a :: x.supers }", None),
    ("S5_failed_resolve_keeps_entry", "an mt_resolve_transfer that failed for gas stays in flight", STRICT,
     "  | .resolveTransferFails k => { S with calls := S.calls.eraseIdx k }", "  | .resolveTransferFails _ => S", None),
    # public keys: add_public_key and remove_public_key
    ("K4_existing_key_added", "add_public_key accepts a key the account already has", AUTH,
     "  else if A.keys.contains (a, k) then none" + NL + "  else some { A with keys := (a, k) :: A.keys }",
     "  else some { A with keys := (a, k) :: A.keys }", None),
    ("K5_missing_key_removed", "remove_public_key accepts a key the account does not have", AUTH,
     "  else if A.keys.contains (a, k) then some { A with keys := A.keys.filter fun e => e != (a, k) }" + NL + "  else none",
     "  else some { A with keys := A.keys.filter fun e => e != (a, k) }", None),
    ("K6_locked_adds_key", "a locked account can add a key", AUTH,
     "  if c.locked.contains a then none" + NL + "  else if implicit k == a then" + NL
     + "    (if A.noImplicit.contains a then some",
     "  if false then none" + NL + "  else if implicit k == a then" + NL + "    (if A.noImplicit.contains a then some", None),
    ("K7_locked_removes_key", "a locked account can remove a key", AUTH,
     "  if c.locked.contains a then none" + NL + "  else if implicit k == a then" + NL
     + "    (if A.noImplicit.contains a then none",
     "  if false then none" + NL + "  else if implicit k == a then" + NL + "    (if A.noImplicit.contains a then none", None),
    ("K8_added_key_not_kept", "add_public_key succeeds and registers nothing", AUTH,
     "  else some { A with keys := (a, k) :: A.keys }", "  else some A", None),
    ("K9_removed_key_kept", "remove_public_key succeeds and the key stays", AUTH,
     "then some { A with keys := A.keys.filter fun e => e != (a, k) }", "then some A", None),
    ("S14_key_added_with_flag_off", "add_public_key runs for an account whose auth-by-predecessor flag is off", STRICT,
     "  | .addKey a k =>" + NL + "    if S.w.L.ctl.authOff.contains a = true then S",
     "  | .addKey a k =>" + NL + "    if false = true then S", None),
    ("S15_key_removed_with_flag_off", "remove_public_key runs for an account whose auth-by-predecessor flag is off", STRICT,
     "  | .removeKey a k =>" + NL + "    if S.w.L.ctl.authOff.contains a = true then S",
     "  | .removeKey a k =>" + NL + "    if false = true then S", None),
]
# The guard (or rule) of the model each change is about, for the score per guard.
GUARD = {
    "M1": "arithmetic of credit and debit", "M2": "arithmetic of credit and debit", "M4": "arithmetic of credit and debit",
    "W1": "arithmetic of credit and debit", "W2": "arithmetic of credit and debit",
    "M5": "refund rules of ft_resolve_withdraw", "M6": "refund rules of ft_resolve_withdraw",
    "M7": "refund rules of ft_resolve_withdraw", "M8": "refund rules of ft_resolve_withdraw",
    "M9": "refund rules of ft_resolve_withdraw", "M11": "refund rules of ft_resolve_withdraw",
    "X8": "refund rules of ft_resolve_withdraw", "X9": "refund rules of ft_resolve_withdraw",
    "X10": "refund rules of ft_resolve_withdraw", "X11": "refund rules of ft_resolve_withdraw",
    "X20": "refund rules of ft_resolve_withdraw",
    "X7": "credit: the amount is positive", "X5": "credit: supply and balance stay within u128",
    "X6": "debit: the amount is positive", "M3": "debit: the account is not locked, unless forced",
    "X22": "debit: the account is not locked, unless forced", "B1": "debit: the amount is within balance and supply",
    "X21": "ft_withdraw: the caller is the owner", "B2": "ft_withdraw: the method is not paused",
    "X1": "ft_withdraw: auth by predecessor is enabled", "E1": "ft_withdraw, ft_force_withdraw: no storage deposit",
    "E2": "ft_withdraw, ft_force_withdraw: no storage deposit", "E3": "startWithdraw: the amount is a u128",
    "X15": "FtWithdraw intent: intents are not paused",
    "X2": "ft_force_withdraw: DAO or UnrestrictedWithdrawer", "X3": "ft_force_withdraw: DAO or UnrestrictedWithdrawer",
    "X4": "ft_force_withdraw: DAO or UnrestrictedWithdrawer",
    "X12": "internal move: source and destination differ, the amount is positive",
    "X13": "internal move: source and destination differ, the amount is positive",
    "B3": "internal move: the amount is within the source balance",
    "E4": "internal move: the destination stays within u128", "X14": "internal move by the owner: the source is not locked",
    "A1": "forced internal move: DAO or UnrestrictedWithdrawer", "A2": "forced internal move: DAO or UnrestrictedWithdrawer",
    "X16": "pause: DAO or PauseManager", "X17": "pause: DAO or PauseManager", "A10": "pause: DAO or PauseManager",
    "B4": "pause: DAO or PauseManager",
    "A3": "unpause: DAO or UnpauseManager", "A11": "unpause: DAO or UnpauseManager", "B5": "unpause: DAO or UnpauseManager",
    "X18": "lock: DAO, locker or account manager", "A4": "lock: DAO, locker or account manager",
    "A5": "lock: DAO, locker or account manager", "A12": "lock: DAO, locker or account manager",
    "X19": "unlock: DAO, unlocker or account manager", "X23": "unlock: DAO, unlocker or account manager",
    "A13": "unlock: DAO, unlocker or account manager",
    "A6": "disable auth by predecessor (self): the flag is on, the account is not locked",
    "B6": "disable auth by predecessor (self): the flag is on, the account is not locked",
    "A9": "SetAuthByPredecessorId intent: applied unless the account is locked",
    "B7": "SetAuthByPredecessorId intent: applied unless the account is locked",
    "A7": "forced auth switch: locker roles to disable, unlocker roles to enable",
    "A8": "forced auth switch: locker roles to disable, unlocker roles to enable",
    "A14": "forced auth switch: locker roles to disable, unlocker roles to enable",
    "M10": "isPaused: the key or ALL", "B8": "isPaused: the key or ALL",
    "W3": "unwrap: intents are not paused", "W4": "unwrap: the account is not locked",
    "V1": "deposit: ft_on_transfer is not paused",
    "V2": "world: what a callback reads is what the other contract returned",
    "V3": "world: what a callback reads is what the other contract returned",
    "V4": "world: what a callback reads is what the other contract returned",
    "V7": "world: what a callback reads is what the other contract returned",
    "V5": "world: which receipts a call starts", "V6": "world: which receipts a call starts",
    "V8": "deposit: the credited account is the one msg names",
    "R1": "mt_resolve_transfer: the refund is the request capped by the amount and by the receiver's balance",
    "R2": "mt_resolve_transfer: the refund is the request capped by the amount and by the receiver's balance",
    "R3": "mt_resolve_transfer: the refund is the request capped by the amount and by the receiver's balance",
    "R4": "mt_resolve_transfer: a positive refund moves from the receiver back to the sender",
    "R5": "mt_resolve_transfer: a positive refund moves from the receiver back to the sender",
    "R6": "mt_resolve_transfer: a positive refund moves from the receiver back to the sender",
    "D1": "mt_transfer*: mt_transfer is not paused, auth by predecessor is enabled",
    "D2": "mt_transfer*: mt_transfer is not paused, auth by predecessor is enabled",
    "D3": "mt_transfer*: mt_transfer is not paused, auth by predecessor is enabled",
    "P1": "signed payload: the verifying contract is this contract",
    "P2": "signed payload: the deadline has not passed",
    "P3": "signed payload: the key is one of the signer's", "K1": "signed payload: the key is one of the signer's",
    "K2": "signed payload: the key is one of the signer's",
    "P4": "signed payload: the nonce is new, and is committed", "P6": "signed payload: the nonce is new, and is committed",
    "P5": "signed payload: the signer is not locked",
    "C1": "acl_grant_role: a super-admin or an admin of the role", "C2": "acl_grant_role: a super-admin or an admin of the role",
    "C3": "acl_revoke_role: a super-admin or an admin of the role", "C4": "acl_renounce_role: the caller's own role goes",
    "C5": "acl_add_admin: a super-admin or an admin of the role", "C6": "acl_revoke_admin: a super-admin or an admin of the role",
    "C7": "acl_renounce_admin: the caller's own admin entry goes",
    "C8": "acl_add_super_admin: a super-admin", "C9": "acl_revoke_super_admin: a super-admin",
    "C10": "acl_transfer_super_admin: a super-admin, who stops being one",
    "C11": "acl_transfer_super_admin: a super-admin, who stops being one",
    "C12": "is_admin: a super-admin, or an admin of that role", "C13": "is_admin: a super-admin, or an admin of that role",
    "S1": "strict world: a transfer call, and only a transfer call, leaves one mt_resolve_transfer in flight",
    "S3": "strict world: a transfer call, and only a transfer call, leaves one mt_resolve_transfer in flight",
    "S4": "strict world: a transfer call, and only a transfer call, leaves one mt_resolve_transfer in flight",
    "S10": "strict world: a transfer call, and only a transfer call, leaves one mt_resolve_transfer in flight",
    "S2": "strict world: mt_resolve_transfer takes its entry, moves the refund, and the entry is gone",
    "S5": "strict world: mt_resolve_transfer takes its entry, moves the refund, and the entry is gone",
    "S8": "strict world: mt_resolve_transfer takes its entry, moves the refund, and the entry is gone",
    "S6": "strict world: an acl_* call updates super-admins, admins and grantees",
    "S7": "strict world: an acl_* call updates super-admins, admins and grantees",
    "S11": "strict world: an acl_* call updates super-admins, admins and grantees",
    "S13": "strict world: a transfer by the owner moves the balance",
    "K4": "add_public_key: the key is not there yet, and is there afterwards",
    "K8": "add_public_key: the key is not there yet, and is there afterwards",
    "K5": "remove_public_key: the key is there, and is gone afterwards",
    "K9": "remove_public_key: the key is there, and is gone afterwards",
    "K6": "add_public_key, remove_public_key: the account is not locked",
    "K7": "add_public_key, remove_public_key: the account is not locked",
    "S14": "strict world: add_public_key and remove_public_key need auth by predecessor enabled",
    "S15": "strict world: add_public_key and remove_public_key need auth by predecessor enabled",
    "K3": "signed payload: the key is one of the signer's",
}
# One-line changes of the new functions that no trace of the mutant set exercises: the last field says which receipt
# would show the change. They are not equivalent changes and they are not counted as noticed; MUT_UNEXERCISED=1 runs
# them too, to record that the replays give no disagreement on them (MUTANTS-REVIEW.md, section 5).
UNEXERCISED = [
    ("K3_implicit_key_not_counted", "the implicit key of an account is not one of its keys", AUTH,
     "(!A.noImplicit.contains a && implicit k == a) || A.keys.contains (a, k)", "A.keys.contains (a, k)",
     "an account whose id is the implicit account id of a key (no account of a trace is one: the generator "
     "registers every key explicitly for a named account)"),
]
START = re.compile(r"^(/--|/-!|theorem |def |structure |inductive |abbrev |instance |namespace |end |open |section "
                   r"|@\[|private |protected |variable |set_option |attribute |example |noncomputable |mutual|deriving |partial "
                   r"|unsafe |opaque |macro |syntax |notation |local |scoped |export |universe |#)")
IS_THM = re.compile(r"^(@\[[^\]]*\]\s*)*((private|protected)\s+)?(theorem|example)\b")
ONLY_ATTR = re.compile(r"^(@\[[^\]]*\]\s*)+$")


def strip_theorems(text):
    """Keeps the definitions, drops theorems and examples (with their doc comments and attribute lines)."""
    chunks, cur = [], []
    for line in text.split(NL):
        if START.match(line) and cur:
            chunks.append(cur)
            cur = []
        cur.append(line)
    chunks.append(cur)
    keep, i = [], 0
    while i < len(chunks):
        c = chunks[i]
        nxt = chunks[i + 1] if i + 1 < len(chunks) else None
        nxt2 = chunks[i + 2] if i + 2 < len(chunks) else None
        head = c[0]
        if IS_THM.match(head):
            i += 1
            continue
        lead = head.startswith("/--") or (ONLY_ATTR.match(head.strip()) is not None and len([x for x in c if x.strip()]) == 1)
        if lead and nxt is not None and IS_THM.match(nxt[0]):
            i += 2
            continue
        if head.startswith("/--") and nxt is not None and nxt2 is not None and ONLY_ATTR.match(nxt[0].strip() or "x") and IS_THM.match(nxt2[0]):
            i += 3
            continue
        keep.append(c)
        i += 1
    return NL.join(NL.join(c) for c in keep)


def strip_tree(d):
    """The executable is rebuilt from the definitions alone: every theorem that depends on the ledger functions
    would stop compiling on a mutant (that is their job), and none is needed to run the model."""
    for sub in ("Intents", "IntentsW"):
        base = os.path.join(d, sub)
        if not os.path.isdir(base):
            continue
        for root, _, fs in os.walk(base):
            for f in fs:
                if f.endswith(".lean"):
                    q = os.path.join(root, f)
                    text = open(q).read()
                    open(q, "w").write(strip_theorems(text))


ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])


def apply(d, rel, old, new):
    """Applies the change to the copy at `d`; returns None, or why it could not be applied."""
    if old is None:
        return None
    q = os.path.join(d, rel)
    s = open(q).read()
    if s.count(old) != 1:
        return f"NOT APPLIED ({s.count(old)} matches)"
    open(q, "w").write(s.replace(old, new))
    return None


def proofs(mid, rel, old, new):
    """Builds the theorems with the change applied. Returns what the first error is, or that there is none."""
    d = os.path.join(WORK, mid + "_proofs")
    shutil.rmtree(d, ignore_errors=True)
    subprocess.run(["rsync", "-a", "--exclude", "src", "--exclude", ".lake/build/bin", SRC + "/", d + "/"], check=True)
    err = apply(d, rel, old, new)
    if err:
        return err
    b = subprocess.run(["lake", "build", "Intents", "IntentsW"], cwd=d, env=ENV, capture_output=True, text=True)
    shutil.rmtree(d, ignore_errors=True)
    if b.returncode == 0:
        return "the theorems still compile"
    m = re.search(r"error: (\S+\.lean):(\d+):\d+", b.stdout + b.stderr)
    if not m:
        return "the theorems do not compile"
    name = None
    try:
        lines = open(os.path.join(SRC, m.group(1))).read().split(NL)[: int(m.group(2))]
        for line in reversed(lines):
            t = re.match(r"^(?:private |protected )?theorem (\S+)", line)
            if t:
                name = t.group(1)
                break
    except OSError:
        pass
    return "the theorems do not compile: first error in " + m.group(1) + (f", theorem {name}" if name else "")


def run(mut):
    mid, what, rel, old, new, equiv = mut
    d = os.path.join(WORK, mid)
    shutil.rmtree(d, ignore_errors=True)
    subprocess.run(["rsync", "-a", "--exclude", "src", "--exclude", ".lake/build/bin", SRC + "/", d + "/"], check=True)
    strip_tree(d)
    rec = {"id": mid, "change": what, "file": rel, "guard": GUARD.get(mid.split("_")[0], "")}
    err = apply(d, rel, old, new)
    if err:
        rec["result"] = err
        shutil.rmtree(d, ignore_errors=True)
        return rec
    b = subprocess.run(["lake", "build", "intentsmodel"], cwd=d, env=ENV, capture_output=True, text=True)
    if b.returncode != 0:
        rec["result"] = "BUILD FAILED"
        rec["detail"] = (b.stdout + b.stderr)[-500:]
    else:
        r = subprocess.run([os.path.join(d, ".lake/build/bin/intentsmodel"), "--summary", "--world"], stdin=open(TRACE),
                           capture_output=True, text=True)
        try:
            last = json.loads(r.stdout.strip().splitlines()[-1])
            tot, wld = last["total"], last["world"]
            both = tot["disagree"] + wld["disagree"]
            rec.update(contract_steps=tot["contract_steps"], agree=tot["agree"], disagree=tot["disagree"],
                       world_receipts=wld["token_receipts"] + wld["contract_receipts"], world_agree=wld["agree"],
                       world_disagree=wld["disagree"])
            rec["noticed_by"] = ("both replays" if tot["disagree"] and wld["disagree"] else "the receipt replay" if tot["disagree"]
                                 else "the world replay" if wld["disagree"] else "neither")
            if old is None:
                rec["result"] = "PASS" if both == 0 else "FAIL"
            elif mid in UNEX_IDS:
                rec["result"] = "NOT EXERCISED" if both == 0 else "DETECTED, although listed as not exercised"
                rec["would_show_in"] = equiv
            elif equiv is None:
                rec["result"] = "DETECTED" if both > 0 else "NOT DETECTED"
            else:
                rec["result"] = "EQUIVALENT" if both == 0 else "DETECTED, although listed as equivalent"
                rec["why_equivalent"] = equiv
        except Exception:
            rec["result"] = "RUN FAILED"
            rec["detail"] = (r.stdout + r.stderr)[-300:]
    shutil.rmtree(d, ignore_errors=True)
    if equiv is not None and mid not in UNEX_IDS:
        rec["proofs"] = proofs(mid, rel, old, new)
    return rec


UNEX_IDS = {m[0] for m in UNEXERCISED}
if os.environ.get("MUT_UNEXERCISED"):
    MUTANTS = MUTANTS + UNEXERCISED
ONLY = [x for x in os.environ.get("MUT_ONLY", "").split(",") if x]
if ONLY:
    MUTANTS = [m for m in MUTANTS if m[0] == "M0_control" or m[0].split("_")[0] in ONLY]
os.makedirs(WORK, exist_ok=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=JOBS) as ex:
    out = list(ex.map(run, MUTANTS))
for rec in out:
    print(rec, flush=True)
json.dump(out, open(OUT, "w"), indent=1, ensure_ascii=False)
muts = [r for r in out if r["id"] != "M0_control"]
by_guard = {}
for r in muts:
    if r["id"] in UNEX_IDS:
        continue
    g = by_guard.setdefault(r.get("guard") or "(no guard named)", {"changes": [], "detected": 0, "equivalent": 0, "missed": 0,
                                                                  "by_the_receipt_replay": 0, "by_the_world_replay": 0})
    g["changes"].append(r["id"].split("_")[0])
    g["by_the_receipt_replay"] += bool(r.get("disagree"))
    g["by_the_world_replay"] += bool(r.get("world_disagree"))
    g["detected" if r.get("result") == "DETECTED" else "equivalent" if r.get("result") == "EQUIVALENT" else "missed"] += 1
json.dump(by_guard, open(os.path.splitext(OUT)[0] + "_by_guard.json", "w"), indent=1, ensure_ascii=False)
for g, v in sorted(by_guard.items()):
    print(f"guard | {g} | {' '.join(v['changes'])} | detected {v['detected']} (receipt replay {v['by_the_receipt_replay']}, "
          f"world replay {v['by_the_world_replay']}) | equivalent {v['equivalent']} | missed {v['missed']}")
det = sum(1 for r in muts if r.get("result") == "DETECTED")
eqv = sum(1 for r in muts if r.get("result") == "EQUIVALENT")
unex = [r["id"] for r in muts if r.get("result") == "NOT EXERCISED"]
bad = [r["id"] for r in muts if r.get("result") not in ("DETECTED", "EQUIVALENT", "NOT EXERCISED")]
muts = [r for r in muts if r["id"] not in UNEX_IDS]
if unex:
    print(f"listed as not exercised by any trace, and not noticed: {len(unex)} {unex}")
print(f"mutants: {len(muts)}; detected: {det}; equivalent: {eqv}; not detected or failed: {len(bad)} {bad}; "
      f"control: {out[0].get('result')}")
