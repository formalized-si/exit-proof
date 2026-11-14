---------------------------- MODULE IntentsLedger ----------------------------
(***************************************************************************)
(* A second, independent formalization of the fungible-token ledger of the *)
(* NEAR Intents contract, written from the Rust source                     *)
(* (contracts/defuse/src/contract/tokens/nep141/deposit.rs, withdraw.rs)   *)
(* and from NEP-141, not from the Lean model in ../lean.  TLC explores     *)
(* every interleaving of receipts and every failure for a small scope.     *)
(*                                                                         *)
(* One step is one receipt.  A receipt either runs or fails with no state  *)
(* change; a callback either runs or is dropped.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Users,            \* accounts with ledger balances
          Start,            \* token balance of every user at the beginning
          MaxAmt,           \* largest amount of one operation
          MaxOps,           \* operations started in one behaviour
          FeeToken,         \* TRUE: the token keeps 1 unit on ft_transfer_call and reports the full amount
          RefundFailedCall  \* TRUE: a variant of the contract that refunds a withdrawal whose
                            \* ft_transfer_call receipt failed (the deployed code keeps the debit)

VARIABLES tok,       \* token balances
          led,       \* ledger balances of the contract
          pend,      \* receipts in flight
          ops,       \* operations started
          stranded   \* ghost: tokens the contract holds that its ledger assigns to nobody

vars == <<tok, led, pend, ops, stranded>>

Accounts == Users \cup {"intents", "recv", "fee"}
Amts     == 1..MaxAmt
Min(a, b) == IF a < b THEN a ELSE b

RECURSIVE SumOver(_, _)
SumOver(f, S) == IF S = {} THEN 0
                 ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})
LedTotal == SumOver(led, Users)
TokTotal == SumOver(tok, Accounts)

\* a receipt in flight: id = the operation it belongs to; k = what will run next
Rc(id, k, u, dst, a, call, x, res, out) ==
    [id |-> id, k |-> k, u |-> u, dst |-> dst, a |-> a, call |-> call, x |-> x, res |-> res, out |-> out]

Init == /\ tok = [a \in Accounts |-> IF a \in Users THEN Start ELSE 0]
        /\ led = [u \in Users |-> 0]
        /\ pend = {}
        /\ ops = 0
        /\ stranded = 0

--------------------------------------------------------------------------------
(* Deposit: token.ft_transfer_call(intents, a) by user u.                       *)

StartDeposit(u, a) ==
    /\ ops < MaxOps /\ tok[u] >= a
    /\ LET fee == IF FeeToken THEN 1 ELSE 0 IN
       tok' = [tok EXCEPT ![u] = @ - a, !["intents"] = @ + (a - fee), !["fee"] = @ + fee]
    /\ pend' = pend \cup {Rc(ops, "on_transfer", u, "intents", a, FALSE, 0, "ok", 0)}
    /\ ops' = ops + 1
    /\ UNCHANGED <<led, stranded>>

\* intents.ft_on_transfer: credits the amount it is told and returns "0" unused; or fails
OnTransfer(r) ==
    /\ r \in pend /\ r.k = "on_transfer"
    /\ \/ /\ led' = [led EXCEPT ![r.u] = @ + r.a]
          /\ pend' = (pend \ {r}) \cup {Rc(r.id, "tok_resolve_dep", r.u, "intents", r.a, FALSE, 0, "ok", 0)}
       \/ /\ UNCHANGED led
          /\ pend' = (pend \ {r}) \cup {Rc(r.id, "tok_resolve_dep", r.u, "intents", r.a, FALSE, r.a, "fail", 0)}
    /\ UNCHANGED <<tok, ops, stranded>>

\* token.ft_resolve_transfer of the deposit: returns the unused part to the sender; or is dropped
TokResolveDep(r) ==
    /\ r \in pend /\ r.k = "tok_resolve_dep"
    /\ pend' = pend \ {r}
    /\ \/ LET refund == Min(r.x, tok["intents"]) IN
          /\ tok' = [tok EXCEPT !["intents"] = @ - refund, ![r.u] = @ + refund]
          /\ stranded' = stranded + (r.x - refund)
       \/ /\ UNCHANGED tok
          /\ stranded' = stranded + r.x
    /\ UNCHANGED <<led, ops>>

--------------------------------------------------------------------------------
(* Withdrawal: intents.ft_withdraw(token, dst, a, msg?) by user u.              *)

StartWithdraw(u, dst, a, call) ==
    /\ ops < MaxOps /\ led[u] >= a
    /\ led' = [led EXCEPT ![u] = @ - a]
    /\ pend' = pend \cup {Rc(ops, "tok_wd", u, dst, a, call, 0, "ok", 0)}
    /\ ops' = ops + 1
    /\ UNCHANGED <<tok, stranded>>

\* the token receipt of the withdrawal: ft_transfer or the first half of ft_transfer_call; or it fails
TokWd(r) ==
    /\ r \in pend /\ r.k = "tok_wd"
    /\ \/ /\ tok["intents"] >= r.a
          /\ tok' = [tok EXCEPT !["intents"] = @ - r.a, ![r.dst] = @ + r.a]
          /\ pend' = (pend \ {r}) \cup
                {IF r.call THEN Rc(r.id, "recv_on_transfer", r.u, r.dst, r.a, TRUE, 0, "ok", r.a)
                           ELSE Rc(r.id, "wd_resolve", r.u, r.dst, r.a, FALSE, r.a, "ok", r.a)}
       \/ /\ UNCHANGED tok
          /\ pend' = (pend \ {r}) \cup {Rc(r.id, "wd_resolve", r.u, r.dst, r.a, r.call, 0, "fail", 0)}
    /\ UNCHANGED <<led, ops, stranded>>

\* the receiver's ft_on_transfer: an arbitrary contract reports any unused amount (a failure counts as all)
RecvOnTransfer(r) ==
    /\ r \in pend /\ r.k = "recv_on_transfer"
    /\ \E unused \in 0..r.a :
          pend' = (pend \ {r}) \cup {Rc(r.id, "tok_resolve_wd", r.u, r.dst, r.a, TRUE, unused, "ok", r.a)}
    /\ UNCHANGED <<tok, led, ops, stranded>>

\* token.ft_resolve_transfer of the withdrawal: takes back what the receiver still has of the unused part
\* and returns the used amount to the contract; or is dropped, and the contract sees a failed promise
TokResolveWd(r) ==
    /\ r \in pend /\ r.k = "tok_resolve_wd"
    /\ \/ LET refund == Min(r.x, tok[r.dst]) IN
          /\ tok' = [tok EXCEPT ![r.dst] = @ - refund, !["intents"] = @ + refund]
          /\ pend' = (pend \ {r}) \cup {Rc(r.id, "wd_resolve", r.u, r.dst, r.a, TRUE, r.a - refund, "ok", r.a - refund)}
       \/ /\ UNCHANGED tok
          /\ pend' = (pend \ {r}) \cup {Rc(r.id, "wd_resolve", r.u, r.dst, r.a, TRUE, 0, "fail", r.a)}
    /\ UNCHANGED <<led, ops, stranded>>

\* intents.ft_resolve_withdraw: credits back what it takes as not delivered; or is dropped
\*   r.x   = the used amount the token reported (when r.res = "ok")
\*   r.out = ghost: what really left the contract and did not come back
Used(r) == IF r.call
           THEN IF r.res = "fail" THEN (IF RefundFailedCall THEN 0 ELSE r.a) ELSE Min(r.x, r.a)
           ELSE IF r.res = "ok" THEN r.a ELSE 0

WdResolve(r) ==
    /\ r \in pend /\ r.k = "wd_resolve"
    /\ pend' = pend \ {r}
    /\ \/ LET refund == r.a - Used(r) IN
          /\ led' = [led EXCEPT ![r.u] = @ + refund]
          /\ stranded' = IF r.a >= r.out + refund THEN stranded + (r.a - r.out - refund) ELSE stranded
       \/ /\ UNCHANGED led
          /\ stranded' = stranded + (r.a - r.out)
    /\ UNCHANGED <<tok, ops>>

--------------------------------------------------------------------------------
(* Other steps.                                                                 *)

\* a plain token transfer by a user or by the receiver contract (no notification)
Xfer(x, y, a) ==
    /\ ops < MaxOps /\ x # y /\ tok[x] >= a
    /\ tok' = [tok EXCEPT ![x] = @ - a, ![y] = @ + a]
    /\ stranded' = IF y = "intents" THEN stranded + a ELSE stranded
    /\ ops' = ops + 1
    /\ UNCHANGED <<led, pend>>

\* an operation inside the ledger (mt_transfer, an intent): keeps the total
Move(u, v, a) ==
    /\ ops < MaxOps /\ u # v /\ led[u] >= a
    /\ led' = [led EXCEPT ![u] = @ - a, ![v] = @ + a]
    /\ ops' = ops + 1
    /\ UNCHANGED <<tok, pend, stranded>>

Next ==
    \/ \E u \in Users, a \in Amts : StartDeposit(u, a)
    \/ \E u \in Users, d \in Users \cup {"recv"}, a \in Amts, c \in BOOLEAN : StartWithdraw(u, d, a, c)
    \/ \E x \in Users \cup {"recv"}, y \in Users \cup {"recv", "intents"}, a \in Amts : Xfer(x, y, a)
    \/ \E u \in Users, v \in Users, a \in Amts : Move(u, v, a)
    \/ \E r \in pend : \/ OnTransfer(r) \/ TokResolveDep(r) \/ TokWd(r)
                       \/ RecvOnTransfer(r) \/ TokResolveWd(r) \/ WdResolve(r)

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
(* Properties.                                                                  *)

TypeOK == /\ tok \in [Accounts -> Nat] /\ led \in [Users -> Nat]
          /\ ops \in 0..MaxOps /\ stranded \in Nat

\* the ledger never credits more than the contract holds
Backing == LedTotal <= tok["intents"]

\* the token itself neither creates nor loses tokens
TokenConserved == TokTotal = Start * Cardinality(Users)

\* with nothing in flight the ledger plus the tokens assigned to nobody is exactly what the contract holds
ExactWhenQuiet == (pend = {}) => (LedTotal + stranded = tok["intents"])

\* the contract can always pay a withdrawal it has debited and not yet sent
CanPay == \A r \in pend : r.k = "tok_wd" => tok["intents"] >= r.a
================================================================================
