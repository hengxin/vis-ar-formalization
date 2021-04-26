-------------------------------- MODULE TCM --------------------------------
EXTENDS Sequences
(*
TLA+ specification of classic transactional consistency models
(hence the name TCM), following the framework proposed by
Andrea Cerone, Giovanni Bernardi, and Alexey Gotsman in their

- CONCUR'2015 paper:
    A Framework for Transactional Consistency Models with Atomic Visibility.
- JACM'2018 paper:
    Analysing Snapshot Isolation
*)
CONSTANTS Key, Val, EventId

Op == [type : {"read", "write"}, key : Key, val : Val]
R(k, v) == [type |-> "read", key |-> k, val |-> v]
W(k, v) == [type |-> "write", key |-> k, val |-> v]

Event == [eid : EventId, op : Op]
REvent(k) == {e \in Event : e.op.type = "read" \land e.op.key = k}
WEvent(k) == {e \in Event : e.op.type = "write" \land e.op.key = k}
HEvent(k) == REvent(k) \cup WEvent(k)

Transaction == Seq(Event)   \* A transaction is a sequence of events.
Session == Seq(Transaction) \* A session is a sequence of transactions.
History == SUBSET Session   \* A history is a set of sessions.
=============================================================================
\* Modification History
\* Last modified Mon Apr 26 21:35:03 CST 2021 by hengxin
\* Created Mon Apr 26 20:51:33 CST 2021 by hengxin
