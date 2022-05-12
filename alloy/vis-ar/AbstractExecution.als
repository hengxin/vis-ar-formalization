module AbstractExecution

let id[A] = A<:iden

// Abstract execution 
sig E {
    op: one Operation,
    rval: Value, // Assuming that the events are complete
    so: set E,
    vis: set E,
    ar: set E,
    session: one Session
}

// A session is a sequence of events
sig Session {
    events: seq E
}

// A history is a set of sessions
one sig History {
    sessions: set Session
}

abstract sig Value {}
one sig v1, v2, v3, v4 extends Value {}
let V = v1 + v2 + v3 + v4
one sig Undef extends Value {} // Initial value
one sig OK extends Value {} // Writes return OK

abstract sig Obj {}
one sig o1, o2, o3 extends Obj {}
let O = o1 + o2 + o3

sig Key extends Obj {}
one sig x, y, z extends Key {}
let K = x + y + z

sig Queue extends Obj {}
one sig p, q extends Queue {}
let Q = p + q 

sig RWOperation {
    key: one K
}
sig QueueOperation {
    queue: one Q
}

// read-write register
sig Read extends RWOperation {}
sig Write extends RWOperation {
    value: V,
    rf: lone Read  // Reads-from relation
}
let Operation = Read + Write

/***************
// key-value store
sig Get extends RWOperation {}
sig Put extends RWOperation {
    value: V
}

// fifo queue
sig Dequeue extends QueueOperation {}
sig Enqueue extends QueueOperation {
    value: V
}
*****************/
fact WellFormedRF {
    rf in Write <: key.~key :> Read 
    all e: op.Read | e.rval = Undef or one e": op.Write | e.rval = e".op.value and e".op.rf = e.op
}

fact WellFormedHistory {
    all s: Session | !s.events.hasDups and !s.events.isEmpty
}

fact AllSessionsInOneHistory {
    all s: Session| s in History.sessions
}

fact AllOpsAreAssociatedWithEvents {
    all o : Operation | one op.o
}

fact EachEventInOneSession {
    all e: E | one s: Session | e in s.events.elems
}

// Each write event returns ok
fact WritesReturnOK {
    all w : op.Write | w.rval = OK
}

// Each read event returns a value or initial value undef
fact ReadsReturnValuesOrUndef {
    all r : op.Read | r.rval in V
}

pred IsTotalOverEvents[s: set E, r: E->E] {
    all disj e, e": E | e in s and e" in s => e.r = e" and e".r != e or e".r = e and e.r != e"
}

fact SessionOrderOverOneSession {so in session.~session and all e: E | e in e.session.events.elems}

fact WellFormedSessionOrder {
    all s: Session | IsTotalOverEvents[s.events.elems,so]
}

fact VisibilityIsAcyclic {
    no id[E] & ^vis
}

fact SessionOrderIsPartial {
    no id[E] & so
    so.so in so
}

fact ArbitrationIsTotalOrder {
    no id[E] & ar
    ar.ar in ar
    E->E in ar + ~ar + id[E]
}

fact VisibilityIsConsistentWithArbitration {
    vis in ar
}

fact SessionOrderIsConsistentWithVisibility {
    so in vis
}

// vis.r = r.(~vis)
fact ReadLastVisibleWrite {
    all r : op.Read | 
        some (op.Write & vis.r) => r.rval=lastVisibleWrite[r].op.value
}

fun lastVisibleWrite(e: E): lone E {
    {w : op.Write | w->e in vis and no ww : op.Write | ww->e in vis and w->ww in ar}
}

// Happens-before relation
fun hb[]: E->E {
    ^(so + vis)
}

// Recipes for visibility
//assert SoInVis {so in vis}
fact CausalVis {hb in vis}

run {#Read>1 and #Write>1} for 6