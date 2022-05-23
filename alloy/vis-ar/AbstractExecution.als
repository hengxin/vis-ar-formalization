module AbstractExecution

let id[A] = A<:iden

// Abstract execution 
sig E {
    op: one Operation,
    rval: Value, // Assuming that the events are complete
    so: set E,
    vis: set E,
    ar: set E,
    session: one Session,
    ve: set E
} {
    all e: E | e in e.@session.events.elems
    all e: E | e.@ve in e.@vis
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
    all e, e": E | e in op.Write and e" in op.Read and e.op->e".op in rf => e->e" in vis
}

fact WellFormedSession { all s: Session | !s.events.hasDups and !s.events.isEmpty }
// All sessions in one history 
fact WellFormedHistory { all s: Session| s in History.sessions }

fact AllOpsAreAssociatedWithEvents { all o : Operation | one op.o }
fact EachEventInOneSession { all e: E | one s: Session | e in s.events.elems }
// Each write event returns ok
fact WritesReturnOK { all w : op.Write | w.rval = OK }
// Each read event returns a value or initial value undef
fact ReadsReturnValuesOrUndef { all r : op.Read | r.rval in V + Undef }

pred IsTotalOverEvents[s: set E, r: E->E] {
    all disj e, e": E | e in s and e" in s => e.r = e" and e".r != e or e".r = e and e.r != e"
}

fact SessionOrderOverOneSession {so in session.~session}
fact SessionOrderIsPartial { no id[E] & so and so.so in so }
fact SessionOrderIsTotalOrderOverOneSession { all s: Session | IsTotalOverEvents[s.events.elems,so] }

fact VisibilityIsAcyclic { no id[E] & ^vis }

fun lastVisibleWrite(e: E): lone E {
    {w : op.Write | w->e in vis and no ww : op.Write | ww->e in vis and w->ww in ar}
}

// An read returns Undef or preceding last write
fact ReadLastVisibleWrite {
    all r : op.Read | 
        some (op.Write & vis.r) => r.rval=lastVisibleWrite[r].op.value
}
// Any read in V(e) of an event e can be justified
fact VeIsReasonable {
    all r: op.Read.ve | r in op.Read => some (op.Write & vis.r) => r.rval=lastVisibleWrite[r].op.value
}

pred ArIsTotalOrder { no id[E] & ar and ar.ar in ar and E->E in ar + ~ar + id[E] }

pred VisAr { vis in ar }
//fact SessionOrderIsConsistentWithVisibility { so in vis }

// Recipes for visibility
pred SoInVis {so in vis}

// Happens-before relation
fun hb[]: E->E { ^(so + vis) }
pred CausalVisibility {hb in vis}

// Recipes for V 
pred Ve { all e: E | e.ve = none }
pred Ve2 { all e: E | e.ve = e.so }
pred Ve3 { all e: E | e.ve = e.vis }

// Causal consistency variants
pred Wcc { CausalVisibility and VisAr and Ve }
pred CM { CausalVisibility and VisAr and Ve2 }
pred SCC { CausalVisibility and VisAr and Ve3 }
pred WCCv { CausalVisibility and VisAr and Ve and ArIsTotalOrder}
pred CMv { CausalVisibility and VisAr and Ve2 and ArIsTotalOrder }
pred SCCv { CausalVisibility and VisAr and Ve3 and ArIsTotalOrder }

let interesting_model[model] {
    model
}

run Wcc {
  interesting_model[Wcc] and #Read>1 and #Write>1
} for 4

run CM {
  interesting_model[CM] and #Read>1 and #Write>1
} for 8

run SCC {
  interesting_model[SCC] and #Read>1 and #Write>1
} for 8

run WCCv {
  interesting_model[Wcc] and #Read>1 and #Write>1
} for 8

run CMv {
  interesting_model[CMv] and #Read>1 and #Write>1
} for 8

run SCCv {
  interesting_model[SCCv] and #Read>1 and #Write>1
} for 8