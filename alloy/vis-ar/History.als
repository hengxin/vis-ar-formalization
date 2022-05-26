module AbstractExecution

let id[A] = A<:iden

// Abstract execution 
sig E {
    op: one Operation,
    rval: Value, // Assuming that the events are complete
    so: set E,
    session: one Session,
    ve: set E
} {
    all e: E | e in e.@session.events.elems
}

sig Visibility {
    rel: set E->E
}

sig Arbitration {
    rel: set E->E
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
    value: V
    //rf: lone Read  // Reads-from relation
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

/*****
fact WellFormedRF {
    rf in Write <: key.~key :> Read 
    all e: op.Read | e.rval = Undef or one e": op.Write | e.rval = e".op.value and e".op.rf = e.op
    all e, e": E | e in op.Write and e" in op.Read and e.op->e".op in rf => e->e" in vis.rel
}
****/

fact WellFormedHistory { 
    all s: Session | !s.events.hasDups and !s.events.isEmpty 
    all s: Session| s in History.sessions // All sessions in one history 
    all o : Operation | one op.o 
    all e: E | one s: Session | e in s.events.elems
    so in session.~session // Session order is over events in the same session 
    no id[E] & so and so.so in so // Session order is partial
    all s: Session | IsTotalOverEvents[s.events.elems,so] // Session order is total over one session
}

pred IsTotalOverEvents[s: set E, r: E->E] {
    all disj e, e": E | e in s and e" in s => e.r = e" and e".r != e or e".r = e and e.r != e"
}

// Each write event returns ok
fact WritesReturnOK { all w : op.Write | w.rval = OK }
// Each read event returns a value or initial value undef
fact ReadsReturnValuesOrUndef { all r : op.Read | r.rval in V + Undef }

fact VisibilityIsAcyclic { no id[E] & ^(Visibility.rel) }

fun lastVisibleWrite[e: E, vis: Visibility, ar: Arbitration]: lone E {
    {w : op.Write | w->e in vis.rel and no ww : op.Write | ww->e in vis.rel and w->ww in ar.rel}
}
// An read returns Undef or preceding last write
pred ReadLastVisibleWrite[vis: Visibility, ar: Arbitration] {
    all r : op.Read | r.rval = Undef and vis.rel.r = none or
        some (op.Write & vis.rel.r) => r.rval=lastVisibleWrite[r,vis,ar].op.value
}
// Any read in V(e) of an event e can be justified
pred VeIsReasonable[vis: Visibility, ar: Arbitration] {
    (op.Read).ve = none or 
    all r: op.Read.ve & op.Read |  r.rval = Undef and vis.rel.r = none or 
        some (op.Write & vis.rel.r) => r.rval=lastVisibleWrite[r,vis,ar].op.value
}

pred ArIsTotalOrder[ar: Arbitration]  { no id[E] & ar.rel and (ar.rel).(ar.rel) in ar.rel and E->E in ar.rel + ~(ar.rel) + id[E] }

pred VisAr[vis: Visibility, ar: Arbitration] {all disj e, e" : E | e->e" in vis.rel =>  e->e"  in ar.rel }
//fact SessionOrderIsConsistentWithVisibility { so in vis }

// Recipes for visibility
pred SoInVis[vis: Visibility] {so in vis.rel}

// Happens-before relation
fun hb[vis: Visibility]: E->E { ^(so + vis.rel) }
pred CausalVisibility[vis: Visibility] {hb[vis] in vis.rel}

fact WellFormedV { all e: E | e.ve in e.(Visibility.rel)}
// Recipes for V 
pred Ve { all e: E | e.ve = none }
pred Ve2 { all e: E | e.ve = e.so }
pred Ve3[vis: Visibility] { all e: E | e.ve = e.(vis.rel) }

// Causal consistency variants
pred Wcc { some vis: Visibility | some ar: Arbitration | ReadLastVisibleWrite[vis,ar] and SoInVis[vis] and CausalVisibility[vis] and VisAr[vis,ar] and Ve }
pred CM { one vis: Visibility | one ar: Arbitration | ReadLastVisibleWrite[vis,ar] and CausalVisibility[vis] and VisAr[vis,ar] and Ve2 }
pred SCC {one vis: Visibility | one ar: Arbitration | ReadLastVisibleWrite[vis,ar] and CausalVisibility[vis]and VisAr[vis,ar] and Ve3[vis] }
pred WCCv { one vis: Visibility | one ar: Arbitration | ReadLastVisibleWrite[vis,ar] and CausalVisibility[vis] and VisAr[vis,ar] and Ve and ArIsTotalOrder[ar] }
pred CMv { one vis: Visibility | one ar: Arbitration | ReadLastVisibleWrite[vis,ar] and CausalVisibility[vis] and VisAr[vis,ar]  and Ve2 and ArIsTotalOrder[ar] }
pred SCCv { one vis: Visibility | one ar: Arbitration | ReadLastVisibleWrite[vis,ar] and CausalVisibility[vis] and VisAr[vis,ar]  and Ve3[vis] and ArIsTotalOrder[ar] }

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
