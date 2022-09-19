module AbstractExecution

let id[A] = A<:iden

// Abstract execution 
sig E {
    op: one RWOperation,
    rval: Value, // Assuming that the events are complete
    so: set E,
    session: one Session,
    ve: set E
} {
    all e: E | e in e.@session.events.elems
}

/***
sig Visibility {
    rel: set E->E
}

sig Arbitration {
    rel: set E->E
}
***/

// A session is a sequence of events
sig Session {
    events: seq E
}

// A history is a set of sessions
one sig History {
    sessions: set Session
}

abstract sig Value {}
sig V extends Value {}
one sig Undef extends Value {} // Initial value
one sig OK extends Value {} // Writes return OK

sig Key {}

sig RWOperation {
    key: one Key
}

// read-write register
sig Read extends RWOperation {}
sig Write extends RWOperation {
    value: one V
    //rf: lone Read  // Reads-from relation
}

fact WellFormedHistory { 
    all s: Session | !s.events.hasDups and !s.events.isEmpty 
    all s: Session| s in History.sessions // All sessions in one history 
    all o : RWOperation | one op.o 
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

pred VisibilityIsAcyclic[vis: set E->E] { no id[E] & vis and vis.vis in vis and no id[E] & ^vis }

fun lastVisibleWrite[e: E, vis: set E->E, ar: set E->E]: lone E {
    {w : op.Write | w->e in vis and no ww : op.Write | ww->e in vis and w->ww in ar}
}
// An read returns Undef or preceding last write
pred ReadLastVisibleWrite[vis: set E->E, ar: set E->E] {
    all r : op.Read | r.rval = Undef and vis.r = none or
        some (op.Write & vis.r) => r.rval=lastVisibleWrite[r,vis,ar].op.value
}
// Any read in V(e) of an event e can be justified
pred VeIsReasonable[vis: set E->E, ar: set E->E] {
    (op.Read).ve = none or 
    all r: op.Read.ve & op.Read |  r.rval = Undef and vis.r = none or 
        some (op.Write & vis.r) => r.rval=lastVisibleWrite[r,vis,ar].op.value
}

pred ArIsPartial[ar: set E->E] {no id[E] & ar and ar.ar in ar }
pred ArIsTotalOrder[ar: set E->E]  { no id[E] & ar and ar.ar in ar and E->E in ar + ~ar + id[E] }

pred VisAr[vis: set E->E, ar: set E->E] { vis in ar }
//fact SessionOrderIsConsistentWithVisibility { so in vis }

// Recipes for visibility
pred SoInVis[vis: set E->E] {so in vis}

// Happens-before relation
fun hb[vis: set E->E]: E->E { ^(so + vis) }
pred CausalVisibility[vis: set E->E] { hb[vis] in vis }

pred WellFormedV[vis: set E->E] { all e: E | e.ve in e.vis }
// Recipes for V 
pred Ve { all e: E | e.ve = none }
pred Ve2 { all e: E | e.ve = e.so }
pred Ve3[vis: set E->E] { all e: E | e.ve = e.vis }

// Causal consistency variants
pred Wcc { 
    one vis: set E->E | one ar: set E->E | 
        VisibilityIsAcyclic[vis] and WellFormedV[vis] and ArIsPartial[ar]
        and SoInVis[vis] and CausalVisibility[vis] and VisAr[vis,ar] and Ve
        and ReadLastVisibleWrite[vis,ar] and VeIsReasonable[vis,ar]
}
pred CM { one vis: set E->E | one ar: set E->E | ReadLastVisibleWrite[vis,ar] and CausalVisibility[vis] and VisAr[vis,ar] and Ve2 }
pred SCC {one vis: set E->E | one ar: set E->E | ReadLastVisibleWrite[vis,ar] and CausalVisibility[vis]and VisAr[vis,ar] and Ve3[vis] }
pred WCCv { one vis: set E->E | one ar: set E->E | ReadLastVisibleWrite[vis,ar] and CausalVisibility[vis] and VisAr[vis,ar] and Ve and ArIsTotalOrder[ar] }
pred CMv { one vis: set E->E | one ar: set E->E | ReadLastVisibleWrite[vis,ar] and CausalVisibility[vis] and VisAr[vis,ar]  and Ve2 and ArIsTotalOrder[ar] }
pred SCCv { one vis: set E->E | one ar: set E->E | ReadLastVisibleWrite[vis,ar] and CausalVisibility[vis] and VisAr[vis,ar]  and Ve3[vis] and ArIsTotalOrder[ar] }

let interesting_model[model] {
    model
}

run Wcc {
  interesting_model[Wcc] and #Read>1 and #Write>1 and #Session=2 
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
