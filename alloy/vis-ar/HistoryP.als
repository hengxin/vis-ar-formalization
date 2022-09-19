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

pred VisibilityIsAcyclic[vis: E->E] { no id[E] & vis and vis.vis in vis and no id[E] & ^vis }

fun lastVisibleWrite[e: E, vis: E->E, ar: E->E]: lone E {
    {w : op.Write | w->e in vis and no ww : op.Write | ww->e in vis and w->ww in ar}
}
// An read returns Undef or preceding last write
pred ReadLastVisibleWrite[vis: E->E, ar: E->E] {
    all r : op.Read | some (op.Write & vis.r) => r.rval=lastVisibleWrite[r,vis,ar].op.value else r.rval=Undef
}
// Any read in V(e) of an event e can be justified
pred VeIsReasonable[vis: E->E, ar: E->E] {
    all r: ve.(op.Read) & op.Read | some (op.Write & vis.r) => r.rval=lastVisibleWrite[r,vis,ar].op.value else r.rval=Undef
}

pred ArIsPartial[ar: E->E] {no id[E] & ar and ar.ar in ar }
pred ArIsTotalOrder[ar: E->E]  { no id[E] & ar and ar.ar in ar and E->E in ar + ~ar + id[E] }

pred VisAr[vis: E->E, ar:  E->E] { vis in ar }

// Recipes for visibility
pred SoInVis[vis: E->E] {so in vis}

// Happens-before relation
fun hb[vis: E->E]: E->E { ^(so + vis) }
pred CausalVisibility[vis: E->E] { hb[vis] in vis }

pred WellFormedV[vis: E->E] { all e: E | e.ve in e.vis }
// Recipes for V 
pred Ve { all e: E | e.ve = none }
pred Ve2 { all disj e, e": E | e" in ve.e <=> e" in so.e }
pred Ve3[vis: E->E] { all e: E | ve.e = vis.e }

// Causal consistency variants
pred Wcc { 
    some vis: E->E | some ar: E->E | 
        VisibilityIsAcyclic[vis] and WellFormedV[vis] and ArIsPartial[ar]
        and SoInVis[vis] and CausalVisibility[vis] and VisAr[vis,ar] and Ve
        and ReadLastVisibleWrite[vis,ar] and VeIsReasonable[vis,ar]
}
pred CM {     
    some vis: E->E | some ar: E->E | 
        VisibilityIsAcyclic[vis] and WellFormedV[vis] and ArIsPartial[ar]
        and SoInVis[vis] and CausalVisibility[vis] and VisAr[vis,ar] and Ve2 
        and ReadLastVisibleWrite[vis,ar] and VeIsReasonable[vis,ar]
}
pred SCC {
    some vis: E->E | some ar: E->E | 
        VisibilityIsAcyclic[vis] and WellFormedV[vis] and ArIsPartial[ar]
         and SoInVis[vis] and CausalVisibility[vis] and VisAr[vis,ar] and Ve3[vis]
        and ReadLastVisibleWrite[vis,ar] and VeIsReasonable[vis,ar]
}
pred WCCv {
    some vis: E->E | some ar: E->E | 
        VisibilityIsAcyclic[vis] and WellFormedV[vis] and ArIsPartial[ar] and ArIsTotalOrder[ar] 
        and SoInVis[vis] and CausalVisibility[vis] and VisAr[vis,ar] and Ve
        and ReadLastVisibleWrite[vis,ar] and VeIsReasonable[vis,ar]
}
pred CMv {
    some vis: E->E | some ar: E->E | 
        VisibilityIsAcyclic[vis] and WellFormedV[vis] and ArIsPartial[ar] and ArIsTotalOrder[ar]
        and SoInVis[vis] and CausalVisibility[vis] and VisAr[vis,ar] and Ve2 
        and ReadLastVisibleWrite[vis,ar] and VeIsReasonable[vis,ar]
}
pred SCCv {
    some vis: E->E | some ar: E->E | 
        VisibilityIsAcyclic[vis] and WellFormedV[vis] and ArIsPartial[ar] and ArIsTotalOrder[ar]
         and SoInVis[vis] and CausalVisibility[vis] and VisAr[vis,ar] and Ve3[vis]
        and ReadLastVisibleWrite[vis,ar] and VeIsReasonable[vis,ar]
}

////////////////////////////////////////////////////////////////////////////////
// =Perturbations=

abstract sig PTag {}

one sig RE extends PTag {} // Remove Even

fun no_p : PTag->univ { // no_p - constant for no perturbation
  (PTag->univ) - (PTag->univ)
}

fun so_p[p: PTag->univ] : E->E { (E - p[RE]) <: so :> (E - p[RE]) }
fun vis_p[vis: E-> E, p: PTag->univ] : E->E { (E - p[RE]) <: vis :> (E - p[RE]) } 
fun ar_p[ar: E-> E, p: PTag->univ] : E->E { (E - p[RE]) <: ar :> (E - p[RE]) } 

pred ArIsPartial_p[ar: E->E, p: PTag->univ] {no id[E- p[RE]] & ar_p and ar_p.ar_p in ar_p }
pred ArIsTotalOrder_p[ar: E->E, p: PTag->univ]  { no id[E- p[RE]] & ar_p and ar_p.ar_p in ar_p and (E- p[RE])->(E- p[RE]) in ar_p + ~ar_p + id[E- p[RE]] }

pred VisAr[vis: E->E, ar: E->E, p: PTag->univ] { vis_p[vis,p] in ar_p[ar,p] }

// Recipes for visibility
pred SoInVis[vis: E->E, p: PTag->univ] {so_p[p] in vis_p[vis,p]}

// Happens-before relation
fun hb_p[vis: E->E, p: PTag->univ]: E->E { ^(so_p[p] + vis_p[vis,p]) }
pred CausalVisibility[vis: E->E, p: PTag->univ] { hb_p[vis,p] in vis_p[vis,p] }

pred WellFormedV_p[vis: E->E, p: PTag->univ] { all e: E | e.ve in e.vis_p[vis,p]}
pred Ve_p { all e: E | e.ve = none }
pred Ve2_p { all disj e, e": E | e" in ve.e <=> e" in so.e }
pred Ve3_p[vis: E->E, p: PTag->univ] { all e: E | ve.e = vis_p[vis,p].e }

pred WCCv_p[p: PTag->univ] {
    some vis: E->E | some ar: E->E | 
        VisibilityIsAcyclic[vis] and WellFormedV_p[vis,p] and ArIsPartial_p[ar,p] and ArIsTotalOrder_p[ar,p]
         and SoInVis_p[vis,p] and CausalVisibility_p[vis] and VisAr_p[vis,ar] and Ve3_p[vis,p]
        and ReadLastVisibleWrite[vis,ar] and VeIsReasonable[vis,ar]
}
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Constraints on the search space
fact {
  all k: Key | some (k.~key) :> Write and some (k.~key) :> Read
}

let interesting_model[model] {
    model
}

let interesting_not_axiom[axiom] {
  not axiom[no_p]

  // All events must be relevant and minimal
  all e: Event | tso_p[RE->e]
}

run Wcc {
  interesting_model[Wcc] and #Read>1 and #Write>1 and #Session=2 
} for 4

run CM {
  interesting_model[CM] and #Read>1 and #Write>1 and #Session=2
} for 8

run SCC {
  interesting_model[SCC] and #Read>1 and #Write>1 and #Session=2 
} for 8

run WCCv {
  interesting_model[WCCv] and #Read>1 and #Write>1 and #Session=2 
} for 4

run CMv {
  interesting_model[CMv] and #Read>1 and #Write>1 and #Session>=2
} for 4

run SCCv {
  interesting_model[SCCv] and #Read>1 and #Write>1 and #Session>=2
} for 8
