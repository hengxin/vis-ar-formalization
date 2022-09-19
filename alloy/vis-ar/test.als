module TransactionalHistory

sig Transaction {
	E : some HEvent,
	po: HEvent -> HEvent,
}{
	all e1, e2 : E | e1!=e2 => (e1->e2 in po or e2->e1 in po) // po is total	
	no po & ~po // po is antisymmetric
	no iden & po // po is irreflexive
	po in E->E // po only contains events from e	
}

one sig History {
	transactions: set Transaction
}

sig Obj {}

abstract sig Op {
	obj: Obj,
	val: Int
}

sig Read,Write extends Op {}

sig EventId {}
abstract sig HEvent {
	id: EventId,
	op: Op,
}{
	all h : HEvent | (h.@id = id) => h = this // event ids are distinct
}

sig REvent extends HEvent {}{ op in Read }
sig WEvent extends HEvent {}{ op in Write }

fun HEventObj[x : Obj] : HEvent { {e : HEvent | e.op.obj = x } }
fun WEventObj[x : Obj] : WEvent { HEventObj[x] & WEvent }
fun REventObj[x : Obj] : REvent { HEventObj[x] & REvent }

fact WellFormedHistory {
    all t: Transaction| t in History.transactions // All transactions belongs to one history 
	all e : HEvent | one E.e // Any HEvent belongs to one Transaction
	Op in HEvent.op   // All ops are associated with HEvents
	Obj in Op.obj  // All objs are associated with ops
}

pred WellFormedVisAr[vis: Transaction->Transaction, ar: Transaction->Transaction] { 
	vis in ar 
	all t : Transaction | t not in t.^vis  // Acyclic vis
	all t : Transaction | t not in t.^ar   // Acyclic ar
	no (iden & ar) and no (ar & ~ar) and all disj t1, t2 : Transaction | t1->t2 in ar or t2->t1 in ar // ar is total
}

////////////////////////////////////////////////////////////////////////////////
// Baseline consistency model: Read Atomic

pred noNonRepeatableReads {
all t : Transaction | 
	all r1,r2 : t.E & REvent |
		// if same object is being read and r1 comes before r2
		((r1.op.obj = r2.op.obj) and (r1->r2 in t.po) and
		// and no write after r1 and before r2
		(no w : t.E & WEvent | (w.op.obj = r1.op.obj and ({r1->w} + {w->r2}) in t.po)))
		// then they will read the same value
		=> 	r1.op.val = r2.op.val
}

//check noNonRepeatableReads

fun max[R : HEvent->HEvent, A : set HEvent] : HEvent { {u : A | all v : A | v=u or v->u in R } }
fun min[R : HEvent->HEvent, A : set HEvent] : HEvent { {u : A | all v : A | v=u or u->v in R } }

// Internal consistency axiom
pred INT {
	all t : Transaction, e : t.E, x : Obj, n : Int |
  		let prevOpX = max[t.po, (t.po).e & HEventObj[x]].op | 
    	(reads[e.op, x, n] and some (t.po).e & HEventObj[x]) => accesses[prevOpX, x, n]
}

// True if op reads n from x or writes n to x
pred accesses[op : Op, x : Obj, n : Int] { op.obj=x and op.val=n }

// True if op reads n from x
pred reads[op : Op, x : Obj, n : Int] { op in Read and accesses[op, x, n] }

// run {noNonRepeatableReads and #Obj =1} for 3

fun committedWrite[t : Transaction, x : Obj] : Int {
    max[t.po, t.E & WEventObj[x]].op.val
}

fun overwrittenWrites[t : Transaction, x : Obj] : set Int {
    (t.E & WEventObj[x]).op.val - committedWrite[t, x]
}

pred noDirtyReads {
	all x : Obj | no t : Transaction |
 	(no t.E & WEventObj[x]) and 
	(some s : Transaction |  some ((t.E & REventObj[x]).op.val & overwrittenWrites[s, x]) - {0})
}

// External consistency axiom
pred EXT[vis: Transaction->Transaction, ar: Transaction->Transaction] {
	all t : Transaction, x : Obj, n : Int |
    	TReads[t, x, n] => 
        	let WritesX = {s : Transaction | (some m : Int | TWrites[s, x, m]) } |
        	(no (vis.t & WritesX) and n=0) or TWrites[(maxAr[vis.t & WritesX, ar]), x, n]
}

// In transaction t, the last write to object x was value n
pred TWrites[t : Transaction, x : Obj, n : Int] {
	let lastWriteX = max[t.po, t.E & WEventObj[x]].op |
		lastWriteX in Write and lastWriteX.obj=x and lastWriteX.val=n
}

// In transaction t, the first access to object x was a read of value n
pred TReads[t : Transaction, x : Obj, n : Int] {
	let firstOpX = min[t.po, t.E & HEventObj[x]].op |
		firstOpX in Read and firstOpX.obj=x and firstOpX.val=n
}

fun maxAr[T: set Transaction, ar: Transaction->Transaction] : Transaction { {t : T | all s : T | s=t or s->t in ar} }

////////////////////////////////////////////////////////////////////////////////
// Stronger consistency model

pred TransVis[vis: Transaction->Transaction] { ^vis in vis }

pred NoConflict[vis: Transaction->Transaction] {
	all t,s : Transaction | 
		(some x : Obj | (t != s and (some m : Int | TWrites[t, x, m]) and (some m : Int | TWrites[s, x, m])))
		 => t->s in vis or s->t in vis
}

pred Prefix[vis: Transaction->Transaction, ar: Transaction->Transaction] { ar.vis in vis }
pred TotalVis[vis: Transaction->Transaction] { no (iden & vis) and no (vis & ~vis) and all disj t,s : Transaction | t->s in vis or s->t in vis}

pred RA { some vis, ar: Transaction->Transaction | WellFormedVisAr[vis,ar] and INT and EXT[vis,ar] }
pred CC { some vis, ar: Transaction->Transaction | WellFormedVisAr[vis,ar] and INT and EXT[vis,ar] and TransVis[vis] }
pred PC {  some vis, ar: Transaction->Transaction | WellFormedVisAr[vis,ar] and INT and EXT[vis,ar] and Prefix[vis,ar] }
pred PSI {  some vis, ar: Transaction->Transaction | WellFormedVisAr[vis,ar] and INT and EXT[vis,ar] and TransVis[vis] and NoConflict[vis]}
pred SI {  some vis, ar: Transaction->Transaction | WellFormedVisAr[vis,ar] and INT and EXT[vis,ar] and Prefix[vis,ar] } 
pred SER {  some vis, ar: Transaction->Transaction | WellFormedVisAr[vis,ar] and INT and EXT[vis,ar] and TotalVis[vis] }

run CC for 4
run {RA not CC and #Transaction=3 and #E=6} for 8
run SER for 4
