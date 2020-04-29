module nedocsis
/*

This module defines a concept used often in inquisitive semantics. 
The weird name "Nedocsis" is just an awkward acronym, it stands for a
Non-Empty DOwnwards Closed Set of Information States.
Issues, Propositions, and Contexts are all defined as Nedocsis,
so the Nedocsis concept allows some degree of code reuse.

Signatures:
- Nedocsis

Predicates:
- isIn (q : InformationState, n : Nedocsis)

*/

open information_states

// Nedocsis: a Non-Empty Downwards Closed Set of Information States
abstract sig Nedocsis {
	states : set InformationState
}

pred isIn (q : InformationState, n : Nedocsis){
	q in n.states
}

fact NonEmpty {
	all n : Nedocsis | some q : InformationState | isIn[q,n]
}

fact DownwardClosed{
	// If (q isIn N) and (t enhances q), then (t isIn N), too
	all n : Nedocsis | all q : InformationState | 
		isIn[q,n] implies 
		all t : InformationState | enhances[t,q] implies isIn[t,n]
}

// It should follow that the inconsistent state (bottom) isIn every issue
assert inconsistentInformationStateisInEveryNedocsis{
	all n : Nedocsis | all q : InformationState |
		inconsistentState[q] implies isIn[q,n]
}
check inconsistentInformationStateisInEveryNedocsis for 20 // seems legit


pred showNedocsis {}
run showNedocsis for 10 
	but exactly 3 PossibleWorld, exactly 1 Nedocsis
