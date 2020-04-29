module nedocsis

open information_states

// Nedocsis: a Non-Empty Downwards Closed Set of Information States
abstract sig Nedocsis {
	states : set InformationState
}

pred isIn (q : InformationState, n : Nedocsis){
	q in n.states

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
