module issues

open information_states

sig Issue {
	states : set InformationState
}

pred resolves(s : InformationState, i : Issue){
	s in i.states
}

// An issue is a non-empty, downward closed set of information states
fact issuesNonEmpty {
	all i : Issue | some s : InformationState | resolves[s,i]
}
fact issuesAreDownwardClosed{
	// If (s resolves I) and (t enhances s), then (t resolves I), too
	all i : Issue | all s : InformationState | 
		resolves[s,i] implies 
		all t : InformationState | enhances[t,s] implies resolves[t,i]
}

// It should follow that the inconsistent state (bottom) resolves every issue
assert inconsistentInformationStateResolvesEveryIssue{
	all i : Issue | all s : InformationState |
		inconsistentState[s] implies resolves[s,i]
}
check inconsistentInformationStateResolvesEveryIssue for 20 // seems legit

// Given an issue, the union Ui of all its elements contains exactly the information
// that is necessary and sufficient to guarrantee that it can be truthfully resolved
pred over (i : Issue, s : InformationState){
	let Ui = i.states.worlds | Ui = s.worlds
}
// It should follow that it is possible to create issues over the entire logical space
run overEntireSpace {
	some i : Issue | some s : InformationState |
		over[i,s] and ignorantState[s]
} for 20 but exactly 4 PossibleWorld, exactly 1 Issue // seems legit
// The trivial issue is resolved by anything
pred trivialIssue(i : Issue, s : InformationState){
	resolves[s,i] and ignorantState[s]  
	and over[i,s] // in reality this is superfluous
}
run trivialIssue for 20 but exactly 4 PossibleWorld, exactly 1 Issue // seems legit

pred showIssues {}
run showIssues for 10 but exactly 3 PossibleWorld, exactly 1 Issue

// One issue can refine another
pred refines[i,j : Issue]{
	(i.states in j.states) and (some s : InformationState | over[i,s] and over[j,s])
}

run showRefinement {
	some i,j:Issue|refines[i,j] and not i=j
} for 10 but exactly 3 PossibleWorld, exactly 2 Issue

/* TODO: 
Running overEntireSpace produces an Issue that is over the entire space but does not
contain the trivial issue.
I want to verify that I am not allowed to compare/refine issues that are over 
the same space but are incompatible.
E.g. I={01,12} J={02,1}
*/

/* TODO:
Least and most inquisitive issues. (should these be functions taking states as params?)
Alternatives in an issue (prob a function)
*/
