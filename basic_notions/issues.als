module issues

open information_states

sig Issue {
	states : set InformationState
}

pred resolves(s : InformationState, i : Issue){
	s in i.states
}

fact issuesNonEmpty {
	all i : Issue | some s : InformationState | resolves[s,i]
}
fact issuesDownwardClosed{
	// If s resolves I and t enhances s, then t resolves I
	all i : Issue | all s : InformationState | 
		resolves[s,i] implies 
		all t : InformationState | enhances[t,s] implies resolves[t,i]
}

assert inconsistentInformationStateAlwaysAResolution{
	all i : Issue | all s : InformationState |
		inconsistentState[s] implies resolves[s,i]
}

check inconsistentInformationStateAlwaysAResolution for 20 // seems valid

pred showIssues {}

run showIssues for 10 but exactly 3 PossibleWorld, exactly 1 Issue
