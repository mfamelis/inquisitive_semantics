module issues
/*

Signatures:
- Issue

Predicates:
- resolves (s : InformationState, i : Issue)
- over (i : Issue, s : InformationState)
- trivialIssue (i : Issue, state: InformationState)
- refines [i,j : Issue]
- proper [i : Issue]

Functions:
- leastInquisitiveIssue [s: InformationState] : one Issue 
- mostInquisitiveIssue [s: InformationState] : one Issue
- alternatives [i : Issue] : set InformationState 

*/

open information_states
open nedocsis

//--------------------------------------------------------------------------------

// An Issue is a Non-Empty Downwards Closed Set of Information States (NEDOCSIS)
sig Issue extends Nedocsis {}

pred resolves (q : InformationState, i : Issue){
	isIn[q,i]
}

pred showIssues {}
run showIssues for 10 but exactly 3 PossibleWorld, exactly 1 Issue

//--------------------------------------------------------------------------------

// An issue I is over a state iff UI=s
// Given an issue I, the state s := Ui, that is the union of all the elements in I 
// contains exactly the information that is necessary and sufficient to guarrantee 
// that it can be truthfully resolved
pred over (i : Issue, s : InformationState) {
	union[i] = s // uses the predicate union from nedocsis
}

// It should follow that it is possible to create issues over the entire logical space
run overEntireSpace {
	some i : Issue | some s : InformationState |
		over[i,s] and ignorantState[s]
} for 20 but exactly 4 PossibleWorld, exactly 1 Issue // seems legit

// The trivial issue over a state is resolved by anything in the state
pred trivialIssue (i : Issue, state: InformationState){
	resolves[state,i] and over[i,state]
}

// The trivial issue over the ignorant state should be resolved by any state
check theTrivialIssueOverTheIgnorantStateIsResolvedByAnything {
	all i:Issue, s:InformationState|
		(ignorantState[s] and trivialIssue[i,s]) implies (no q:InformationState | not resolves[q,i])
} for 20 but exactly 3 PossibleWorld // seems legit

// Shows trivial issues over states that are not necessarily the ignorant state
run trivialIssue for 20 but exactly 4 PossibleWorld, exactly 1 Issue // seems legit

//--------------------------------------------------------------------------------

// An issue I can refine another issue J
pred refines [i,j : Issue]{
	(i.states in j.states) and (some s : InformationState | over[i,s] and over[j,s])
}

run showRefinement {
	// i refines j
	some i,j:Issue|refines[i,j] and not i=j
} for 10 but exactly 3 PossibleWorld, exactly 2 Issue

//--------------------------------------------------------------------------------

fun leastInquisitiveIssue [s: InformationState] : one Issue {
	{i : Issue | trivialIssue[i,s]}
}
// Shows the least inquisitive state for states that are not the ignorant state
run showLeastInquisitiveIssue {
	some state : InformationState, i : Issue | not ignorantState[state] and i=leastInquisitiveIssue[state]
} for 20 but exactly 4 PossibleWorld, exactly 1 Issue


fun mostInquisitiveIssue [s: InformationState] : one Issue {
	{i : Issue | over[i,s] and 
		all t : InformationState | resolves[t,i] implies 
			(#(t.worlds)=1 or inconsistentState[t]) 
	}
}
// Shows the most inquisitive issue for states that are not necessarily the ignorant state
run showMostInquisitiveIssue {
	some state : InformationState, i : Issue | i=mostInquisitiveIssue[state]
} for 20 but exactly 4 PossibleWorld, exactly 1 Issue

// If a most inquisitive issue is over a state that is not {w} or {empty} 
// then that state should not resolve it
check complexStateOverWhichMostInquisitiveIssueIsDefinedDoesNotResolveIt {
	all state:InformationState, i:Issue |
		i=mostInquisitiveIssue[state] implies (
			not resolves[state,i] or
			inconsistentState[state] or (#state.worlds=1)
		)
} for 20 but exactly 4 PossibleWorld, exactly 1 Issue //seems legit

//--------------------------------------------------------------------------------

// The alternatives of an issue are its maximal elements
// A maximal element of an Issue i is a state s that resolves it and
// it is not a proper enhancement of any other state that also resolves it
fun alternatives [i : Issue] : set InformationState {
	{alt : InformationState | 
		resolves[alt,i] and 
		no other : InformationState | 
			isProperEnhancement[alt,other] and resolves[other,i]
	}
}

// If an issue over a state is trivial, it has exactly one alternative: the state
check trivialIssuesHaveExactlyOneAlternative{
	all q:InformationState, i:Issue|
		trivialIssue[i,q] implies q=alternatives[i]
} for 20 but exactly 4 PossibleWorld, exactly 1 Issue //seems legit

// An issue is called proper if it has more than one alternative
pred proper [i : Issue]{
	#alternatives[i]>1
}
// Good way to visualize the alternatives[] pred using the evaluator
run proper for 20 but exactly 3 PossibleWorld, exactly 1 Issue

// A proper issue is not trivial
check properIssueIsNonTrivial{
	all q:InformationState, i:Issue|
		(over[i,q] and proper[i]) implies (not trivialIssue[i,q])
} for 20 but exactly 4 PossibleWorld, exactly 1 Issue //seems legit

