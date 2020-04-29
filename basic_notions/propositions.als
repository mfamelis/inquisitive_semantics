module propositions
/*

Signatures:
- Proposition

Predicates:

Functions:

*/

open information_states
open nedocsis
open issues

//--------------------------------------------------------------------------------

// A Proposition is a Non-Empty Downwards Closed Set of Information States (NEDOCSIS)
sig Proposition extends Nedocsis {}

// Informative content of a proposition
fun info [p : Proposition] : one InformationState {
	union[p]
}

// An issue embodied by a proposition is one that is resolved in a state q iff q in P
pred embodied [i : Issue, p : Proposition] {
	all q : InformationState |
		resolves[q,i] iff isIn[q,p]	
}

/*
A simple way to see that the definitions above work is to open the evaluator and compare
the results for:
{k:Issue|embodied[k,Proposition$0]}
alternatives[issues/Issue$1]
info[Proposition$0] 
*/
run showPropositions {
	all p:Proposition| some i:Issue | embodied[i,p] and proper[i]
} 
for 10 but exactly 3 PossibleWorld, exactly 1 Proposition, exactly 2 Issue

check theEmbodiedIssueIsOverTheInfo {
	all p:Proposition, i:Issue | embodied[i,p] implies over[i,info[p]]
} for 20 but exactly 3 PossibleWorld // seems legit

//--------------------------------------------------------------------------------
