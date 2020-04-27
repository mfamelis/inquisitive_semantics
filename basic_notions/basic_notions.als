open util/relation

sig PossibleWorld {}

sig InformationState {
	pw : set PossibleWorld
}


/* An InformationState t enhances s if t subseteq s */
pred enhances_p(t,s: InformationState){
	all p: PossibleWorld | p in t.pw implies p in s.pw
}

one sig EnhancementHierarchy
{ enhances : InformationState->InformationState }
{	
	/* We always need the empty InfoState (i.e., false) */
	some emptyInformationState : InformationState | 
		#(emptyInformationState.pw)=0
	/* And let's also add the complete space of possibilities (i.e., true) */
	some completeInformationState : InformationState | 
		#(completeInformationState.pw)=#PossibleWorld
	/* Let's show enhancements as arrows */
	all t,s:InformationState| t->s in enhances iff enhances_p[t,s]
	// NOTE: this does not require all possible enhancements to be generated!
	// How do I make it generate all possible InfoStates?
}


/* Two information states are the same if they have the same possible worlds */
fact uniqueInformationStates {
	all t,s:InformationState |
	(t.pw in s.pw and s.pw in t.pw) implies (t=s)
}

fact {partialOrder[EnhancementHierarchy.enhances,InformationState]}

run {} for 4 but exactly 0 Issue

/* An Issue is a non-empty downward closed set of InformationStates */
sig Issue {
	states : set InformationState
}{
	// non empty
	#(states) >1
	// downward closed: if I contains s, then it contains all t that enhance s
	all s,t:InformationState | 
		(s in states and enhances_p[t,s])
	implies 
		(t in states)
}

run {} for 4 but 10 InformationState, exactly 1 Issue, exactly 4 PossibleWorld
