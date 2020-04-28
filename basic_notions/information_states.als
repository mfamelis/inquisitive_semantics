module information_states

open util/relation

sig PossibleWorld {}

sig InformationState {
	worlds 		: set PossibleWorld,
	enhances	: set InformationState
}

fact uniqueInformationStates {
	all t,s : InformationState | (t.worlds = s.worlds) iff (t = s)
}

pred discards(s : InformationState, w : PossibleWorld){
	w not in s.worlds
}

pred ignorantState(s: InformationState){
	no w : PossibleWorld | discards[s,w]
}
fact topExists {
	some s : InformationState | ignorantState[s]
}

pred inconsistentState(s: InformationState){
 all w : PossibleWorld | discards[s,w]
}
fact bottomExists {
	some s : InformationState | inconsistentState[s]
}

pred enhances(t,s : InformationState){
	s in t.enhances
}
fact enhancesIsSubsets {
	all t,s : InformationState | enhances[t,s] iff (t.worlds in s.worlds)
}
fact allEnhancementsExist { // necessary for being able to define downward closure
	all s: InformationState | all w : PossibleWorld | (w in s.worlds) implies
		some t : InformationState | enhances[t,s] and (t.worlds = s.worlds-w)
}
fact enhancementIsAPartialOrder { //uses predicate from util/relation
	partialOrder[enhances,InformationState]
}

pred isProperEnhancement(t,s : InformationState){
	enhances[t,s] and not (t=s)
}
run showProperEnhancement{
	some q,t : InformationState | isProperEnhancement[t,q]
} for 10 but exactly 3 PossibleWorld

pred showInformationStates {}

run showInformationStates 
	for 10 but exactly 3 PossibleWorld
