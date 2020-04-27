open util/relation

sig Atom {}

sig Set {
	atoms 		: set Atom,
	subsetOf	: set Set
}

fact uniqueSets {
	all t,s : Set | (t.atoms = s.atoms) iff (t = s)
}
fact top {
	some s : Set | all a : Atom | a in s.atoms
}
fact bottom {
	some s : Set | no a : Atom | a in s.atoms
}

fact subsets {
	all t,s : Set | (s in t.subsetOf) iff (t.atoms in s.atoms)
}

fact allSubsets {
	all s: Set | all a : Atom | (a in s.atoms) implies
		some t : Set | (s in t.subsetOf) and (t.atoms = s.atoms-a)
}

run {} for 10 but exactly 3 Atom

fact{partialOrder[subsetOf,Set]}
