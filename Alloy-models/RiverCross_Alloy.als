module examples/puzzles/farmer

/*
 * The classic river crossing puzzle. A farmer is carrying a fox, a
 * chicken, and a sack of grain. He must cross a river using a boat
 * that can only hold the farmer and at most one other thing. If the
 * farmer leaves the fox alone with the chicken, the fox will eat the
 * chicken; and if he leaves the chicken alone with the grain, the
 * chicken will eat the grain. How can the farmer bring everything
 * to the far side of the river intact?
 *
 * authors: Greg Dennis, Rob Seater
 *
 * Acknowledgements to Derek Rayside and his students for finding and
 * fixing a bug in the "crossRiver" dicate.
 */

open util/ordering[State] as ord

/**
 * The farmer and all his possessions will be represented as Objects.
 * Some objects eat other objects when the Farmer's not around.
 */
abstract sig Object { eats: set Object }
one sig Farmer, Fox, Chicken, Grain extends Object {}

/**
 * Define what eats what when the Farmer' not around.
 * Fox eats the chicken and the chicken eats the grain.
 */
fact eating { eats = Fox->Chicken + Chicken->Grain }

/**
 * The near and far relations contain the objects held on each
 * side of the river in a given state, respectively.
 */
sig State {
   near: set Object,
   far: set Object
}

/**
 * In the initial state, all objects are on the near side.
 */
fact initialState {
   let s0 = ord/first |
     s0.near = Object && no s0.far
}

/**
 * Constrains at most one item to move from 'from' to 'to'.
 * Also constrains which objects get eaten.
 */
pred crossRiver [from, from', to, to': set Object] {
   // either the Farmer takes no items
   (from' = from - Farmer - from'.eats and
    to' = to + Farmer) or
    // or the Farmer takes one item
    (one x : from - Farmer | {
       from' = from - Farmer - x - from'.eats
       to' = to + Farmer + x })
}

/**
 * crossRiver transitions between states
 */
fact stateTransition {
  all s: State, s': ord/next[s] {
    Farmer in s.near =>
      crossRiver[s.near, s'.near, s.far, s'.far] else
      crossRiver[s.far, s'.far, s.near, s'.near]
  }
}

/**
 * the farmer moves everything to the far side of the river.
 */
pred solvePuzzle {
     ord/last.far = Object
}

run solvePuzzle for exactly 8 State expect 1

/**
 * no Object can be in two places at once
 * this is implied by both definitions of crossRiver
 */
assert NoQuantumObjects {
   no s : State | some x : Object | x in s.near and x in s.far
}

check NoQuantumObjects for 7 State 
check NoQuantumObjects for 8 State 
check NoQuantumObjects for 9 State 
check NoQuantumObjects for 10 State
check NoQuantumObjects for 11 State
check NoQuantumObjects for 12 State
check NoQuantumObjects for 13 State
check NoQuantumObjects for 14 State
check NoQuantumObjects for 15 State
check NoQuantumObjects for 20 State
check NoQuantumObjects for 30 State
check NoQuantumObjects for 40 State
check NoQuantumObjects for 50 State
check NoQuantumObjects for 75 State
check NoQuantumObjects for 100 State


assert FarmerAlwaysThere {
	all s : State | Farmer in s.near or Farmer in s.far
}

check FarmerAlwaysThere for 7 State 
check FarmerAlwaysThere for 8 State
check FarmerAlwaysThere for 9 State 
check FarmerAlwaysThere for 10 State 
check FarmerAlwaysThere for 11 State
check FarmerAlwaysThere for 12 State
check FarmerAlwaysThere for 13 State
check FarmerAlwaysThere for 14 State 
check FarmerAlwaysThere for 15 State 
check FarmerAlwaysThere for 20 State 
check FarmerAlwaysThere for 30 State 
check FarmerAlwaysThere for 40 State 
check FarmerAlwaysThere for 50 State 
check FarmerAlwaysThere for 75 State 
check FarmerAlwaysThere for 100 State

assert NoResurection {
	all s1 : State, s2: ^ord/next[s1] | all x : Object | !(x in s1.near or x in s1.far) implies !(x in s2.near or x in s2.far)   
}

check NoResurection for 7 State
check NoResurection for 8 State 
check NoResurection for 9 State 
check NoResurection for 10 State 
check NoResurection for 11 State 
check NoResurection for 12 State 
check NoResurection for 13 State 
check NoResurection for 14 State 
check NoResurection for 15 State 
check NoResurection for 16 State 
check NoResurection for 17 State 
check NoResurection for 18 State 
check NoResurection for 19 State 
check NoResurection for 20 State 
check NoResurection for 30 State 
check NoResurection for 40 State 
check NoResurection for 50 State 
check NoResurection for 75 State 
check NoResurection for 100 State 
