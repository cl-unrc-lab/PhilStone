open util/relation

-- basic signatures

pred true {no none}
pred false {some none}

abstract sig Node{}
abstract sig Prop{}
abstract sig Enum{}
abstract sig NumVar{}
abstract sig EnumVar{}

-- for bool propositions
one sig Prop_cs extends Prop{}
one sig Prop_try3 extends Prop{}

-- for int vars

-- for enum vars

-- definition of the propositions in the model

-- definition of the propositions in the model corresponding to volatile Bools
one sig Prop_try1 extends Prop{}
one sig Prop_try2 extends Prop{}
one sig Prop_turn0 extends Prop{}
one sig Prop_turn1 extends Prop{}

-- definition of the int in the model

-- definition of the int in the model correpsonding to volatile ints

-- definition of the int in the model

-- definition of the int in the model correpsonding to volatile ints

-- definition of the enums, one enum for each possible value

-- definition of the inc fun for every enum type

-- definition of the dec fun for every enum type

pred Prop_cs[m:proc3Meta,n:Node]{Prop_cs in m.val[n] }
pred Prop_try3[m:proc3Meta,n:Node]{Prop_try3 in m.val[n] }






pred Prop_try1[m:proc3Meta,n:Node]{Prop_try1 in m.val[n] }
pred Prop_try2[m:proc3Meta,n:Node]{Prop_try2 in m.val[n] }
pred Prop_turn0[m:proc3Meta,n:Node]{Prop_turn0 in m.val[n] }
pred Prop_turn1[m:proc3Meta,n:Node]{Prop_turn1 in m.val[n] }



-- additional vars for shared non-rpimitive vars representing the locks associated to each of them




-- similarly for the shared non-primitive  ints




-- and for the shared non-primitive enums




-- and variables for those locks that are not linked to any variables





one sig proc3Meta{
	nodes:set Node,
	val: nodes -> Prop,
,
,
	succs : nodes -> nodes,
	local: nodes -> nodes,
	env: nodes -> nodes,
	ACTsetTryTurn:nodes -> nodes,
	ACTenterCS:nodes -> nodes,
	ACTleaveCS:nodes -> nodes,
    ACTchange_try1:nodes -> nodes,
    ACTchange_try2:nodes -> nodes,
    ACTchange_turn0:nodes -> nodes,
    ACTchange_turn1:nodes -> nodes,

}
{
        succs = ACTsetTryTurn+ACTenterCS+ACTleaveCS 
         + ACTchange_try1+ACTchange_try2+ACTchange_turn0+ACTchange_turn1 
        local = ACTsetTryTurn+ACTenterCS+ACTleaveCS
        env = ACTchange_try1+ACTchange_try2+ACTchange_turn0+ACTchange_turn1
	/* 
        no (local & env)
    */
}

-- actions axioms
    fact Action_setTryTurn_Ax1{ all s:proc3Meta.nodes | all s':proc3Meta.ACTsetTryTurn[s] | (( (not Prop_cs[proc3Meta,s]) and (not Prop_try3[proc3Meta,s]))) implies ((Prop_turn0[proc3Meta,s'] and (Prop_try3[proc3Meta,s']) and (not Prop_turn1[proc3Meta,s']))) } 
    fact Action_enterCS_Ax1{ all s:proc3Meta.nodes | all s':proc3Meta.ACTenterCS[s] | ((Prop_try3[proc3Meta,s] and (not Prop_cs[proc3Meta,s]))) implies ((Prop_cs[proc3Meta,s'])) } 
    fact Action_leaveCS_Ax1{ all s:proc3Meta.nodes | all s':proc3Meta.ACTleaveCS[s] | ((Prop_cs[proc3Meta,s])) implies (( (not Prop_cs[proc3Meta,s']) and (not Prop_try3[proc3Meta,s']))) }  

    fact Action_setTryTurn_Ax2{ all s:proc3Meta.nodes | (not (( (not Prop_cs[proc3Meta,s]) and (not Prop_try3[proc3Meta,s])))) implies (no proc3Meta.ACTsetTryTurn[s])} 
    fact Action_enterCS_Ax2{ all s:proc3Meta.nodes | (not ((Prop_try3[proc3Meta,s] and (not Prop_cs[proc3Meta,s])))) implies (no proc3Meta.ACTenterCS[s])} 
    fact Action_leaveCS_Ax2{ all s:proc3Meta.nodes | (not ((Prop_cs[proc3Meta,s]))) implies (no proc3Meta.ACTleaveCS[s])}  

    fact Action_setTryTurn_Ax3{ all s:proc3Meta.nodes | (( (not Prop_cs[proc3Meta,s]) and (not Prop_try3[proc3Meta,s]))) implies (some proc3Meta.ACTsetTryTurn[s])  } 
    fact Action_enterCS_Ax3{ all s:proc3Meta.nodes | ((Prop_try3[proc3Meta,s] and (not Prop_cs[proc3Meta,s]))) implies (some proc3Meta.ACTenterCS[s])  } 
    fact Action_leaveCS_Ax3{ all s:proc3Meta.nodes | ((Prop_cs[proc3Meta,s])) implies (some proc3Meta.ACTleaveCS[s])  }  


-- resource axioms for booleans
-- similar axioms for those variables that are only locks, no data associated to them
-- these axioms state that local actions cannot change shared variables which locks are not owned by the process

-- the following axioms state that environment actions are unrestricted
/*
*/

/*
-- new version of these axioms, using the * instead of next, it should be more efficient...
*/

/*
-- similarly for volatile booleans
    fact ResAx5 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.env)[s]) | Prop_try1[proc3Meta,s']) }fact ResAx5 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.env)[s]) | Prop_try2[proc3Meta,s']) }fact ResAx5 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.env)[s]) | Prop_turn0[proc3Meta,s']) }fact ResAx5 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.env)[s]) | Prop_turn1[proc3Meta,s']) }  
    fact ResAx6 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.env)[s]) | not Prop_try1[proc3Meta,s']) }fact ResAx6 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.env)[s]) | not Prop_try2[proc3Meta,s']) }fact ResAx6 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.env)[s]) | not Prop_turn0[proc3Meta,s']) }fact ResAx6 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.env)[s]) | not Prop_turn1[proc3Meta,s']) } 
*/


/*
-- similarly for volatile booleans
    fact ResAx5 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.ACTchange_try1)[s]) | Prop_try1[proc3Meta,s']) }fact ResAx5 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.ACTchange_try2)[s]) | Prop_try2[proc3Meta,s']) }fact ResAx5 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.ACTchange_turn0)[s]) | Prop_turn0[proc3Meta,s']) }fact ResAx5 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.ACTchange_turn1)[s]) | Prop_turn1[proc3Meta,s']) }  
    fact ResAx6 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.ACTchange_try1)[s]) | not Prop_try1[proc3Meta,s']) }fact ResAx6 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.ACTchange_try2)[s]) | not Prop_try2[proc3Meta,s']) }fact ResAx6 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.ACTchange_turn0)[s]) | not Prop_turn0[proc3Meta,s']) }fact ResAx6 { all s:proc3Meta.nodes | (some s':(*(proc3Meta.ACTchange_turn1)[s]) | not Prop_turn1[proc3Meta,s']) } 

*/

    fact ResAx5 { all s:proc3Meta.nodes | (some s':proc3Meta.ACTchange_try1[s] | Prop_try1[proc3Meta,s']) }fact ResAx5 { all s:proc3Meta.nodes | (some s':proc3Meta.ACTchange_try2[s] | Prop_try2[proc3Meta,s']) }fact ResAx5 { all s:proc3Meta.nodes | (some s':proc3Meta.ACTchange_turn0[s] | Prop_turn0[proc3Meta,s']) }fact ResAx5 { all s:proc3Meta.nodes | (some s':proc3Meta.ACTchange_turn1[s] | Prop_turn1[proc3Meta,s']) }  
    fact ResAx6 { all s:proc3Meta.nodes | (some s':proc3Meta.ACTchange_try1[s] | not Prop_try1[proc3Meta,s']) }fact ResAx6 { all s:proc3Meta.nodes | (some s':proc3Meta.ACTchange_try2[s] | not Prop_try2[proc3Meta,s']) }fact ResAx6 { all s:proc3Meta.nodes | (some s':proc3Meta.ACTchange_turn0[s] | not Prop_turn0[proc3Meta,s']) }fact ResAx6 { all s:proc3Meta.nodes | (some s':proc3Meta.ACTchange_turn1[s] | not Prop_turn1[proc3Meta,s']) } 

-- resource axioms for ints
-- and axioms stating that environment actions are not restricted for ints
-- and similar for volatile ints

-- Resourse axioms for enums
-- and similar for volatile enums

-- frame axioms for local  variables
 
    fact FrameAxiomssetTryTurn{ 
                all s:proc3Meta.nodes | all s':proc3Meta.ACTsetTryTurn[s] | (Prop_cs[proc3Meta,s] iff Prop_cs[proc3Meta, s']) and (Prop_try1[proc3Meta,s] iff Prop_try1[proc3Meta, s']) and (Prop_try2[proc3Meta,s] iff Prop_try2[proc3Meta, s'])
            }

    fact FrameAxiomsenterCS{ 
                all s:proc3Meta.nodes | all s':proc3Meta.ACTenterCS[s] | (Prop_try1[proc3Meta,s] iff Prop_try1[proc3Meta, s']) and (Prop_try2[proc3Meta,s] iff Prop_try2[proc3Meta, s']) and (Prop_turn0[proc3Meta,s] iff Prop_turn0[proc3Meta, s']) and (Prop_turn1[proc3Meta,s] iff Prop_turn1[proc3Meta, s']) and (Prop_try3[proc3Meta,s] iff Prop_try3[proc3Meta, s'])
            }

    fact FrameAxiomsleaveCS{ 
                all s:proc3Meta.nodes | all s':proc3Meta.ACTleaveCS[s] | (Prop_try1[proc3Meta,s] iff Prop_try1[proc3Meta, s']) and (Prop_try2[proc3Meta,s] iff Prop_try2[proc3Meta, s']) and (Prop_turn0[proc3Meta,s] iff Prop_turn0[proc3Meta, s']) and (Prop_turn1[proc3Meta,s] iff Prop_turn1[proc3Meta, s'])
            }



-- frame axioms for locks (shared vars)
-- for volatile vars we just say that local and non-volatile vars are not changed by the environmental methods that change volatile vars
fact FrameAxiomstry1{ 
    all s:proc3Meta.nodes | all s':proc3Meta.ACTchange_try1[s] | true
        and
         (Prop_cs[proc3Meta,s] iff Prop_cs[proc3Meta, s']) and  (Prop_try3[proc3Meta,s] iff Prop_try3[proc3Meta, s'])
        and 
        (Prop_try2[proc3Meta,s] iff Prop_try2[proc3Meta, s']) and (Prop_turn0[proc3Meta,s] iff Prop_turn0[proc3Meta, s']) and (Prop_turn1[proc3Meta,s] iff Prop_turn1[proc3Meta, s'])
}
fact FrameAxiomstry2{ 
    all s:proc3Meta.nodes | all s':proc3Meta.ACTchange_try2[s] | true
        and
         (Prop_cs[proc3Meta,s] iff Prop_cs[proc3Meta, s']) and  (Prop_try3[proc3Meta,s] iff Prop_try3[proc3Meta, s'])
        and 
        (Prop_try1[proc3Meta,s] iff Prop_try1[proc3Meta, s']) and (Prop_turn0[proc3Meta,s] iff Prop_turn0[proc3Meta, s']) and (Prop_turn1[proc3Meta,s] iff Prop_turn1[proc3Meta, s'])
}
fact FrameAxiomsturn0{ 
    all s:proc3Meta.nodes | all s':proc3Meta.ACTchange_turn0[s] | true
        and
         (Prop_cs[proc3Meta,s] iff Prop_cs[proc3Meta, s']) and  (Prop_try3[proc3Meta,s] iff Prop_try3[proc3Meta, s'])
        and 
        (Prop_try1[proc3Meta,s] iff Prop_try1[proc3Meta, s']) and (Prop_try2[proc3Meta,s] iff Prop_try2[proc3Meta, s']) and (Prop_turn1[proc3Meta,s] iff Prop_turn1[proc3Meta, s'])
}
fact FrameAxiomsturn1{ 
    all s:proc3Meta.nodes | all s':proc3Meta.ACTchange_turn1[s] | true
        and
         (Prop_cs[proc3Meta,s] iff Prop_cs[proc3Meta, s']) and  (Prop_try3[proc3Meta,s] iff Prop_try3[proc3Meta, s'])
        and 
        (Prop_try1[proc3Meta,s] iff Prop_try1[proc3Meta, s']) and (Prop_try2[proc3Meta,s] iff Prop_try2[proc3Meta, s']) and (Prop_turn0[proc3Meta,s] iff Prop_turn0[proc3Meta, s'])
}




pred Form24[i:proc3Meta, s:Node]{
 some s':(*(proc3Meta.succs)[s]) | Prop_cs[proc3Meta,s']}

-- Pred with inital condition and Invariants
pred Mod[s:proc3Meta.nodes]{ 
    -- all s':(*(proc3Meta.succs)[s]) | some proc3Meta.succs[s'] -- if ew want any node has a succ
     Form24[proc3Meta,s]  
    (((((not (Prop_cs[proc3Meta,s])) and (not (Prop_turn0[proc3Meta,s]))) and (not (Prop_turn1[proc3Meta,s]))) and (not (Prop_try3[proc3Meta,s]))) and (not (Prop_try2[proc3Meta,s]))) and (not (Prop_try1[proc3Meta,s]))

}

run Mod for 15
