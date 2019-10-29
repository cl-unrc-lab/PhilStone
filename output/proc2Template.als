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
one sig Prop_try2 extends Prop{}

-- for int vars

-- for enum vars

-- definition of the propositions in the model

-- definition of the propositions in the model corresponding to volatile Bools
one sig Prop_try1 extends Prop{}
one sig Prop_turn0 extends Prop{}
one sig Prop_turn1 extends Prop{}
one sig Prop_try3 extends Prop{}

-- definition of the int in the model

-- definition of the int in the model correpsonding to volatile ints

-- definition of the int in the model

-- definition of the int in the model correpsonding to volatile ints

-- definition of the enums, one enum for each possible value

-- definition of the inc fun for every enum type

-- definition of the dec fun for every enum type

pred Prop_cs[m:proc2Meta,n:Node]{Prop_cs in m.val[n] }
pred Prop_try2[m:proc2Meta,n:Node]{Prop_try2 in m.val[n] }






pred Prop_try1[m:proc2Meta,n:Node]{Prop_try1 in m.val[n] }
pred Prop_turn0[m:proc2Meta,n:Node]{Prop_turn0 in m.val[n] }
pred Prop_turn1[m:proc2Meta,n:Node]{Prop_turn1 in m.val[n] }
pred Prop_try3[m:proc2Meta,n:Node]{Prop_try3 in m.val[n] }



-- additional vars for shared non-rpimitive vars representing the locks associated to each of them




-- similarly for the shared non-primitive  ints




-- and for the shared non-primitive enums




-- and variables for those locks that are not linked to any variables





one sig proc2Meta{
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
    ACTchange_turn0:nodes -> nodes,
    ACTchange_turn1:nodes -> nodes,
    ACTchange_try3:nodes -> nodes,

}
{
        succs = ACTsetTryTurn+ACTenterCS+ACTleaveCS 
         + ACTchange_try1+ACTchange_turn0+ACTchange_turn1+ACTchange_try3 
        local = ACTsetTryTurn+ACTenterCS+ACTleaveCS
        env = ACTchange_try1+ACTchange_turn0+ACTchange_turn1+ACTchange_try3
	/* 
        no (local & env)
    */
}

-- actions axioms
    fact Action_setTryTurn_Ax1{ all s:proc2Meta.nodes | all s':proc2Meta.ACTsetTryTurn[s] | (( (not Prop_cs[proc2Meta,s]) and (not Prop_try2[proc2Meta,s]))) implies ((Prop_turn1[proc2Meta,s'] and (Prop_try2[proc2Meta,s']) and (not Prop_turn0[proc2Meta,s']))) } 
    fact Action_enterCS_Ax1{ all s:proc2Meta.nodes | all s':proc2Meta.ACTenterCS[s] | ((Prop_try2[proc2Meta,s] and (not Prop_cs[proc2Meta,s]))) implies ((Prop_cs[proc2Meta,s'])) } 
    fact Action_leaveCS_Ax1{ all s:proc2Meta.nodes | all s':proc2Meta.ACTleaveCS[s] | ((Prop_cs[proc2Meta,s])) implies (( (not Prop_cs[proc2Meta,s']) and (not Prop_try2[proc2Meta,s']))) }  

    fact Action_setTryTurn_Ax2{ all s:proc2Meta.nodes | (not (( (not Prop_cs[proc2Meta,s]) and (not Prop_try2[proc2Meta,s])))) implies (no proc2Meta.ACTsetTryTurn[s])} 
    fact Action_enterCS_Ax2{ all s:proc2Meta.nodes | (not ((Prop_try2[proc2Meta,s] and (not Prop_cs[proc2Meta,s])))) implies (no proc2Meta.ACTenterCS[s])} 
    fact Action_leaveCS_Ax2{ all s:proc2Meta.nodes | (not ((Prop_cs[proc2Meta,s]))) implies (no proc2Meta.ACTleaveCS[s])}  

    fact Action_setTryTurn_Ax3{ all s:proc2Meta.nodes | (( (not Prop_cs[proc2Meta,s]) and (not Prop_try2[proc2Meta,s]))) implies (some proc2Meta.ACTsetTryTurn[s])  } 
    fact Action_enterCS_Ax3{ all s:proc2Meta.nodes | ((Prop_try2[proc2Meta,s] and (not Prop_cs[proc2Meta,s]))) implies (some proc2Meta.ACTenterCS[s])  } 
    fact Action_leaveCS_Ax3{ all s:proc2Meta.nodes | ((Prop_cs[proc2Meta,s])) implies (some proc2Meta.ACTleaveCS[s])  }  


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
    fact ResAx5 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.env)[s]) | Prop_try1[proc2Meta,s']) }fact ResAx5 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.env)[s]) | Prop_turn0[proc2Meta,s']) }fact ResAx5 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.env)[s]) | Prop_turn1[proc2Meta,s']) }fact ResAx5 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.env)[s]) | Prop_try3[proc2Meta,s']) }  
    fact ResAx6 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.env)[s]) | not Prop_try1[proc2Meta,s']) }fact ResAx6 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.env)[s]) | not Prop_turn0[proc2Meta,s']) }fact ResAx6 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.env)[s]) | not Prop_turn1[proc2Meta,s']) }fact ResAx6 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.env)[s]) | not Prop_try3[proc2Meta,s']) } 
*/


/*
-- similarly for volatile booleans
    fact ResAx5 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.ACTchange_try1)[s]) | Prop_try1[proc2Meta,s']) }fact ResAx5 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.ACTchange_turn0)[s]) | Prop_turn0[proc2Meta,s']) }fact ResAx5 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.ACTchange_turn1)[s]) | Prop_turn1[proc2Meta,s']) }fact ResAx5 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.ACTchange_try3)[s]) | Prop_try3[proc2Meta,s']) }  
    fact ResAx6 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.ACTchange_try1)[s]) | not Prop_try1[proc2Meta,s']) }fact ResAx6 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.ACTchange_turn0)[s]) | not Prop_turn0[proc2Meta,s']) }fact ResAx6 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.ACTchange_turn1)[s]) | not Prop_turn1[proc2Meta,s']) }fact ResAx6 { all s:proc2Meta.nodes | (some s':(*(proc2Meta.ACTchange_try3)[s]) | not Prop_try3[proc2Meta,s']) } 

*/

    fact ResAx5 { all s:proc2Meta.nodes | (some s':proc2Meta.ACTchange_try1[s] | Prop_try1[proc2Meta,s']) }fact ResAx5 { all s:proc2Meta.nodes | (some s':proc2Meta.ACTchange_turn0[s] | Prop_turn0[proc2Meta,s']) }fact ResAx5 { all s:proc2Meta.nodes | (some s':proc2Meta.ACTchange_turn1[s] | Prop_turn1[proc2Meta,s']) }fact ResAx5 { all s:proc2Meta.nodes | (some s':proc2Meta.ACTchange_try3[s] | Prop_try3[proc2Meta,s']) }  
    fact ResAx6 { all s:proc2Meta.nodes | (some s':proc2Meta.ACTchange_try1[s] | not Prop_try1[proc2Meta,s']) }fact ResAx6 { all s:proc2Meta.nodes | (some s':proc2Meta.ACTchange_turn0[s] | not Prop_turn0[proc2Meta,s']) }fact ResAx6 { all s:proc2Meta.nodes | (some s':proc2Meta.ACTchange_turn1[s] | not Prop_turn1[proc2Meta,s']) }fact ResAx6 { all s:proc2Meta.nodes | (some s':proc2Meta.ACTchange_try3[s] | not Prop_try3[proc2Meta,s']) } 

-- resource axioms for ints
-- and axioms stating that environment actions are not restricted for ints
-- and similar for volatile ints

-- Resourse axioms for enums
-- and similar for volatile enums

-- frame axioms for local  variables
 
    fact FrameAxiomssetTryTurn{ 
                all s:proc2Meta.nodes | all s':proc2Meta.ACTsetTryTurn[s] | (Prop_cs[proc2Meta,s] iff Prop_cs[proc2Meta, s']) and (Prop_try1[proc2Meta,s] iff Prop_try1[proc2Meta, s']) and (Prop_try3[proc2Meta,s] iff Prop_try3[proc2Meta, s'])
            }

    fact FrameAxiomsenterCS{ 
                all s:proc2Meta.nodes | all s':proc2Meta.ACTenterCS[s] | (Prop_try1[proc2Meta,s] iff Prop_try1[proc2Meta, s']) and (Prop_try2[proc2Meta,s] iff Prop_try2[proc2Meta, s']) and (Prop_turn0[proc2Meta,s] iff Prop_turn0[proc2Meta, s']) and (Prop_turn1[proc2Meta,s] iff Prop_turn1[proc2Meta, s']) and (Prop_try3[proc2Meta,s] iff Prop_try3[proc2Meta, s'])
            }

    fact FrameAxiomsleaveCS{ 
                all s:proc2Meta.nodes | all s':proc2Meta.ACTleaveCS[s] | (Prop_try1[proc2Meta,s] iff Prop_try1[proc2Meta, s']) and (Prop_turn0[proc2Meta,s] iff Prop_turn0[proc2Meta, s']) and (Prop_turn1[proc2Meta,s] iff Prop_turn1[proc2Meta, s']) and (Prop_try3[proc2Meta,s] iff Prop_try3[proc2Meta, s'])
            }



-- frame axioms for locks (shared vars)
-- for volatile vars we just say that local and non-volatile vars are not changed by the environmental methods that change volatile vars
fact FrameAxiomstry1{ 
    all s:proc2Meta.nodes | all s':proc2Meta.ACTchange_try1[s] | true
        and
         (Prop_cs[proc2Meta,s] iff Prop_cs[proc2Meta, s']) and  (Prop_try2[proc2Meta,s] iff Prop_try2[proc2Meta, s'])
        and 
        (Prop_turn0[proc2Meta,s] iff Prop_turn0[proc2Meta, s']) and (Prop_turn1[proc2Meta,s] iff Prop_turn1[proc2Meta, s']) and (Prop_try3[proc2Meta,s] iff Prop_try3[proc2Meta, s'])
}
fact FrameAxiomsturn0{ 
    all s:proc2Meta.nodes | all s':proc2Meta.ACTchange_turn0[s] | true
        and
         (Prop_cs[proc2Meta,s] iff Prop_cs[proc2Meta, s']) and  (Prop_try2[proc2Meta,s] iff Prop_try2[proc2Meta, s'])
        and 
        (Prop_try1[proc2Meta,s] iff Prop_try1[proc2Meta, s']) and (Prop_turn1[proc2Meta,s] iff Prop_turn1[proc2Meta, s']) and (Prop_try3[proc2Meta,s] iff Prop_try3[proc2Meta, s'])
}
fact FrameAxiomsturn1{ 
    all s:proc2Meta.nodes | all s':proc2Meta.ACTchange_turn1[s] | true
        and
         (Prop_cs[proc2Meta,s] iff Prop_cs[proc2Meta, s']) and  (Prop_try2[proc2Meta,s] iff Prop_try2[proc2Meta, s'])
        and 
        (Prop_try1[proc2Meta,s] iff Prop_try1[proc2Meta, s']) and (Prop_turn0[proc2Meta,s] iff Prop_turn0[proc2Meta, s']) and (Prop_try3[proc2Meta,s] iff Prop_try3[proc2Meta, s'])
}
fact FrameAxiomstry3{ 
    all s:proc2Meta.nodes | all s':proc2Meta.ACTchange_try3[s] | true
        and
         (Prop_cs[proc2Meta,s] iff Prop_cs[proc2Meta, s']) and  (Prop_try2[proc2Meta,s] iff Prop_try2[proc2Meta, s'])
        and 
        (Prop_try1[proc2Meta,s] iff Prop_try1[proc2Meta, s']) and (Prop_turn0[proc2Meta,s] iff Prop_turn0[proc2Meta, s']) and (Prop_turn1[proc2Meta,s] iff Prop_turn1[proc2Meta, s'])
}




pred Form12[i:proc2Meta, s:Node]{
 some s':(*(proc2Meta.succs)[s]) | Prop_cs[proc2Meta,s']}

-- Pred with inital condition and Invariants
pred Mod[s:proc2Meta.nodes]{ 
    -- all s':(*(proc2Meta.succs)[s]) | some proc2Meta.succs[s'] -- if ew want any node has a succ
     Form12[proc2Meta,s]  
    (((((not (Prop_cs[proc2Meta,s])) and (not (Prop_turn0[proc2Meta,s]))) and (not (Prop_turn1[proc2Meta,s]))) and (not (Prop_try3[proc2Meta,s]))) and (not (Prop_try2[proc2Meta,s]))) and (not (Prop_try1[proc2Meta,s]))

}

run Mod for 15
