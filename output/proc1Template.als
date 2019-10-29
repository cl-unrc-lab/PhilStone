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
one sig Prop_s1 extends Prop{}
one sig Prop_a1 extends Prop{}

-- for int vars

-- for enum vars

-- definition of the propositions in the model

-- definition of the propositions in the model corresponding to volatile Bools
one sig Prop_s3 extends Prop{}
one sig Prop_a2 extends Prop{}
one sig Prop_a3 extends Prop{}
one sig Prop_s2 extends Prop{}

-- definition of the int in the model

-- definition of the int in the model correpsonding to volatile ints

-- definition of the int in the model

-- definition of the int in the model correpsonding to volatile ints

-- definition of the enums, one enum for each possible value

-- definition of the inc fun for every enum type

-- definition of the dec fun for every enum type

pred Prop_s1[m:proc1Meta,n:Node]{Prop_s1 in m.val[n] }
pred Prop_a1[m:proc1Meta,n:Node]{Prop_a1 in m.val[n] }






pred Prop_s3[m:proc1Meta,n:Node]{Prop_s3 in m.val[n] }
pred Prop_a2[m:proc1Meta,n:Node]{Prop_a2 in m.val[n] }
pred Prop_a3[m:proc1Meta,n:Node]{Prop_a3 in m.val[n] }
pred Prop_s2[m:proc1Meta,n:Node]{Prop_s2 in m.val[n] }



-- additional vars for shared non-rpimitive vars representing the locks associated to each of them




-- similarly for the shared non-primitive  ints




-- and for the shared non-primitive enums




-- and variables for those locks that are not linked to any variables





one sig proc1Meta{
	nodes:set Node,
	val: nodes -> Prop,
,
,
	succs : nodes -> nodes,
	local: nodes -> nodes,
	env: nodes -> nodes,
	ACTfinishA:nodes -> nodes,
	ACTstartB:nodes -> nodes,
	ACTfinishB:nodes -> nodes,
	ACTstartA:nodes -> nodes,
    ACTchange_s3:nodes -> nodes,
    ACTchange_a2:nodes -> nodes,
    ACTchange_a3:nodes -> nodes,
    ACTchange_s2:nodes -> nodes,

}
{
        succs = ACTfinishA+ACTstartB+ACTfinishB+ACTstartA 
         + ACTchange_s3+ACTchange_a2+ACTchange_a3+ACTchange_s2 
        local = ACTfinishA+ACTstartB+ACTfinishB+ACTstartA
        env = ACTchange_s3+ACTchange_a2+ACTchange_a3+ACTchange_s2
	/* 
        no (local & env)
    */
}

-- actions axioms
    fact Action_finishA_Ax1{ all s:proc1Meta.nodes | all s':proc1Meta.ACTfinishA[s] | ((Prop_s1[proc1Meta,s] and (Prop_a1[proc1Meta,s]))) implies (( (not Prop_s1[proc1Meta,s']))) } 
    fact Action_startB_Ax1{ all s:proc1Meta.nodes | all s':proc1Meta.ACTstartB[s] | ((Prop_a1[proc1Meta,s] and (not Prop_s1[proc1Meta,s]))) implies ((Prop_s1[proc1Meta,s'] and (not Prop_a1[proc1Meta,s']))) } 
    fact Action_finishB_Ax1{ all s:proc1Meta.nodes | all s':proc1Meta.ACTfinishB[s] | ((Prop_s1[proc1Meta,s] and (not Prop_a1[proc1Meta,s]))) implies (( (not Prop_s1[proc1Meta,s']))) } 
    fact Action_startA_Ax1{ all s:proc1Meta.nodes | all s':proc1Meta.ACTstartA[s] | (( (not Prop_s1[proc1Meta,s]) and (not Prop_a1[proc1Meta,s]))) implies ((Prop_s1[proc1Meta,s'] and (Prop_a1[proc1Meta,s']))) }  

    fact Action_finishA_Ax2{ all s:proc1Meta.nodes | (not ((Prop_s1[proc1Meta,s] and (Prop_a1[proc1Meta,s])))) implies (no proc1Meta.ACTfinishA[s])} 
    fact Action_startB_Ax2{ all s:proc1Meta.nodes | (not ((Prop_a1[proc1Meta,s] and (not Prop_s1[proc1Meta,s])))) implies (no proc1Meta.ACTstartB[s])} 
    fact Action_finishB_Ax2{ all s:proc1Meta.nodes | (not ((Prop_s1[proc1Meta,s] and (not Prop_a1[proc1Meta,s])))) implies (no proc1Meta.ACTfinishB[s])} 
    fact Action_startA_Ax2{ all s:proc1Meta.nodes | (not (( (not Prop_s1[proc1Meta,s]) and (not Prop_a1[proc1Meta,s])))) implies (no proc1Meta.ACTstartA[s])}  

    fact Action_finishA_Ax3{ all s:proc1Meta.nodes | ((Prop_s1[proc1Meta,s] and (Prop_a1[proc1Meta,s]))) implies (some proc1Meta.ACTfinishA[s])  } 
    fact Action_startB_Ax3{ all s:proc1Meta.nodes | ((Prop_a1[proc1Meta,s] and (not Prop_s1[proc1Meta,s]))) implies (some proc1Meta.ACTstartB[s])  } 
    fact Action_finishB_Ax3{ all s:proc1Meta.nodes | ((Prop_s1[proc1Meta,s] and (not Prop_a1[proc1Meta,s]))) implies (some proc1Meta.ACTfinishB[s])  } 
    fact Action_startA_Ax3{ all s:proc1Meta.nodes | (( (not Prop_s1[proc1Meta,s]) and (not Prop_a1[proc1Meta,s]))) implies (some proc1Meta.ACTstartA[s])  }  


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
    fact ResAx5 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.env)[s]) | Prop_s3[proc1Meta,s']) }fact ResAx5 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.env)[s]) | Prop_a2[proc1Meta,s']) }fact ResAx5 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.env)[s]) | Prop_a3[proc1Meta,s']) }fact ResAx5 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.env)[s]) | Prop_s2[proc1Meta,s']) }  
    fact ResAx6 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.env)[s]) | not Prop_s3[proc1Meta,s']) }fact ResAx6 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.env)[s]) | not Prop_a2[proc1Meta,s']) }fact ResAx6 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.env)[s]) | not Prop_a3[proc1Meta,s']) }fact ResAx6 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.env)[s]) | not Prop_s2[proc1Meta,s']) } 
*/


/*
-- similarly for volatile booleans
    fact ResAx5 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.ACTchange_s3)[s]) | Prop_s3[proc1Meta,s']) }fact ResAx5 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.ACTchange_a2)[s]) | Prop_a2[proc1Meta,s']) }fact ResAx5 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.ACTchange_a3)[s]) | Prop_a3[proc1Meta,s']) }fact ResAx5 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.ACTchange_s2)[s]) | Prop_s2[proc1Meta,s']) }  
    fact ResAx6 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.ACTchange_s3)[s]) | not Prop_s3[proc1Meta,s']) }fact ResAx6 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.ACTchange_a2)[s]) | not Prop_a2[proc1Meta,s']) }fact ResAx6 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.ACTchange_a3)[s]) | not Prop_a3[proc1Meta,s']) }fact ResAx6 { all s:proc1Meta.nodes | (some s':(*(proc1Meta.ACTchange_s2)[s]) | not Prop_s2[proc1Meta,s']) } 

*/

    fact ResAx5 { all s:proc1Meta.nodes | (some s':proc1Meta.ACTchange_s3[s] | Prop_s3[proc1Meta,s']) }fact ResAx5 { all s:proc1Meta.nodes | (some s':proc1Meta.ACTchange_a2[s] | Prop_a2[proc1Meta,s']) }fact ResAx5 { all s:proc1Meta.nodes | (some s':proc1Meta.ACTchange_a3[s] | Prop_a3[proc1Meta,s']) }fact ResAx5 { all s:proc1Meta.nodes | (some s':proc1Meta.ACTchange_s2[s] | Prop_s2[proc1Meta,s']) }  
    fact ResAx6 { all s:proc1Meta.nodes | (some s':proc1Meta.ACTchange_s3[s] | not Prop_s3[proc1Meta,s']) }fact ResAx6 { all s:proc1Meta.nodes | (some s':proc1Meta.ACTchange_a2[s] | not Prop_a2[proc1Meta,s']) }fact ResAx6 { all s:proc1Meta.nodes | (some s':proc1Meta.ACTchange_a3[s] | not Prop_a3[proc1Meta,s']) }fact ResAx6 { all s:proc1Meta.nodes | (some s':proc1Meta.ACTchange_s2[s] | not Prop_s2[proc1Meta,s']) } 

-- resource axioms for ints
-- and axioms stating that environment actions are not restricted for ints
-- and similar for volatile ints

-- Resourse axioms for enums
-- and similar for volatile enums

-- frame axioms for local  variables
 
    fact FrameAxiomsfinishA{ 
                all s:proc1Meta.nodes | all s':proc1Meta.ACTfinishA[s] | (Prop_a1[proc1Meta,s] iff Prop_a1[proc1Meta, s']) and (Prop_s3[proc1Meta,s] iff Prop_s3[proc1Meta, s']) and (Prop_a2[proc1Meta,s] iff Prop_a2[proc1Meta, s']) and (Prop_a3[proc1Meta,s] iff Prop_a3[proc1Meta, s']) and (Prop_s2[proc1Meta,s] iff Prop_s2[proc1Meta, s'])
            }

    fact FrameAxiomsstartB{ 
                all s:proc1Meta.nodes | all s':proc1Meta.ACTstartB[s] | (Prop_s3[proc1Meta,s] iff Prop_s3[proc1Meta, s']) and (Prop_a2[proc1Meta,s] iff Prop_a2[proc1Meta, s']) and (Prop_a3[proc1Meta,s] iff Prop_a3[proc1Meta, s']) and (Prop_s2[proc1Meta,s] iff Prop_s2[proc1Meta, s'])
            }

    fact FrameAxiomsfinishB{ 
                all s:proc1Meta.nodes | all s':proc1Meta.ACTfinishB[s] | (Prop_a1[proc1Meta,s] iff Prop_a1[proc1Meta, s']) and (Prop_s3[proc1Meta,s] iff Prop_s3[proc1Meta, s']) and (Prop_a2[proc1Meta,s] iff Prop_a2[proc1Meta, s']) and (Prop_a3[proc1Meta,s] iff Prop_a3[proc1Meta, s']) and (Prop_s2[proc1Meta,s] iff Prop_s2[proc1Meta, s'])
            }

    fact FrameAxiomsstartA{ 
                all s:proc1Meta.nodes | all s':proc1Meta.ACTstartA[s] | (Prop_s3[proc1Meta,s] iff Prop_s3[proc1Meta, s']) and (Prop_a2[proc1Meta,s] iff Prop_a2[proc1Meta, s']) and (Prop_a3[proc1Meta,s] iff Prop_a3[proc1Meta, s']) and (Prop_s2[proc1Meta,s] iff Prop_s2[proc1Meta, s'])
            }



-- frame axioms for locks (shared vars)
-- for volatile vars we just say that local and non-volatile vars are not changed by the environmental methods that change volatile vars
fact FrameAxiomss3{ 
    all s:proc1Meta.nodes | all s':proc1Meta.ACTchange_s3[s] | true
        and
         (Prop_s1[proc1Meta,s] iff Prop_s1[proc1Meta, s']) and  (Prop_a1[proc1Meta,s] iff Prop_a1[proc1Meta, s'])
        and 
        (Prop_a2[proc1Meta,s] iff Prop_a2[proc1Meta, s']) and (Prop_a3[proc1Meta,s] iff Prop_a3[proc1Meta, s']) and (Prop_s2[proc1Meta,s] iff Prop_s2[proc1Meta, s'])
}
fact FrameAxiomsa2{ 
    all s:proc1Meta.nodes | all s':proc1Meta.ACTchange_a2[s] | true
        and
         (Prop_s1[proc1Meta,s] iff Prop_s1[proc1Meta, s']) and  (Prop_a1[proc1Meta,s] iff Prop_a1[proc1Meta, s'])
        and 
        (Prop_s3[proc1Meta,s] iff Prop_s3[proc1Meta, s']) and (Prop_a3[proc1Meta,s] iff Prop_a3[proc1Meta, s']) and (Prop_s2[proc1Meta,s] iff Prop_s2[proc1Meta, s'])
}
fact FrameAxiomsa3{ 
    all s:proc1Meta.nodes | all s':proc1Meta.ACTchange_a3[s] | true
        and
         (Prop_s1[proc1Meta,s] iff Prop_s1[proc1Meta, s']) and  (Prop_a1[proc1Meta,s] iff Prop_a1[proc1Meta, s'])
        and 
        (Prop_s3[proc1Meta,s] iff Prop_s3[proc1Meta, s']) and (Prop_a2[proc1Meta,s] iff Prop_a2[proc1Meta, s']) and (Prop_s2[proc1Meta,s] iff Prop_s2[proc1Meta, s'])
}
fact FrameAxiomss2{ 
    all s:proc1Meta.nodes | all s':proc1Meta.ACTchange_s2[s] | true
        and
         (Prop_s1[proc1Meta,s] iff Prop_s1[proc1Meta, s']) and  (Prop_a1[proc1Meta,s] iff Prop_a1[proc1Meta, s'])
        and 
        (Prop_s3[proc1Meta,s] iff Prop_s3[proc1Meta, s']) and (Prop_a2[proc1Meta,s] iff Prop_a2[proc1Meta, s']) and (Prop_a3[proc1Meta,s] iff Prop_a3[proc1Meta, s'])
}




pred Form3[i:proc1Meta, s:Node]{
 some s':(*(proc1Meta.succs)[s]) | (not (Prop_a1[proc1Meta,s'])) and (not (Prop_s1[proc1Meta,s']))}

-- Pred with inital condition and Invariants
pred Mod[s:proc1Meta.nodes]{ 
    -- all s':(*(proc1Meta.succs)[s]) | some proc1Meta.succs[s'] -- if ew want any node has a succ
     Form3[proc1Meta,s]  
    (((((Prop_s1[proc1Meta,s]) and (Prop_a1[proc1Meta,s])) and (Prop_s2[proc1Meta,s])) and (Prop_a2[proc1Meta,s])) and (Prop_s3[proc1Meta,s])) and (Prop_a3[proc1Meta,s])

}

run Mod for 20
