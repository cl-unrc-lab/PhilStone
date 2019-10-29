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

-- for int vars

-- for enum vars
one sig EnumVar_st extends EnumVar{}

-- definition of the propositions in the model

-- definition of the propositions in the model corresponding to volatile Bools

-- definition of the int in the model

-- definition of the int in the model correpsonding to volatile ints

-- definition of the int in the model

-- definition of the int in the model correpsonding to volatile ints

-- definition of the enums, one enum for each possible value
one sig Arflow extends Enum{}
one sig Touchdown extends Enum{}

-- definition of the inc fun for every enum type
--fun Inc:Enum->Enum { } 
--fun Inc:Enum->Enum { } 

-- definition of the dec fun for every enum type
-- fun Dec:Enum->Enum { } 
-- fun Dec:Enum->Enum { } 



fun Val_st[m:arrivingPlaneMeta,n:Node]:Enum {m.enums[n][EnumVar_st] }







-- additional vars for shared non-rpimitive vars representing the locks associated to each of them




-- similarly for the shared non-primitive  ints




-- and for the shared non-primitive enums




-- and variables for those locks that are not linked to any variables
one sig Av_lane extends Prop{}

one sig Own_lane extends Prop{}

pred Av_lane[m:arrivingPlaneMeta, n:Node]{Av_lane in m.val[n]}

pred Own_lane[m:arrivingPlaneMeta, n:Node]{Own_lane in m.val[n]}


one sig arrivingPlaneMeta{
	nodes:set Node,
	val: nodes -> Prop,
,
    enums : (nodes-> EnumVar) -> one Enum ,
	succs : nodes -> nodes,
	local: nodes -> nodes,
	env: nodes -> nodes,
	ACTtryLand:nodes -> nodes,
    ACTchange_lane:nodes -> nodes,

}
{
        succs = ACTtryLand 
         + ACTchange_lane 
        local = ACTtryLand
        env = ACTchange_lane
	/* 
        no (local & env)
    */
}

-- actions axioms
    fact Action_tryLand_Ax1{ all s:arrivingPlaneMeta.nodes | all s':arrivingPlaneMeta.ACTtryLand[s] | (((Val_st[arrivingPlaneMeta,s] = Arflow) and (Av_lane[arrivingPlaneMeta,s]))) implies (((Val_st[arrivingPlaneMeta,s'] = Touchdown) and (Own_lane[arrivingPlaneMeta,s']))) }  

    fact Action_tryLand_Ax2{ all s:arrivingPlaneMeta.nodes | (not (((Val_st[arrivingPlaneMeta,s] = Arflow) and (Av_lane[arrivingPlaneMeta,s])))) implies (no arrivingPlaneMeta.ACTtryLand[s])}  

    fact Action_tryLand_Ax3{ all s:arrivingPlaneMeta.nodes | (((Val_st[arrivingPlaneMeta,s] = Arflow) and (Av_lane[arrivingPlaneMeta,s]))) implies (some arrivingPlaneMeta.ACTtryLand[s])  }  


-- resource axioms for booleans
-- similar axioms for those variables that are only locks, no data associated to them
    fact ResAx1 { all s:arrivingPlaneMeta.nodes | Own_lane[arrivingPlaneMeta, s] implies (not Av_lane[arrivingPlaneMeta, s]) } 
    fact ResAx2 { all s:arrivingPlaneMeta.nodes | (not Own_lane[arrivingPlaneMeta,s]) iff (some arrivingPlaneMeta.ACTchange_lane[s]) }  
    fact ResAx3 { all s:arrivingPlaneMeta.nodes | all s':arrivingPlaneMeta.ACTchange_lane[s] | Av_lane[arrivingPlaneMeta,s] iff (not Av_lane[arrivingPlaneMeta, s']) }  

-- these axioms state that local actions cannot change shared variables which locks are not owned by the process
    fact ResAx4 { all s:arrivingPlaneMeta.nodes | all s':(arrivingPlaneMeta.env[s] - arrivingPlaneMeta.ACTchange_lane[s]) | Av_lane[arrivingPlaneMeta,s] iff Av_lane[arrivingPlaneMeta, s'] } 


-- the following axioms state that environment actions are unrestricted
/*
*/

/*
-- new version of these axioms, using the * instead of next, it should be more efficient...
*/

/*
-- similarly for volatile booleans
*/


/*
-- similarly for volatile booleans
*/

-- resource axioms for ints
-- and axioms stating that environment actions are not restricted for ints
-- and similar for volatile ints

-- Resourse axioms for enums
-- and similar for volatile enums

-- frame axioms for local  variables
 
    fact FrameAxiomstryLand{ 
            }



-- frame axioms for locks (shared vars)
fact FrameAxiomslane{ 
    all s:arrivingPlaneMeta.nodes | all s':arrivingPlaneMeta.ACTchange_lane[s] | (Own_lane[arrivingPlaneMeta,s] iff Own_lane[arrivingPlaneMeta, s'])
      
             and 
              (Val_st[arrivingPlaneMeta,s] = Val_st[arrivingPlaneMeta, s'])
    }

-- for volatile vars we just say that local and non-volatile vars are not changed by the environmental methods that change volatile vars


pred Form2[i:arrivingPlaneMeta, s:Node]{
 all s':(*(arrivingPlaneMeta.succs)[s]) | (not (Own_lane[arrivingPlaneMeta,s'])) or (Own_lane[arrivingPlaneMeta,s']) }

-- Pred with inital condition and Invariants
pred Mod[s:arrivingPlaneMeta.nodes]{ 
    -- all s':(*(arrivingPlaneMeta.succs)[s]) | some arrivingPlaneMeta.succs[s'] -- if ew want any node has a succ
     Form2[arrivingPlaneMeta,s]  
    ((Val_st[arrivingPlaneMeta,s] = Arflow)) and (Av_lane[arrivingPlaneMeta,s])

}

run Mod for 20
