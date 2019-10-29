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
one sig Touchdown extends Enum{}
one sig Parked extends Enum{}
one sig Tax16lc3 extends Enum{}

-- definition of the inc fun for every enum type
--fun Inc:Enum->Enum { } 
--fun Inc:Enum->Enum { } 
--fun Inc:Enum->Enum { } 

-- definition of the dec fun for every enum type
-- fun Dec:Enum->Enum { } 
-- fun Dec:Enum->Enum { } 
-- fun Dec:Enum->Enum { } 



fun Val_st[m:parkingAirplaneMeta,n:Node]:Enum {m.enums[n][EnumVar_st] }







-- additional vars for shared non-rpimitive vars representing the locks associated to each of them




-- similarly for the shared non-primitive  ints




-- and for the shared non-primitive enums




-- and variables for those locks that are not linked to any variables
one sig Av_llane extends Prop{}
one sig Av_tlane extends Prop{}
one sig Av_freeLane extends Prop{}

one sig Own_llane extends Prop{}
one sig Own_tlane extends Prop{}
one sig Own_freeLane extends Prop{}

pred Av_llane[m:parkingAirplaneMeta, n:Node]{Av_llane in m.val[n]}
pred Av_tlane[m:parkingAirplaneMeta, n:Node]{Av_tlane in m.val[n]}
pred Av_freeLane[m:parkingAirplaneMeta, n:Node]{Av_freeLane in m.val[n]}

pred Own_llane[m:parkingAirplaneMeta, n:Node]{Own_llane in m.val[n]}
pred Own_tlane[m:parkingAirplaneMeta, n:Node]{Own_tlane in m.val[n]}
pred Own_freeLane[m:parkingAirplaneMeta, n:Node]{Own_freeLane in m.val[n]}


one sig parkingAirplaneMeta{
	nodes:set Node,
	val: nodes -> Prop,
,
    enums : (nodes-> EnumVar) -> one Enum ,
	succs : nodes -> nodes,
	local: nodes -> nodes,
	env: nodes -> nodes,
	ACTgetL1:nodes -> nodes,
	ACTwait:nodes -> nodes,
	ACTexitRW3:nodes -> nodes,
	ACTcrossRW3:nodes -> nodes,
    ACTchange_llane:nodes -> nodes,
    ACTchange_tlane:nodes -> nodes,
    ACTchange_freeLane:nodes -> nodes,

}
{
        succs = ACTgetL1+ACTwait+ACTexitRW3+ACTcrossRW3 
         + ACTchange_llane+ACTchange_tlane+ACTchange_freeLane 
        local = ACTgetL1+ACTwait+ACTexitRW3+ACTcrossRW3
        env = ACTchange_llane+ACTchange_tlane+ACTchange_freeLane
	/* 
        no (local & env)
    */
}

-- actions axioms
    fact Action_getL1_Ax1{ all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTgetL1[s] | (((Val_st[parkingAirplaneMeta,s] = Touchdown) and (Own_llane[parkingAirplaneMeta,s]) and (Av_freeLane[parkingAirplaneMeta,s]))) implies ((Own_freeLane[parkingAirplaneMeta,s'])) } 
    fact Action_wait_Ax1{ all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTwait[s] | (((Val_st[parkingAirplaneMeta,s] = Touchdown))) implies (((Val_st[parkingAirplaneMeta,s'] = Touchdown))) } 
    fact Action_exitRW3_Ax1{ all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTexitRW3[s] | ((Own_llane[parkingAirplaneMeta,s] and (Own_freeLane[parkingAirplaneMeta,s]))) implies (((Val_st[parkingAirplaneMeta,s'] = Tax16lc3) and (Av_llane[parkingAirplaneMeta,s']))) } 
    fact Action_crossRW3_Ax1{ all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTcrossRW3[s] | (((Val_st[parkingAirplaneMeta,s] = Tax16lc3) and (Av_tlane[parkingAirplaneMeta,s]) and (Own_freeLane[parkingAirplaneMeta,s]))) implies (((Val_st[parkingAirplaneMeta,s'] = Parked) and (Av_freeLane[parkingAirplaneMeta,s']))) }  

    fact Action_getL1_Ax2{ all s:parkingAirplaneMeta.nodes | (not (((Val_st[parkingAirplaneMeta,s] = Touchdown) and (Own_llane[parkingAirplaneMeta,s]) and (Av_freeLane[parkingAirplaneMeta,s])))) implies (no parkingAirplaneMeta.ACTgetL1[s])} 
    fact Action_wait_Ax2{ all s:parkingAirplaneMeta.nodes | (not (((Val_st[parkingAirplaneMeta,s] = Touchdown)))) implies (no parkingAirplaneMeta.ACTwait[s])} 
    fact Action_exitRW3_Ax2{ all s:parkingAirplaneMeta.nodes | (not ((Own_llane[parkingAirplaneMeta,s] and (Own_freeLane[parkingAirplaneMeta,s])))) implies (no parkingAirplaneMeta.ACTexitRW3[s])} 
    fact Action_crossRW3_Ax2{ all s:parkingAirplaneMeta.nodes | (not (((Val_st[parkingAirplaneMeta,s] = Tax16lc3) and (Av_tlane[parkingAirplaneMeta,s]) and (Own_freeLane[parkingAirplaneMeta,s])))) implies (no parkingAirplaneMeta.ACTcrossRW3[s])}  

    fact Action_getL1_Ax3{ all s:parkingAirplaneMeta.nodes | (((Val_st[parkingAirplaneMeta,s] = Touchdown) and (Own_llane[parkingAirplaneMeta,s]) and (Av_freeLane[parkingAirplaneMeta,s]))) implies (some parkingAirplaneMeta.ACTgetL1[s])  } 
    fact Action_wait_Ax3{ all s:parkingAirplaneMeta.nodes | (((Val_st[parkingAirplaneMeta,s] = Touchdown))) implies (some parkingAirplaneMeta.ACTwait[s])  } 
    fact Action_exitRW3_Ax3{ all s:parkingAirplaneMeta.nodes | ((Own_llane[parkingAirplaneMeta,s] and (Own_freeLane[parkingAirplaneMeta,s]))) implies (some parkingAirplaneMeta.ACTexitRW3[s])  } 
    fact Action_crossRW3_Ax3{ all s:parkingAirplaneMeta.nodes | (((Val_st[parkingAirplaneMeta,s] = Tax16lc3) and (Av_tlane[parkingAirplaneMeta,s]) and (Own_freeLane[parkingAirplaneMeta,s]))) implies (some parkingAirplaneMeta.ACTcrossRW3[s])  }  


-- resource axioms for booleans
-- similar axioms for those variables that are only locks, no data associated to them
    fact ResAx1 { all s:parkingAirplaneMeta.nodes | Own_llane[parkingAirplaneMeta, s] implies (not Av_llane[parkingAirplaneMeta, s]) } fact ResAx1 { all s:parkingAirplaneMeta.nodes | Own_tlane[parkingAirplaneMeta, s] implies (not Av_tlane[parkingAirplaneMeta, s]) } fact ResAx1 { all s:parkingAirplaneMeta.nodes | Own_freeLane[parkingAirplaneMeta, s] implies (not Av_freeLane[parkingAirplaneMeta, s]) } 
    fact ResAx2 { all s:parkingAirplaneMeta.nodes | (not Own_llane[parkingAirplaneMeta,s]) iff (some parkingAirplaneMeta.ACTchange_llane[s]) }  fact ResAx2 { all s:parkingAirplaneMeta.nodes | (not Own_tlane[parkingAirplaneMeta,s]) iff (some parkingAirplaneMeta.ACTchange_tlane[s]) }  fact ResAx2 { all s:parkingAirplaneMeta.nodes | (not Own_freeLane[parkingAirplaneMeta,s]) iff (some parkingAirplaneMeta.ACTchange_freeLane[s]) }  
    fact ResAx3 { all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTchange_llane[s] | Av_llane[parkingAirplaneMeta,s] iff (not Av_llane[parkingAirplaneMeta, s']) }fact ResAx3 { all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTchange_tlane[s] | Av_tlane[parkingAirplaneMeta,s] iff (not Av_tlane[parkingAirplaneMeta, s']) }fact ResAx3 { all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTchange_freeLane[s] | Av_freeLane[parkingAirplaneMeta,s] iff (not Av_freeLane[parkingAirplaneMeta, s']) }  

-- these axioms state that local actions cannot change shared variables which locks are not owned by the process
    fact ResAx4 { all s:parkingAirplaneMeta.nodes | all s':(parkingAirplaneMeta.env[s] - parkingAirplaneMeta.ACTchange_llane[s]) | Av_llane[parkingAirplaneMeta,s] iff Av_llane[parkingAirplaneMeta, s'] }fact ResAx4 { all s:parkingAirplaneMeta.nodes | all s':(parkingAirplaneMeta.env[s] - parkingAirplaneMeta.ACTchange_tlane[s]) | Av_tlane[parkingAirplaneMeta,s] iff Av_tlane[parkingAirplaneMeta, s'] }fact ResAx4 { all s:parkingAirplaneMeta.nodes | all s':(parkingAirplaneMeta.env[s] - parkingAirplaneMeta.ACTchange_freeLane[s]) | Av_freeLane[parkingAirplaneMeta,s] iff Av_freeLane[parkingAirplaneMeta, s'] } 


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
 
    fact FrameAxiomsgetL1{ 
                all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTgetL1[s] | (Val_st[parkingAirplaneMeta,s] = Val_st[parkingAirplaneMeta, s'])
                    and 
                    all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTgetL1[s] | 
                (Av_llane[parkingAirplaneMeta,s] iff Av_llane[parkingAirplaneMeta, s']) and (Av_tlane[parkingAirplaneMeta,s] iff Av_tlane[parkingAirplaneMeta, s']) 
                and
                (Own_llane[parkingAirplaneMeta,s] iff Own_llane[parkingAirplaneMeta, s']) and (Own_tlane[parkingAirplaneMeta,s] iff Own_tlane[parkingAirplaneMeta, s'])
            }

    fact FrameAxiomswait{ 
                    all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTwait[s] | 
                (Av_llane[parkingAirplaneMeta,s] iff Av_llane[parkingAirplaneMeta, s']) and (Av_tlane[parkingAirplaneMeta,s] iff Av_tlane[parkingAirplaneMeta, s']) and (Av_freeLane[parkingAirplaneMeta,s] iff Av_freeLane[parkingAirplaneMeta, s']) 
                and
                (Own_llane[parkingAirplaneMeta,s] iff Own_llane[parkingAirplaneMeta, s']) and (Own_tlane[parkingAirplaneMeta,s] iff Own_tlane[parkingAirplaneMeta, s']) and (Own_freeLane[parkingAirplaneMeta,s] iff Own_freeLane[parkingAirplaneMeta, s'])
            }

    fact FrameAxiomsexitRW3{ 
                    all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTexitRW3[s] | 
                (Av_tlane[parkingAirplaneMeta,s] iff Av_tlane[parkingAirplaneMeta, s']) and (Av_freeLane[parkingAirplaneMeta,s] iff Av_freeLane[parkingAirplaneMeta, s']) 
                and
                (Own_tlane[parkingAirplaneMeta,s] iff Own_tlane[parkingAirplaneMeta, s']) and (Own_freeLane[parkingAirplaneMeta,s] iff Own_freeLane[parkingAirplaneMeta, s'])
            }

    fact FrameAxiomscrossRW3{ 
                    all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTcrossRW3[s] | 
                (Av_llane[parkingAirplaneMeta,s] iff Av_llane[parkingAirplaneMeta, s']) and (Av_tlane[parkingAirplaneMeta,s] iff Av_tlane[parkingAirplaneMeta, s']) 
                and
                (Own_llane[parkingAirplaneMeta,s] iff Own_llane[parkingAirplaneMeta, s']) and (Own_tlane[parkingAirplaneMeta,s] iff Own_tlane[parkingAirplaneMeta, s'])
            }



-- frame axioms for locks (shared vars)
fact FrameAxiomsllane{ 
    all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTchange_llane[s] | (Own_llane[parkingAirplaneMeta,s] iff Own_llane[parkingAirplaneMeta, s'])
      
             and 
              (Val_st[parkingAirplaneMeta,s] = Val_st[parkingAirplaneMeta, s'])
            and
        (Av_tlane[parkingAirplaneMeta,s] iff Av_tlane[parkingAirplaneMeta, s']) and (Av_freeLane[parkingAirplaneMeta,s] iff Av_freeLane[parkingAirplaneMeta, s']) 
            and
         (Own_tlane[parkingAirplaneMeta,s] iff Own_tlane[parkingAirplaneMeta, s'])and (Own_freeLane[parkingAirplaneMeta,s] iff Own_freeLane[parkingAirplaneMeta, s'])
    }
fact FrameAxiomstlane{ 
    all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTchange_tlane[s] | (Own_tlane[parkingAirplaneMeta,s] iff Own_tlane[parkingAirplaneMeta, s'])
      
             and 
              (Val_st[parkingAirplaneMeta,s] = Val_st[parkingAirplaneMeta, s'])
            and
        (Av_llane[parkingAirplaneMeta,s] iff Av_llane[parkingAirplaneMeta, s']) and (Av_freeLane[parkingAirplaneMeta,s] iff Av_freeLane[parkingAirplaneMeta, s']) 
            and
         (Own_llane[parkingAirplaneMeta,s] iff Own_llane[parkingAirplaneMeta, s'])and (Own_freeLane[parkingAirplaneMeta,s] iff Own_freeLane[parkingAirplaneMeta, s'])
    }
fact FrameAxiomsfreeLane{ 
    all s:parkingAirplaneMeta.nodes | all s':parkingAirplaneMeta.ACTchange_freeLane[s] | (Own_freeLane[parkingAirplaneMeta,s] iff Own_freeLane[parkingAirplaneMeta, s'])
      
             and 
              (Val_st[parkingAirplaneMeta,s] = Val_st[parkingAirplaneMeta, s'])
            and
        (Av_llane[parkingAirplaneMeta,s] iff Av_llane[parkingAirplaneMeta, s']) and (Av_tlane[parkingAirplaneMeta,s] iff Av_tlane[parkingAirplaneMeta, s']) 
            and
         (Own_llane[parkingAirplaneMeta,s] iff Own_llane[parkingAirplaneMeta, s'])and (Own_tlane[parkingAirplaneMeta,s] iff Own_tlane[parkingAirplaneMeta, s'])
    }

-- for volatile vars we just say that local and non-volatile vars are not changed by the environmental methods that change volatile vars


pred Form4[i:parkingAirplaneMeta, s:Node]{
 some s':(*(parkingAirplaneMeta.succs)[s]) | (Val_st[parkingAirplaneMeta,s'] = Parked)}

-- Pred with inital condition and Invariants
pred Mod[s:parkingAirplaneMeta.nodes]{ 
    -- all s':(*(parkingAirplaneMeta.succs)[s]) | some parkingAirplaneMeta.succs[s'] -- if ew want any node has a succ
     Form4[parkingAirplaneMeta,s]  
    ((((Val_st[parkingAirplaneMeta,s] = Touchdown)) and (Own_llane[parkingAirplaneMeta,s])) and (Av_tlane[parkingAirplaneMeta,s])) and (Av_freeLane[parkingAirplaneMeta,s])

}

run Mod for 20
