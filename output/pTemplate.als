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
one sig Prop_try extends Prop{}
one sig Prop_ncs extends Prop{}

-- for int vars

-- for enum vars

-- definition of the propositions in the model

-- definition of the propositions in the model corresponding to volatile Bools

-- definition of the int in the model

-- definition of the int in the model correpsonding to volatile ints

-- definition of the int in the model

-- definition of the int in the model correpsonding to volatile ints

-- definition of the enums, one enum for each possible value

-- definition of the inc fun for every enum type

-- definition of the dec fun for every enum type

pred Prop_cs[m:pMeta,n:Node]{Prop_cs in m.val[n] }
pred Prop_try[m:pMeta,n:Node]{Prop_try in m.val[n] }
pred Prop_ncs[m:pMeta,n:Node]{Prop_ncs in m.val[n] }









-- additional vars for shared non-rpimitive vars representing the locks associated to each of them




-- similarly for the shared non-primitive  ints




-- and for the shared non-primitive enums




-- and variables for those locks that are not linked to any variables
one sig Av_m extends Prop{}

one sig Own_m extends Prop{}

pred Av_m[m:pMeta, n:Node]{Av_m in m.val[n]}

pred Own_m[m:pMeta, n:Node]{Own_m in m.val[n]}


one sig pMeta{
	nodes:set Node,
	val: nodes -> Prop,
,
,
	succs : nodes -> nodes,
	local: nodes -> nodes,
	env: nodes -> nodes,
	ACTenterTry:nodes -> nodes,
	ACTenterCS:nodes -> nodes,
	ACTenterNCS:nodes -> nodes,
	ACTgetLock:nodes -> nodes,
    ACTchange_m:nodes -> nodes,

}
{
        succs = ACTenterTry+ACTenterCS+ACTenterNCS+ACTgetLock 
         + ACTchange_m 
        local = ACTenterTry+ACTenterCS+ACTenterNCS+ACTgetLock
        env = ACTchange_m
	/* 
        no (local & env)
    */
}

-- actions axioms
    fact Action_enterTry_Ax1{ all s:pMeta.nodes | all s':pMeta.ACTenterTry[s] | ((Prop_ncs[pMeta,s]) or (Prop_try[pMeta,s] and (not Own_m[pMeta,s]))) implies ((Prop_try[pMeta,s'])) } 
    fact Action_enterCS_Ax1{ all s:pMeta.nodes | all s':pMeta.ACTenterCS[s] | ((Prop_try[pMeta,s] and (Own_m[pMeta,s]))) implies ((Prop_cs[pMeta,s'] and (Own_m[pMeta,s']))) } 
    fact Action_enterNCS_Ax1{ all s:pMeta.nodes | all s':pMeta.ACTenterNCS[s] | ((Prop_cs[pMeta,s])) implies ((Prop_ncs[pMeta,s'] and (not Own_m[pMeta,s']))) } 
    fact Action_getLock_Ax1{ all s:pMeta.nodes | all s':pMeta.ACTgetLock[s] | ((Prop_try[pMeta,s] and (Av_m[pMeta,s]))) implies ((Prop_try[pMeta,s'] and (Own_m[pMeta,s']))) }  

    fact Action_enterTry_Ax2{ all s:pMeta.nodes | (not ((Prop_ncs[pMeta,s]) or (Prop_try[pMeta,s] and (not Own_m[pMeta,s])))) implies (no pMeta.ACTenterTry[s])} 
    fact Action_enterCS_Ax2{ all s:pMeta.nodes | (not ((Prop_try[pMeta,s] and (Own_m[pMeta,s])))) implies (no pMeta.ACTenterCS[s])} 
    fact Action_enterNCS_Ax2{ all s:pMeta.nodes | (not ((Prop_cs[pMeta,s]))) implies (no pMeta.ACTenterNCS[s])} 
    fact Action_getLock_Ax2{ all s:pMeta.nodes | (not ((Prop_try[pMeta,s] and (Av_m[pMeta,s])))) implies (no pMeta.ACTgetLock[s])}  

    fact Action_enterTry_Ax3{ all s:pMeta.nodes | ((Prop_ncs[pMeta,s]) or (Prop_try[pMeta,s] and (not Own_m[pMeta,s]))) implies (some pMeta.ACTenterTry[s])  } 
    fact Action_enterCS_Ax3{ all s:pMeta.nodes | ((Prop_try[pMeta,s] and (Own_m[pMeta,s]))) implies (some pMeta.ACTenterCS[s])  } 
    fact Action_enterNCS_Ax3{ all s:pMeta.nodes | ((Prop_cs[pMeta,s])) implies (some pMeta.ACTenterNCS[s])  } 
    fact Action_getLock_Ax3{ all s:pMeta.nodes | ((Prop_try[pMeta,s] and (Av_m[pMeta,s]))) implies (some pMeta.ACTgetLock[s])  }  


-- resource axioms for booleans
-- similar axioms for those variables that are only locks, no data associated to them
    fact ResAx1 { all s:pMeta.nodes | Own_m[pMeta, s] implies (not Av_m[pMeta, s]) } 
    fact ResAx2 { all s:pMeta.nodes | (not Own_m[pMeta,s]) iff (some pMeta.ACTchange_m[s]) }  
    fact ResAx3 { all s:pMeta.nodes | all s':pMeta.ACTchange_m[s] | Av_m[pMeta,s] iff (not Av_m[pMeta, s']) }  

-- these axioms state that local actions cannot change shared variables which locks are not owned by the process
    fact ResAx4 { all s:pMeta.nodes | all s':(pMeta.env[s] - pMeta.ACTchange_m[s]) | Av_m[pMeta,s] iff Av_m[pMeta, s'] } 


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
 
    fact FrameAxiomsenterTry{ 
                all s:pMeta.nodes | all s':pMeta.ACTenterTry[s] | (Prop_cs[pMeta,s] iff Prop_cs[pMeta, s'])
                    and 
                (Av_m[pMeta,s] iff Av_m[pMeta, s']) 
                and
                (Own_m[pMeta,s] iff Own_m[pMeta, s'])
            }

    fact FrameAxiomsenterCS{ 
             
                        all s:pMeta.nodes,  s':pMeta.ACTenterCS[s] |(Prop_ncs[pMeta,s] iff Prop_ncs[pMeta, s']) 
            }

    fact FrameAxiomsenterNCS{ 
             
                        all s:pMeta.nodes,  s':pMeta.ACTenterNCS[s] |(Prop_try[pMeta,s] iff Prop_try[pMeta, s']) 
            }

    fact FrameAxiomsgetLock{ 
                all s:pMeta.nodes | all s':pMeta.ACTgetLock[s] | (Prop_cs[pMeta,s] iff Prop_cs[pMeta, s']) and (Prop_try[pMeta,s] iff Prop_try[pMeta, s']) and (Prop_ncs[pMeta,s] iff Prop_ncs[pMeta, s'])
            }



-- frame axioms for locks (shared vars)
fact FrameAxiomsm{ 
    all s:pMeta.nodes | all s':pMeta.ACTchange_m[s] | (Own_m[pMeta,s] iff Own_m[pMeta, s'])
     
            and 
             (Prop_cs[pMeta,s] iff Prop_cs[pMeta, s']) and  (Prop_try[pMeta,s] iff Prop_try[pMeta, s']) and  (Prop_ncs[pMeta,s] iff Prop_ncs[pMeta, s'])
    }

-- for volatile vars we just say that local and non-volatile vars are not changed by the environmental methods that change volatile vars


pred Form5[i:pMeta, s:Node]{
 all s':(*(pMeta.succs)[s]) | (not ((Prop_ncs[pMeta,s']) and (Prop_try[pMeta,s']))) and (not ((Prop_try[pMeta,s']) and (Prop_cs[pMeta,s']))) }

-- Pred with inital condition and Invariants
pred Mod[s:pMeta.nodes]{ 
    -- all s':(*(pMeta.succs)[s]) | some pMeta.succs[s'] -- if ew want any node has a succ
     Form5[pMeta,s]  
    (((Prop_ncs[pMeta,s]) and (not (Prop_cs[pMeta,s]))) and (not (Prop_try[pMeta,s]))) and (Av_m[pMeta,s])

}

run Mod for 16
