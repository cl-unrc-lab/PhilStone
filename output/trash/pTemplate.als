open util/relation

abstract sig Node{}
abstract sig Prop{}
abstract sig NumVar{}

one sig Prop_cs extends Prop{}
one sig Prop_try extends Prop{}
one sig Prop_ncs extends Prop{}


one sig Prop_m extends Prop{}


pred Prop_cs[m:pMeta,n:Node]{Prop_cs in m.val[n] }
pred Prop_try[m:pMeta,n:Node]{Prop_try in m.val[n] }
pred Prop_ncs[m:pMeta,n:Node]{Prop_ncs in m.val[n] }


pred Prop_m[m:pMeta,n:Node]{Prop_m in m.val[n] }


one sig Av_m extends Prop{}

one sig Own_m extends Prop{}

pred Av_m[m:pMeta, n:Node]{Av_m in m.val[n]}

pred Own_m[m:pMeta, n:Node]{Own_m in m.val[n]}






one sig pMeta{
	nodes:set Node,
	val: nodes -> Prop,
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
	   no (local & env)
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
    fact ResAx1 { all s:pMeta.nodes | Own_m[pMeta, s] implies (not Av_m[pMeta, s]) } 
    fact ResAx2 { all s:pMeta.nodes | (not Own_m[pMeta,s]) iff (some pMeta.ACTchange_m[s]) }  
    fact ResAx3 { all s:pMeta.nodes | all s':pMeta.ACTchange_m[s] | Av_m[pMeta,s] iff (not Av_m[pMeta, s']) }  

-- these axioms state that local actions cannot change shared variables which locks ore not owned by the process
    fact ResAx4 {  all s:pMeta.nodes | (not Own_m[pMeta,s]) implies (all s':pMeta.local[s] | (Prop_m[pMeta,s] iff Prop_m[pMeta,s']) ) } 

    fact ResAx4 { all s:pMeta.nodes | all s':(pMeta.env[s] - pMeta.ACTchange_m[s]) | Av_m[pMeta,s] iff Av_m[pMeta, s'] } 

-- the following axioms state that environment actions are unrestricted
    fact ResAx5 { all s:pMeta.nodes | ((not Own_m[pMeta,s]) and (not Av_m[pMeta,s])) implies (some s':pMeta.ACTchange_m[s] | Prop_m[pMeta,s']) }  
    fact ResAx6 { all s:pMeta.nodes | ((not Own_m[pMeta,s]) and (not Av_m[pMeta,s])) implies (some s':pMeta.ACTchange_m[s] | not Prop_m[pMeta,s']) } 

-- resource axioms for ints
-- and axioms stating that environment actions are not restricted for ints
-- frame axioms for local boolean variables
 
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

pred Form8[i:pMeta, s:Node]{
 all s':(*(pMeta.succs)[s]) | ((not ((Prop_ncs[pMeta,s']) and (Prop_try[pMeta,s']))) and (not ((Prop_try[pMeta,s']) and (Prop_cs[pMeta,s'])))) and (not ((Prop_ncs[pMeta,s']) and (Prop_cs[pMeta,s']))) }

-- Pred with inital condition and Invariants
pred Mod[s:pMeta.nodes]{ 
    all s':(*(pMeta.succs)[s]) | some pMeta.succs[s']
     Form8[pMeta,s]  
    (((Prop_ncs[pMeta,s]) and (not (Prop_cs[pMeta,s]))) and (not (Prop_try[pMeta,s]))) and (Av_m[pMeta,s])

}

run Mod for 11
