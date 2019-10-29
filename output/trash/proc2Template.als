open util/relation

abstract sig Node{}
abstract sig Prop{}
abstract sig NumVar{}

one sig Prop_cs extends Prop{}


one sig Prop_try2 extends Prop{}
one sig Prop_turn extends Prop{}


pred Prop_cs[m:proc2Meta,n:Node]{Prop_cs in m.val[n] }


pred Prop_try2[m:proc2Meta,n:Node]{Prop_try2 in m.val[n] }
pred Prop_turn[m:proc2Meta,n:Node]{Prop_turn in m.val[n] }


one sig Av_try2 extends Prop{}
one sig Av_turn extends Prop{}

one sig Own_try2 extends Prop{}
one sig Own_turn extends Prop{}

pred Av_try2[m:proc2Meta, n:Node]{Av_try2 in m.val[n]}
pred Av_turn[m:proc2Meta, n:Node]{Av_turn in m.val[n]}

pred Own_try2[m:proc2Meta, n:Node]{Own_try2 in m.val[n]}
pred Own_turn[m:proc2Meta, n:Node]{Own_turn in m.val[n]}






one sig proc2Meta{
	nodes:set Node,
	val: nodes -> Prop,
	succs : nodes -> nodes,
	local: nodes -> nodes,
	env: nodes -> nodes,
	ACTlocktry2:nodes -> nodes,
	ACTunlocktry2:nodes -> nodes,
	ACTlockturn:nodes -> nodes,
	ACTturnOn:nodes -> nodes,
	ACTenterCS:nodes -> nodes,
	ACTleaveCS:nodes -> nodes,
	ACTchange_try2:nodes -> nodes,
	ACTchange_turn:nodes -> nodes,
}
{
        succs = ACTlocktry2+ACTunlocktry2+ACTlockturn+ACTturnOn+ACTenterCS+ACTleaveCS 
         + ACTchange_try2+ACTchange_turn 
        local = ACTlocktry2+ACTunlocktry2+ACTlockturn+ACTturnOn+ACTenterCS+ACTleaveCS
        env = ACTchange_try2+ACTchange_turn
	   no (local & env)
}

-- actions axioms
    fact Action_locktry2_Ax1{ all s:proc2Meta.nodes | all s':proc2Meta.ACTlocktry2[s] | ((Av_try2[proc2Meta,s] and (not Prop_cs[proc2Meta,s]))) implies ((Own_try2[proc2Meta,s'])) } 
    fact Action_unlocktry2_Ax1{ all s:proc2Meta.nodes | all s':proc2Meta.ACTunlocktry2[s] | ((Prop_cs[proc2Meta,s] and (Own_try2[proc2Meta,s]))) implies (( (not Prop_cs[proc2Meta,s']) and (not Own_try2[proc2Meta,s']))) } 
    fact Action_lockturn_Ax1{ all s:proc2Meta.nodes | all s':proc2Meta.ACTlockturn[s] | ((Av_turn[proc2Meta,s] and (not Prop_cs[proc2Meta,s]))) implies ((Own_turn[proc2Meta,s'])) } 
    fact Action_turnOn_Ax1{ all s:proc2Meta.nodes | all s':proc2Meta.ACTturnOn[s] | ((Own_turn[proc2Meta,s] and (not Prop_cs[proc2Meta,s]))) implies (( (not Prop_turn[proc2Meta,s']))) } 
    fact Action_enterCS_Ax1{ all s:proc2Meta.nodes | all s':proc2Meta.ACTenterCS[s] | (( (not Prop_cs[proc2Meta,s]))) implies ((Prop_cs[proc2Meta,s'])) } 
    fact Action_leaveCS_Ax1{ all s:proc2Meta.nodes | all s':proc2Meta.ACTleaveCS[s] | ((Prop_cs[proc2Meta,s] and (Own_turn[proc2Meta,s]))) implies (( (not Prop_cs[proc2Meta,s']) and (not Prop_turn[proc2Meta,s']) and (not Own_turn[proc2Meta,s']))) }  
    fact Action_locktry2_Ax2{ all s:proc2Meta.nodes | (not ((Av_try2[proc2Meta,s] and (not Prop_cs[proc2Meta,s])))) implies (no proc2Meta.ACTlocktry2[s])} 
    fact Action_unlocktry2_Ax2{ all s:proc2Meta.nodes | (not ((Prop_cs[proc2Meta,s] and (Own_try2[proc2Meta,s])))) implies (no proc2Meta.ACTunlocktry2[s])} 
    fact Action_lockturn_Ax2{ all s:proc2Meta.nodes | (not ((Av_turn[proc2Meta,s] and (not Prop_cs[proc2Meta,s])))) implies (no proc2Meta.ACTlockturn[s])} 
    fact Action_turnOn_Ax2{ all s:proc2Meta.nodes | (not ((Own_turn[proc2Meta,s] and (not Prop_cs[proc2Meta,s])))) implies (no proc2Meta.ACTturnOn[s])} 
    fact Action_enterCS_Ax2{ all s:proc2Meta.nodes | (not (( (not Prop_cs[proc2Meta,s])))) implies (no proc2Meta.ACTenterCS[s])} 
    fact Action_leaveCS_Ax2{ all s:proc2Meta.nodes | (not ((Prop_cs[proc2Meta,s] and (Own_turn[proc2Meta,s])))) implies (no proc2Meta.ACTleaveCS[s])}  
/*
    fact Action_locktry2_Ax3{ all s:proc2Meta.nodes | ((Av_try2[proc2Meta,s] and (not Prop_cs[proc2Meta,s]))) implies (some proc2Meta.ACTlocktry2[s])  } 
    fact Action_unlocktry2_Ax3{ all s:proc2Meta.nodes | ((Prop_cs[proc2Meta,s] and (Own_try2[proc2Meta,s]))) implies (some proc2Meta.ACTunlocktry2[s])  } 
    fact Action_lockturn_Ax3{ all s:proc2Meta.nodes | ((Av_turn[proc2Meta,s] and (not Prop_cs[proc2Meta,s]))) implies (some proc2Meta.ACTlockturn[s])  } 
    fact Action_turnOn_Ax3{ all s:proc2Meta.nodes | ((Own_turn[proc2Meta,s] and (not Prop_cs[proc2Meta,s]))) implies (some proc2Meta.ACTturnOn[s])  } 
    fact Action_enterCS_Ax3{ all s:proc2Meta.nodes | (( (not Prop_cs[proc2Meta,s]))) implies (some proc2Meta.ACTenterCS[s])  } 
    fact Action_leaveCS_Ax3{ all s:proc2Meta.nodes | ((Prop_cs[proc2Meta,s] and (Own_turn[proc2Meta,s]))) implies (some proc2Meta.ACTleaveCS[s])  }  
 */


-- resource axioms for booleans
    fact ResAx1 { all s:proc2Meta.nodes | Own_try2[proc2Meta, s] implies (not Av_try2[proc2Meta, s]) } fact ResAx1 { all s:proc2Meta.nodes | Own_turn[proc2Meta, s] implies (not Av_turn[proc2Meta, s]) } 
    fact ResAx2 { all s:proc2Meta.nodes | (not Own_try2[proc2Meta,s]) iff (some proc2Meta.ACTchange_try2[s]) }  fact ResAx2 { all s:proc2Meta.nodes | (not Own_turn[proc2Meta,s]) iff (some proc2Meta.ACTchange_turn[s]) }  
    fact ResAx3 { all s:proc2Meta.nodes | all s':proc2Meta.ACTchange_try2[s] | Av_try2[proc2Meta,s] iff (not Av_try2[proc2Meta, s']) }fact ResAx3 { all s:proc2Meta.nodes | all s':proc2Meta.ACTchange_turn[s] | Av_turn[proc2Meta,s] iff (not Av_turn[proc2Meta, s']) }  

-- these axioms state that local actions cannot change shared variables which locks ore not owned by the process
    fact ResAx4 {  all s:proc2Meta.nodes | (not Own_try2[proc2Meta,s]) implies (all s':proc2Meta.local[s] | (Prop_try2[proc2Meta,s] iff Prop_try2[proc2Meta,s']) ) } fact ResAx4 {  all s:proc2Meta.nodes | (not Own_turn[proc2Meta,s]) implies (all s':proc2Meta.local[s] | (Prop_turn[proc2Meta,s] iff Prop_turn[proc2Meta,s']) ) } 

    fact ResAx4 { all s:proc2Meta.nodes | all s':(proc2Meta.env[s] - proc2Meta.ACTchange_try2[s]) | Av_try2[proc2Meta,s] iff Av_try2[proc2Meta, s'] }fact ResAx4 { all s:proc2Meta.nodes | all s':(proc2Meta.env[s] - proc2Meta.ACTchange_turn[s]) | Av_turn[proc2Meta,s] iff Av_turn[proc2Meta, s'] } 

-- the following axioms state that environment actions are unrestricted
    fact ResAx5 { all s:proc2Meta.nodes | ((not Own_try2[proc2Meta,s]) and (not Av_try2[proc2Meta,s])) implies (some s':proc2Meta.ACTchange_try2[s] | Prop_try2[proc2Meta,s']) }fact ResAx5 { all s:proc2Meta.nodes | ((not Own_turn[proc2Meta,s]) and (not Av_turn[proc2Meta,s])) implies (some s':proc2Meta.ACTchange_turn[s] | Prop_turn[proc2Meta,s']) }  
    fact ResAx6 { all s:proc2Meta.nodes | ((not Own_try2[proc2Meta,s]) and (not Av_try2[proc2Meta,s])) implies (some s':proc2Meta.ACTchange_try2[s] | not Prop_try2[proc2Meta,s']) }fact ResAx6 { all s:proc2Meta.nodes | ((not Own_turn[proc2Meta,s]) and (not Av_turn[proc2Meta,s])) implies (some s':proc2Meta.ACTchange_turn[s] | not Prop_turn[proc2Meta,s']) } 

-- resource axioms for ints
-- and axioms stating that environment actions are not restricted for ints
-- frame axioms for local boolean variables
 
    fact FrameAxiomslocktry2{ 
                all s:proc2Meta.nodes | all s':proc2Meta.ACTlocktry2[s] | (Prop_cs[proc2Meta,s] iff Prop_cs[proc2Meta, s'])
                    and 
                (Av_turn[proc2Meta,s] iff Av_turn[proc2Meta, s']) 
                and
                (Own_turn[proc2Meta,s] iff Own_turn[proc2Meta, s'])
            }

    fact FrameAxiomsunlocktry2{ 
                    all s:proc2Meta.nodes | all s':proc2Meta.ACTunlocktry2[s] | 
                (Av_turn[proc2Meta,s] iff Av_turn[proc2Meta, s']) 
                and
                (Own_turn[proc2Meta,s] iff Own_turn[proc2Meta, s'])
            }

    fact FrameAxiomslockturn{ 
                all s:proc2Meta.nodes | all s':proc2Meta.ACTlockturn[s] | (Prop_cs[proc2Meta,s] iff Prop_cs[proc2Meta, s'])
                    and 
                (Av_try2[proc2Meta,s] iff Av_try2[proc2Meta, s']) 
                and
                (Own_try2[proc2Meta,s] iff Own_try2[proc2Meta, s'])
            }

    fact FrameAxiomsturnOn{ 
                all s:proc2Meta.nodes | all s':proc2Meta.ACTturnOn[s] | (Prop_cs[proc2Meta,s] iff Prop_cs[proc2Meta, s'])
                    and 
                (Av_try2[proc2Meta,s] iff Av_try2[proc2Meta, s']) 
                and
                (Own_try2[proc2Meta,s] iff Own_try2[proc2Meta, s'])
            }

    fact FrameAxiomsenterCS{ 
                    all s:proc2Meta.nodes | all s':proc2Meta.ACTenterCS[s] | 
                (Av_try2[proc2Meta,s] iff Av_try2[proc2Meta, s']) and (Av_turn[proc2Meta,s] iff Av_turn[proc2Meta, s']) 
                and
                (Own_try2[proc2Meta,s] iff Own_try2[proc2Meta, s']) and (Own_turn[proc2Meta,s] iff Own_turn[proc2Meta, s'])
            }

    fact FrameAxiomsleaveCS{ 
                    all s:proc2Meta.nodes | all s':proc2Meta.ACTleaveCS[s] | 
                (Av_try2[proc2Meta,s] iff Av_try2[proc2Meta, s']) 
                and
                (Own_try2[proc2Meta,s] iff Own_try2[proc2Meta, s'])
            }



-- frame axioms for locks (shared vars)
fact FrameAxiomstry2{ 
    all s:proc2Meta.nodes | all s':proc2Meta.ACTchange_try2[s] | (Own_try2[proc2Meta,s] iff Own_try2[proc2Meta, s'])
     
            and 
             (Prop_cs[proc2Meta,s] iff Prop_cs[proc2Meta, s'])
            and
        (Av_turn[proc2Meta,s] iff Av_turn[proc2Meta, s']) 
            and
         (Own_turn[proc2Meta,s] iff Own_turn[proc2Meta, s'])
        and
        (Prop_turn[proc2Meta,s] iff Prop_turn[proc2Meta, s'])
    }
fact FrameAxiomsturn{ 
    all s:proc2Meta.nodes | all s':proc2Meta.ACTchange_turn[s] | (Own_turn[proc2Meta,s] iff Own_turn[proc2Meta, s'])
     
            and 
             (Prop_cs[proc2Meta,s] iff Prop_cs[proc2Meta, s'])
            and
        (Av_try2[proc2Meta,s] iff Av_try2[proc2Meta, s']) 
            and
         (Own_try2[proc2Meta,s] iff Own_try2[proc2Meta, s'])
        and
        (Prop_try2[proc2Meta,s] iff Prop_try2[proc2Meta, s'])
    }

pred Form10[i:proc2Meta, s:Node]{
 some s':(*(proc2Meta.succs)[s]) | Prop_cs[proc2Meta,s']}

-- Pred with inital condition and Invariants
pred Mod[s:proc2Meta.nodes]{ 
    all s':(*(proc2Meta.succs)[s]) | some proc2Meta.succs[s']
     Form10[proc2Meta,s]  
    (not (Prop_cs[proc2Meta,s])) and (not (Own_try2[proc2Meta,s]))

}

run Mod for 11
