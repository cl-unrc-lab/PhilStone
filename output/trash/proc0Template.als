open util/relation

abstract sig Node{}
abstract sig Prop{}
abstract sig NumVar{}

one sig Prop_cs extends Prop{}


one sig Prop_try1 extends Prop{}
one sig Prop_try2 extends Prop{}
one sig Prop_turn extends Prop{}


pred Prop_cs[m:proc0Meta,n:Node]{Prop_cs in m.val[n] }


pred Prop_try1[m:proc0Meta,n:Node]{Prop_try1 in m.val[n] }
pred Prop_try2[m:proc0Meta,n:Node]{Prop_try2 in m.val[n] }
pred Prop_turn[m:proc0Meta,n:Node]{Prop_turn in m.val[n] }


one sig Av_try1 extends Prop{}
one sig Av_try2 extends Prop{}
one sig Av_turn extends Prop{}

one sig Own_try1 extends Prop{}
one sig Own_try2 extends Prop{}
one sig Own_turn extends Prop{}

pred Av_try1[m:proc0Meta, n:Node]{Av_try1 in m.val[n]}
pred Av_try2[m:proc0Meta, n:Node]{Av_try2 in m.val[n]}
pred Av_turn[m:proc0Meta, n:Node]{Av_turn in m.val[n]}

pred Own_try1[m:proc0Meta, n:Node]{Own_try1 in m.val[n]}
pred Own_try2[m:proc0Meta, n:Node]{Own_try2 in m.val[n]}
pred Own_turn[m:proc0Meta, n:Node]{Own_turn in m.val[n]}






one sig proc0Meta{
	nodes:set Node,
	val: nodes -> Prop,
	succs : nodes -> nodes,
	local: nodes -> nodes,
	env: nodes -> nodes,
	ACTlocktry1:nodes -> nodes,
	ACTunlocktry1:nodes -> nodes,
	ACTlockturn:nodes -> nodes,
	ACTturnOn:nodes -> nodes,
	ACTenterCS:nodes -> nodes,
	ACTleaveCS:nodes -> nodes,
	ACTchange_try1:nodes -> nodes,
	ACTchange_try2:nodes -> nodes,
	ACTchange_turn:nodes -> nodes,
}
{
        succs = ACTlocktry1+ACTunlocktry1+ACTlockturn+ACTturnOn+ACTenterCS+ACTleaveCS 
         + ACTchange_try1+ACTchange_try2+ACTchange_turn 
        local = ACTlocktry1+ACTunlocktry1+ACTlockturn+ACTturnOn+ACTenterCS+ACTleaveCS
        env = ACTchange_try1+ACTchange_try2+ACTchange_turn
	   no (local & env)
}

-- actions axioms
    fact Action_locktry1_Ax1{ all s:proc0Meta.nodes | all s':proc0Meta.ACTlocktry1[s] | ((Av_try1[proc0Meta,s] and (not Prop_cs[proc0Meta,s]))) implies ((Own_try1[proc0Meta,s'])) } 
    fact Action_unlocktry1_Ax1{ all s:proc0Meta.nodes | all s':proc0Meta.ACTunlocktry1[s] | ((Prop_cs[proc0Meta,s] and (Own_try1[proc0Meta,s]))) implies (( (not Prop_cs[proc0Meta,s']) and (not Own_try1[proc0Meta,s']))) } 
    fact Action_lockturn_Ax1{ all s:proc0Meta.nodes | all s':proc0Meta.ACTlockturn[s] | ((Av_turn[proc0Meta,s])) implies ((Own_turn[proc0Meta,s'])) } 
    fact Action_turnOn_Ax1{ all s:proc0Meta.nodes | all s':proc0Meta.ACTturnOn[s] | ((Own_try1[proc0Meta,s] and (not Prop_cs[proc0Meta,s]))) implies ((Prop_turn[proc0Meta,s'])) } 
    fact Action_enterCS_Ax1{ all s:proc0Meta.nodes | all s':proc0Meta.ACTenterCS[s] | (( (not Prop_try2[proc0Meta,s]) and (not Prop_cs[proc0Meta,s])) or ( (not Prop_turn[proc0Meta,s]) and (not Prop_cs[proc0Meta,s]))) implies ((Prop_cs[proc0Meta,s'])) } 
    fact Action_leaveCS_Ax1{ all s:proc0Meta.nodes | all s':proc0Meta.ACTleaveCS[s] | ((Prop_cs[proc0Meta,s] and (Own_turn[proc0Meta,s]))) implies ((Prop_turn[proc0Meta,s'] and (not Prop_cs[proc0Meta,s']) and (not Own_turn[proc0Meta,s']))) }  
    fact Action_locktry1_Ax2{ all s:proc0Meta.nodes | (not ((Av_try1[proc0Meta,s] and (not Prop_cs[proc0Meta,s])))) implies (no proc0Meta.ACTlocktry1[s])} 
    fact Action_unlocktry1_Ax2{ all s:proc0Meta.nodes | (not ((Prop_cs[proc0Meta,s] and (Own_try1[proc0Meta,s])))) implies (no proc0Meta.ACTunlocktry1[s])} 
    fact Action_lockturn_Ax2{ all s:proc0Meta.nodes | (not ((Av_turn[proc0Meta,s]))) implies (no proc0Meta.ACTlockturn[s])} 
    fact Action_turnOn_Ax2{ all s:proc0Meta.nodes | (not ((Own_try1[proc0Meta,s] and (not Prop_cs[proc0Meta,s])))) implies (no proc0Meta.ACTturnOn[s])} 
    fact Action_enterCS_Ax2{ all s:proc0Meta.nodes | (not (( (not Prop_try2[proc0Meta,s]) and (not Prop_cs[proc0Meta,s])) or ( (not Prop_turn[proc0Meta,s]) and (not Prop_cs[proc0Meta,s])))) implies (no proc0Meta.ACTenterCS[s])} 
    fact Action_leaveCS_Ax2{ all s:proc0Meta.nodes | (not ((Prop_cs[proc0Meta,s] and (Own_turn[proc0Meta,s])))) implies (no proc0Meta.ACTleaveCS[s])}  
    fact Action_locktry1_Ax3{ all s:proc0Meta.nodes | ((Av_try1[proc0Meta,s] and (not Prop_cs[proc0Meta,s]))) implies (some proc0Meta.ACTlocktry1[s])  } 
    fact Action_unlocktry1_Ax3{ all s:proc0Meta.nodes | ((Prop_cs[proc0Meta,s] and (Own_try1[proc0Meta,s]))) implies (some proc0Meta.ACTunlocktry1[s])  } 
    fact Action_lockturn_Ax3{ all s:proc0Meta.nodes | ((Av_turn[proc0Meta,s])) implies (some proc0Meta.ACTlockturn[s])  } 
    fact Action_turnOn_Ax3{ all s:proc0Meta.nodes | ((Own_try1[proc0Meta,s] and (not Prop_cs[proc0Meta,s]))) implies (some proc0Meta.ACTturnOn[s])  } 
    fact Action_enterCS_Ax3{ all s:proc0Meta.nodes | (( (not Prop_try2[proc0Meta,s]) and (not Prop_cs[proc0Meta,s])) or ( (not Prop_turn[proc0Meta,s]) and (not Prop_cs[proc0Meta,s]))) implies (some proc0Meta.ACTenterCS[s])  } 
    fact Action_leaveCS_Ax3{ all s:proc0Meta.nodes | ((Prop_cs[proc0Meta,s] and (Own_turn[proc0Meta,s]))) implies (some proc0Meta.ACTleaveCS[s])  }  
 


-- resource axioms for booleans
    fact ResAx1 { all s:proc0Meta.nodes | Own_try1[proc0Meta, s] implies (not Av_try1[proc0Meta, s]) } fact ResAx1 { all s:proc0Meta.nodes | Own_try2[proc0Meta, s] implies (not Av_try2[proc0Meta, s]) } fact ResAx1 { all s:proc0Meta.nodes | Own_turn[proc0Meta, s] implies (not Av_turn[proc0Meta, s]) } 
    fact ResAx2 { all s:proc0Meta.nodes | (not Own_try1[proc0Meta,s]) implies (some proc0Meta.ACTchange_try1[s]) }  fact ResAx2 { all s:proc0Meta.nodes | (not Own_try2[proc0Meta,s]) implies (some proc0Meta.ACTchange_try2[s]) }  fact ResAx2 { all s:proc0Meta.nodes | (not Own_turn[proc0Meta,s]) implies (some proc0Meta.ACTchange_turn[s]) }  
    fact ResAx3 { all s:proc0Meta.nodes | all s':proc0Meta.ACTchange_try1[s] | Av_try1[proc0Meta,s] iff (not Av_try1[proc0Meta, s']) }fact ResAx3 { all s:proc0Meta.nodes | all s':proc0Meta.ACTchange_try2[s] | Av_try2[proc0Meta,s] iff (not Av_try2[proc0Meta, s']) }fact ResAx3 { all s:proc0Meta.nodes | all s':proc0Meta.ACTchange_turn[s] | Av_turn[proc0Meta,s] iff (not Av_turn[proc0Meta, s']) }  
    fact ResAx4 { all s:proc0Meta.nodes | all s':(proc0Meta.env[s] - proc0Meta.ACTchange_try1[s]) | Av_try1[proc0Meta,s] iff Av_try1[proc0Meta, s'] }fact ResAx4 { all s:proc0Meta.nodes | all s':(proc0Meta.env[s] - proc0Meta.ACTchange_try2[s]) | Av_try2[proc0Meta,s] iff Av_try2[proc0Meta, s'] }fact ResAx4 { all s:proc0Meta.nodes | all s':(proc0Meta.env[s] - proc0Meta.ACTchange_turn[s]) | Av_turn[proc0Meta,s] iff Av_turn[proc0Meta, s'] } 

-- the following axioms state that environment actions are unrestricted
    fact ResAx5 { all s:proc0Meta.nodes | (not Own_try1[proc0Meta,s]) implies (some s':proc0Meta.ACTchange_try1[s] | Prop_try1[proc0Meta,s']) }fact ResAx5 { all s:proc0Meta.nodes | (not Own_try2[proc0Meta,s]) implies (some s':proc0Meta.ACTchange_try2[s] | Prop_try2[proc0Meta,s']) }fact ResAx5 { all s:proc0Meta.nodes | (not Own_turn[proc0Meta,s]) implies (some s':proc0Meta.ACTchange_turn[s] | Prop_turn[proc0Meta,s']) }  
    fact ResAx6 { all s:proc0Meta.nodes | (not Own_try1[proc0Meta,s]) implies (some s':proc0Meta.ACTchange_try1[s] | not Prop_try1[proc0Meta,s']) }fact ResAx6 { all s:proc0Meta.nodes | (not Own_try2[proc0Meta,s]) implies (some s':proc0Meta.ACTchange_try2[s] | not Prop_try2[proc0Meta,s']) }fact ResAx6 { all s:proc0Meta.nodes | (not Own_turn[proc0Meta,s]) implies (some s':proc0Meta.ACTchange_turn[s] | not Prop_turn[proc0Meta,s']) } 

-- resource axioms for ints
-- and axioms stating that environment actions are not restricted for ints
-- frame axioms for boolean variables
 
    fact FrameAxiomslocktry1{ 
                    all s:proc0Meta.nodes | all s':proc0Meta.ACTlocktry1[s] | 
                (Av_try2[proc0Meta,s] iff Av_try2[proc0Meta, s']) and (Av_turn[proc0Meta,s] iff Av_turn[proc0Meta, s']) 
                and
                (Own_try2[proc0Meta,s] iff Own_try2[proc0Meta, s']) and (Own_turn[proc0Meta,s] iff Own_turn[proc0Meta, s'])
            }

    fact FrameAxiomsunlocktry1{ 
                    all s:proc0Meta.nodes | all s':proc0Meta.ACTunlocktry1[s] | 
                (Av_try2[proc0Meta,s] iff Av_try2[proc0Meta, s']) and (Av_turn[proc0Meta,s] iff Av_turn[proc0Meta, s']) 
                and
                (Own_try2[proc0Meta,s] iff Own_try2[proc0Meta, s']) and (Own_turn[proc0Meta,s] iff Own_turn[proc0Meta, s'])
            }

    fact FrameAxiomslockturn{ 
                    all s:proc0Meta.nodes | all s':proc0Meta.ACTlockturn[s] | 
                (Av_try1[proc0Meta,s] iff Av_try1[proc0Meta, s']) and (Av_try2[proc0Meta,s] iff Av_try2[proc0Meta, s']) 
                and
                (Own_try1[proc0Meta,s] iff Own_try1[proc0Meta, s']) and (Own_try2[proc0Meta,s] iff Own_try2[proc0Meta, s'])
            }

    fact FrameAxiomsturnOn{ 
                    all s:proc0Meta.nodes | all s':proc0Meta.ACTturnOn[s] | 
                (Av_try1[proc0Meta,s] iff Av_try1[proc0Meta, s']) and (Av_try2[proc0Meta,s] iff Av_try2[proc0Meta, s']) 
                and
                (Own_try1[proc0Meta,s] iff Own_try1[proc0Meta, s']) and (Own_try2[proc0Meta,s] iff Own_try2[proc0Meta, s'])
            }

    fact FrameAxiomsenterCS{ 
                    all s:proc0Meta.nodes | all s':proc0Meta.ACTenterCS[s] | 
                (Av_try1[proc0Meta,s] iff Av_try1[proc0Meta, s']) and (Av_try2[proc0Meta,s] iff Av_try2[proc0Meta, s']) and (Av_turn[proc0Meta,s] iff Av_turn[proc0Meta, s']) 
                and
                (Own_try1[proc0Meta,s] iff Own_try1[proc0Meta, s']) and (Own_try2[proc0Meta,s] iff Own_try2[proc0Meta, s']) and (Own_turn[proc0Meta,s] iff Own_turn[proc0Meta, s'])
            }

    fact FrameAxiomsleaveCS{ 
                    all s:proc0Meta.nodes | all s':proc0Meta.ACTleaveCS[s] | 
                (Av_try1[proc0Meta,s] iff Av_try1[proc0Meta, s']) and (Av_try2[proc0Meta,s] iff Av_try2[proc0Meta, s']) 
                and
                (Own_try1[proc0Meta,s] iff Own_try1[proc0Meta, s']) and (Own_try2[proc0Meta,s] iff Own_try2[proc0Meta, s'])
            }



-- frame axioms for locks (shared vars)
fact FrameAxiomstry1{ 
    all s:proc0Meta.nodes | all s':proc0Meta.ACTchange_try1[s] | (Own_try1[proc0Meta,s] iff Own_try1[proc0Meta, s'])
     
            and 
             (Prop_cs[proc0Meta,s] iff Prop_cs[proc0Meta, s'])
            and
        (Av_try2[proc0Meta,s] iff Av_try2[proc0Meta, s']) and (Av_turn[proc0Meta,s] iff Av_turn[proc0Meta, s']) 
            and
         (Own_try2[proc0Meta,s] iff Own_try2[proc0Meta, s'])and (Own_turn[proc0Meta,s] iff Own_turn[proc0Meta, s'])
    }
fact FrameAxiomstry2{ 
    all s:proc0Meta.nodes | all s':proc0Meta.ACTchange_try2[s] | (Own_try2[proc0Meta,s] iff Own_try2[proc0Meta, s'])
     
            and 
             (Prop_cs[proc0Meta,s] iff Prop_cs[proc0Meta, s'])
            and
        (Av_try1[proc0Meta,s] iff Av_try1[proc0Meta, s']) and (Av_turn[proc0Meta,s] iff Av_turn[proc0Meta, s']) 
            and
         (Own_try1[proc0Meta,s] iff Own_try1[proc0Meta, s'])and (Own_turn[proc0Meta,s] iff Own_turn[proc0Meta, s'])
    }
fact FrameAxiomsturn{ 
    all s:proc0Meta.nodes | all s':proc0Meta.ACTchange_turn[s] | (Own_turn[proc0Meta,s] iff Own_turn[proc0Meta, s'])
     
            and 
             (Prop_cs[proc0Meta,s] iff Prop_cs[proc0Meta, s'])
            and
        (Av_try1[proc0Meta,s] iff Av_try1[proc0Meta, s']) and (Av_try2[proc0Meta,s] iff Av_try2[proc0Meta, s']) 
            and
         (Own_try1[proc0Meta,s] iff Own_try1[proc0Meta, s'])and (Own_try2[proc0Meta,s] iff Own_try2[proc0Meta, s'])
    }


-- Pred with inital condition and Invariants
pred Mod[s:proc0Meta.nodes]{ 
    all s':(*(proc0Meta.succs)[s]) | some proc0Meta.succs[s']
     (Prop_cs[proc0Meta,s]) or (not (Prop_cs[proc0Meta,s]))  
    (not (Prop_cs[proc0Meta,s])) and (not (Own_try1[proc0Meta,s]))

}

run Mod for 10
