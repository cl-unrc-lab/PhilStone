open util/relation

abstract sig Node{}
abstract sig Prop{}
abstract sig NumVar{}

one sig Prop_cs extends Prop{}


one sig Prop_try1 extends Prop{}
one sig Prop_turn extends Prop{}


pred Prop_cs[m:proc1Meta,n:Node]{Prop_cs in m.val[n] }


pred Prop_try1[m:proc1Meta,n:Node]{Prop_try1 in m.val[n] }
pred Prop_turn[m:proc1Meta,n:Node]{Prop_turn in m.val[n] }


one sig Av_try1 extends Prop{}
one sig Av_turn extends Prop{}

one sig Own_try1 extends Prop{}
one sig Own_turn extends Prop{}

pred Av_try1[m:proc1Meta, n:Node]{Av_try1 in m.val[n]}
pred Av_turn[m:proc1Meta, n:Node]{Av_turn in m.val[n]}

pred Own_try1[m:proc1Meta, n:Node]{Own_try1 in m.val[n]}
pred Own_turn[m:proc1Meta, n:Node]{Own_turn in m.val[n]}






one sig proc1Meta{
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
	ACTchange_turn:nodes -> nodes,
}
{
        succs = ACTlocktry1+ACTunlocktry1+ACTlockturn+ACTturnOn+ACTenterCS+ACTleaveCS 
         + ACTchange_try1+ACTchange_turn 
        local = ACTlocktry1+ACTunlocktry1+ACTlockturn+ACTturnOn+ACTenterCS+ACTleaveCS
        env = ACTchange_try1+ACTchange_turn
	   no (local & env)
}

-- actions axioms
    fact Action_locktry1_Ax1{ all s:proc1Meta.nodes | all s':proc1Meta.ACTlocktry1[s] | ((Av_try1[proc1Meta,s] and (not Prop_cs[proc1Meta,s]))) implies ((Own_try1[proc1Meta,s'])) } 
    fact Action_unlocktry1_Ax1{ all s:proc1Meta.nodes | all s':proc1Meta.ACTunlocktry1[s] | ((Prop_cs[proc1Meta,s] and (Own_try1[proc1Meta,s]))) implies (( (not Prop_cs[proc1Meta,s']) and (not Own_try1[proc1Meta,s']))) } 
    fact Action_lockturn_Ax1{ all s:proc1Meta.nodes | all s':proc1Meta.ACTlockturn[s] | ((Av_turn[proc1Meta,s] and (not Prop_cs[proc1Meta,s]))) implies ((Own_turn[proc1Meta,s'])) } 
    fact Action_turnOn_Ax1{ all s:proc1Meta.nodes | all s':proc1Meta.ACTturnOn[s] | ((Own_turn[proc1Meta,s] and (not Prop_cs[proc1Meta,s]))) implies ((Prop_turn[proc1Meta,s'])) } 
    fact Action_enterCS_Ax1{ all s:proc1Meta.nodes | all s':proc1Meta.ACTenterCS[s] | (( (not Prop_cs[proc1Meta,s]))) implies ((Prop_cs[proc1Meta,s'])) } 
    fact Action_leaveCS_Ax1{ all s:proc1Meta.nodes | all s':proc1Meta.ACTleaveCS[s] | ((Prop_cs[proc1Meta,s] and (Own_turn[proc1Meta,s]))) implies ((Prop_turn[proc1Meta,s'] and (not Prop_cs[proc1Meta,s']) and (not Own_turn[proc1Meta,s']))) }  
    fact Action_locktry1_Ax2{ all s:proc1Meta.nodes | (not ((Av_try1[proc1Meta,s] and (not Prop_cs[proc1Meta,s])))) implies (no proc1Meta.ACTlocktry1[s])} 
    fact Action_unlocktry1_Ax2{ all s:proc1Meta.nodes | (not ((Prop_cs[proc1Meta,s] and (Own_try1[proc1Meta,s])))) implies (no proc1Meta.ACTunlocktry1[s])} 
    fact Action_lockturn_Ax2{ all s:proc1Meta.nodes | (not ((Av_turn[proc1Meta,s] and (not Prop_cs[proc1Meta,s])))) implies (no proc1Meta.ACTlockturn[s])} 
    fact Action_turnOn_Ax2{ all s:proc1Meta.nodes | (not ((Own_turn[proc1Meta,s] and (not Prop_cs[proc1Meta,s])))) implies (no proc1Meta.ACTturnOn[s])} 
    fact Action_enterCS_Ax2{ all s:proc1Meta.nodes | (not (( (not Prop_cs[proc1Meta,s])))) implies (no proc1Meta.ACTenterCS[s])} 
    fact Action_leaveCS_Ax2{ all s:proc1Meta.nodes | (not ((Prop_cs[proc1Meta,s] and (Own_turn[proc1Meta,s])))) implies (no proc1Meta.ACTleaveCS[s])}  
/*
    fact Action_locktry1_Ax3{ all s:proc1Meta.nodes | ((Av_try1[proc1Meta,s] and (not Prop_cs[proc1Meta,s]))) implies (some proc1Meta.ACTlocktry1[s])  } 
    fact Action_unlocktry1_Ax3{ all s:proc1Meta.nodes | ((Prop_cs[proc1Meta,s] and (Own_try1[proc1Meta,s]))) implies (some proc1Meta.ACTunlocktry1[s])  } 
    fact Action_lockturn_Ax3{ all s:proc1Meta.nodes | ((Av_turn[proc1Meta,s] and (not Prop_cs[proc1Meta,s]))) implies (some proc1Meta.ACTlockturn[s])  } 
    fact Action_turnOn_Ax3{ all s:proc1Meta.nodes | ((Own_turn[proc1Meta,s] and (not Prop_cs[proc1Meta,s]))) implies (some proc1Meta.ACTturnOn[s])  } 
    fact Action_enterCS_Ax3{ all s:proc1Meta.nodes | (( (not Prop_cs[proc1Meta,s]))) implies (some proc1Meta.ACTenterCS[s])  } 
    fact Action_leaveCS_Ax3{ all s:proc1Meta.nodes | ((Prop_cs[proc1Meta,s] and (Own_turn[proc1Meta,s]))) implies (some proc1Meta.ACTleaveCS[s])  }  
 */


-- resource axioms for booleans
    fact ResAx1 { all s:proc1Meta.nodes | Own_try1[proc1Meta, s] implies (not Av_try1[proc1Meta, s]) } fact ResAx1 { all s:proc1Meta.nodes | Own_turn[proc1Meta, s] implies (not Av_turn[proc1Meta, s]) } 
    fact ResAx2 { all s:proc1Meta.nodes | (not Own_try1[proc1Meta,s]) iff (some proc1Meta.ACTchange_try1[s]) }  fact ResAx2 { all s:proc1Meta.nodes | (not Own_turn[proc1Meta,s]) iff (some proc1Meta.ACTchange_turn[s]) }  
    fact ResAx3 { all s:proc1Meta.nodes | all s':proc1Meta.ACTchange_try1[s] | Av_try1[proc1Meta,s] iff (not Av_try1[proc1Meta, s']) }fact ResAx3 { all s:proc1Meta.nodes | all s':proc1Meta.ACTchange_turn[s] | Av_turn[proc1Meta,s] iff (not Av_turn[proc1Meta, s']) }  

-- these axioms state that local actions cannot change shared variables which locks ore not owned by the process
    fact ResAx4 {  all s:proc1Meta.nodes | (not Own_try1[proc1Meta,s]) implies (all s':proc1Meta.local[s] | (Prop_try1[proc1Meta,s] iff Prop_try1[proc1Meta,s']) ) } fact ResAx4 {  all s:proc1Meta.nodes | (not Own_turn[proc1Meta,s]) implies (all s':proc1Meta.local[s] | (Prop_turn[proc1Meta,s] iff Prop_turn[proc1Meta,s']) ) } 

    fact ResAx4 { all s:proc1Meta.nodes | all s':(proc1Meta.env[s] - proc1Meta.ACTchange_try1[s]) | Av_try1[proc1Meta,s] iff Av_try1[proc1Meta, s'] }fact ResAx4 { all s:proc1Meta.nodes | all s':(proc1Meta.env[s] - proc1Meta.ACTchange_turn[s]) | Av_turn[proc1Meta,s] iff Av_turn[proc1Meta, s'] } 

-- the following axioms state that environment actions are unrestricted
    fact ResAx5 { all s:proc1Meta.nodes | ((not Own_try1[proc1Meta,s]) and (not Av_try1[proc1Meta,s])) implies (some s':proc1Meta.ACTchange_try1[s] | Prop_try1[proc1Meta,s']) }fact ResAx5 { all s:proc1Meta.nodes | ((not Own_turn[proc1Meta,s]) and (not Av_turn[proc1Meta,s])) implies (some s':proc1Meta.ACTchange_turn[s] | Prop_turn[proc1Meta,s']) }  
    fact ResAx6 { all s:proc1Meta.nodes | ((not Own_try1[proc1Meta,s]) and (not Av_try1[proc1Meta,s])) implies (some s':proc1Meta.ACTchange_try1[s] | not Prop_try1[proc1Meta,s']) }fact ResAx6 { all s:proc1Meta.nodes | ((not Own_turn[proc1Meta,s]) and (not Av_turn[proc1Meta,s])) implies (some s':proc1Meta.ACTchange_turn[s] | not Prop_turn[proc1Meta,s']) } 

-- resource axioms for ints
-- and axioms stating that environment actions are not restricted for ints
-- frame axioms for local boolean variables
 
    fact FrameAxiomslocktry1{ 
                all s:proc1Meta.nodes | all s':proc1Meta.ACTlocktry1[s] | (Prop_cs[proc1Meta,s] iff Prop_cs[proc1Meta, s'])
                    and 
                (Av_turn[proc1Meta,s] iff Av_turn[proc1Meta, s']) 
                and
                (Own_turn[proc1Meta,s] iff Own_turn[proc1Meta, s'])
            }

    fact FrameAxiomsunlocktry1{ 
                    all s:proc1Meta.nodes | all s':proc1Meta.ACTunlocktry1[s] | 
                (Av_turn[proc1Meta,s] iff Av_turn[proc1Meta, s']) 
                and
                (Own_turn[proc1Meta,s] iff Own_turn[proc1Meta, s'])
            }

    fact FrameAxiomslockturn{ 
                all s:proc1Meta.nodes | all s':proc1Meta.ACTlockturn[s] | (Prop_cs[proc1Meta,s] iff Prop_cs[proc1Meta, s'])
                    and 
                (Av_try1[proc1Meta,s] iff Av_try1[proc1Meta, s']) 
                and
                (Own_try1[proc1Meta,s] iff Own_try1[proc1Meta, s'])
            }

    fact FrameAxiomsturnOn{ 
                all s:proc1Meta.nodes | all s':proc1Meta.ACTturnOn[s] | (Prop_cs[proc1Meta,s] iff Prop_cs[proc1Meta, s'])
                    and 
                (Av_try1[proc1Meta,s] iff Av_try1[proc1Meta, s']) 
                and
                (Own_try1[proc1Meta,s] iff Own_try1[proc1Meta, s'])
            }

    fact FrameAxiomsenterCS{ 
                    all s:proc1Meta.nodes | all s':proc1Meta.ACTenterCS[s] | 
                (Av_try1[proc1Meta,s] iff Av_try1[proc1Meta, s']) and (Av_turn[proc1Meta,s] iff Av_turn[proc1Meta, s']) 
                and
                (Own_try1[proc1Meta,s] iff Own_try1[proc1Meta, s']) and (Own_turn[proc1Meta,s] iff Own_turn[proc1Meta, s'])
            }

    fact FrameAxiomsleaveCS{ 
                    all s:proc1Meta.nodes | all s':proc1Meta.ACTleaveCS[s] | 
                (Av_try1[proc1Meta,s] iff Av_try1[proc1Meta, s']) 
                and
                (Own_try1[proc1Meta,s] iff Own_try1[proc1Meta, s'])
            }



-- frame axioms for locks (shared vars)
fact FrameAxiomstry1{ 
    all s:proc1Meta.nodes | all s':proc1Meta.ACTchange_try1[s] | (Own_try1[proc1Meta,s] iff Own_try1[proc1Meta, s'])
     
            and 
             (Prop_cs[proc1Meta,s] iff Prop_cs[proc1Meta, s'])
            and
        (Av_turn[proc1Meta,s] iff Av_turn[proc1Meta, s']) 
            and
         (Own_turn[proc1Meta,s] iff Own_turn[proc1Meta, s'])
        and
        (Prop_turn[proc1Meta,s] iff Prop_turn[proc1Meta, s'])
    }
fact FrameAxiomsturn{ 
    all s:proc1Meta.nodes | all s':proc1Meta.ACTchange_turn[s] | (Own_turn[proc1Meta,s] iff Own_turn[proc1Meta, s'])
     
            and 
             (Prop_cs[proc1Meta,s] iff Prop_cs[proc1Meta, s'])
            and
        (Av_try1[proc1Meta,s] iff Av_try1[proc1Meta, s']) 
            and
         (Own_try1[proc1Meta,s] iff Own_try1[proc1Meta, s'])
        and
        (Prop_try1[proc1Meta,s] iff Prop_try1[proc1Meta, s'])
    }

pred Form0[i:proc1Meta, s:Node]{
 some s':(*(proc1Meta.succs)[s]) | Prop_cs[proc1Meta,s']}
pred Form5[i:proc1Meta, s:Node]{
 all s':(*(proc1Meta.succs)[s]) | (not (Prop_cs[proc1Meta,s'])) or (Form3[proc1Meta,s']) }
pred Form3[i:proc1Meta, s:Node]{
 some s':(*(proc1Meta.succs)[s]) | not (Prop_cs[proc1Meta,s'])}

-- Pred with inital condition and Invariants
pred Mod[s:proc1Meta.nodes]{ 
    all s':(*(proc1Meta.succs)[s]) | some proc1Meta.succs[s']
     (Form0[proc1Meta,s]) and (Form5[proc1Meta,s])  
    (not (Prop_cs[proc1Meta,s])) and (not (Own_try1[proc1Meta,s]))

}

run Mod for 11
