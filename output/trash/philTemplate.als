open util/relation

abstract sig Node{}
abstract sig Prop{}
abstract sig NumVar{}

one sig Prop_hungry extends Prop{}
one sig Prop_eating extends Prop{}
one sig Prop_thinking extends Prop{}


one sig Prop_left extends Prop{}
one sig Prop_right extends Prop{}


pred Prop_hungry[m:philMeta,n:Node]{Prop_hungry in m.val[n] }
pred Prop_eating[m:philMeta,n:Node]{Prop_eating in m.val[n] }
pred Prop_thinking[m:philMeta,n:Node]{Prop_thinking in m.val[n] }


pred Prop_left[m:philMeta,n:Node]{Prop_left in m.val[n] }
pred Prop_right[m:philMeta,n:Node]{Prop_right in m.val[n] }


one sig Av_left extends Prop{}
one sig Av_right extends Prop{}

one sig Own_left extends Prop{}
one sig Own_right extends Prop{}

pred Av_left[m:philMeta, n:Node]{Av_left in m.val[n]}
pred Av_right[m:philMeta, n:Node]{Av_right in m.val[n]}

pred Own_left[m:philMeta, n:Node]{Own_left in m.val[n]}
pred Own_right[m:philMeta, n:Node]{Own_right in m.val[n]}






one sig philMeta{
	nodes:set Node,
	val: nodes -> Prop,
	succs : nodes -> nodes,
	local: nodes -> nodes,
	env: nodes -> nodes,
	ACTstartThinking:nodes -> nodes,
	ACTbecomeHunrgy:nodes -> nodes,
	ACTgetLeft:nodes -> nodes,
	ACTgetRight:nodes -> nodes,
	ACTeat:nodes -> nodes,
	ACTchange_left:nodes -> nodes,
	ACTchange_right:nodes -> nodes,
}
{
        succs = ACTstartThinking+ACTbecomeHunrgy+ACTgetLeft+ACTgetRight+ACTeat 
         + ACTchange_left+ACTchange_right 
        local = ACTstartThinking+ACTbecomeHunrgy+ACTgetLeft+ACTgetRight+ACTeat
        env = ACTchange_left+ACTchange_right
	   no (local & env)
}

-- actions axioms
    fact Action_startThinking_Ax1{ all s:philMeta.nodes | all s':philMeta.ACTstartThinking[s] | ((Prop_eating[philMeta,s])) implies ((Prop_thinking[philMeta,s'] and (Av_left[philMeta,s']) and (Av_right[philMeta,s']) and (not Prop_eating[philMeta,s']))) } 
    fact Action_becomeHunrgy_Ax1{ all s:philMeta.nodes | all s':philMeta.ACTbecomeHunrgy[s] | ((Prop_thinking[philMeta,s])) implies ((Prop_hungry[philMeta,s'] and (not Prop_thinking[philMeta,s']))) } 
    fact Action_getLeft_Ax1{ all s:philMeta.nodes | all s':philMeta.ACTgetLeft[s] | ((Av_left[philMeta,s] and (Prop_hungry[philMeta,s]))) implies ((Own_left[philMeta,s'])) } 
    fact Action_getRight_Ax1{ all s:philMeta.nodes | all s':philMeta.ACTgetRight[s] | ((Av_right[philMeta,s] and (Prop_hungry[philMeta,s]))) implies ((Own_right[philMeta,s'])) } 
    fact Action_eat_Ax1{ all s:philMeta.nodes | all s':philMeta.ACTeat[s] | ((Prop_hungry[philMeta,s] and (Own_left[philMeta,s]) and (Own_right[philMeta,s]))) implies ((Prop_eating[philMeta,s'] and (not Prop_hungry[philMeta,s']))) }  
    fact Action_startThinking_Ax2{ all s:philMeta.nodes | (not ((Prop_eating[philMeta,s]))) implies (no philMeta.ACTstartThinking[s])} 
    fact Action_becomeHunrgy_Ax2{ all s:philMeta.nodes | (not ((Prop_thinking[philMeta,s]))) implies (no philMeta.ACTbecomeHunrgy[s])} 
    fact Action_getLeft_Ax2{ all s:philMeta.nodes | (not ((Av_left[philMeta,s] and (Prop_hungry[philMeta,s])))) implies (no philMeta.ACTgetLeft[s])} 
    fact Action_getRight_Ax2{ all s:philMeta.nodes | (not ((Av_right[philMeta,s] and (Prop_hungry[philMeta,s])))) implies (no philMeta.ACTgetRight[s])} 
    fact Action_eat_Ax2{ all s:philMeta.nodes | (not ((Prop_hungry[philMeta,s] and (Own_left[philMeta,s]) and (Own_right[philMeta,s])))) implies (no philMeta.ACTeat[s])}  
    fact Action_startThinking_Ax3{ all s:philMeta.nodes | ((Prop_eating[philMeta,s])) implies (some philMeta.ACTstartThinking[s])  } 
    fact Action_becomeHunrgy_Ax3{ all s:philMeta.nodes | ((Prop_thinking[philMeta,s])) implies (some philMeta.ACTbecomeHunrgy[s])  } 
    fact Action_getLeft_Ax3{ all s:philMeta.nodes | ((Av_left[philMeta,s] and (Prop_hungry[philMeta,s]))) implies (some philMeta.ACTgetLeft[s])  } 
    fact Action_getRight_Ax3{ all s:philMeta.nodes | ((Av_right[philMeta,s] and (Prop_hungry[philMeta,s]))) implies (some philMeta.ACTgetRight[s])  } 
    fact Action_eat_Ax3{ all s:philMeta.nodes | ((Prop_hungry[philMeta,s] and (Own_left[philMeta,s]) and (Own_right[philMeta,s]))) implies (some philMeta.ACTeat[s])  }  
 


-- resource axioms for booleans
    fact ResAx1 { all s:philMeta.nodes | Own_left[philMeta, s] implies (not Av_left[philMeta, s]) } fact ResAx1 { all s:philMeta.nodes | Own_right[philMeta, s] implies (not Av_right[philMeta, s]) } 
    fact ResAx2 { all s:philMeta.nodes | (not Own_left[philMeta,s]) iff (some philMeta.ACTchange_left[s]) }  fact ResAx2 { all s:philMeta.nodes | (not Own_right[philMeta,s]) iff (some philMeta.ACTchange_right[s]) }  
    fact ResAx3 { all s:philMeta.nodes | all s':philMeta.ACTchange_left[s] | Av_left[philMeta,s] iff (not Av_left[philMeta, s']) }fact ResAx3 { all s:philMeta.nodes | all s':philMeta.ACTchange_right[s] | Av_right[philMeta,s] iff (not Av_right[philMeta, s']) }  

-- these axioms state that local actions cannot change shared variables which locks ore not owned by the process
    fact ResAx4 {  all s:philMeta.nodes | (not Own_left[philMeta,s]) implies (all s':philMeta.local[s] | (Prop_left[philMeta,s] iff Prop_left[philMeta,s']) ) } fact ResAx4 {  all s:philMeta.nodes | (not Own_right[philMeta,s]) implies (all s':philMeta.local[s] | (Prop_right[philMeta,s] iff Prop_right[philMeta,s']) ) } 

    fact ResAx4 { all s:philMeta.nodes | all s':(philMeta.env[s] - philMeta.ACTchange_left[s]) | Av_left[philMeta,s] iff Av_left[philMeta, s'] }fact ResAx4 { all s:philMeta.nodes | all s':(philMeta.env[s] - philMeta.ACTchange_right[s]) | Av_right[philMeta,s] iff Av_right[philMeta, s'] } 

-- the following axioms state that environment actions are unrestricted
    fact ResAx5 { all s:philMeta.nodes | ((not Own_left[philMeta,s]) and (not Av_left[philMeta,s])) implies (some s':philMeta.ACTchange_left[s] | Prop_left[philMeta,s']) }fact ResAx5 { all s:philMeta.nodes | ((not Own_right[philMeta,s]) and (not Av_right[philMeta,s])) implies (some s':philMeta.ACTchange_right[s] | Prop_right[philMeta,s']) }  
    fact ResAx6 { all s:philMeta.nodes | ((not Own_left[philMeta,s]) and (not Av_left[philMeta,s])) implies (some s':philMeta.ACTchange_left[s] | not Prop_left[philMeta,s']) }fact ResAx6 { all s:philMeta.nodes | ((not Own_right[philMeta,s]) and (not Av_right[philMeta,s])) implies (some s':philMeta.ACTchange_right[s] | not Prop_right[philMeta,s']) } 

-- resource axioms for ints
-- and axioms stating that environment actions are not restricted for ints
-- frame axioms for local boolean variables
 
    fact FrameAxiomsstartThinking{ 
             
                        all s:philMeta.nodes,  s':philMeta.ACTstartThinking[s] |(Prop_hungry[philMeta,s] iff Prop_hungry[philMeta, s']) 
            }

    fact FrameAxiomsbecomeHunrgy{ 
                all s:philMeta.nodes | all s':philMeta.ACTbecomeHunrgy[s] | (Prop_eating[philMeta,s] iff Prop_eating[philMeta, s'])
                    and 
                (Av_left[philMeta,s] iff Av_left[philMeta, s']) and (Av_right[philMeta,s] iff Av_right[philMeta, s']) 
                and
                (Own_left[philMeta,s] iff Own_left[philMeta, s']) and (Own_right[philMeta,s] iff Own_right[philMeta, s'])
            }

    fact FrameAxiomsgetLeft{ 
                all s:philMeta.nodes | all s':philMeta.ACTgetLeft[s] | (Prop_hungry[philMeta,s] iff Prop_hungry[philMeta, s']) and (Prop_eating[philMeta,s] iff Prop_eating[philMeta, s']) and (Prop_thinking[philMeta,s] iff Prop_thinking[philMeta, s'])
                    and 
                (Av_right[philMeta,s] iff Av_right[philMeta, s']) 
                and
                (Own_right[philMeta,s] iff Own_right[philMeta, s'])
            }

    fact FrameAxiomsgetRight{ 
                all s:philMeta.nodes | all s':philMeta.ACTgetRight[s] | (Prop_hungry[philMeta,s] iff Prop_hungry[philMeta, s']) and (Prop_eating[philMeta,s] iff Prop_eating[philMeta, s']) and (Prop_thinking[philMeta,s] iff Prop_thinking[philMeta, s'])
                    and 
                (Av_left[philMeta,s] iff Av_left[philMeta, s']) 
                and
                (Own_left[philMeta,s] iff Own_left[philMeta, s'])
            }

    fact FrameAxiomseat{ 
                all s:philMeta.nodes | all s':philMeta.ACTeat[s] | (Prop_thinking[philMeta,s] iff Prop_thinking[philMeta, s'])
                    and 
                (Av_left[philMeta,s] iff Av_left[philMeta, s']) and (Av_right[philMeta,s] iff Av_right[philMeta, s']) 
                and
                (Own_left[philMeta,s] iff Own_left[philMeta, s']) and (Own_right[philMeta,s] iff Own_right[philMeta, s'])
            }



-- frame axioms for locks (shared vars)
fact FrameAxiomsleft{ 
    all s:philMeta.nodes | all s':philMeta.ACTchange_left[s] | (Own_left[philMeta,s] iff Own_left[philMeta, s'])
     
            and 
             (Prop_hungry[philMeta,s] iff Prop_hungry[philMeta, s']) and  (Prop_eating[philMeta,s] iff Prop_eating[philMeta, s']) and  (Prop_thinking[philMeta,s] iff Prop_thinking[philMeta, s'])
            and
        (Av_right[philMeta,s] iff Av_right[philMeta, s']) 
            and
         (Own_right[philMeta,s] iff Own_right[philMeta, s'])
    }
fact FrameAxiomsright{ 
    all s:philMeta.nodes | all s':philMeta.ACTchange_right[s] | (Own_right[philMeta,s] iff Own_right[philMeta, s'])
     
            and 
             (Prop_hungry[philMeta,s] iff Prop_hungry[philMeta, s']) and  (Prop_eating[philMeta,s] iff Prop_eating[philMeta, s']) and  (Prop_thinking[philMeta,s] iff Prop_thinking[philMeta, s'])
            and
        (Av_left[philMeta,s] iff Av_left[philMeta, s']) 
            and
         (Own_left[philMeta,s] iff Own_left[philMeta, s'])
    }

pred Form8[i:philMeta, s:Node]{
 all s':(*(philMeta.succs)[s]) | ((not ((Prop_thinking[philMeta,s']) and (Prop_hungry[philMeta,s']))) and (not ((Prop_thinking[philMeta,s']) and (Prop_eating[philMeta,s'])))) and (not ((Prop_hungry[philMeta,s']) and (Prop_eating[philMeta,s']))) }
pred Form9[i:philMeta, s:Node]{
 some s':(*(philMeta.succs)[s]) | Prop_eating[philMeta,s']}

-- Pred with inital condition and Invariants
pred Mod[s:philMeta.nodes]{ 
    all s':(*(philMeta.succs)[s]) | some philMeta.succs[s']
     (Form8[philMeta,s]) and (Form9[philMeta,s])  
    ((((Prop_thinking[philMeta,s]) and (not (Prop_hungry[philMeta,s]))) and (not (Prop_eating[philMeta,s]))) and (Av_left[philMeta,s])) and (Av_right[philMeta,s])

}

run Mod for 11
