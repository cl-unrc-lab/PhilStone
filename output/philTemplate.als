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
one sig Thinking extends Enum{}
one sig Hungry extends Enum{}
one sig Eating extends Enum{}

-- definition of the inc fun for every enum type
--fun Inc:Enum->Enum { } 
--fun Inc:Enum->Enum { } 
--fun Inc:Enum->Enum { } 

-- definition of the dec fun for every enum type
-- fun Dec:Enum->Enum { } 
-- fun Dec:Enum->Enum { } 
-- fun Dec:Enum->Enum { } 



fun Val_st[m:philMeta,n:Node]:Enum {m.enums[n][EnumVar_st] }







-- additional vars for shared non-rpimitive vars representing the locks associated to each of them




-- similarly for the shared non-primitive  ints




-- and for the shared non-primitive enums




-- and variables for those locks that are not linked to any variables
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
,
    enums : (nodes-> EnumVar) -> one Enum ,
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
	/* 
        no (local & env)
    */
}

-- actions axioms
    fact Action_startThinking_Ax1{ all s:philMeta.nodes | all s':philMeta.ACTstartThinking[s] | (((Val_st[philMeta,s] = Eating))) implies (((Val_st[philMeta,s'] = Thinking) and (Av_left[philMeta,s']) and (Av_right[philMeta,s']))) } 
    fact Action_becomeHunrgy_Ax1{ all s:philMeta.nodes | all s':philMeta.ACTbecomeHunrgy[s] | (((Val_st[philMeta,s] = Thinking))) implies (((Val_st[philMeta,s'] = Hungry))) } 
    fact Action_getLeft_Ax1{ all s:philMeta.nodes | all s':philMeta.ACTgetLeft[s] | ((Av_left[philMeta,s] and ((Val_st[philMeta,s] = Hungry)))) implies ((Own_left[philMeta,s'])) } 
    fact Action_getRight_Ax1{ all s:philMeta.nodes | all s':philMeta.ACTgetRight[s] | ((Av_right[philMeta,s] and ((Val_st[philMeta,s] = Hungry)))) implies ((Own_right[philMeta,s'])) } 
    fact Action_eat_Ax1{ all s:philMeta.nodes | all s':philMeta.ACTeat[s] | (((Val_st[philMeta,s] = Hungry) and (Own_left[philMeta,s]) and (Own_right[philMeta,s]))) implies (((Val_st[philMeta,s'] = Eating))) }  

    fact Action_startThinking_Ax2{ all s:philMeta.nodes | (not (((Val_st[philMeta,s] = Eating)))) implies (no philMeta.ACTstartThinking[s])} 
    fact Action_becomeHunrgy_Ax2{ all s:philMeta.nodes | (not (((Val_st[philMeta,s] = Thinking)))) implies (no philMeta.ACTbecomeHunrgy[s])} 
    fact Action_getLeft_Ax2{ all s:philMeta.nodes | (not ((Av_left[philMeta,s] and ((Val_st[philMeta,s] = Hungry))))) implies (no philMeta.ACTgetLeft[s])} 
    fact Action_getRight_Ax2{ all s:philMeta.nodes | (not ((Av_right[philMeta,s] and ((Val_st[philMeta,s] = Hungry))))) implies (no philMeta.ACTgetRight[s])} 
    fact Action_eat_Ax2{ all s:philMeta.nodes | (not (((Val_st[philMeta,s] = Hungry) and (Own_left[philMeta,s]) and (Own_right[philMeta,s])))) implies (no philMeta.ACTeat[s])}  

    fact Action_startThinking_Ax3{ all s:philMeta.nodes | (((Val_st[philMeta,s] = Eating))) implies (some philMeta.ACTstartThinking[s])  } 
    fact Action_becomeHunrgy_Ax3{ all s:philMeta.nodes | (((Val_st[philMeta,s] = Thinking))) implies (some philMeta.ACTbecomeHunrgy[s])  } 
    fact Action_getLeft_Ax3{ all s:philMeta.nodes | ((Av_left[philMeta,s] and ((Val_st[philMeta,s] = Hungry)))) implies (some philMeta.ACTgetLeft[s])  } 
    fact Action_getRight_Ax3{ all s:philMeta.nodes | ((Av_right[philMeta,s] and ((Val_st[philMeta,s] = Hungry)))) implies (some philMeta.ACTgetRight[s])  } 
    fact Action_eat_Ax3{ all s:philMeta.nodes | (((Val_st[philMeta,s] = Hungry) and (Own_left[philMeta,s]) and (Own_right[philMeta,s]))) implies (some philMeta.ACTeat[s])  }  


-- resource axioms for booleans
-- similar axioms for those variables that are only locks, no data associated to them
    fact ResAx1 { all s:philMeta.nodes | Own_left[philMeta, s] implies (not Av_left[philMeta, s]) } fact ResAx1 { all s:philMeta.nodes | Own_right[philMeta, s] implies (not Av_right[philMeta, s]) } 
    fact ResAx2 { all s:philMeta.nodes | (not Own_left[philMeta,s]) iff (some philMeta.ACTchange_left[s]) }  fact ResAx2 { all s:philMeta.nodes | (not Own_right[philMeta,s]) iff (some philMeta.ACTchange_right[s]) }  
    fact ResAx3 { all s:philMeta.nodes | all s':philMeta.ACTchange_left[s] | Av_left[philMeta,s] iff (not Av_left[philMeta, s']) }fact ResAx3 { all s:philMeta.nodes | all s':philMeta.ACTchange_right[s] | Av_right[philMeta,s] iff (not Av_right[philMeta, s']) }  

-- these axioms state that local actions cannot change shared variables which locks are not owned by the process
    fact ResAx4 { all s:philMeta.nodes | all s':(philMeta.env[s] - philMeta.ACTchange_left[s]) | Av_left[philMeta,s] iff Av_left[philMeta, s'] }fact ResAx4 { all s:philMeta.nodes | all s':(philMeta.env[s] - philMeta.ACTchange_right[s]) | Av_right[philMeta,s] iff Av_right[philMeta, s'] } 


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
 
    fact FrameAxiomsstartThinking{ 
            }

    fact FrameAxiomsbecomeHunrgy{ 
                    all s:philMeta.nodes | all s':philMeta.ACTbecomeHunrgy[s] | 
                (Av_left[philMeta,s] iff Av_left[philMeta, s']) and (Av_right[philMeta,s] iff Av_right[philMeta, s']) 
                and
                (Own_left[philMeta,s] iff Own_left[philMeta, s']) and (Own_right[philMeta,s] iff Own_right[philMeta, s'])
            }

    fact FrameAxiomsgetLeft{ 
                all s:philMeta.nodes | all s':philMeta.ACTgetLeft[s] | (Val_st[philMeta,s] = Val_st[philMeta, s'])
                    and 
                    all s:philMeta.nodes | all s':philMeta.ACTgetLeft[s] | 
                (Av_right[philMeta,s] iff Av_right[philMeta, s']) 
                and
                (Own_right[philMeta,s] iff Own_right[philMeta, s'])
            }

    fact FrameAxiomsgetRight{ 
                all s:philMeta.nodes | all s':philMeta.ACTgetRight[s] | (Val_st[philMeta,s] = Val_st[philMeta, s'])
                    and 
                    all s:philMeta.nodes | all s':philMeta.ACTgetRight[s] | 
                (Av_left[philMeta,s] iff Av_left[philMeta, s']) 
                and
                (Own_left[philMeta,s] iff Own_left[philMeta, s'])
            }

    fact FrameAxiomseat{ 
                    all s:philMeta.nodes | all s':philMeta.ACTeat[s] | 
                (Av_left[philMeta,s] iff Av_left[philMeta, s']) and (Av_right[philMeta,s] iff Av_right[philMeta, s']) 
                and
                (Own_left[philMeta,s] iff Own_left[philMeta, s']) and (Own_right[philMeta,s] iff Own_right[philMeta, s'])
            }



-- frame axioms for locks (shared vars)
fact FrameAxiomsleft{ 
    all s:philMeta.nodes | all s':philMeta.ACTchange_left[s] | (Own_left[philMeta,s] iff Own_left[philMeta, s'])
      
             and 
              (Val_st[philMeta,s] = Val_st[philMeta, s'])
            and
        (Av_right[philMeta,s] iff Av_right[philMeta, s']) 
            and
         (Own_right[philMeta,s] iff Own_right[philMeta, s'])
    }
fact FrameAxiomsright{ 
    all s:philMeta.nodes | all s':philMeta.ACTchange_right[s] | (Own_right[philMeta,s] iff Own_right[philMeta, s'])
      
             and 
              (Val_st[philMeta,s] = Val_st[philMeta, s'])
            and
        (Av_left[philMeta,s] iff Av_left[philMeta, s']) 
            and
         (Own_left[philMeta,s] iff Own_left[philMeta, s'])
    }

-- for volatile vars we just say that local and non-volatile vars are not changed by the environmental methods that change volatile vars


pred Form0[i:philMeta, s:Node]{
 some s':(*(philMeta.succs)[s]) | (Val_st[philMeta,s'] = Eating)}

-- Pred with inital condition and Invariants
pred Mod[s:philMeta.nodes]{ 
    -- all s':(*(philMeta.succs)[s]) | some philMeta.succs[s'] -- if ew want any node has a succ
     Form0[philMeta,s]  
    (((Val_st[philMeta,s] = Thinking)) and (Av_left[philMeta,s])) and (Av_right[philMeta,s])

}

run Mod for 14
