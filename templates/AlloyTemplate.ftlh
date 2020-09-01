
<#-- This template is used to generated the Alloy Specs  -->
<#-- Author: Pablo Castro -->

<#-- some basic definitions -->
<#assign boolProps0 = boolProps?map(x->x.name)>
<#assign intVars0 = intVars?map(x->x.name)>
<#assign enumVars0 = enumVars?map(x->x.name)>
<#assign sharedBoolProps0 = sharedBoolProps?map(x->x.name)>
<#assign sharedIntVars0 = sharedIntVars?map(x->x.name)>
<#assign sharedEnumVars0 = sharedEnumVars?map(x->x.name)>
<#assign sharedPrimBoolProps0 = sharedPrimBoolProps?map(x->x.name)>
<#assign sharedPrimIntVars0 = sharedPrimIntVars?map(x->x.name)>
<#assign sharedPrimEnumVars0 = sharedPrimEnumVars?map(x->x.name)>
<#assign onlyLocks0 = onlyLocks?map(x->x.name)>


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
<#list boolProps0 as p>
one sig Prop_${p} extends Prop{}
</#list>

-- for enum vars
<#list enumVars0 as e>
one sig EnumVar_${e} extends EnumVar{}
</#list>

-- for int vars
<#list intVars0 as i>
one sig NumVar_${i} extends NumVar{}
</#list>

-- definition of the global propositions 
<#list sharedBoolProps0 as p>
one sig Prop_${p} extends Prop{}
</#list>

-- definition of the global volatile propositions 
<#list sharedPrimBoolProps0 as p>
one sig Prop_${p} extends Prop{}
</#list>

-- definition of global ints 
<#list sharedIntVars0 as i>
one sig NumVar_${i} extends NumVar{}
</#list>

-- definition of global volatile ints 
<#list sharedPrimIntVars0 as i>
one sig NumVar_${i} extends NumVar{}
</#list>

-- definition of global enums 
<#list sharedEnumVars0 as e>
one sig EnumVar_${e} extends EnumVar{}
</#list>

-- definition of global volatile enums 
<#list sharedPrimEnumVars0 as e>
one sig EnumVar_${e} extends EnumVar{}
</#list>

-- definition of the enums, one enum for each possible value
<#list enumTypes as t>
one sig ${t.name} extends Enum{}
</#list>

<#list boolProps0 as p>
pred Prop_${p} [m:${name}Meta,n:Node]{Prop_${p} in m.val[n] }
</#list>

<#list intVars0 as i>
fun Val_${i}[m:${name}Meta,n:Node]:Int {m.ints[n][NumVar_${i}] }
</#list>

<#list enumVars0 as e>
fun Val_${e}[m:<name>Meta,n:Node]:Enum {m.enums[n][EnumVar_${e}] }
</#list>

<#list sharedBoolProps0 as p>
pred Prop_${p}[m:<name>Meta,n:Node]{Prop_${p} in m.val[n] }
</#list>

<#list sharedEnumVars0 as e>
fun Val_${e}[m:<name>Meta,n:Node]{m.enum[n][EnumVar_${e}] }
</#list>

<#list sharedPrimBoolProps0 as p>
pred Prop_${p}[m:<name>Meta,n:Node]{Prop_${p} in m.val[n] }
</#list>

<#list sharedPrimIntVars0 as i>
fun Val_${i}[m:<name>Meta,n:Node]{m.ints[n][NumVar_${i}] }
</#list>

<#list sharedPrimEnumVars0 as e>
fun Val_${e}[m:<name>Meta,n:Node]{m.enums[n][EnumVar_${e}] }
</#list>

-- additional vars for shared non-primitive vars representing the locks associated to each of them

<#list sharedBoolProps0 as p>
one sig Av_${p} extends Prop{}
</#list>

<#list sharedBoolProps0 as p>
one sig Own_${p} extends Prop{}
</#list>

<#list sharedBoolProps0 as p>
pred Av_${p}[m:<name>Meta, n:Node]{Av_${p} in m.val[n]}
</#list>

<#list sharedBoolProps0 as p>
pred Own_${p}[m:<name>Meta, n:Node]{Own_${p} in m.val[n]}
</#list>

-- and for the shared non-primitive ints

<#list sharedIntVars0 as i>
one sig Av_${i} extends Prop{}
</#list>

<#list sharedIntVars0 as i>
one sig Own_${i} extends Prop{}
</#list>

<#list sharedIntVars0 as i>
pred Av_${i} [m:<name>Meta, n:Node]{Av_${i} in m.val[n]}
</#list>

<#list sharedIntVars0 as i>
pred Own_${i}[m:<name>Meta, n:Node]{Own_${i} in m.val[n]}
</#list>

-- and for the shared non-primitive enums

<#list sharedEnumVars0 as e>
one sig Av_${e} extends Prop{}
</#list>

<#list sharedEnumVars0 as e>
one sig Own_${e} extends Prop{}
</#list>

<#list sharedEnumVars0 as e>
pred Av_${e}[m:<name>Meta, n:Node]{Av_${e} in m.val[n]}
</#list>

<#list sharedEnumVars0 as e>
pred Own_${e}[m:<name>Meta, n:Node]{Own_${e} in m.val[n]}
</#list>

<#list onlyLocks0 as l>
one sig Av_${l} extends Prop{}
</#list>

<#list onlyLocks0 as l>
one sig Own_${l} extends Prop{}
</#list>

<#list onlyLocks0 as l>
pred Av_${l}[m:${name}Meta, n:Node]{Av_${l} in m.val[n]}
</#list>

<#list onlyLocks0 as l>
pred Own_${l}[m:${name}Meta, n:Node]{Own_${l} in m.val[n]}
</#list>

<#list auxVars as s>
 ${s}
</#list>

one sig ${name}Meta{
	nodes:set Node,
	val: nodes -> Prop,
    <#if containsInts> ints: (nodes -> NumVar) -> one Int, </#if>
    <#if containsEnums> enums : (nodes-> EnumVar) -> one Enum </#if>
	succs : nodes -> nodes,
	local: nodes -> nodes,
	env: nodes -> nodes,
    <#list actions as a>
    ACT${a.name}:nodes ->nodes,    
    </#list>
    <#list sharedBoolProps0 as p>
    ACTchange_${p}:nodes -> nodes,    
    </#list>
    <#list onlyLocks0 as l>
    ACTchange_${l}:nodes -> nodes,  
    </#list>
    <#list sharedIntVars0 as i>
    ACTchange_${i}:nodes -> nodes,
    </#list>
    <#list sharedEnumVars0 as e>
    ACTchange_${e}:nodes -> nodes,
    </#list>
    <#list sharedPrimBoolProps0 as b>
    ACTchange_${b}:nodes -> nodes,
    </#list>
    <#list sharedPrimIntVars0 as i>
    ACTchange_${i}:nodes -> nodes,
    </#list>
    <#list sharedPrimEnumVars0 as e>
    ACTchange_${e}:nodes -> nodes,
    </#list>
}
{
    <#assign localActions = actions?map(a->"ACT"+a.name)>
    <#assign globalActions0 = sharedBoolProps0+onlyLocks0+sharedIntVars0+sharedEnumVars0+sharedPrimBoolProps0+sharedPrimIntVars0+sharedPrimEnumVars0>
    <#assign globalActions = globalActions0?map(a->"ACTchange_"+a)>
    <#assign allActions = globalActions+localActions>   
    <#if allActions?size !=0>
        succs = ${allActions?join("+")}
    </#if>
    <#if localActions?size != 0>
        local = ${localActions?join("+")}
    </#if>
    <#if globalActions?size != 0>
        env = ${globalActions?join("+")}
    </#if>
    <#list auxAxioms as a>
        ${a}
    </#list>     
}

-- actions axioms
<#if actions?size != 0>
    <#list actions as a>
        fact Action_${a.name}_Ax1{all s:${name}Meta.nodes | all s':${name}Meta.ACT${a.name}[s] | ${a.pre} implies ${a.post} }
    </#list>
    <#list actions as a>
        fact Action_${a.name}_Ax2{ all s:${name}Meta.nodes | (not ${a.pre}) implies (no ${name}Meta.ACT${a.name}[s])} 
    </#list>
     <#list actions as a>
        fact Action_${a.name}_Ax3{ all s:${name}Meta.nodes | ${a.pre} implies (some ${name}Meta.ACT${a.name}[s])  }
    </#list>
</#if>

-- resource axioms for global variables
<#if globalActions0?size != 0>
    <#list globalActions0 as a>
       fact ResAx1 { all s:${name}Meta.nodes | Own_${a}[${name}Meta, s] implies (not Av_${a}[${name}Meta, s]) }
    </#list>
    <#list globalActions0 as a>
       fact ResAx2 { all s:${name}Meta.nodes | (not Own_${a}[${name}Meta,s]) iff (some ${name}Meta.ACTchange_${a}[s]) } 
    </#list>
     <#list globalActions0 as a>
       fact ResAx3 { all s:${name}Meta.nodes | all s':${name}Meta.ACTchange_${a}[s] | Av_${a}[${name}Meta,s] iff (not Av_${a}[${name}Meta, s']) }
    </#list>
</#if>

-- Axioms stating that local actions cannot change shared variables whose locks are not owned by the process
<#if sharedBoolProps?size != 0>
   <#list sharedBoolsProps0 as p>
        fact ResAx4 {  all s:${name}Meta.nodes | (not Own_${p}[${name}Meta,s]) implies (all s':${name}Meta.local[s] | (Prop_${p}[<name>Meta,s] iff Prop_${p}[${name}Meta,s']) ) }
   </#list>
</#if>

-- similar for enums and ints
<#if (sharedEnumVars+sharedIntVars)?size != 0>
    <#list sharedEnumVars0+sharedIntVars0 as e>
        fact ResAx4 {  all s:${name}Meta.nodes | (not Own_${e}[${name}Meta,s]) implies (all s':${name}Meta.local[s] | (Val_${e}[${name}Meta,s] iff Val_${e}[${name}Meta,s']) ) }
    </#list>
</#if>

<#if globalActions0?size != 0>
    <#list globalActions0 as g>
    fact ResAx4 { all s:${name}Meta.nodes | all s':(${name}Meta.env[s] - ${name}Meta.ACTchange_${g}[s]) | Av_${g}[${name}Meta,s] iff Av_${g}[${name}Meta, s'] } 
    </#list>
</#if>

-- the following axioms state that environment actions are unrestricted for booleans
<#if sharedBoolProps?size != 0>
    <#list sharedBoolProps0 as p>
        fact ResAx5 { all s:${name}Meta.nodes | ((not Own_${p}[${name}Meta,s]) and (not Av_${sh}[${name}Meta,s])) implies (some s':(*(${name}Meta.ACTchange_${p})[s]) | Prop_${p}[<name>Meta,s']) }
    </#list>
     <#list sharedBoolProps0 as p>
        fact ResAx6 { all s:${name}Meta.nodes | ((not Own_${p}[${name}Meta,s]) and (not Av_${p}[${name}Meta,s])) implies (some s':(*(${name}Meta.ACTchange_${p})[s]) | not Prop_${p}[${name}Meta,s']) }} > 
    </#list>   
</#if>

-- similarly for volatile booleans
<#if sharedPrimBoolProps?size !=0>
    <#list sharedPrimBoolProps0 as p>
        fact ResAx5 { all s:${name}Meta.nodes | (some s':${name}Meta.ACTchange_${p}[s] | Prop_${p}[${name}Meta,s'])}  
        fact ResAx6 { all s:${name}Meta.nodes | (some s':${name}Meta.ACTchange_${p}[s] | not Prop_${p}[${name}Meta,s']) }
    </#list>
</#if>

-- axioms stating that environment actions are not restricted for ints
<#if sharedIntVars?size != 0>
    <#list sharedIntVars0 as v>
        <#list intSet as i>
            fact ResIntAx${i} { all s:${name}Meta.nodes | (not Own_${v}[${name}Meta,s]) implies  (some s':${name}Meta.ACTchange_${v}[s] | Val_${v}[${name}Meta,s']=${i} }
        </#list>
    </#list>
</#if>

-- and similar for volatile ints
<#if sharedPrimIntVars?size != 0>
    <#list sharedPrimIntVars0 as v>
        <#list intSet as i>
            fact ResPrimIntAx${i} { all s:${name}Meta.nodes  | (some s':${name}Meta.ACTchange_${v}[s] | Val_${v}[${name}Meta,s']=${i} }
        </#list>
    </#list>
</#if>

-- axioms stating that environment actions are not restricted for enums
<#if sharedEnumVars?size != 0>
    <#list sharedEnumVars as e>
        <#list e.values as v>
            fact ResEnumAx${v} { all s:${name}Meta.nodes | (not Own_${e.name}[${name}Meta,s]) implies  (some s':${name}Meta.ACTchange_${e.name}[s] | Val_${e.name}[${name}Meta,s']=${v} }
        </#list>
    </#list>
</#if>

--- and similar for volatile enums
<#if sharedPrimEnumVars?size != 0>
    <#list sharedPrimEnumVars as e>
        <#list e.values as v>
            fact ResPrimEnumAx${v} { all s:${name}Meta.nodes  | (some s':${name}Meta.ACTchange_${e.name}[s] | Val_${e.name}[${name}Meta,s']=${v} }
        </#list>
    </#list>
</#if>

<#assign locks = onlyLocks0+sharedBoolProps0+sharedIntVars0+sharedEnumVars0>
<#assign lockProps = locks?map(x->"Av_"+x) + locks?map(x->"Own_"+x)>
<#assign lockActions = locks?map(x->"ACTchange_"+x)>
<#assign varVals = sharedEnumVars0 + sharedPrimEnumVars0 + sharedIntVars0 + sharedPrimIntVars0 + enumVars0 + intVars0>
<#assign varProps = sharedBoolProps0 + sharedPrimBoolProps0 + boolProps0>
<#assign localProps = boolProps0>
<#assign globalProps = sharedBoolProps0 + sharedPrimBoolProps0>
<#assign localVarVals = enumVars0 + intVars0>
<#assign globalVarVals = sharedEnumVars0 + sharedPrimEnumVars0 + sharedIntVars0 + sharedPrimIntVars0>
<#assign primVars = sharedPrimEnumVars0 + sharedPrimIntVars0>

-- frame axioms for local actions
<#list actions as a>
        fact frame${a.name}{  all s:${name}Meta.nodes |  all s':${name}Meta.ACT${a.name}[s] | true 
        <#list varVals?filter(x->!a.frame?seq_contains(x)) as v> 
                <#if v?is_first> and </#if>
                (Val_${v}[${name}Meta,s] = Val_${v}[${name}Meta, s']) <#sep> and </#sep>
        </#list>
        <#list varProps?filter(x->!a.frame?seq_contains(x)) as p>
                <#if p?is_first> and </#if>
                (Prop_${p}[${name}Meta,s] iff Prop_${p}[${name}Meta,s'])
                <#sep> and </#sep>
        </#list>
        <#list locks?filter(x->!a.frame?seq_contains(x)) as l>
                <#if l?is_first> and </#if>
                (Own_${l}[${name}Meta,s] iff Own_${l}[${name}Meta,s']) and  (Av_${l}[${name}Meta,s] iff Av_${l}[${name}Meta,s'])
                <#sep> and </#sep>
        </#list>
        }
</#list>

-- frame axioms for global actions
<#list locks as l>
    fact frameAxioms${l}{
     all s:${name}Meta.nodes | all s':${name}Meta.ACTchange_${l}[s] | (Own_${l}[${name}Meta,s] iff Own_${l}[${name}Meta, s'])
     <#list varProps as p>
        and (Prop_${p}[${name}Meta,s] iff Prop_${p}[${name}Meta,s'])
     </#list>
     <#list varVals as v>
        and val_${v}[${name}Meta,s] = val_${v}[${name}Meta,s]
     </#list>
     <#list locks as l1>
        <#if l!=l1>
        and (Av_${l1}[${name}Meta,s] iff Av_${l1}[${name}Meta,s']) and (Own_${l1}[${name}Meta,s] iff Av_${l1}[${name}Meta,s'])
        </#if>
     </#list>
     }
</#list>

-- for prim vars we say that the environmental actions do not change the rest of the variables
<#list primVars as p>
    fact primVarFrame${p}
     all s:${name}Meta.nodes | all s':${name}Meta.ACTchange_${p}[s] | true
     <#list varProps as p0>
        <#if p!=p0> and (Prop_${p}[${name}Meta,s] iff Prop_${p}[${name}Meta,s']) </#if>
     </#list>
     <#list varVals as v>
        <#if p!=v> and (Val${v}[${name}Meta,s] iff Val_${v}[${name}Meta,s']) </#if>
     </#list>
     <#list locks as l>
         and (Av_${l}[${name}Meta,s] iff Av_${l}[${name}Meta,s']) and (Own_${l}[${name}Meta,s] iff Av_${l}[${name}Meta,s'])
     </#list>
     }
</#list>

--auxiliary predicates
<#list auxPreds as p>
    ${p}
</#list>

-- Pred with inital condition and Invariants
pred Mod[s:${name}Meta.nodes]{ 
    -- all s':(*(${name}Meta.succs)[s]) | some ${name}Meta.succs[s'] -- if we want, any node has a succ
    <#list invariants as i>
        ${i}
    </#list>
    ${init}
    
}

run Mod for ${scope}














