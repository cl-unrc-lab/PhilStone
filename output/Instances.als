abstract sig Node{}
one sig Node14 extends Node{}
one sig Node13 extends Node{}
one sig Node16 extends Node{}
one sig Node15 extends Node{}
one sig Node10 extends Node{}
one sig Node12 extends Node{}
one sig Node11 extends Node{}
one sig Node9 extends Node{}
one sig Node8 extends Node{}
one sig Node7 extends Node{}
one sig Node6 extends Node{}
one sig Node5 extends Node{}
one sig Node4 extends Node{}
one sig Node17 extends Node{}
one sig Node3 extends Node{}
one sig Node2 extends Node{}
one sig Node1 extends Node{}
one sig Node0 extends Node{}
abstract sig Prop{}
one sig Av_tlane extends Prop{}
pred Av_tlane[m:InstanceparkingAirplane,n:Node]{Av_tlane in m.val[n]}
one sig Own_freeLane extends Prop{}
pred Own_freeLane[m:InstanceparkingAirplane,n:Node]{Own_freeLane in m.val[n]}
one sig Av_llane extends Prop{}
pred Av_llane[m:InstanceparkingAirplane,n:Node]{Av_llane in m.val[n]}
one sig Own_llane extends Prop{}
pred Own_llane[m:InstanceparkingAirplane,n:Node]{Own_llane in m.val[n]}
one sig Av_freeLane extends Prop{}
pred Av_freeLane[m:InstanceparkingAirplane,n:Node]{Av_freeLane in m.val[n]}
abstract sig Enum{}
one sig Touchdown extends Enum{}
one sig Parked extends Enum{}
one sig Tax16lc3 extends Enum{}
abstract sig EnumVar{}
one sig EnumVar_st extends EnumVar{}
fun  Val_st[m:InstanceparkingAirplane,n:Node]:Enum { m.enums[n][EnumVar_st]} 
one sig InstanceparkingAirplane{
    nodes : set Node,
    succs : nodes -> nodes,
    val: nodes -> Prop,
    enums : (nodes-> EnumVar) -> one Enum,
    ACTgetL1: nodes -> nodes,
    ACTexitRW3: nodes -> nodes,
    ACTcrossRW3: nodes -> nodes,
    ACTchange_llane: nodes -> nodes,
    ACTchange_tlane: nodes -> nodes,
    ACTchange_freeLane: nodes -> nodes,
    local: nodes -> nodes,
    env: nodes -> nodes
}
{
    nodes = Node14+Node13+Node16+Node15+Node10+Node12+Node11+Node9+Node8+Node7+Node6+Node5+Node4+Node17+Node3+Node2+Node1+Node0
    ACTgetL1 in (Node16->Node3) + (Node12->Node5)
    ACTexitRW3 in (Node5->Node1) + (Node3->Node4)
    ACTcrossRW3 in (Node4->Node17) + (Node0->Node15)
    ACTchange_llane = (Node14->Node13) + (Node13->Node14) + (Node15->Node17) + (Node10->Node9) + (Node9->Node10) + (Node8->Node6) + (Node6->Node8) + (Node4->Node0) + (Node17->Node15) + (Node2->Node1) + (Node1->Node2) + (Node0->Node4)
    ACTchange_tlane = (Node14->Node8) + (Node13->Node6) + (Node16->Node12) + (Node15->Node9) + (Node10->Node17) + (Node12->Node16) + (Node11->Node7) + (Node9->Node15) + (Node8->Node14) + (Node7->Node11) + (Node6->Node13) + (Node5->Node3) + (Node4->Node1) + (Node17->Node10) + (Node3->Node5) + (Node2->Node0) + (Node1->Node4) + (Node0->Node2)
    ACTchange_freeLane = (Node14->Node9) + (Node13->Node10) + (Node16->Node7) + (Node15->Node8) + (Node10->Node13) + (Node12->Node11) + (Node11->Node12) + (Node9->Node14) + (Node8->Node15) + (Node7->Node16) + (Node6->Node17) + (Node17->Node6)

    val =     Node13->Av_llane + Node16->Av_tlane + Node16->Av_freeLane + Node16->Own_llane + Node15->Av_tlane + Node15->Av_freeLane + Node10->Av_llane + Node10->Av_freeLane + Node12->Av_freeLane + Node12->Own_llane + Node11->Own_llane + Node9->Av_freeLane + Node8->Av_tlane + Node7->Av_tlane + Node7->Own_llane + Node6->Av_llane + Node6->Av_tlane + Node5->Own_llane + Node5->Own_freeLane + Node4->Av_llane + Node4->Av_tlane + Node4->Own_freeLane + Node17->Av_llane + Node17->Av_tlane + Node17->Av_freeLane + Node3->Av_tlane + Node3->Own_llane + Node3->Own_freeLane + Node2->Own_freeLane + Node1->Av_llane + Node1->Own_freeLane + Node0->Av_tlane + Node0->Own_freeLane
    enums = Node14->EnumVar_st->Parked + Node13->EnumVar_st->Parked + Node16->EnumVar_st->Touchdown + Node15->EnumVar_st->Parked + Node10->EnumVar_st->Parked + Node12->EnumVar_st->Touchdown + Node11->EnumVar_st->Touchdown + Node9->EnumVar_st->Parked + Node8->EnumVar_st->Parked + Node7->EnumVar_st->Touchdown + Node6->EnumVar_st->Parked + Node5->EnumVar_st->Touchdown + Node4->EnumVar_st->Tax16lc3 + Node17->EnumVar_st->Parked + Node3->EnumVar_st->Touchdown + Node2->EnumVar_st->Tax16lc3 + Node1->EnumVar_st->Tax16lc3 + Node0->EnumVar_st->Tax16lc3
    succs = ACTgetL1+ACTexitRW3+ACTcrossRW3+ACTchange_llane+ACTchange_tlane+ACTchange_freeLane
    env =ACTchange_tlane+ACTchange_llane+ACTchange_freeLane
    local = succs - env
(not (Node3 in succs[Node16]))and (not (Node5 in succs[Node12])) or (not (Node1 in succs[Node5]))and (not (Node4 in succs[Node3])) or (not (Node17 in succs[Node4]))and (not (Node15 in succs[Node0]))

}
pred Form4[i:InstanceparkingAirplane, s:Node]{
 some s':(*(InstanceparkingAirplane.succs)[s]) | (Val_st[InstanceparkingAirplane,s'] = Parked)}
pred compile[s:Node]{s=Node16
Form4[InstanceparkingAirplane,s]
}
run compile for 18 but 1 InstanceparkingAirplane
