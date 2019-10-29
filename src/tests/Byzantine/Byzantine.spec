spec byzantine
/* 1 is an attack message 0 is retray */
/* we consider only 4 generals adn 1 traitor for this version */

mgc1: prim_boolean; /* represent the messages to the other commanders */

process general{
    td,d,tr:boolean; /* d:the decision td: if the decision have been taken, tr: if it is a traitor */
    owns:mgc1;
    init: !this.d && !this.td && !this.tr && !global.mgc1;
    action decideAttack(){
        frame: d,td;
        pre: !this.td;
        post: this.td && this.d; /* take some decision */
    }
    
    action decideRetray(){
        frame: d,td;
        pre: !this.td;
        post: this.td && !this.d; /* take some decision */
    }
    
    action betray(){
        frame: tr;
        pre: !this.tr && !this.td;
        post: this.tr;
    }
    
    action sendMAttack(){
        frame: mgc1;
        pre: this.td && this.d && !this.tr;
        post: global.mgc1 ;
    }
    
    action sendMRetray(){
        frame: mgc1;
        pre: this.td && !this.d && !this.tr;
        post: !global.mgc1;
    }
    
    action lyeAttack(){ 
        frame: mgc1,tr;
        pre: this.tr && this.td && this.d;
        post: this.tr && !global.mgc1;
    }
     action lyeRetray(){ 
        frame: mgc1,tr;
        pre: this.tr && this.td && !this.d;
        post: this.tr && global.mgc1;
    }
    
    invariant: AG[!this.tr || AG[this.tr]] && AG[!this.td || (this.d && AG[this.d]) || (!this.d && AG[!this.d])] && EF[this.d] && EF[!this.d] && AG[!(this.td && !this.tr) || AX[!this.tr]];
}

process commander1{
    d,td,tr:boolean; /* d:the decision td: if the decision have been taken, tr: if it is a traitor */
    init: !this.d && !this.td && !this.tr && !global.mgc1;
    action decideAttack(){
        frame: d,td;
        pre: !this.td;
        post: this.td && this.d; /* take some decision, here the syntehsized code will should tae the correct decision: majority */
    }
    
    action decideRetray(){
        frame: d,td;
        pre: !this.td;
        post: this.td && !this.d; /* take some decision, here the syntehsized code will should tae the correct decision: majority */
    }
    
    action betray(){
        frame: tr;
        pre: !this.tr;
        post: this.tr;
    }
    
    invariant: AG[!this.tr || AG[this.tr]] && AG[!this.td || (this.d && AG[this.d]) || (!this.d && AG[!this.d])] && AG[!(this.td && !this.tr) || AX[!this.tr]];
}

main(){
	g1:general;
    c1:commander1;
    run g1();
    run c1();
}
property: !EF[g1.td && g1.d && !c1.tr && c1.td && !c1.d] && !EF[g1.td && !g1.d && !c1.tr && c1.td && c1.d];