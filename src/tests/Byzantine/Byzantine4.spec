spec byzantine
/* 1 is an attack message 0 is retray */
/* we consider only 4 generals adn 1 traitor for this version */

mgc1,mgc2,mgc3,mc1c2,mc1c3,mc2c1,mc2c3,mc3c1,mc3c2: prim_boolean; /* represent the messages to the other commanders */

process general{
    td,d,tr:boolean; /* d:the decision td: if the decision have been taken, tr: if it is a traitor */
    owns:mgc1,mgc2,mgc3;
    init: !this.d && !this.td && !this.tr && !global.mgc1 && !global.mgc2 && !global.mgc3 && !global.mc1c2 && !global.mc1c3 && !global.mc2c1 && !global.mc2c3 && !global.mc3c1 && !global.mc3c2;
    action decide(){
        frame: d,td;
        pre: !this.td;
        post: this.td; /* take some decision */
    }
    
    action betray(){
        frame: tr;
        pre: !this.tr;
        post: this.tr;
    }
    
    action sendMAttack(){
        frame: mgc1, mgc2,mgc3;
        pre: !this.tr && this.d;
        post: global.mgc1 && global.mgc2 && global.mgc3;
    }
    
    action sendMRetray(){
        frame: mgc1, mgc2,mgc3;
        pre: !this.tr && !this.d;
        post: !global.mgc1 && !global.mgc2 && !global.mgc3;
    }
    
    action lyeAttack(){ 
        frame: mgc1, mgc2,mgc3,tr;
        pre: this.tr && this.d;
        post: this.tr;
    }
    
    invariant: AG[!this.tr || AG[this.tr]] && AG[!this.td || (this.d && AG[this.d]) || (!this.d && AG[!this.d])] && EF[this.d] && EF[!this.d];
}

process commander1{
    d,td,tr:boolean; /* d:the decision td: if the decision have been taken, tr: if it is a traitor */
    owns:mc1c2,mc1c3;
    init: !this.d && !this.td && !this.tr && !global.mgc1 && !global.mgc2 && !global.mgc3 && !global.mc1c2 && !global.mc1c3 && !global.mc2c1 && !global.mc2c3 && !global.mc3c1 && !global.mc3c2;
    action decide(){
        frame: d,td;
        pre: !this.td;
        post: this.td; /* take some decision, here the syntehsized code will should tae the correct decision: majority */
    }
    
    action betray(){
        frame: tr;
        pre: !this.tr;
        post: this.tr;
    }
    
    action sendMAttack(){
        frame: mc1c2, mc1c3;
        pre: !this.tr && global.mgc1;
        post: global.mc1c2 && global.mc1c3;
    }
    
    action sendMRetray(){
        frame: mc1c2, mc1c3;
        pre: !this.tr && !global.mgc1;
        post: !global.mc1c2 && !global.mc1c3;
    }
    
    action lye(){ 
        frame: mc1c2, mc1c3,tr;
        pre: this.tr;
        post: this.tr;
    }
    
    invariant: AG[!this.tr || AG[this.tr]] && AG[!this.td || (this.d && AG[this.d]) || (!this.d && AG[!this.d])] && EF[this.d];
}

process commander2{
    d,td,tr:boolean; /* d:the decision td: if the decision have been taken, tr: if it is a traitor */
    owns:mc2c1,mc2c3;
    init: !this.d && !this.td && !this.tr && !global.mgc1 && !global.mgc2 && !global.mgc3 && !global.mc1c2 && !global.mc1c3 && !global.mc2c1 && !global.mc2c3 && !global.mc3c1 && !global.mc3c2;
    action decide(){
        frame: d,td;
        pre: !this.td;
        post: this.td; /* take some decision, here the syntehsized code will should tae the correct decision: majority */
    }
    
    action betray(){
        frame: tr;
        pre: !this.tr;
        post: this.tr;
    }
    
    action sendMAttack(){
        frame: mc2c1, mc2c3;
        pre: !this.tr && global.mgc2;
        post: global.mc2c1 && global.mc2c3;
    }
    
    action sendMRetray(){
        frame: mc2c1, mc2c3;
        pre: !this.tr && !global.mgc2;
        post: !global.mc2c1 && !global.mc2c1;
    }
    
    action lye(){ 
        frame: mc2c1, mc2c3,tr;
        pre: this.tr;
        post: this.tr;
    }
    
    invariant: AG[!this.tr || AG[this.tr]] && AG[!this.td || (this.d && AG[this.d]) || (!this.d && AG[!this.d])];
}

process commander3{
    d,td,tr:boolean; /* d:the decision td: if the decision have been taken, tr: if it is a traitor */
    owns:mc3c1,mc3c2;
    init: !this.d && !this.td && !this.tr &&  !global.mgc1 && !global.mgc2 && !global.mgc3 && !global.mc1c2 && !global.mc1c3 && !global.mc2c1 && !global.mc2c3 && !global.mc3c1 && !global.mc3c2;
    action decide(){
        frame: d,td;
        pre: !this.td;
        post: this.td; /* take some decision, here the syntehsized code will should tae the correct decision: majority */
    }
    
    action betray(){
        frame: tr;
        pre: !this.tr;
        post: this.tr;
    }
    
    action sendMAttack(){
        frame: mc3c1, mc3c2;
        pre: !this.tr && global.mgc3;
        post: global.mc3c1 && global.mc3c2;
    }
    
    action sendMRetray(){
        frame: mc3c1, mc3c2;
        pre: !this.tr && !global.mgc3;
        post: !global.mc3c1 && !global.mc3c2;
    }
    
    action lye(){ 
        frame: mc3c1, mc3c2,tr;
        pre: this.tr;
        post: this.tr;
    }
    
    invariant: AG[!this.tr || AG[this.tr]] && AG[!this.td || (this.d && AG[this.d]) || (!this.d && AG[!this.d])] && EF[this.d];
}


main(){
	g1:general;
    c1:commander1;
    c2:commander2;
    c3:commander3;
    run g1();
    run c1();
    run c2();
    run c3();
}
property: !EF[g1.td && g1.d && !c1.tr && c1.td && !c1.d] && !EF[g1.td && g1.d && !c1.tr && c1.td && !c1.d];
/*property: AG[!g1.td || (g1.tr || (g1.d && AF[c1.tr || c1.d] && AF[c2.tr || c2.d] && AF[c3.tr || c3.d]) || (!g1.d && AF[c1.tr || !c1.d] && AF[c2.tr || !c2.d] && AF[c3.tr || !c3.d]))];*/
