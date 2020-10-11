spec arbiter

token, g1, g2, r1, r2:prim_boolean;

process envR1{
    owns: r1;
    init: !global.r1;
    
    action requestR1(){
        frame: r1;
        pre: !global.r1;
        post: global.r1;
    }
    
    action downR1(){
        frame: r1;
        pre: global.r1;
        post: !global.r1;
    }
    
    invariant: AG[EF[global.r1]] && AG[EF[global.r1]];
}

process envR2{
    owns: r2;
    init: !global.r2;
    
    action requestR2(){
        frame: r2;
        pre: !global.r2;
        post: global.r2;
    }
    
    action downR1(){
        frame: r2;
        pre: global.r2;
        post: !global.r2;
    }
    
    invariant: AG[EF[global.r2]] && AG[EF[global.r2]];
}



process process1{
    owns: g1;
    init:  !global.token && !global.g1; 
    
    action giveGrant(){
        frame: g1;
        pre : !global.token;
        post: global.g1;
    }
	action	passToken () {
				frame:  token, g1;
				pre: !global.token && global.g1;
				post: global.token && !global.g1;
    }
    

    invariant: AG[!global.r1 || EF[global.g1]];
}

process process2{
	owns: g2;
    init:  global.token && !global.g2; 
    
    action giveGrant(){
        frame: g2;
        pre : global.token;
        post: global.g2;
    }
	action	passToken () {
				frame:  token, g2;
				pre: global.token && global.g2;
				post: !global.token && !global.g2;
    }
    

    invariant: AG[!global.r2 || EF[global.g2]];
}



main(){
    p1:process1;
    p2:process2;
    e1:envR1;
    e2:envR2;
    run p1();
    run p2();
    run e1();
    run e2();
    
} 

/* Temporal Spec */

property:  AG[!(global.g1 && global.g2)] && AG[!global.r1 || EF[global.g1]] && AG[!global.r2 || EF[global.g2]];
