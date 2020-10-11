spec arbiter

token:prim_boolean;


process process1{
	g,r1:boolean;
    init:  !global.token && !this.g && this.r1; 

    action getRequest(){
        frame: r1;
        pre:  !this.r1;
        post: this.r1;
    }
    
    
    action giveGrant(){
        frame: g;
        pre : !global.token && this.r1 && !this.g;
        post: this.g;
    }
	action	passToken () {
				frame:  token, g, r1;
				pre: !global.token && this.g;
				post: global.token && !this.g && !this.r1;
    }
    

    invariant: AG[!this.r1 || EF[this.g]];
}

process process2{
	g,r1:boolean;
    init:  global.token && !this.g && this.r1; 

    action getRequest(){
        frame: r1;
        pre:  !this.r1;
        post: this.r1;
    }
    
    
    action giveGrant(){
        frame: g;
        pre : global.token && this.r1 && !this.g;
        post: this.g;
    }
	action	passToken () {
				frame:  token, g, r1;
				pre: global.token && this.g;
				post: !global.token && !this.g && !this.r1;
    }
    

    invariant: AG[!this.r1 || EF[this.g]];
}



main(){
    p1:process1;
    p2:process2;
    run p1();
    run p2();
    
} 


/* Assumption: */
/* Temporal Spec */
property:  AG[!(p1.g && p2.g)] && AG[!p1.r1 || EF[p1.g]] && AG[!p2.r1 || EF[p2.g]];
