spec arbiter

tokenb1,tokenb2:prim_boolean;


process process1{
	g,r1:boolean;
    init:  !global.tokenb1 && !global.tokenb2 && !this.g && this.r1; 

    action getRequest(){
        frame: r1;
        pre:  !this.r1;
        post: this.r1;
    }
    
    
    action giveGrant(){
        frame: g;
        pre : !global.tokenb1 && !global.tokenb2 && this.r1 && !this.g;
        post: this.g;
    }
	action	passToken () {
				frame:  tokenb1, g, r1;
				pre: !global.tokenb1 && !global.tokenb2 && this.g;
				post: global.tokenb1 && !this.g && !this.r1;
    }
    

    invariant: AG[!this.r1 || EF[this.g]];
}

process process2{
	g,r1:boolean;
    init:  !global.tokenb1 && !global.tokenb2 && !this.g && this.r1; 

    action getRequest(){
        frame: r1;
        pre:  !this.r1;
        post: this.r1;
    }
    
    
    action giveGrant(){
        frame: g;
        pre : global.tokenb1 && !global.tokenb2 && this.r1 && !this.g;
        post: this.g;
    }
	action	passToken () {
				frame:  tokenb1, tokenb2, g, r1;
				pre: global.tokenb1 && !global.tokenb2 && this.g;
				post: !global.tokenb1 && global.tokenb2 && !this.g && !this.r1;
    }
    

    invariant: AG[!this.r1 || EF[this.g]];
}

process process3{
	g,r1:boolean;
    init:  !global.tokenb1 && !global.tokenb2 && !this.g && this.r1; 

    action getRequest(){
        frame: r1;
        pre:  !this.r1;
        post: this.r1;
    }
    
    action giveGrant(){
        frame: g;
        pre : !global.tokenb1 && global.tokenb2 && this.r1 && !this.g;
        post: this.g;
    }
	action	passToken () {
				frame:  tokenb2,  g, r1;
				pre: !global.tokenb1 && global.tokenb2 && this.g;
				post: !global.tokenb2  && !this.g && !this.r1;
    }
    

    invariant: AG[!this.r1 || EF[this.g]];
}



main(){
    p1:process1;
    p2:process2;
    p3:process3;
    run p1();
    run p2();
    run p3();
    
} 

/* Temporal Spec */

property:  AG[!(p1.g && p2.g) && !(p2.g&&p3.g) && !(p1.g && p3.g)] && AG[!p1.r1 || EF[p1.g]] && AG[!p2.r1 || EF[p2.g]];
