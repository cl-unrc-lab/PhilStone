/* bits: b2 b1*/
spec arbiter


tokenb1,tokenb2,r1,r2,r3,r4:prim_boolean;


process process1{
	g:boolean;
    init:  !global.tokenb1 && !global.tokenb2 && !this.g && !global.r1; 
    
    action giveGrant(){
        frame: g;
        pre : !global.tokenb1 && !global.tokenb2;/* && global.r1 && !this.g;*/
        post: this.g;
    }
	action	passToken () {
				frame:  tokenb1, g;
				pre: !global.tokenb1 && !global.tokenb2 && this.g;
				post: global.tokenb1 && !this.g ;
    }
     action giveUpGrant(){
        frame: g;
        pre: !global.tokenb1 && !global.tokenb2;
        post: !this.g;
    }

    invariant: AG[!global.r1 || EF[this.g]];
}

process process2{
	g:boolean;
    init:  !global.tokenb1 && !global.tokenb2;/* && !this.g && !global.r2; */

    
    action giveGrant(){
        frame: g;
        pre : global.tokenb1 && !global.tokenb2 && global.r2 && !this.g;
        post: this.g;
    }
    
	action	passToken () {
				frame:  tokenb1, tokenb2, g;
				pre: global.tokenb1 && !global.tokenb2 && this.g;
				post: !global.tokenb1 && global.tokenb2 && !this.g;
    }
     action giveUpGrant(){
        frame: g;
        pre: global.tokenb1 && !global.tokenb2;
        post: !this.g;
    }

    invariant: AG[!global.r2 || EF[this.g]];
}

process process3{
	g:boolean;
    init:  !global.tokenb1 && !global.tokenb2 && !this.g && !global.r3; 
    
    
    action giveGrant(){
        frame: g;
        pre : !global.tokenb1 && global.tokenb2; /*&& global.r3 && !this.g;*/
        post: this.g;
    }
	action	passToken () {
				frame:   tokenb1,  g;
				pre: !global.tokenb1 && global.tokenb2 && this.g;
				post: global.tokenb1  && !this.g;
    }
     action giveUpGrant(){
        frame: g;
        pre: !global.tokenb1 && global.tokenb2;
        post: !this.g;
    }

    invariant: AG[!global.r3 || EF[this.g]];
}

process process4{
	g:boolean;
    init:  !global.tokenb1 && !global.tokenb2 && !this.g && !global.r4; 
    
    action giveGrant(){
        frame: g;
        pre : global.tokenb1 && global.tokenb2; /* && global.r4 && !this.g;*/
        post: this.g;
    }
	action	passToken () {
				frame:  tokenb2, tokenb1,  g;
				pre: global.tokenb1 && global.tokenb2;/* && this.g;*/
				post: !global.tokenb2  && !global.tokenb1 && !this.g;
    }
    
    action giveUpGrant(){
        frame: g;
        pre: global.tokenb1 && global.tokenb2;
        post: !this.g;
    }

    invariant: AG[!global.r4 || EF[this.g]];
}


main(){
    p1:process1;
    p2:process2;
    p3:process3;
    p4:process4;
    run p1();
    run p2();
    run p3();
    run p4();
    
} 

/* Temporal Spec */

property:  AG[!(p1.g && p2.g) && !(p2.g&&p3.g) && !(p1.g && p3.g) && !(p1.g && p4.g) && !(p2.g && p3.g) && !(p2.g && p4.g) && !(p3.g && p4.g)] && AG[!global.r1 || EF[p1.g]] && AG[!global.r2 || EF[p2.g]] && AG[!global.r3 || EF[p3.g]] && AG[!global.r4 || EF[p4.g]]
;