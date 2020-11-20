/* This is an implementation of N-Peterson based on tournaments, see the book of Lynch,
   processes are the leaves of the tree, and nodes takes the results up in the tree
*/
spec peterson

turn12, turn23, try1, try2, try3: prim_boolean;

process proc1{
    cs, presentp1n1: boolean;
    owns:  try1;
	init: !this.cs &&  !global.turn12 && !global.turn23 && !global.try1 && !this.presentp1n1; 

     action competeForN1(){
		frame: turn12, try1;
		pre: !this.cs && !global.try1 && !this.presentp1n1; 
		post: global.try1; /*global.turn12 && global.try1;*/
	}

	action enterN1(){
		frame: presentp1n1;
        pre: global.try1 && !this.cs && !this.presentp1n1;
		post: this.presentp1n1;
	}
    
    action competeForCS(){
		frame: turn23;
		pre: !this.cs && this.presentp1n1;
		post: global.turn23; /* turn23 gives the turn to process 3 */
	}
    
    action enterCS(){
		frame: cs;
		/*this condition will be synthesized: pre: (global.try2 && !this.cs && global.turn) || (!global.try1 && !this.cs && global.try2);*/
        pre: global.try1 && !this.cs;
		post: this.cs;
	}
    
    action leaveCS(){
        frame: cs,  try1, presentp1n1;
        pre: this.cs;
        post: !this.cs &&  !global.try1 && !this.presentp1n1;   
    }
   
	invariant: AG[!this.cs || EF[!this.cs]] && AG[EF[this.cs]];
}

process proc2{
    cs, presentp2n1:boolean;
    owns: try2;
	init: !this.cs &&  !global.turn12 && !global.turn23 && !global.try2 && !this.presentp2n1;

     action competeForN1(){
		frame: turn12, try2;
		pre: !this.cs && !global.try2 && !this.presentp2n1;
		post: global.try2; /* !global.turn12 && global.try2;*/
	}

	action enterN1(){
		frame: presentp2n1;
        pre: global.try2 && !this.cs && !this.presentp2n1;
		post: this.presentp2n1;
	}
    
    action competeForCS(){
		frame: turn23;
		pre: !this.cs &&  this.presentp2n1;
		post: global.turn23;
	}
    
    action enterCS(){
		frame: cs;
		/* this condition will be synthesized : pre: (global.try2 && !this.cs && global.turn23) || (!global.try3 && !this.cs && global.try2);*/
        pre: global.try2 && !this.cs;
		post: this.cs;
	}
    
    action leaveCS(){
        frame: cs,  try2, presentp2n1;
        pre: this.cs;
        post: !this.cs &&  !global.try2 && !this.presentp2n1;   
    }
   
	invariant: AG[EF[this.cs]]; /*&& AG[!this.cs || EF[!this.cs]];*/
}

process proc3{
    cs:boolean;
    owns:try3;
	init: !this.cs &&  !global.turn23 &&  !global.try3;

     action setTryTurn(){
		frame: turn23, try3;
		pre: !this.cs && !global.try3;
		post: !global.turn23 && global.try3;
	}

	action enterCS(){
		frame: cs;
		/*pre: (global.try2 && !this.cs && global.turn) || (!global.try1 && !this.cs && global.try2);*/
        pre: global.try3 && !this.cs;
		post: this.cs;
	}
    action leaveCS(){
        frame: cs,  try3;
        pre: this.cs;
        post: !this.cs &&  !global.try3;    
    }
   
	invariant: AG[EF[this.cs]]; /*&& AG[!this.cs || EF[!this.cs]];*/
}

main(){
	p1:proc1;
    p2:proc2;
    p3:proc3;
	run p1();
    run p2();
    run p3();	 	
}
property: AG[(!p1.cs || !p2.cs) && (!p2.cs || !p3.cs) && (!p3.cs || !p1.cs)] && AG[!global.try3 || AF[p3.cs]] && AG[!global.try1 || !p1.presentp1n1 || AF[p1.cs]]  && AG[!p2.presentp2n1 || AF[p2.cs]];
/*AG[(!p1.cs && !p2.cs) && (!p2.cs || !p3.cs) && (!p3.cs || !p1.cs)] && AG[!global.try1 || AF[p1.cs]] && AG[!global.try2 || AF[p2.cs]] && AG[!global.try3 || AF[p3.cs]];*/
