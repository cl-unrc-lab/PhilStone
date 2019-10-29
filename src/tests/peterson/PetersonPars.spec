/* Peterson Spec using parameters */

spec peterson
try1, try2:prim_boolean;
turn:boolean;

process proc1(try:prim_boolean, othertry:prim_boolean, turn:boolean){
    cs:boolean;
    owns:try1;
	init: !this.cs && own(try) && av(turn)  && !try;
    
    action getTurnLock(){
        frame: turn;
        pre: !this.cs && av(turn);
        post: own(turn);
    }
    
	action setTryTurn(){
		frame: turn, try;
		pre: !this.cs &&  own(try) && !try && own(turn);
		post: turn && try && av(turn) && own(try);
	}
	action enterCS(){
		frame: cs;
		pre: (try && !this.cs && !turn) || (!othertry && !this.cs && try);
		post: this.cs;
	}
    action leaveCS(){
        frame: cs,  try;
        pre: this.cs && own(try);
        post: !this.cs &&  !try && own(try);    
    }
   
	invariant: EF[this.cs] && AG[!this.cs || EF[!this.cs]];
}

process proc2(try:prim_boolean, othertry:prim_boolean, turn:boolean){
    cs:boolean;
    owns: try2;
	init: !this.cs && own(try) && av(turn)  && !try;
    
    action getTurnLock(){
        frame: turn;
        pre: !this.cs && av(turn);
        post: own(turn);
    }
   
	action setTryTurn(){
		frame: turn,  try;
		pre: !this.cs && own(try) && !try && own(turn);
		post:  !turn && try && av(turn) && own(try);
	}
	action enterCS(){
		frame: cs;
		pre: (try && !this.cs && turn) || (!othertry && !this.cs && try);
		post: this.cs;
	}
    action leaveCS(){
        frame: cs,  try;
        pre: this.cs && own(try);
        post: !this.cs &&  !try && own(try);    
    }
   
	invariant: EF[this.cs] && AG[!this.cs || EF[!this.cs]];
}

main(){
	p1:proc1;
    p2:proc2;
	run p1(try1, try2, turn);
    run p2(try2, try1, turn);
}

property: AG[!p1.cs || !p2.cs] && AG[!global.try1 || AF[p1.cs]] && AG[!global.try2 || AF[p2.cs]];

