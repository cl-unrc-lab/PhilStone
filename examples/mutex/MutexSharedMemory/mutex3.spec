spec mutex
m:lock;
process p{
	try, ncs, cs:boolean;
	init : this.ncs && !this.cs && !this.try && av(global.m);
	
	action enterTry(){
		frame: ncs, try;
		pre: (this.ncs  || this.try) ;
		post: this.try;
	}	
	
    /*the tool needs to */
	action enterCS(){
		frame: try, m, cs;
		pre: this.try ;
		post: this.cs; 
	}

	action enterNCS(){
		frame: cs, ncs, m;
		pre:  this.cs;
		post: this.ncs;
	}
	action getLock(){
		frame: m;
		pre: this.try && av(m);
		post: this.try && own(m);
	}	
	invariant: AG[!(this.ncs && this.try)&&!(this.try&&this.cs)&&!(this.ncs&&this.cs)] && AG[EF[this.cs]] && AG[EF[this.ncs]];
}

main(){
 p1:p;
 p2:p;
 p3:p;
 run p1();
 run p2();
 run p3();
}

property: AG[(!p1.cs && !p2.cs) || (!p2.cs && !p3.cs) || (!p1.cs && !p3.cs)];
