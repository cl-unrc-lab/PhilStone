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
	
	action enterCS(){
		frame: try, m, cs;
		pre: this.try ;
		post: this.cs ; 
	}

	action enterNCS(){
		frame: cs, ncs, m;
		pre:  this.cs;
		post: this.ncs;
	}
	action getLock(){
		frame: m;
		pre: this.try && av(global.m);
		post: this.try && own(global.m);
	}	
	invariant: AG[!(this.ncs && this.try)&&!(this.try&&this.cs)] && AG[EF[this.cs]] && AG[EF[this.ncs]];
}

main(){
 p1:p;
 p2:p;
 run p1();
 run p2();
}

property: AG[!p1.cs || !p2.cs];
