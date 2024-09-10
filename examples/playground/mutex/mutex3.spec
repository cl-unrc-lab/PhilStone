spec mutex
m:lock;
process p{
	try, ncs, cs:boolean;
	init : this.ncs && !this.cs && !this.try && av(global.m);
	
	action enterTry(){
		frame: ncs, try, m;
		pre: this.ncs ;
		post: this.try;
	}	
	
	action enterCS(){
		frame: try, cs, m;
		pre: this.try ;
		post: this.cs ; 
	}

	action enterNCS(){
		frame: cs, ncs, m;
		pre:  this.cs;
		post: this.ncs;
	}
	invariant: AG[!(this.ncs && this.try)&&!(this.try&&this.cs)] && AG[EF[this.cs]] && AG[EF[this.ncs]] && AG[EF[this.cs && own(global.m)]];
}


main(){
 p1:p;
 p2:p;
 p3:p;
 run p1();
 run p2();
 run p3();
}

property: AG[(!p1.cs || !p2.cs) && (!p2.cs || !p3.cs) && (!p1.cs || !p3.cs)];
