spec mutex
m:lock;
process p{
	try, ncs, cs:boolean;
	init : this.ncs && !this.cs && !this.try && av(global.m);
	
	action enterTry(){
		frame: ncs, try;
		pre: this.ncs ;
		post: this.try && !this.ncs;
	}	
	
	action enterCS(){
		frame: try, cs;
		pre: this.try;
		post: this.cs && !this.try; 
	}

	action enterNCS(){
		frame: m, cs, ncs;
		pre:  this.cs;
		post: this.ncs && !this.cs && (!own(global.m));
	}
	action getLock(){
		frame: m;
		pre:  av(global.m);
		post: own(global.m);
	}	
	action freeLock(){
		frame: m;
		pre:  own(global.m);
		post: av(global.m);
	}
	invariant: AG[!(this.ncs && this.try)&&!(this.try&&this.cs)] && AG[EF[own(global.m)]] && AG[!own(global.m) || EF[av(global.m)]];
}

main(){
 p1:p;
 p2:p;
 run p1();
 run p2();
}

property: AG[!p1.cs || !p2.cs];
