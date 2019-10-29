spec mutex
l:lock;
process p{
	try, ncs, cs:boolean;
	init : this.ncs && !this.cs && !this.try && av(global.l);
	
	action enterTry(){
		frame: ncs, try;
		pre: (this.ncs ) || (this.try && !own(global.l)) ;
		post: this.try;
	}	
	
	action enterCS(){
		frame: try, l, cs;
		pre: this.try &&  own(global.l);
		post: this.cs && own(global.l); 
	}

	action enterNCS(){
		frame: cs, ncs, l;
		pre:  this.cs;
		post: this.ncs && (!own(global.l));
	}
	action getLock(){
		frame: l;
		pre: this.try && av(global.l);
		post: this.try && own(global.l);
	}	
	invariant: AG[!(this.ncs && this.try)&&!(this.try&&this.cs)];
}

main(){
 p1:p;
 p2:p;
 run p1();
 run p2();
}

property: AG[!p1.cs || !p2.cs];
