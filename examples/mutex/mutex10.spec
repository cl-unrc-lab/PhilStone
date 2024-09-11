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
 run p1();
 run p2();
}

property: AG[!p1.cs || !p2.cs];
/*
This is a version of the mutex problem: several processes competing for a shared resource  we consider a lock m, each process needs to obtain the lock and then goes to the critical section, every process' action 
is able to own the lock, we should synthesize a way of obtaining the such that mutual exclusion is ensured.
*/

spec mutex
m:lock;
process p{
	enum st = {Cs,Ncs,Try};
	init : this.st = Ncs && av(global.m);
	
	action enterTry(){
		frame: st, m; /* the action may get the lock*/
		pre:  this.st = Ncs;
		post: this.st = Try;
	}	
	
	action enterCS(){
		frame: st, m; /* the action may get the lock*/
		pre: this.st = Try ;
		post: this.st = Cs ; 
	}

	action enterNCS(){
		frame: st, m; /* the action may get the lock*/
		pre:  this.st = Cs;
		post: this.st = Ncs;
	}
    /*This invariant guarantees that the state Cs and Ncs are eventually visited*/
	invariant: AG[EF[this.st = Cs]] && AG[EF[this.st = Ncs]];
}            


/*
This is a version of the mutex problem: several processes competing for a shared resource  we consider a lock m, each process needs to obtain the lock and then goes to the critical section, every process' action 
is able to own the lock, we should synthesize a way of obtaining the such that mutual exclusion is ensured.
*/

spec mutex
m:lock;
process p{
	enum st = {Cs,Ncs,Try};
	init : this.st = Ncs && av(global.m);
	
	action enterTry(){
		frame: st, m; /* the action may get the lock*/
		pre:  this.st = Ncs;
		post: this.st = Try;
	}	
	
	action enterCS(){
		frame: st, m; /* the action may get the lock*/
		pre: this.st = Try ;
		post: this.st = Cs ; 
	}

	action enterNCS(){
		frame: st, m; /* the action may get the lock*/
		pre:  this.st = Cs;
		post: this.st = Ncs;
	}
    /*This invariant guarantees that the state Cs and Ncs are eventually visited*/
	invariant: AG[EF[this.st = Cs]] && AG[EF[this.st = Ncs]];
}            

main(){p1:pp2:pp3:pp4:pp5:pp6:pp7:pp8:pp9:pp10:prun p10()run p10()run p10()run p10()run p10()run p10()run p10()run p10()run p10()run p10()}property: AG[!(p1.st=Cs&&p2.st=Cs)]&&AG[!(p1.st=Cs&&p3.st=Cs)]&&AG[!(p1.st=Cs&&p4.st=Cs)]&&AG[!(p1.st=Cs&&p5.st=Cs)]&&AG[!(p1.st=Cs&&p6.st=Cs)]&&AG[!(p1.st=Cs&&p7.st=Cs)]&&AG[!(p1.st=Cs&&p8.st=Cs)]&&AG[!(p1.st=Cs&&p9.st=Cs)]&&AG[!(p1.st=Cs&&p10.st=Cs)]&&AG[!(p2.st=Cs&&p1.st=Cs)]&&AG[!(p2.st=Cs&&p3.st=Cs)]&&AG[!(p2.st=Cs&&p4.st=Cs)]&&AG[!(p2.st=Cs&&p5.st=Cs)]&&AG[!(p2.st=Cs&&p6.st=Cs)]&&AG[!(p2.st=Cs&&p7.st=Cs)]&&AG[!(p2.st=Cs&&p8.st=Cs)]&&AG[!(p2.st=Cs&&p9.st=Cs)]&&AG[!(p2.st=Cs&&p10.st=Cs)]&&AG[!(p3.st=Cs&&p1.st=Cs)]&&AG[!(p3.st=Cs&&p2.st=Cs)]&&AG[!(p3.st=Cs&&p4.st=Cs)]&&AG[!(p3.st=Cs&&p5.st=Cs)]&&AG[!(p3.st=Cs&&p6.st=Cs)]&&AG[!(p3.st=Cs&&p7.st=Cs)]&&AG[!(p3.st=Cs&&p8.st=Cs)]&&AG[!(p3.st=Cs&&p9.st=Cs)]&&AG[!(p3.st=Cs&&p10.st=Cs)]&&AG[!(p4.st=Cs&&p1.st=Cs)]&&AG[!(p4.st=Cs&&p2.st=Cs)]&&AG[!(p4.st=Cs&&p3.st=Cs)]&&AG[!(p4.st=Cs&&p5.st=Cs)]&&AG[!(p4.st=Cs&&p6.st=Cs)]&&AG[!(p4.st=Cs&&p7.st=Cs)]&&AG[!(p4.st=Cs&&p8.st=Cs)]&&AG[!(p4.st=Cs&&p9.st=Cs)]&&AG[!(p4.st=Cs&&p10.st=Cs)]&&AG[!(p5.st=Cs&&p1.st=Cs)]&&AG[!(p5.st=Cs&&p2.st=Cs)]&&AG[!(p5.st=Cs&&p3.st=Cs)]&&AG[!(p5.st=Cs&&p4.st=Cs)]&&AG[!(p5.st=Cs&&p6.st=Cs)]&&AG[!(p5.st=Cs&&p7.st=Cs)]&&AG[!(p5.st=Cs&&p8.st=Cs)]&&AG[!(p5.st=Cs&&p9.st=Cs)]&&AG[!(p5.st=Cs&&p10.st=Cs)]&&AG[!(p6.st=Cs&&p1.st=Cs)]&&AG[!(p6.st=Cs&&p2.st=Cs)]&&AG[!(p6.st=Cs&&p3.st=Cs)]&&AG[!(p6.st=Cs&&p4.st=Cs)]&&AG[!(p6.st=Cs&&p5.st=Cs)]&&AG[!(p6.st=Cs&&p7.st=Cs)]&&AG[!(p6.st=Cs&&p8.st=Cs)]&&AG[!(p6.st=Cs&&p9.st=Cs)]&&AG[!(p6.st=Cs&&p10.st=Cs)]&&AG[!(p7.st=Cs&&p1.st=Cs)]&&AG[!(p7.st=Cs&&p2.st=Cs)]&&AG[!(p7.st=Cs&&p3.st=Cs)]&&AG[!(p7.st=Cs&&p4.st=Cs)]&&AG[!(p7.st=Cs&&p5.st=Cs)]&&AG[!(p7.st=Cs&&p6.st=Cs)]&&AG[!(p7.st=Cs&&p8.st=Cs)]&&AG[!(p7.st=Cs&&p9.st=Cs)]&&AG[!(p7.st=Cs&&p10.st=Cs)]&&AG[!(p8.st=Cs&&p1.st=Cs)]&&AG[!(p8.st=Cs&&p2.st=Cs)]&&AG[!(p8.st=Cs&&p3.st=Cs)]&&AG[!(p8.st=Cs&&p4.st=Cs)]&&AG[!(p8.st=Cs&&p5.st=Cs)]&&AG[!(p8.st=Cs&&p6.st=Cs)]&&AG[!(p8.st=Cs&&p7.st=Cs)]&&AG[!(p8.st=Cs&&p9.st=Cs)]&&AG[!(p8.st=Cs&&p10.st=Cs)]&&AG[!(p9.st=Cs&&p1.st=Cs)]&&AG[!(p9.st=Cs&&p2.st=Cs)]&&AG[!(p9.st=Cs&&p3.st=Cs)]&&AG[!(p9.st=Cs&&p4.st=Cs)]&&AG[!(p9.st=Cs&&p5.st=Cs)]&&AG[!(p9.st=Cs&&p6.st=Cs)]&&AG[!(p9.st=Cs&&p7.st=Cs)]&&AG[!(p9.st=Cs&&p8.st=Cs)]&&AG[!(p9.st=Cs&&p10.st=Cs)]&&AG[!(p10.st=Cs&&p1.st=Cs)]&&AG[!(p10.st=Cs&&p2.st=Cs)]&&AG[!(p10.st=Cs&&p3.st=Cs)]&&AG[!(p10.st=Cs&&p4.st=Cs)]&&AG[!(p10.st=Cs&&p5.st=Cs)]&&AG[!(p10.st=Cs&&p6.st=Cs)]&&AG[!(p10.st=Cs&&p7.st=Cs)]&&AG[!(p10.st=Cs&&p8.st=Cs)]&&AG[!(p10.st=Cs&&p9.st=Cs)]
/*
This is a version of the mutex problem: several processes competing for a shared resource  we consider a lock m, each process needs to obtain the lock and then goes to the critical section, every process' action 
is able to own the lock, we should synthesize a way of obtaining the such that mutual exclusion is ensured.
*/

spec mutex
m:lock;
process p{
	enum st = {Cs,Ncs,Try};
	init : this.st = Ncs && av(global.m);
	
	action enterTry(){
		frame: st, m; /* the action may get the lock*/
		pre:  this.st = Ncs;
		post: this.st = Try;
	}	
	
	action enterCS(){
		frame: st, m; /* the action may get the lock*/
		pre: this.st = Try ;
		post: this.st = Cs ; 
	}

	action enterNCS(){
		frame: st, m; /* the action may get the lock*/
		pre:  this.st = Cs;
		post: this.st = Ncs;
	}
    /*This invariant guarantees that the state Cs and Ncs are eventually visited*/
	invariant: AG[EF[this.st = Cs]] && AG[EF[this.st = Ncs]];
}            

main(){p1:p
p2:p
p3:p
p4:p
p5:p
p6:p
p7:p
p8:p
p9:p
p10:p
run p10()
run p10()
run p10()
run p10()
run p10()
run p10()
run p10()
run p10()
run p10()
run p10()
}
property: AG[!(p1.st=Cs&&p2.st=Cs)]&&AG[!(p1.st=Cs&&p3.st=Cs)]&&AG[!(p1.st=Cs&&p4.st=Cs)]&&AG[!(p1.st=Cs&&p5.st=Cs)]&&AG[!(p1.st=Cs&&p6.st=Cs)]&&AG[!(p1.st=Cs&&p7.st=Cs)]&&AG[!(p1.st=Cs&&p8.st=Cs)]&&AG[!(p1.st=Cs&&p9.st=Cs)]&&AG[!(p1.st=Cs&&p10.st=Cs)]&&AG[!(p2.st=Cs&&p1.st=Cs)]&&AG[!(p2.st=Cs&&p3.st=Cs)]&&AG[!(p2.st=Cs&&p4.st=Cs)]&&AG[!(p2.st=Cs&&p5.st=Cs)]&&AG[!(p2.st=Cs&&p6.st=Cs)]&&AG[!(p2.st=Cs&&p7.st=Cs)]&&AG[!(p2.st=Cs&&p8.st=Cs)]&&AG[!(p2.st=Cs&&p9.st=Cs)]&&AG[!(p2.st=Cs&&p10.st=Cs)]&&AG[!(p3.st=Cs&&p1.st=Cs)]&&AG[!(p3.st=Cs&&p2.st=Cs)]&&AG[!(p3.st=Cs&&p4.st=Cs)]&&AG[!(p3.st=Cs&&p5.st=Cs)]&&AG[!(p3.st=Cs&&p6.st=Cs)]&&AG[!(p3.st=Cs&&p7.st=Cs)]&&AG[!(p3.st=Cs&&p8.st=Cs)]&&AG[!(p3.st=Cs&&p9.st=Cs)]&&AG[!(p3.st=Cs&&p10.st=Cs)]&&AG[!(p4.st=Cs&&p1.st=Cs)]&&AG[!(p4.st=Cs&&p2.st=Cs)]&&AG[!(p4.st=Cs&&p3.st=Cs)]&&AG[!(p4.st=Cs&&p5.st=Cs)]&&AG[!(p4.st=Cs&&p6.st=Cs)]&&AG[!(p4.st=Cs&&p7.st=Cs)]&&AG[!(p4.st=Cs&&p8.st=Cs)]&&AG[!(p4.st=Cs&&p9.st=Cs)]&&AG[!(p4.st=Cs&&p10.st=Cs)]&&AG[!(p5.st=Cs&&p1.st=Cs)]&&AG[!(p5.st=Cs&&p2.st=Cs)]&&AG[!(p5.st=Cs&&p3.st=Cs)]&&AG[!(p5.st=Cs&&p4.st=Cs)]&&AG[!(p5.st=Cs&&p6.st=Cs)]&&AG[!(p5.st=Cs&&p7.st=Cs)]&&AG[!(p5.st=Cs&&p8.st=Cs)]&&AG[!(p5.st=Cs&&p9.st=Cs)]&&AG[!(p5.st=Cs&&p10.st=Cs)]&&AG[!(p6.st=Cs&&p1.st=Cs)]&&AG[!(p6.st=Cs&&p2.st=Cs)]&&AG[!(p6.st=Cs&&p3.st=Cs)]&&AG[!(p6.st=Cs&&p4.st=Cs)]&&AG[!(p6.st=Cs&&p5.st=Cs)]&&AG[!(p6.st=Cs&&p7.st=Cs)]&&AG[!(p6.st=Cs&&p8.st=Cs)]&&AG[!(p6.st=Cs&&p9.st=Cs)]&&AG[!(p6.st=Cs&&p10.st=Cs)]&&AG[!(p7.st=Cs&&p1.st=Cs)]&&AG[!(p7.st=Cs&&p2.st=Cs)]&&AG[!(p7.st=Cs&&p3.st=Cs)]&&AG[!(p7.st=Cs&&p4.st=Cs)]&&AG[!(p7.st=Cs&&p5.st=Cs)]&&AG[!(p7.st=Cs&&p6.st=Cs)]&&AG[!(p7.st=Cs&&p8.st=Cs)]&&AG[!(p7.st=Cs&&p9.st=Cs)]&&AG[!(p7.st=Cs&&p10.st=Cs)]&&AG[!(p8.st=Cs&&p1.st=Cs)]&&AG[!(p8.st=Cs&&p2.st=Cs)]&&AG[!(p8.st=Cs&&p3.st=Cs)]&&AG[!(p8.st=Cs&&p4.st=Cs)]&&AG[!(p8.st=Cs&&p5.st=Cs)]&&AG[!(p8.st=Cs&&p6.st=Cs)]&&AG[!(p8.st=Cs&&p7.st=Cs)]&&AG[!(p8.st=Cs&&p9.st=Cs)]&&AG[!(p8.st=Cs&&p10.st=Cs)]&&AG[!(p9.st=Cs&&p1.st=Cs)]&&AG[!(p9.st=Cs&&p2.st=Cs)]&&AG[!(p9.st=Cs&&p3.st=Cs)]&&AG[!(p9.st=Cs&&p4.st=Cs)]&&AG[!(p9.st=Cs&&p5.st=Cs)]&&AG[!(p9.st=Cs&&p6.st=Cs)]&&AG[!(p9.st=Cs&&p7.st=Cs)]&&AG[!(p9.st=Cs&&p8.st=Cs)]&&AG[!(p9.st=Cs&&p10.st=Cs)]&&AG[!(p10.st=Cs&&p1.st=Cs)]&&AG[!(p10.st=Cs&&p2.st=Cs)]&&AG[!(p10.st=Cs&&p3.st=Cs)]&&AG[!(p10.st=Cs&&p4.st=Cs)]&&AG[!(p10.st=Cs&&p5.st=Cs)]&&AG[!(p10.st=Cs&&p6.st=Cs)]&&AG[!(p10.st=Cs&&p7.st=Cs)]&&AG[!(p10.st=Cs&&p8.st=Cs)]&&AG[!(p10.st=Cs&&p9.st=Cs)]