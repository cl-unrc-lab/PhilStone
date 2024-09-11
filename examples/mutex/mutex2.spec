
/*
This is a version of the mutex problem: several processes competing for a shared resource  we consider a lock m, each process needs to obtain the lock and then goes to the critical section, every process' action 
is able to own the lock, we should synthesize a way of obtaining the such that mutual exclusion is ensured.
*/

spec mutex2
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

main(){p1:p;
p2:p;
run p1();
run p2();
}
property: AG[!(p1.st=Cs&&p2.st=Cs)] && EF[p1.st=Cs || p2.st=Cs]; 
/* this last requirement is needed for discarding models in which safety is ensured by removing too many states */
