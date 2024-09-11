
/*
* This is a version of the mutex problem: several processes competing for a shared 
* resource  we consider a lock m, each process needs to obtain the lock and then goes to the critical section, every process' action 
* is able to own the lock, we should synthesize a way of obtaining the such that mutual exclusion is ensured.
*/

spec mutex5
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
p3:p;
p4:p;
p5:p;
run p1();
run p2();
run p3();
run p4();
run p5();
}
property: AG[!(p1.st=Cs&&p2.st=Cs)]&&AG[!(p1.st=Cs&&p3.st=Cs)]&&AG[!(p1.st=Cs&&p4.st=Cs)]&&AG[!(p1.st=Cs&&p5.st=Cs)]&&AG[!(p2.st=Cs&&p3.st=Cs)]&&AG[!(p2.st=Cs&&p4.st=Cs)]&&AG[!(p2.st=Cs&&p5.st=Cs)]&&AG[!(p3.st=Cs&&p4.st=Cs)]&&AG[!(p3.st=Cs&&p5.st=Cs)]&&AG[!(p4.st=Cs&&p5.st=Cs)]&&EF[p1.st=Cs||p2.st=Cs||p3.st=Cs||p4.st=Cs||p5.st=Cs];