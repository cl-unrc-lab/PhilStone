
spec readerwriter

r,lock1,lock2:lock; /*r is the common resource*/



process reader(mylock:lock){
	enum st = {Idle, Waiting, Reading};
	init: this.st = Idle && av(global.r) && av(mylock);

    action getLock(){
		frame: mylock;
		pre: av(mylock);
		post: own(mylock);	
	}	
    
    action releaseLock(){
		frame: mylock;
		pre: own(mylock);
        post: av(mylock);
    }
	action startRead(){
		frame: st;
		pre: this.st=Waiting;
		post: this.st=Reading;
	}
    
    action startWait(){
        frame:st;
        pre: this.st=Idle;
        post: this.st= Waiting;
    }

	action finishRead(){
		frame: st;
		pre: this.st = Reading;
		post: this.st = Idle;
	}
	invariant: AG[EF[this.st = Reading]] && AG[EF[this.st= Idle]] && AG[!own(mylock) || EF[!own(mylock)]];
}

process writer1(wlock:lock){
	writing: boolean;
	init: !this.writing && av(wlock) && av(global.lock1) && av(global.lock2);

	action write(){
		frame: wlock, writing;
		pre: !this.writing && av(wlock);
		post: this.writing && own(wlock);
	}

	action stopWriting(){
		frame: wlock, writing;
		pre: this.writing && own(wlock);
		post: !this.writing && av(wlock);	
	}

	invariant: AG[EF[this.writing]] && AG[EF[!this.writing]] && AG[!own(wlock) || EF[!own(wlock)]];
}

/*
process writer2{
	writing: boolean;
	init: !this.writing && av(global.r) && av(global.lock1) && av(global.lock2);

	action write(){
		frame: r, writing;
		pre: !this.writing && av(global.r);
		post: this.writing && own(global.r);
	}

	action stopWriting(){
		frame: r, writing;
		pre: this.writing && own(global.r);
		post: !this.writing && av(global.r);	
	}

	invariant: AG[EF[this.writing]] && AG[EF[!this.writing]] && AG[!own(global.r) || EF[!own(global.r)]];
}

*/

main(){
	w1:writer1;
    w2:writer1;
	r1:reader;
    r2:reader;
	run w1(r);
    run w2(r);
	run r1(lock1);
    run r2(lock2);
}

property: G[(!(r1.st=Reading) || !w1.writing) && (!(r2.st=Reading)|| !w1.writing) && (!(r1.st=Reading) || !w2.writing) && (!(r2.st=Reading)|| !w2.writing) && (!w2.writing || !w1.writing)] 
&& G[!(r1.st = Waiting) || F[r1.st = Reading]]
&& G[!(r2.st = Waiting) || F[r2.st = Reading]]
&& F[r1.st = Reading || r2.st = Reading || w1.writing || w2.writing];
/*
&& G[!(r2.st = Waiting) || F[r2.st = Reading]] && F[r1.st= Reading || r2.st = Reading || w1.writing || w2.writing];*/
/*&& G[F[r2.st=Reading] || F[r1.st=Reading] || F[w1.writing]]; */
