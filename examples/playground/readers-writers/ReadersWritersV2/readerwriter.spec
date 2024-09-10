spec readerwriter

r:lock; /*r is the common resource*/

process writer{
	writing: boolean;
	init: !this.writing && av(global.r);

	/*action lockR(){
		frame: r;
		pre: av(global.r);
		post: own(global.r);
	}*/

	action write(){
		frame: r,writing;
		pre: !this.writing && av(global.r);
		post: this.writing && own(global.r);
	}

	action stopWriting(){
		frame: r,writing;
		pre: this.writing;
		post: !this.writing && av(global.r);	
	}

	/*action unlockR(){
		frame: r;
		pre: own(global.r);
		post: av(global.r);
	}*/
	invariant: AG[EF[this.writing]] && AG[EF[!this.writing]] && AG[!own(global.r) || EF[!own(global.r)]];
}

process reader{
	enum st = {Idle, Waiting, Reading};
	init: this.st = Idle && av(global.r);

    action getWLock(){
		frame: r;
		pre: av(global.r);
		post: own(global.r);	
	}	
    action releaseWLock(){
		frame: r;
		pre: own(global.r);
        post: av(global.r);
    }
	action startRead(){
		frame: st;
		pre: this.st=Waiting; /* && av(global.r) && av(mylock);*/
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
	invariant: AG[EF[this.st = Reading]] && AG[EF[this.st= Waiting]] && AG[!own(global.r) || EF[!own(global.r)]];
}

main(){
	w1:writer;
	r1:reader;
	run w1();
	run r1();
}

property: G[(!(r1.st=Reading) || !w1.writing)] 
          && G[!(r1.st = Waiting) || F[r1.st = Reading]] ;
          /*&& G[F[r1.st=Reading] || F[w1.writing]]; */
