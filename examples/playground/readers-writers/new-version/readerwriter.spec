spec readerwriter

r:lock; /*r is the common resource*/
read1:lock;  /*this is a global atribute, used for signaling that the reader 1 is reading*/

process writer{
	enum st = {Writing, Waiting};
	init: this.st = Waiting  && av(global.r) && av(global.read1);

	action getLock(){
		frame: r, st;
		pre: av(global.r);
		post: own(global.r) && (this.st = Writing);
	}

	action freeLock(){
		frame: r, st;
		pre: own(global.r);
		post: av(global.r) && (this.st = Waiting);
	}
	
	invariant: AG[EF[this.st = Writing]] &&  AG[EF[this.st = Waiting]];
}

process reader(mylock:lock){
	enum st = {Reading, Waiting};
	init: (this.st = Waiting) && av(global.r) && av(mylock);

	action getLock(){
		frame: r;
		pre: av(global.r);
		post: own(global.r);
	}

	action freeLock(){
		frame: r;
		pre: own(global.r);
		post: av(global.r);
	}

	action getRLock(){
		frame: mylock, st;
		pre: av(mylock);
		post: own(mylock) && this.st = Reading;
	}

	action freeRLock(){
		frame: mylock, st;
		pre: own(mylock);
		post: av(mylock) && this.st = Waiting;
	}

	invariant: EF[this.st = Reading] && AG[EF[this.st = Waiting]];
}

main(){
	w1:writer;
	r1:reader;
	run w1();
	run r1(read1);
}

property: AG[!(r1.st = Reading && w1.st = Writing)] && EF[r1.st = Reading || w1.st = Writing]; 
