
spec readers1writers1
/*
* This version of the readers and writers is based in the basic solution given in
* "Concurrent Reading while Writing" (Peterson 1982)
* Each reader has a flag ri indicating if she is reading,
* and the writer uses a lock for blocking the entry (a flag can be aso used).
* The synthesizer should resolve when the writer and reader can start writing and reading in such
* a way that mutual exclusion is preserved.
* Author: Pablo.
*/
w  : lock;  /* w is the lock for the writer 1 */ 
r1  : prim_boolean;  /* r1 is the lock for the reader 1 */ 

process writer1{
	enum st = {Writing, Waiting}; /* the writer can be waiting or reading */
	init: this.st = Waiting  &&  !global.r1 && av(global.w);
    
	/* Writer's action for adquiring the lock */
	action startWriting(){
		frame: w, st;
		pre: av(global.w);
		post: own(global.w) && (this.st = Writing);
	}

	/* Writers action for freeing the lock */
	action stopWriting(){
		frame: w, st;
		pre: own(global.w);
		post: av(global.w) && (this.st = Waiting);
	}
	/* The invariant ensures that the states Writing and Waiting are revisited */
	invariant: AG[EF[this.st = Writing]] &&  AG[EF[this.st = Waiting]];
}
 process reader1{
	enum st = {Reading, Waiting}; /* the reader is reading or waiting */
	owns: r1; /* this flag is only modified by this process */
	init: (this.st = Waiting) &&  !global.r1 && av(global.w);

	action startReading(){
		frame: st, r1;
		pre: this.st = Waiting;
		post: this.st = Reading && global.r1;
	}

	action stopReading(){
		frame:  st, r1;
		pre: this.st = Reading;
		post: this.st = Waiting && !global.r1;
	}

	invariant: AG[EF[this.st = Reading]] && AG[EF[this.st = Waiting]];
}
main(){
   pw1:writer1;
   pr1:reader1;
   run pw1();
   run pr1();
}
property :AG[!(pr1.st=Reading&&pw1.st=Writing)] && EF[(pr1.st = Reading)||(pw1.st = Writing)]&& AG[!(pw1.st = Writing) || EF[pw1.st = Waiting]]&& AG[!(pr1.st = Reading) || EF[pr1.st = Waiting]];