spec readerwriter
/*
* This version of the readers and writers is based in the basic solution given in
* "Concurrent Reading while Writing" (Peterson 1982)
* Each reader has a flag ri indicating if she is reading,
* and the writer uses a lock for blocking the entry (a flag can be aso used).
* The synthesizer should resolve when the writer and reader can start writing and reading in such
* a way that mutual exclusion is preserved.
*/


w  : prim_boolean;  /* w is the lock for the writer */
r1 : prim_boolean;  /* this is a global atribute, used for signaling that reader 1 is reading  */

process writer{
	enum st = {Writing, Waiting}; /* the writer can be waiting or reading*/
    owns : w;  /* this flag is only modified by this processor */
	init: this.st = Waiting  && !global.w && !global.r1;
    
    
    /* Writer's action for adquiring the lock */
	action startWriting(){
		frame: w, st;
		pre: !global.w;
		post: global.w && (this.st = Writing);
	}

    /* Writers action for freeing the lock */
	action stopWriting(){
		frame: w, st;
		pre: global.w;
		post: !global.w && (this.st = Waiting);
	}
	/* The invariant ensures that the states Writing and Waiting are revisited */
	invariant: AG[EF[this.st = Writing]] &&  AG[EF[this.st = Waiting]];
}

process reader{
	enum st = {Reading, Waiting}; /* the reader is reading or waiting */
    owns: r1; /* this flag is only modified by this processor */
	init: (this.st = Waiting) && !global.r1 && !global.w;

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
	pw:writer;
	pr:reader;
	run pw();
	run pr();
}

/* 
*  Safety Property: the reader and writer cannot be writing and reading at the same time 
*  Also we add a subformula stating the some of the process has to read o write, otherwise we can obtain 
*  a trivial implementation: the processes block each other and the safety propety holds.
*  Additionally we request that if a process is writing then it has to be waiting at some point, this is to avoid
*  instances where a process block itself in the writing state, for instance waiting for r1 comes true. Similarly for the reader.
*/
property: AG[!((pr.st = Reading) && (pw.st = Writing))] && EF[(pr.st = Reading) || (pw.st=Writing)] 
	  && AG[!(pr.st = Reading) || EF[pr.st = Waiting]] && AG[!(pw.st=Writing) || EF[pw.st = Waiting]]; 
