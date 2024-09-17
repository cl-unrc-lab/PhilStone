
spec readers3writers1
/*
* This version of the readers and writers is based in the basic solution given in
* "Concurrent Reading while Writing" (Peterson 1982)
* Each reader has a flag ri indicating if she is reading,
* and the writer uses a lock for blocking the entry (a flag can be aso used).
* The synthesizer should resolve when the writer and reader can start writing and reading in such
* a way that mutual exclusion is preserved.
* Author: Pablo.
*/
w  : lock;  /* w is the lock for the writers */ 
r1  : prim_boolean;  /* r1 is the lock for the reader 1 */ 
r2  : prim_boolean;  /* r2 is the lock for the reader 2 */ 
r3  : prim_boolean;  /* r3 is the lock for the reader 3 */ 

process writer1{
	enum st = {Writing, Waiting}; /* the writer can be waiting or reading */
	init: this.st = Waiting  &&  !global.r1 && !global.r2 && !global.r3 && av(global.w);
    
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
	init: (this.st = Waiting) && !global.r1 && av(global.w);

	action startReading(){
		frame: st, r1;
		pre: this.st = Waiting && av(w);
		post: this.st = Reading && global.r1;
	}

	action stopReading(){
		frame:  st, r1;
		pre: this.st = Reading;
		post: this.st = Waiting && !global.r1;
	}

	invariant: AG[EF[this.st = Reading]] && AG[EF[this.st = Waiting]];
}
process reader2{
	enum st = {Reading, Waiting}; /* the reader is reading or waiting */
	owns: r2; /* this flag is only modified by this process */
	init: (this.st = Waiting) && !global.r2 && av(global.w);

	action startReading(){
		frame: st, r2;
		pre: this.st = Waiting && av(w);
		post: this.st = Reading && global.r2;
	}

	action stopReading(){
		frame:  st, r2;
		pre: this.st = Reading;
		post: this.st = Waiting && !global.r2;
	}

	invariant: AG[EF[this.st = Reading]] && AG[EF[this.st = Waiting]];
}
process reader3{
	enum st = {Reading, Waiting}; /* the reader is reading or waiting */
	owns: r3; /* this flag is only modified by this process */
	init: (this.st = Waiting) && !global.r3 && av(global.w);

	action startReading(){
		frame: st, r3;
		pre: this.st = Waiting && av(w);
		post: this.st = Reading && global.r3;
	}

	action stopReading(){
		frame:  st, r3;
		pre: this.st = Reading;
		post: this.st = Waiting && !global.r3;
	}

	invariant: AG[EF[this.st = Reading]] && AG[EF[this.st = Waiting]];
}
main(){
   pw1:writer1;
   pr1:reader1;
   pr2:reader2;
   pr3:reader3;
   run pw1();
   run pr1();
   run pr2();
   run pr3();
}
property :AG[!(pr1.st=Reading&&pw1.st=Writing)]&&AG[!(pr2.st=Reading&&pw1.st=Writing)]&&AG[!(pr3.st=Reading&&pw1.st=Writing)] && EF[(pr1.st = Reading)||(pr2.st = Reading)||(pr3.st = Reading)||(pw1.st = Writing)];