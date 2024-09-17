#!/usr/bin/python
"""
This is a script for generating the reader writers example, basic usage:

python genRW n

where n is the number of processes. the result will be saved to the current folder
"""
import sys, getopt
import random
import math

try:
	# number of readers
    n = int(sys.argv[1])
    # number of writers
    m = int(sys.argv[2])
except ValueError:
    print("Error in the parameters.")
    print("Usage: python genRW n m")


fileName = f"""readers{n}writers{m}.spec"""
file = open(fileName, "w")
file.write(f"""
spec readers{n}writers{m}
/*
* This version of the readers and writers is based in the basic solution given in
* "Concurrent Reading while Writing" (Peterson 1982)
* Each reader has a flag ri indicating if she is reading,
* and the writer uses a lock for blocking the entry (a flag can be aso used).
* The synthesizer should resolve when the writer and reader can start writing and reading in such
* a way that mutual exclusion is preserved.
* Author: Pablo.
*/
""")
#for all the writers we define the shared variables
#for i in range(1,m+1) :
file.write(f"""w  : lock;  /* w is the lock for the writers */ \n""")

#for all the readers we define the shared variables
for i in range(1,n+1) :
    file.write(f"""r{i}  : prim_boolean;  /* r{i} is the lock for the reader {i} */ \n""")
           
# we calculate the global init condition 
globalinit_writer = "&&".join([f""" !global.r{i} """ for i in range(1,n+1)]) + "&& av(global.w)" #[f""" !global.w{i} """ for i in range(1,m+1)])

globalinit_reader = [f"""!global.r{i} && av(global.w)""" for i in range(1,n+1)] #[f""" !global.w{i} """ for i in range(1,m+1)])




# we define the writer processes
for i in range(1,m+1) :
    file.write(f"""
process writer{i}{{
	enum st = {{Writing, Waiting}}; /* the writer can be waiting or reading */
	init: this.st = Waiting  && {globalinit_writer};
    
	/* Writer's action for adquiring the lock */
	action startWriting(){{
		frame: w, st;
		pre: av(global.w);
		post: own(global.w) && (this.st = Writing);
	}}

	/* Writers action for freeing the lock */
	action stopWriting(){{
		frame: w, st;
		pre: own(global.w);
		post: av(global.w) && (this.st = Waiting);
	}}
	/* The invariant ensures that the states Writing and Waiting are revisited */
	invariant: AG[EF[this.st = Writing]] &&  AG[EF[this.st = Waiting]];
}}\n """)

# we define the reader processes
for i in range(1,n+1) :
    file.write(f"""process reader{i}{{
	enum st = {{Reading, Waiting}}; /* the reader is reading or waiting */
	owns: r{i}; /* this flag is only modified by this process */
	init: (this.st = Waiting) && {globalinit_reader[i-1]};

	action startReading(){{
		frame: st, r{i};
		pre: this.st = Waiting && av(w);
		post: this.st = Reading && global.r{i};
	}}

	action stopReading(){{
		frame:  st, r{i};
		pre: this.st = Reading;
		post: this.st = Waiting && !global.r{i};
	}}

	invariant: AG[EF[this.st = Reading]] && AG[EF[this.st = Waiting]];
}}
""")
    
# and the main process
file.write(f"""main(){{
""")
# we create the writer processes
for i in range(1,m+1) :
    file.write(f"""   pw{i}:writer{i};\n""")
            
for i in range(1,n+1) :
    file.write(f"""   pr{i}:reader{i};\n""")
    
for i in range(1,m+1) :
    file.write(f"""   run pw{i}();\n""")

for i in range(1,n+1) :
    file.write(f"""   run pr{i}();\n""")

file.write("}\n")
# and the global property:
# combinations readers writers
combinations_rw =  [ f"""AG[!(pr{a}.st=Reading&&pw{b}.st=Writing)]""" for a in range(1,n+1) for b in range(1,m+1)]

# combinations writers writers
combinations_ww =  [ f"""AG[!(pw{a}.st=Writing&&pw{b}.st=Writing)]""" for a in range(1,m+1) for b in range(a,m+1) if a != b]

# someone reads or write
someone_reads = "||".join([f"""(pr{i}.st = Reading)""" for i in range(1,n+1)]);
someone_writes = "||".join([f"""(pw{i}.st = Writing)""" for i in range(1,m+1)])

safety = "&&".join(combinations_rw + combinations_ww)
liveness = "EF["+  someone_reads + "||" + someone_writes + "]"
formula = safety + " && " + liveness
#for i in range(1,m+1) : 
#    formula = formula + f"""&& AG[!(pw{i}.st = Writing) || EF[pw{i}.st = Waiting]]"""
#for i in range(1,n+1) : 
#    formula = formula + f"""&& AG[!(pr{i}.st = Reading) || EF[pr{i}.st = Waiting]]"""

file.write("property :" + formula + ";")
file.close()

