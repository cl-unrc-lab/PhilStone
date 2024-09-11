#!/usr/bin/python
"""
This is a script for generating the mutex example, basic usage:

python genMutex n

where n is the number of processes. the result will be saved to 
"""
import sys, getopt
import random
import math

try:
    n = int(sys.argv[1])
except ValueError:
    print("Error in the parameters.")


fileName = f"""mutex{n}.spec"""
file = open(fileName, "w")
file.write(f"""
/*
* This is a version of the mutex problem: several processes competing for a shared 
* resource  we consider a lock m, each process needs to obtain the lock and then goes to the critical section, every process' action 
* is able to own the lock, we should synthesize a way of obtaining the such that mutual exclusion is ensured.
*/

spec mutex{n}
m:lock;
process p{{
	enum st = {{Cs,Ncs,Try}};
	init : this.st = Ncs && av(global.m);
	
	action enterTry(){{
		frame: st, m; /* the action may get the lock*/
		pre:  this.st = Ncs;
		post: this.st = Try;
	}}	
	
	action enterCS(){{
		frame: st, m; /* the action may get the lock*/
		pre: this.st = Try ;
		post: this.st = Cs ; 
	}}

	action enterNCS(){{
		frame: st, m; /* the action may get the lock*/
		pre:  this.st = Cs;
		post: this.st = Ncs;
	}}
    /*This invariant guarantees that the state Cs and Ncs are eventually visited*/
	invariant: AG[EF[this.st = Cs]] && AG[EF[this.st = Ncs]];
}}            

""")

file.write(f"main(){{")

# now we write the part that depends on n
for i in range(1,n+1) :
    file.write(f"p{i}:p;\n")

for i in range(1,n+1) :
    file.write(f"run p{i}();\n")

file.write(f"}}\n")

file.write(f"""property: """)

combinations =  [ f"""AG[!(p{a}.st=Cs&&p{b}.st=Cs)]""" for a in range(1,n+1) for b in range(a,n+1) if a!=b ]
formula = "&&".join(combinations)

all_cs = [f"""p{a}.st=Cs""" for a in range(1,n+1)]
liveness_formula = "EF["+ "||".join(all_cs) + "]"
formula = formula + "&&" + liveness_formula
file.write(formula+";")   
file.close()









