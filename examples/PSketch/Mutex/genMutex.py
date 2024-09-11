#!/usr/bin/python
"""
This is a script for generating the mutex example for psketch, basic usage:

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


fileName = f"""mutex{n}.sk"""
file = open(fileName, "w")

# we compute the assert, this is the hardest part.

combinations =  [ f"""!(cs[{a}] && cs[{b}])""" for a in range(0,n) for b in range(a,n) if a!=b ]
formula = "&&".join(combinations)

file.write(f"""
/*
This is a version of the mutex problem of psketch: several processes competing for a shared resource, the array cs is used to signaling if the 
corresponding process is in the critical zone, time (T) is set to 2 in this example, this only two iterations are consideres for each process.
*/

int N = {n}; 
int T = 2;
bit sp () {{ return 1; }}

bit main () implements sp {{
    int resource=0;
    bit[N] cs = 0;
    fork (int i; N){{
        for (int j=0; j<T; j++){{
            for (int k=0;k<N;k++){{
                if (k!=i)
                   assert !(cs[i] && cs[k]);
            }}
            reorder{{
                cs[i] = 0;
                cs[i] = 1;
                unlock(resource);
                lock(resource);
            }}
        }}
    }}
    return 1;
}}           
""")

file.close()