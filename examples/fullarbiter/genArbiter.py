#!/usr/bin/python
"""
This is a script for generating the arbiter example, basic usage:

python genArbiter n

where n is the number of processes. the result will be saved to current folder
"""
import sys, getopt
import random
import math

try:
    n = int(sys.argv[1])
except ValueError:
    print("Error in the parameters.")


fileName = f"""fullarbiter{n}.spec"""
file = open(fileName, "w")
file.write(f"""
/*
* This is a version of the arbiter problem
*/

spec arbiter{n}
""")
var_dec1 = ",".join([f"""send{i+1}""" for i in range(n)])
var_dec2 = ",".join([f"""r{i+1}""" for i in range(n)])
var_dec = var_dec1 +", "+ var_dec2 + ": prim_boolean;"
file.write(var_dec+"\n")
# we write the processes
for i in range(1,n+1) :
    file.write(
    f"""process process{i}{{
    g{i}, hasToken: boolean;
    init: !this.g{i} && !global.r{i}; 
    
    action giveGrant(){{
        frame: g{i};
        pre : !this.g{i};
        post: this.g{i};
    }}
    
    action downGrant(){{
        frame: g{i};
        pre : global.r{i} || !global.r{i} ;
        post: !this.g{i};
    }}
    invariant: AG[EF[global.send{(i%n)+1}]]&&AG[EF[this.g{i}]] && AG[EF[!this.g{i}]];
    }}"""
    )
file.write("""
main(){
""")
for i in range(1,n+1) :
    file.write(
    f"""p{i}:process{i};
    """)
for i in range(1,n+1) :
    file.write(
    f"""run p{i}();
    """)
file.write(
"""
}
""")
    
# we write the property
liveness = "&&".join([f"""G[!global.r{i} || F[p{i}.g{i}]]""" for i in range(1,n+1)])
safety = "&&".join([f"""G[!(p{i}.g{i} && p{j}.g{j})]""" for i in range(1,n) for j in range(i,n+1)])
no_spurious_start = "&&".join([f"""![(!global.r{i} && !p{i}.g{i}) U (!global.r{i} && p{i}.g{i})]""" for i in range(1,n+1)])
no_spurious = "&&".join([f"""!F[[p{i}.g{i} U [!global.r{i} && !p{i}.g{i} U p{i}.g{i} && !global.r{i}]]]""" for i in range(1,n+1)])
grant_lowered = "&&".join([f"""G[ !(!global.r{i} && p{i}.g{i}) || F[(global.r{i} && p{i}.g{i}) || (!p{i}.g{i})] ]""" for i in range(1,n+1) ])
file.write("property: "+ liveness + "\n &&" + safety +"\n &&"+ no_spurious_start +"\n &&"+ no_spurious +"\n &&"+ grant_lowered +";\n")

# we write the assumptions
asumption = "&&".join([f"""G[F[p{i}.hasToken]] """ for i in range(1,n+1)])
file.write("""        assumption: """+asumption+";")
file.close()
