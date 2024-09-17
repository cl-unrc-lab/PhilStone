import sys, os, subprocess, csv, re, signal

"""
This script runs the benchmarks, and saves the results in .cvs files in folder report
"""

def clean_output() :
    for f in os.listdir("../output") :
        if (not f.endswith(".xml")) and  (not f.endswith(".dot")) and (not f.endswith(".als")) and (not f.endswith(".imp")):
            continue
        os.remove(os.path.join("../output", f))

# Method for running the examples
def run_example(command, name, dir, fileName, scope, timeout) :
    row = {}
    row["Example"] = name
    row["Scope"] = scope
    row["Local Time"] = "-"
    row["Global Time"] = "-"
    row["It."] = "-"
    row["#R.States"] = "-"
    row["#T.States"] = "-"
    row["Result"] = "UNSAT"
    try: 
        print("Running: "+name+" with scope:"+scope)
        #output = subprocess.run(["./"+command,scope, dir+fileName], capture_output=True, timeout=timeout).stdout.decode()
        proc = subprocess.Popen(["./"+command,scope, dir+fileName],stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        output, err = proc.communicate(timeout=timeout)
        for line in output.decode().splitlines() : 
            words = line.split()
            if line.startswith("+ Time for generating the models") :
                row["Local Time"] = words[7] #we add the property checked to the dictionary
            elif line.startswith("+ Number of iterations:") : 
                row["It."] = words[4]
            elif line.startswith("+ Total Time") :
                row["Global Time"] = words[4]
            elif line.startswith("- Spec UNSAT") :
                row["Result"] = "UNSAT"
            elif line.startswith("+ Program Synthesized") :
                row["Result"] = "Found"
            elif line.startswith("- Program not found") :
                row["Result"] = "Not Found"
        # if success we check the number of states with NuSMV
        if row["Result"] == "Found" :
            try :
                sizes = [] 
                regex = r"(\d*\^(\d+(\.\d\d)?))" # a regex for n^m pattern
                output = subprocess.run(["NuSMV","-r", "../output/"+fileName.replace('.spec','.imp')], capture_output=True).stdout.decode()
                for line in output.splitlines() : 
                    sizes = re.findall(regex, line)
                    if (len(sizes) == 2 ) :
                        row["#R.States"] = sizes[0][0]
                        row["#T.States"] = sizes[1][0]
            except :
                print("Problem executing NuSMV")
                sys.exit()

    except subprocess.TimeoutExpired:
        row["Global Time"] = "T/O"
        row["Result"] = "-"
        os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
        pass
    return row


# main code, it runs the function for all the examples
maindir = "../examples/"
timeout = 1600 # by default we set a timeout of 30min

examples = ["mutex", "phils","readerswriters","barrier", "peterson","arbiter","fullarbiter","pnueliarbiter"]
commands = ["exp2", "exp4", "exp8", "lineal10", "lineal100", "tokenexp2", "tokenexp4", "tokenexp8","tokenlineal10","tokenlineal100"]
token_commands = ["tokenexp2", "tokenexp4", "tokenexp8","tokenlineal10","tokenlineal100"]
token_examples = ["arbiter","fullarbiter","pnueliarbiter"]
if len(sys.argv) == 1 :
    print("\nUsage: python run_benchmark.py <command> <example>")
    print("""
where: 
<command> in ["all","exp2", "exp4", "exp8", "lineal10", "lineal100", "tokenexp2", "tokenexp4", "tokenexp8","tokenlineal10","tokenlineal100"]
<example> in ["all","mutex", "phils","readerswriters","barrier", "peterson","arbiter","fullarbiter","pnueliarbiter"]
all: runs the all the benchmarks/commands
           """)
    sys.exit()

target = examples
# the script may take as an argument a specific example
try :
    arg = sys.argv[1]
    assert arg in commands or arg == "all"
    if arg != "all" :
        commands = [arg]
except : 
    command = commands # default command
    pass

try :
    arg = sys.argv[2]
    assert arg in examples or arg == "all"
    if arg != "all" :
        target = [arg]
except :
    pass 



instances = {}
instances["phils"] = ["phils3","phils4","phils5","phils6","phils7"]
instances["mutex"] = ["mutex2","mutex3","mutex4","mutex5", "mutex6","mutex7"]
# examples with 4 readers are removed, all them give a timeout in the sat
instances["readerswriters"] = ["readers1writers1","readers2writers1","readers3writers1", "readers1writers2",
                                "readers2writers2","readers3writers2", "readers1writers3","readers2writers3","readers3writers3"]
instances["barrier"] = ["tsensebarrier2","tsensebarrier3","tsensebarrier4"]
instances["peterson"] = ["peterson2","peterson3"]
instances["arbiter"] = ["arbiter2","arbiter3","arbiter4","arbiter4","arbiter5"]
instances["pnueliarbiter"] = ["arbiter2","arbiter3","arbiter4","arbiter4","arbiter5"]
instances["fullarbiter"] = ["fullarbiter2","fullarbiter3","fullarbiter4","fullarbiter4","fullarbiter5"]

scopes = {}
scopes["phils3"] = [13,14]
scopes["phils4"] = [13,14]
scopes["phils5"] = [13,14]
scopes["phils6"] = [13,14]
scopes["phils7"] = [13,14]
scopes["mutex2"] = [3,4]
scopes["mutex3"] = [3,4]
scopes["mutex4"] = [3,4]
scopes["mutex5"] = [3,4]
scopes["mutex6"] = [3,4]
scopes["mutex7"] = [3,4]
scopes["readers1writers1"] = [5,6]
scopes["readers2writers1"] = [11,12]
scopes["readers3writers1"] = [23,24]
scopes["readers4writers1"] = [50,51] # this is a timeout
scopes["readers1writers2"] = [5,6]
scopes["readers2writers2"] = [11,12]
scopes["readers3writers2"] = [23,24]
scopes["readers4writers2"] = [50,51] # this is a timeout
scopes["readers1writers3"] = [5,6]
scopes["readers2writers3"] = [11,12]
scopes["readers3writers3"] = [23,24]
scopes["readers4writers3"] = [50,51] # this is a timeout
scopes["tsensebarrier2"] = [15,16]
scopes["tsensebarrier3"] = [15,16]
scopes["tsensebarrier4"] = [15,16]
scopes["peterson2"] = [11,12]
scopes["peterson3"] = [19,20]
scopes["arbiter2"] = [11,12]
scopes["arbiter3"] = [11,12]
scopes["arbiter4"] = [11,12]
scopes["arbiter5"] = [11,12]
scopes["fullarbiter2"] = [11,12]
scopes["fullarbiter3"] = [11,12]
scopes["fullarbiter4"] = [11,12]
scopes["fullarbiter5"] = [11,12]
scopes["pnueliarbiter2"] = [11,12]
scopes["pnueliarbiter3"] = [11,12]
scopes["pnueliarbiter4"] = [11,12]
scopes["pnueliarbiter5"] = [11,12]

script = {
           "exp2" : "batch2ExpSynt.sh",
           "exp4" : "batch4ExpSynt.sh",
           "exp8" : "batch4ExpSynt.sh",
           "lineal10" : "batchLineal10Synt.sh",
           "lineal100" : "batchLineal100Synt.sh",
           "tokenexp2" : "token2ExpSynt.sh",
           "tokenexp4" : "token4ExpSynt.sh",
           "tokenexp8" : "token8ExpSynt.sh",
           "tokenlineal10" : "token10LinealSynt.sh",
           "tokenlineal100" : "token100LinealSynt.sh"
}

for command in commands :
    for example in target :
        if (example in token_examples and not (command in token_commands)) or (not (example in token_examples) and (command in token_commands)) :
            continue; 
        results = []
        #for scope in scopes[example] :
        for instance in instances[example] :
            for scope in scopes[instance] :
                row = run_example(script[command],instance, maindir+example+"/", instance+".spec", f'''{scope}''', timeout)
                results.append(row)
        # finally a .cvs is generated
        keys = results[0].keys()
        # the results are saved in a file
        with open(f'results/results-{command}-{example}.csv', 'w', newline='') as output_file:
            dict_writer = csv.DictWriter(output_file, keys)
            dict_writer.writeheader()
            dict_writer.writerows(results)


       
   
