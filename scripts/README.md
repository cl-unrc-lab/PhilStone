# This folder provides the main scripts for executing the tool

The basic scrips for testing the benchmark are the folowing:

+ batch2ExpSynth.sh executes the tool with the progression 2,4,8,16
+ batch4ExpSynth.sh executes the tool with the progression 2,8,18,32
+ batchLinealSynth.sh executes the tool with the progression 10,20,30,40
+ noCexSynth.sh executes the tool in which no counterexamples are used for synthesizing

# Running the scrips

For running the scripts you have to execute the corresponding scripts together with the scope, for instance:

./batch2ExpSynth.sh 16 ../examples/phils/Phils3.spec 

Other scripts are also provided but they are experimental.
