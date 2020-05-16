# PhilStone
A simple tool for the synthesis of concurrent programs using Alloy-Tool and Model Checking

- Compiling the Tool

You can compile the code with the ant tool, just running 'ant' The .class files will be generated and saved in folder build/


- Running the tool using the script

just: cd scripts/

and execute: ./nusmvSynth [SCOPE] [SPEC]

for instance:

 ./nusmvSynt.sh 16 ../examples/phils/Phils3.spec
 
synthesizes the phils example with a scope of 16. All the examples are in examples/

- Generating JAR file:

 The .jar file can be generated executing 'ant jar', you can find the file in bin/jar, the tool also can be executed using the jar.  

- The examples can be found in examples/ folder, they use a pre/post condition style of specification. After running the tool, an Alloy
specification is generated and saved in the "output" folder. This specification is in First-Order Logic.
 

