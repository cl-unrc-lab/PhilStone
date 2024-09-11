package PS;

import java.util.*;

import java.io.FileWriter;
import java.io.InputStreamReader;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.PrintStream;
import java.io.ByteArrayOutputStream;
import java.lang.reflect.Method;
import java.lang.reflect.Field;
import java.lang.Runtime;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import FormulaSpec.Formula;
import FormulaSpec.Type;
import LTS.*;
import Spec.*;
import Utils.XMLAlloy;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import faulty.Program;
import formula.FormulaElement;
import mc.DCTL_MC;
import mc.FormulaParser;
import mc.ProgramParser;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Paths;



/**
 * An implementation of search using batches. The idea is as follows:
 * 
 * 
 * 
 * @author pablo
 *
 */
public class BatchSearch extends BasicSearch {
	private LinkedList<Integer> progression; // the progression for algorithm
	private LinkedList<CounterExample> foundCexs;
	

	public BatchSearch(Spec mySpec, String outputPath, String templatePath, boolean showInfo, boolean printPDF, int scope, boolean alloySearch, int pathBound, LinkedList<Integer> progression) {
		super(mySpec, outputPath, templatePath, showInfo, printPDF, scope, alloySearch, pathBound);
		this.progression = progression;
		foundCexs = new LinkedList<CounterExample>();
	}
	
	/**
	 * This method start the search: it set all the variables and call {@code search}
	 */
	public void startSearch() {
		
		System.out.println("Using Batch Synthesis ...");
		
		
		
		// STEP 1: We generate the initial model for each instance
		// this initial model consider as much non-determinism as possible.
		// this is obtained via Alloy.
		long overallStartTime = System.currentTimeMillis();
		for (int i=0; i<processes.size(); i++){
			
			// we save the actual time
			long startTime = System.currentTimeMillis();    

			// Obtain the current i process
			String currentProcess = processes.get(i);
			
			// the output file for the Alloy model
			String outputfilename = outputPath+currentProcess+".xml";
			
			// we obtain the alloy specification for the initial model
			String metamodel = mySpec.metamodelToString(currentProcess, templatePath, scope);
			try{			
				// we write the specification to a file
			    PrintWriter writer = new PrintWriter(outputPath+currentProcess+"Template.als", "UTF-8");
			    writer.print(metamodel);
			    writer.close();
			} catch (IOException e) {
				System.out.println("Error trying to write the alloy specifications for the processes.");
				e.printStackTrace(System.out);
			}
		
			A4Solution sol = this.getAlloyInitialSolution(currentProcess);
			try{
				sol.writeXML(outputfilename); 
			}
			catch (Exception e){
				//System.out.println("Error trying to write the alloy specifications for the processes.");
				//e.printStackTrace(System.out);
				double estimatedTime = (System.currentTimeMillis() - overallStartTime)/1000.0;
				System.out.println("- Spec UNSAT");
				System.out.println("+ Total Time (Seconds): "+estimatedTime);
				
				System.exit(0);
			}
			LTS lts = new LTS(mySpec.getProcessByName(currentProcess));
			lts.setName(currentProcess);
			if (mySpec.isTokenRing())
				lts.setTokenRing();
			
			// we read the LTS
			lts.fromAlloyXML(outputfilename);
			
			// we store the candidate model for each process
			mapProcessModels.put(currentProcess, lts);
			
			// we store the laxest model for each instance. 
			// At the beginning they coincide with those of the processes
			for (int j=0; j<instancesList.size();j++){
				if (instances.get(instancesList.get(j)).equals(currentProcess)){
					// For each instance of process, we set the model as the initial model
					mapInsModels.put(instancesList.get(j), lts); 
					if (this.printPDF)
						lts.toDot(outputPath+"lax"+instancesList.get(j)+".dot");
				}
			}
		
			// Compute the estimated time
			long estimatedTime = System.currentTimeMillis() - startTime;
			
			// the time is took to compute the initial model is printed, should be added if verbose is set on
			// System.out.println(currentProcess+" time:" + estimatedTime);
		}
		double estimatedTime = (System.currentTimeMillis() - overallStartTime)/1000.0;
		System.out.println("+ Local Models Generated");
		System.out.println("+ Time for generating the models (seconds): "+ estimatedTime);
		
		// STEP 2: we call the search procedure
		
		boolean found = false;
		
		// For all the steps in the progression we try the search
		for (int batch : this.progression) {
		//System.out.println("Batch:"+batch);
			found = search(0, scope, batch);
			if (found)
				break;
			else {
				this.foundCexs.clear();
				this.foundCexs.addAll(this.cexs);
			}// endelse
				
		}// end for
		double totalTime = (long)(System.currentTimeMillis() - overallStartTime)/1000.0;
		if (found){
			// If found, the program is saved to the output folder
			System.out.println("+ Program Synthesized, saved to output folder.."); 
			
			// The number of iteration is shown
			System.out.println("+ Number of iterations: "+iterations);
			System.out.println("+ Total Time (seconds): "+totalTime);
			
			// If prinPDF is true, then the dots are generated
			if (this.printPDF){  // we print the dots			
				for (int i=0; i<this.instancesList.size(); i++)
					this.mapInsModels.get(instancesList.get(i)).toDot(outputPath+instancesList.get(i)+"final.dot");
			}
			// the program is written to the output folder
			try{
				PrintWriter writer = new PrintWriter(outputPath+mySpec.getName()+".imp", "UTF-8");
				writer.print(syntProgram);
				writer.flush();
				writer.close();
			}
			catch(Exception e){
				System.out.println(e);
			}
		}
		else{ // Otherwise: the program is not found
			System.out.println("- Program not found.."); 
			System.out.println("+ Number of iterations: "+iterations);
			System.out.println("+ Total Time (seconds): "+totalTime);
		}
	}
	
	/**
	 * This is the main search procedure.
	 * @param instance
	 * @param scope
	 * @return	true iff an implementation is found
	 */
	public boolean search(int insNumber, int scope, int batch) {
		
		// The current instance's name
		String currentIns = instancesList.get(insNumber);
		
		//this.currentSol[insNumber] = null;
		if (insNumber == (this.numberIns - 1)){ //  Base Case
			
			// A message to know that we are in the last instance
			//System.out.println("Last instance: "+currentIns);
			
			// we set the specification of the current instance process
			LTS lts = new LTS(mySpec.getProcessSpec(currentIns));
			
			// we set the name of the current instance
			lts.setName(currentIns);
			
			// if a token ring then we set this out
			if (mySpec.isTokenRing())
				lts.setTokenRing();
			
			// 
			LTS formerLTS = mapInsModels.get(currentIns);
			boolean checkResult = false;
			checkResult = selectChecker(currentIns);
			iterations++;
			if (checkResult)
				return true;
			
			
			int j = 0;		
			
			// We obtain the solver for the actual instance with the actual cexs
			A4Solution solver = this.getAlloySolutionWithCexs(currentIns, this.foundCexs);
			//A4Solution solver = this.getAlloySolution(currentIns);
			
			//System.out.println(cexs);
		
			while (solver.satisfiable() && j < batch){ //add refined & !disjointCexFound.get(currentIns)
				
				// one iteration more is performed
				this.iterations++;
				
				// we try to write the model, an exception if this is not possible
				try{
					solver.writeXML(outputPath+"temp"+j+".xml");
				}
				catch (Exception e){ // an exception otherwise
					System.out.println(e);
				}
				
				// we read the alloy instance and write this out to a LTS
				lts.fromAlloyXML(outputPath+"temp"+j+".xml");
				// adn to dot
				lts.toDot(outputPath+currentIns+iterations+".dot");
				
				// we show the iteration number
				/// System.out.println("iteration:"+iterations);
				if (showInfo) 
					System.out.println("Instance "+ currentIns + ", Iteration Number:"+j);
				j++;
				
				// we map the current instance to the found lts
				mapInsModels.put(currentIns, lts);
				
				// the model was change
				changed.put(currentIns, new Boolean(true));	// we changed the model
				
				// we check the result
				checkResult = selectChecker(currentIns);	
				
				// if successful we are done
				if (checkResult)
					return true;	
				
				// otherwise we restore the previous model
				mapInsModels.put(currentIns, formerLTS);
				changed.put(currentIns, new Boolean(false));
				
				// and try the next one
				try{
					solver = solver.next();	
				}
				catch (Exception e){
					throw new RuntimeException("error generating solver");
				}
			}//end while					
		}// end of base case
		// RECURSIVE CASE:
		else{ 
				//System.out.println("Inspecting Instance: "+currentIns);
				int p=0; // aux var needed for numbering the files
				LTS lts = new LTS(mySpec.getProcessSpec(currentIns));
				lts.setName(currentIns);
				if (mySpec.isTokenRing())
					lts.setTokenRing();
				LTS formerLTS = mapInsModels.get(currentIns);
				int j = 0;
				if (this.search(insNumber+1, scope, batch)) // model check generates new counterexamples, 
					return true;
				// gets an initial solution for this instance
				A4Solution solver = this.getAlloySolutionWithCexs(currentIns, this.foundCexs);
				//A4Solution solver = this.getAlloySolution(currentIns);
				while (solver.satisfiable() && j < batch){  
					try{
						// we write the instance to a file
						solver.writeXML(outputPath+"temp"+p+".xml");
					}
					catch(Exception e){
						System.out.println("Input-Output Error trying to write Alloy files.");
						e.printStackTrace();//System.out.println(e);
						System.exit(0);
					}
					lts.fromAlloyXML(outputPath+"temp"+p+".xml");
					lts.toDot(outputPath+"instance"+insNumber+":"+p+".dot");
					p++;
					mapInsModels.put(currentIns, lts);
					changed.put(currentIns, new Boolean(true));	
					
					// we try with this model recursively
					if (this.search(insNumber+1, scope, batch)) // model check generates new counterexamples, 
						return true;
			
					//System.out.print("comeback to  instance"+currentIns);
					changed.put(currentIns, new Boolean(false));
					mapInsModels.put(currentIns, formerLTS);
								
					try{
						solver = solver.next();	
					}
					catch (Exception e){
						throw new RuntimeException("error generating solver");
					}
					j++;
				}//endwhile
		}			
		return false;
	}

	/**
	 * A simple implementatino of this method
	 */
	public void processCounterExample(CounterExample cex) {
		this.cexs.add(cex);
	}
	
}
