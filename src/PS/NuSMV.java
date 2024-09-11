package PS;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import FormulaSpec.AF;
import FormulaSpec.AG;
import FormulaSpec.BoolVar;
import FormulaSpec.Conjunction;
import FormulaSpec.Disjunction;
import FormulaSpec.EF;
import FormulaSpec.EG;
import FormulaSpec.EnumConstant;
import FormulaSpec.EnumVar;
import FormulaSpec.EqComparison;
import FormulaSpec.Expression;
import FormulaSpec.F;
import FormulaSpec.Formula;
import FormulaSpec.G;
import FormulaSpec.Negation;
import FormulaSpec.Own;
import FormulaSpec.Type;
import FormulaSpec.U;
import FormulaSpec.W;
import LTS.LTS;
import Spec.ProcessSpec;
import Spec.Spec;

/**
 * It provides basic methods creating NuSMV specs
 * @author pablo
 *
 */
public class NuSMV {
	
	/**
	 * 
	 * @return	A NuSMV Model corresponding to the Concurrent Program
	 */
	public static String generateNuSMVSpec(HashMap<String, LTS> mapProcessModels, HashMap<String, LTS> mapInsModels, HashMap<String, Boolean> changed, Spec mySpec, boolean open){
	
		// WE CONSTRUCT THE PROGRAM
		String program = "";
		String space = "    ";
		
		LinkedList<String> definedProcesses = new LinkedList<String>(); // a list to save the processes that must be defined in the program
		Iterator<String> it = mapInsModels.keySet().iterator();
		while(it.hasNext()){
			String currentIns = it.next();
			if (!changed.get(currentIns) && !definedProcesses.contains(mySpec.getInstanceTypes().get(currentIns))) // if not changed and the process is not in the list
				definedProcesses.add(mySpec.getInstanceTypes().get(currentIns));
			if (changed.get(currentIns)) // if changed we add it
				definedProcesses.add(currentIns);
		}
		
		HashMap<String, String> globalVars = mySpec.getGlobalVarsTypes();
		Formula prop =  mySpec.getGlobalProperty();
		LinkedList<String> writtenProcesses = new LinkedList<String>(); // a list to keep track of the written processes until now to avoid repetitions
		
		// first we declare the enum types, an enum type for each process
		//Iterator<String> it1 = processes.keySet().iterator();
		program += "MODULE main \n\n";
		program += "VAR\n";
		Iterator<String> it1 = definedProcesses.iterator();
		while (it1.hasNext()){
			String currentProcess = it1.next();
			LTS currentLTS = null;
			if (mapProcessModels.containsKey(currentProcess)) // if it is a process defined in the program
				currentLTS = mapProcessModels.get(currentProcess);
			else // otherwise is an instance with its own process definition
				currentLTS = mapInsModels.get(currentProcess);
			//program += space + "state"+currentProcess +" : {";
			//LinkedList<String> nodes = currentLTS.getEqClassesNames();
			//for (int i=0; i<nodes.size(); i++){
				//program += (i==0)? nodes.get(i) : ","+nodes.get(i);
			//}
			//program += "};\n";
		}
		
		// now for those 
		// now the global vars
		Iterator<String> it2 = globalVars.keySet().iterator();
		//program += "Global ";
		while (it2.hasNext()){
			String currentVar = it2.next();
			//if (it2.hasNext())
			//	program += currentVar+" : "+ globalVars.get(currentVar)+",";
			//else
				//program += "Global "+currentVar+" : "+ globalVars.get(currentVar)+";\n"; // this has to be added when we have monitors			
				if (!mySpec.isPrimVar(currentVar))
					program += space + "Av_"+currentVar+" : boolean;\n"; // for each global var we have a lock
				if (globalVars.get(currentVar).equals("BOOL") || globalVars.get(currentVar).equals("PRIMBOOL"))
					program += space + "Prop_"+currentVar+" : boolean;\n"; // and the corresponding current var
				// we add the enums
				if (globalVars.get(currentVar).equals("ENUM") || globalVars.get(currentVar).equals("PRIMENUM")){
					program += space + "EnumVar_"+currentVar+":{";
					LinkedList<String> values = ((EnumVar) mySpec.getGlobalVarByName(currentVar)).getValues();
					for (int k=0; k<values.size();k++){
						if (k==0)
							program += values.get(k);
						else
							program += ","+ values.get(k);
					}
					program += "};\n";
				}
				//	program += space + "EnumVar_"+currentVar+""
				// TO DO: ADD INTEGERS
				// we need to distinguish between locks, ints and bools
		}
		program += "\n";
		
		// we generate the instances for the processes 
		//Iterator<String> it5 = instances.keySet().iterator();
		Iterator<String> it5 = mapInsModels.keySet().iterator();
		while (it5.hasNext()){
			String currentInstance = it5.next();
			//program +=  currentInstance+":";
			if (changed.get(currentInstance))
				program  += space + currentInstance +":process "+currentInstance+"Process(";
			else
				program  += space + currentInstance +":process "+ mySpec.getInstanceTypes().get(currentInstance)+"(";
			LinkedList<String> parameters = mySpec.getActualPars(currentInstance);
			// in NuSMV the global vars that are used in the process need to be passed as pars
			// we add the used shared vars to the parameters of the methods
			for (String gvar:mySpec.getGlobalVarsNames()){
				if (!parameters.contains(gvar) && (mySpec.getProcessSpec(currentInstance).usesSharedVar(gvar) || (mySpec.isTokenRing() && gvar.contains("send"))))
					parameters.add(gvar);
			}
			//for (int i=parameters.size()-1; i>=0;i--){
			for (int i=0; i<parameters.size();i++){
				if (i==0 && parameters.size()>=1){
						//program+=parameters.get(i) + ", Av_"+parameters.get(i); // this must be changed for monitors
					if (mySpec.getGlobalVarType(parameters.get(i)) == Type.BOOL)
						program+= "Prop_"+parameters.get(i)+", Av_"+parameters.get(i);
					if (mySpec.getGlobalVarType(parameters.get(i)) == Type.PRIMBOOL)
						program+= "Prop_"+parameters.get(i);
					if (mySpec.getGlobalVarType(parameters.get(i)) == Type.LOCK)
						program+= "Av_"+parameters.get(i);
				}
				else{
					if (mySpec.getGlobalVarType(parameters.get(i)) == Type.BOOL)
						program+= ","+"Prop_"+parameters.get(i)+", Av_"+parameters.get(i);
					if (mySpec.getGlobalVarType(parameters.get(i)) == Type.PRIMBOOL)
						program+= ","+"Prop_"+parameters.get(i);
					if (mySpec.getGlobalVarType(parameters.get(i)) == Type.LOCK && parameters.size()>1){
						program+= ","+"Av_"+parameters.get(i);
					}
					if (mySpec.getGlobalVarType(parameters.get(i)) == Type.LOCK && parameters.size()==1){
						program+= "Av_"+parameters.get(i);
					}
				}
			}
			program += ");\n";
		}
		
		// in the case of open systems we generate an environment
		if (open){
			program += space + "env :process Env(";
			LinkedList<String> primVars = mySpec.getGlobalVarsNamesByType(Type.PRIMBOOL);
			for (int i=0; i<primVars.size();i++){
				if (i==0 && primVars.size()>=1){
					if (!mySpec.isTokenRing() || !primVars.get(i).contains("send")){
						if (mySpec.getGlobalVarType(primVars.get(i)) == Type.PRIMBOOL) // by now all are primbools
							program+= "Prop_"+primVars.get(i);
					}
				}
				else{
					if (!mySpec.isTokenRing() || !primVars.get(i).contains("send")){
						if (mySpec.getGlobalVarType(mySpec.getGlobalVarsNames().get(i)) == Type.PRIMBOOL)
								program+= ","+"Prop_"+mySpec.getGlobalVarsNames().get(i);	
					}
				}
			}
		program += ");\n";
		}
			
		// we set the init formula
		program += "ASSIGN\n";
		LinkedList<String> initialisedVars = new LinkedList<String>();
		String lastInstance = ""; // to keep some instance
		for (String currentInstance:mapInsModels.keySet()){
			int k=0;
			for (String par:mySpec.getActualPars(currentInstance)){
				ProcessSpec currentProcess = mySpec.getProcessByName(mySpec.getInstanceTypes().get(currentInstance));
				String fpar = currentProcess.getIthFormalPar(k).getName();
				if (!initialisedVars.contains(par)){
					initialisedVars.add(par);
					if (mySpec.getGlobalVarType(par) == Type.BOOL){
						program += space + "init(Prop_"+par+") := "+ mapInsModels.get(currentInstance).getNuXMVInitValue(fpar) + ";\n";
						program += space +"init(Av_"+par+") := TRUE;\n"; // we assume that resources are available at the beginning					
					}
					if (mySpec.getGlobalVarType(par) == Type.PRIMBOOL)
						program += space + "init(Prop_"+par+") := "+ mapInsModels.get(currentInstance).getNuXMVInitValue(fpar) + ";\n";
					if (mySpec.getGlobalVarType(par) == Type.LOCK){
						program += space + "init(Av_"+par+") := TRUE;\n";	
					}
				}
				k++;
			}
			lastInstance = currentInstance;
		}
		// we initialised the rest of the vars
		for (String gvar:globalVars.keySet()){
			if (!initialisedVars.contains(gvar)){ // if not initialased
				if (mySpec.getGlobalVarType(gvar) == Type.BOOL){
					program += "init(Prop_"+gvar+") := "+ mapInsModels.get(lastInstance).getNuXMVInitValue("Prop_"+gvar) + ";\n";
					program += "init(Av_"+gvar+") := "+ mapInsModels.get(lastInstance).getNuXMVInitValue("Av_"+gvar) + ";\n";					
				}
				if (mySpec.getGlobalVarType(gvar) == Type.PRIMBOOL)
					program += "init(Prop_"+gvar+") := "+ mapInsModels.get(lastInstance).getNuXMVInitValue("Prop_"+gvar) + ";\n";
				if (mySpec.getGlobalVarType(gvar) == Type.LOCK)
					program += "init(Av_"+gvar+") := "+ mapInsModels.get(lastInstance).getNuXMVInitValue("Av_"+gvar) + ";\n";
			}
		}
		
		// the global property is written down
		if (!open){
			program += "LTLSPEC\n";
			program += space + generateNuSMVFormula(mySpec.getGlobalProperty())+"\n";
					
		}
		else{ /// if it is an open system we generate the assumptions
			program += "LTLSPEC\n";
			program +=  space +"(! ("+ generateNuSMVFormula(mySpec.getAssumptionProperty())+")) | ("+ generateNuSMVFormula(mySpec.getGlobalProperty())+")\n";
		}
		
		// the processes are written down
		//Iterator<String> it3 = processes.keySet().iterator();
		Iterator<String> it3 = definedProcesses.iterator();		
		while (it3.hasNext()){
			HashMap<String, String> pars = new HashMap<String, String>();
			LinkedList<String> parList = new LinkedList<String>();
			String currentProcess = it3.next();
			
			if (mapProcessModels.containsKey(currentProcess)){
							
				LinkedList<String> processBoolPars = mySpec.getProcessByName(currentProcess).getBoolParNames();
				for (int i=0; i<processBoolPars.size();i++){
					pars.put(processBoolPars.get(i), "BOOL");
				}
				LinkedList<String> processPrimBoolPars = mySpec.getProcessByName(currentProcess).getBoolPrimParNames();
				for (int i=0; i<processPrimBoolPars.size();i++){
					pars.put(processPrimBoolPars.get(i), "PRIMBOOL");
				}			
				LinkedList<String> processLockPars = mySpec.getProcessByName(currentProcess).getLockParNames();
				for (int i=0; i<processLockPars.size();i++){
					pars.put(processLockPars.get(i), "LOCK");
				}
				// we add all the parameters in the list of the parameters
				parList.addAll(mySpec.getProcessByName(currentProcess).getParNames());
				// we also add the global vars that are not in the params and are used by the process
				for (String gvar:mySpec.getGlobalVarsNames()){
					if ((mySpec.getProcessByName(currentProcess).usesSharedVar(gvar) || (mySpec.isTokenRing() && gvar.contains("send"))) && !pars.containsKey(gvar)){
						// we add the globalvar as a parameter
						parList.add(gvar);
						if (mySpec.getGlobalVarType(gvar) == Type.BOOL){
							pars.put(gvar, "BOOL");
						}
						if (mySpec.getGlobalVarType(gvar) == Type.PRIMBOOL){
							pars.put(gvar, "PRIMBOOL");
						}
						if (mySpec.getGlobalVarType(gvar) == Type.LOCK){
							pars.put(gvar, "LOCK");
						}
					}
				}
					
				program += mapProcessModels.get(currentProcess).toNuSMVProcess(pars, parList, currentProcess, currentProcess); // no parameters by now
				
			}
			else{
				parList.addAll(mySpec.getProcessByName(mySpec.getInstanceTypes().get(currentProcess)).getParNames());
				LinkedList<String> processPars = mySpec.getProcessByName(mySpec.getInstanceTypes().get(currentProcess)).getBoolParNames();
				for (int i=0; i<processPars.size();i++){
					pars.put(processPars.get(i), "BOOL");
				}
				LinkedList<String> processPrimBoolPars = mySpec.getProcessByName(mySpec.getInstanceTypes().get(currentProcess)).getBoolPrimParNames();
				for (int i=0; i<processPrimBoolPars.size();i++){
					pars.put(processPrimBoolPars.get(i), "PRIMBOOL");
				}
				
				LinkedList<String> processLockPars = mySpec.getProcessByName(mySpec.getInstanceTypes().get(currentProcess)).getLockParNames();
				for (int i=0; i<processLockPars.size();i++){
					pars.put(processLockPars.get(i), "LOCK");
				}
				
				for (String gvar:mySpec.getGlobalVarsNames()){
					if ((mySpec.getProcessByName(mySpec.getInstanceTypes().get(currentProcess)).usesSharedVar(gvar) || (mySpec.isTokenRing() && gvar.contains("send"))) && !pars.containsKey(gvar)){
						// we add the globalvar as a parameter
						parList.add(gvar);
						if (mySpec.getGlobalVarType(gvar) == Type.BOOL){
							pars.put(gvar, "BOOL");
						}
						if (mySpec.getGlobalVarType(gvar) == Type.PRIMBOOL){
							pars.put(gvar, "PRIMBOOL");
						}
						if (mySpec.getGlobalVarType(gvar) == Type.LOCK){
							pars.put(gvar, "LOCK");
						}
					}
				}
				
				program += mapInsModels.get(currentProcess).toNuSMVProcess(pars, parList, currentProcess+"Process", currentProcess);
				program += "\n";
				
			}
		}
		
		// If it is an open system we write an environment process
		if (open)	
			program += generateEnvProcess(mySpec);
				
		//System.out.println(program);
		return program;
	}
	
	/**
	 * @param f
	 * @param state
	 * @return	A String representation of the global formula in NuSMV spec language
	 */
	private static String generateNuSMVFormula(Formula f){
		String result = "";
		// if numQUan =0  then we leave state otherwise we increment by one
		//String quantifiedVar = "s"+numQuan;
		if (f instanceof BoolVar){
			BoolVar theVar = (BoolVar) f;
			if (theVar.getOwner().equals("global"))
				//result += ((BoolVar) f).toAlloy(mapInsModels.get(this.instancesList.get(0)).getName()+"Process", "elem."+this.instancesList.get(0));
				result += "Prop_"+((BoolVar) f).getUnqualifiedName();
			else
				//result +=  ((BoolVar) f).toAlloy(mapInsModels.get(theVar.getOwner()).getName()+"Process", "s."+theVar.getOwner());
				result +=  theVar.getOwner()+".Prop_"+theVar.getUnqualifiedName();
			return result;
		}
		if (f instanceof EqComparison){
			result += "("+generateNuSMVExpr(((EqComparison) f).getExp1())+"="+generateNuSMVExpr(((EqComparison) f).getExp2())+")";
			return result;
		}
		if (f instanceof Own){
			Own theVar = (Own) f;
			result += theVar.toString();
			//result +=  ((Own) f).toAlloy(mapInsModels.get(theVar.getOwner()).getName()+"Process", "elem."+theVar.getOwner());
			return result;
		}
		if (f instanceof Conjunction){
			Conjunction theCon = (Conjunction) f;
			result +=  "("+generateNuSMVFormula(theCon.getExpr1())+ ") & ("+generateNuSMVFormula(theCon.getExpr2())+")";
			return result;
		}
		if (f instanceof Disjunction){
			Disjunction theDis = (Disjunction) f;
			result +=  "(" + generateNuSMVFormula(theDis.getExpr1())+ " | "+generateNuSMVFormula(theDis.getExpr2()) + ")";
			return result;
		}
		if (f instanceof Negation){
			Negation theNeg = (Negation) f;
			result +=  "!("+generateNuSMVFormula(theNeg.getExpr1()) + ")";
			return result;
		}
		if (f instanceof AG){
			result += "( G ("+generateNuSMVFormula(((AG) f).getExpr1())+"))";
			return result;
		}
		if (f instanceof EG){
			result += "( G ("+generateNuSMVFormula(((EG) f).getExpr1())+"))";
			return result;
		}
		if (f instanceof EF){
			result += "(F("+generateNuSMVFormula(((EF) f).getExpr1())+"))";
			return result;
		}
		if (f instanceof AF){
			result += "(F ("+generateNuSMVFormula(((AF) f).getExpr1())+"))";
			return result;
		}
		if (f instanceof F){
			result += "(F ("+generateNuSMVFormula(((F) f).getExpr1())+"))";
			return result;
		}
		if (f instanceof G){
			result += "( G ("+generateNuSMVFormula(((G) f).getExpr1())+"))";
			return result;
		}
		if (f instanceof U){
			U theF = (U) f;
			result +=  "(" + generateNuSMVFormula(theF.getExpr1())+ " U "+generateNuSMVFormula(theF.getExpr2()) + ")";
			return result;
		}
		if (f instanceof W){
			W theF = (W) f;
			result +=  "(" + generateNuSMVFormula(theF.getExpr1())+ " U "+generateNuSMVFormula(theF.getExpr2()) + ") | (G !"+generateNuSMVFormula(theF.getExpr2())+")";
			return result;
		}
		
		throw new RuntimeException("nuSMV Bounded Model Checking not defined for the given formula");
	}
	
	/**
	 * @return	A NuSMV process representing the environment.
	 */
	private static String generateEnvProcess(Spec mySpec){
		String result = "";
		String space = "    ";
		// write the global vars as a parameters
		LinkedList<String> boolVars = mySpec.getGlobalVarsNamesByType(Type.PRIMBOOL);
		result += "MODULE Env(";
		for (int i=0; i< boolVars.size(); i++){
				if (!mySpec.isTokenRing() || !boolVars.get(i).contains("send"))
					result += i==0?boolVars.get(i):","+boolVars.get(i);
		}
		result += ")\n";
		result += "ASSIGN\n";
		for (String var : mySpec.getGlobalVarsNamesByType(Type.PRIMBOOL)){
			if (!var.contains("token") && (!mySpec.isTokenRing() || !var.contains("send"))){
				result += "next("+var+") :=case \n";
				result += space+"TRUE: {TRUE};\n";
				result += space+"TRUE: {FALSE};\n";
				result += "esac;\n";
			}
			else{
				if (!mySpec.isTokenRing() || !var.contains("send"))
					result += "next("+var+") := {"+var+"};\n";
			}
		}
		for (String var : mySpec.getGlobalVarsNamesByType(Type.ENUM)){
			result += "next("+var+") :=case \n";
			for (String value : ((EnumVar) mySpec.getGlobalVarByName(var)).getEnumType().getValues()){
				result += space+"TRUE: {"+value+"};\n";	
			}
			result += "esac;";
		}
		result += "FAIRNESS running;\n";
		return result;
		
	}
	
	/**
	 * @param e	an expression
	 * @return	The NuSMV representation of the expression
	 */
	private static String generateNuSMVExpr(Expression e){
		String result = "";
		if (e instanceof EnumConstant){
			result += e.toString();
			return result;	
		}
		if (e instanceof EnumVar){
			EnumVar theVar = (EnumVar) e;
			if (theVar.getOwner().equals("global"))
				result += "Prop_"+((EnumVar) e).getUnqualifiedName();
			else
				result +=  theVar.getOwner()+".EnumVar_"+theVar.getUnqualifiedName();
			return result;
		}
		throw new RuntimeException("nuSMV Bounded Model Checking not defined for the given expression.");
	}
}
