
package Spec;

import java.util.*;
import java.io.*;
import org.stringtemplate.v4.*;
import Utils.Pair;

import FormulaSpec.*;
import JFlex.Out;

/**
 * @author Pablo
 * A Class for the Specification of a Process
 */
public class ProcessSpec {
	private String name; // the name of the process
	private LinkedList<Action> actions; // the actions of the process
	private LinkedList<Var> sharedVars; // the global vars
	private LinkedList<Var> localVars;  // the local vars of the process
	private LinkedList<Var> pars;		// the parameters of the process
	private LinkedList<String> ownedVars; // this list keeps track of those vars that are "owned" by the process, i.e.,
								  // the process always has the lock of the variable, this allows for optimizations
								  // these are global vars.
	private LinkedList<TemporalFormula> invs; // the invariants of the process
	private LinkedList<String> instances; // the instances of the specification
	private LinkedList<EnumType> enums; // the enums defined in the specification
	private Spec mySpec;
	private Formula init;
	int intSize; // the size of the ints
	
	/**
	 * Basic Class Constructor
	 * @param name
	 */
	public ProcessSpec(String name) {
		this.name = name;
		this.sharedVars = new LinkedList<Var>();
		this.localVars = new LinkedList<Var>();
		this.pars = new LinkedList<Var>();
		this.actions = new LinkedList<Action>();
		this.invs = new LinkedList<TemporalFormula>();
		this.ownedVars = new LinkedList<String>();
		this.enums = new LinkedList<EnumType>();
	}
	
	/**
	 * Basic Class Constructor with intSize
	 * @param name
	 */
	public ProcessSpec(String name, int intSize) {
		this.name = name;
		this.sharedVars = new LinkedList<Var>();
		this.localVars = new LinkedList<Var>();
		this.pars = new LinkedList<Var>();
		this.actions = new LinkedList<Action>();
		this.invs = new LinkedList<TemporalFormula>();
		this.intSize = intSize;
		this.ownedVars = new LinkedList<String>();
		this.enums = new LinkedList<EnumType>();
	}

	/**
	 * 
	 * @return	the name of the Process
	 */
	public String getName() {
		return name;
	}

	/**
	 * Setter for the name
	 * @param name	the new name
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * Adds an action
	 * @param act
	 */
	public void addAction(Action act){
		actions.add(act);
	}
	
	/**
	 * Adds an invariant
	 * @param inv
	 */
	public void addInv(TemporalFormula inv){
		invs.add(inv);
	}
	
	/**
	 * Adds a shared variable
	 * @param v
	 */
	public void addSharedVar(Var v){
		sharedVars.add(v);
	}
	
	
	/**
	 * Adds an enum type tu the process spec
	 * @param e	the enumtype to be added
	 */
	public void addEnumType(EnumType e){
		this.enums.add(e);
	}
	
	public void addOwnedVar(String v){
		this.ownedVars.add(v);
	}
	
	public void addAllSharedVar(LinkedList<Var> list){
		sharedVars.addAll(list);
	}
	
	/**
	 * Adds a local var to the process
	 * @param v
	 */
	public void addLocalVar(Var v){
		localVars.add(v);
	}
	
	
	
	public void addPar(Var v){
		this.pars.add(v);
	}
	
	public void addInstance(String name){
		instances.add(name);
	}
	
	public void setInit(Formula f){
		this.init = f;
	}
	
	public Formula getInit(){
		return this.init;
	}
	
	public void setSpec(Spec mySpec){
		this.mySpec = mySpec;
	}
	
	/**
	 * Set the enum type of an enum variable
	 * @param v		the variable to which we set the enum
	 * @param values	 the set of values of the enum type 
	 */
	public void setTypeEnum(EnumVar v, LinkedList<String> values){
		if (this.localVars.contains(v)){ // if the var is already in the collection of shared vars
			for (EnumType e:this.enums){
				if (e.checkEqValues(values)){
					e.addVar(v);
					v.setEnumType(e);
				}
				else{
					EnumType etype = new EnumType();
					etype.addValues(values);
					etype.addVar(v);
					this.enums.add(etype);
				}
			}
		}
	}
	
	
	public Type getParType(String name){
		for (Var v:this.pars) {
			if (v.getName().equals(name))
				return v.getType();
		}
		return Type.ERROR;
	}
	
	public LinkedList<String> getSharedVarsNames(){
		return this.mySpec.getGlobalVarsNames();
	}
	
	
	public LinkedList<String> getOnlyLocksNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<mySpec.getLocks().size(); i++){
			if (mySpec.getLocks().get(i).isOnlyLock())
				result.add(mySpec.getLocks().get(i).getName());
		}
		return result;
	}
	
	
	public Type getSharedVarType(String var){
		return this.mySpec.getGlobalVarType(var);
	}
	
	
	public Var getLocalVarByName(String name){
		for (Var v:this.localVars){
			if (v.getName().equals(name))
				return v;
		}
		throw new RuntimeException("wrong var name...");
	}
	
	public Spec getSpec(){
		return this.mySpec;
	}
	
	/**
	 * 
	 * @return	the collection of enum types in this process
	 */
	public LinkedList<EnumType> getEnumTypes(){
		return this.enums;
	}
	
	public LinkedList<String> getValuesForEnum(String var){
		LinkedList<String> result = new LinkedList<String>();
		for (Var v:this.localVars){
			if (v.getName().equals(var) && v.getType() == Type.ENUM){
				result.addAll(((EnumVar) v).getValues());
				return result;
			}
		}
		throw new RuntimeException("Enum Variable not Found");
	}
	
	public LinkedList<String> getSharedVarsNamesByType(Type t){
		return this.mySpec.getGlobalVarsNamesByType(t);
	}
	
	public LinkedList<String> getOwnedSharedVarsNamesbyType(Type t){
		LinkedList<String> sharedVars = this.mySpec.getGlobalVarsNamesByType(t);
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.ownedVars.size(); i++){
			if (sharedVars.contains(this.ownedVars.get(i)))
				result.add(this.ownedVars.get(i));
		}
		return result;
	}
	
	
	/**
	 * 
	 * @param t
	 * @return	returns those global vars with names and type t which have an associated lock
	 */
	public LinkedList<String> getSharedVarsNamesByTypeWithLock(Type t){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.mySpec.getGlobalNonPrimVarsNamesByType(t).size(); i++){
			String current = this.mySpec.getGlobalNonPrimVarsNamesByType(t).get(i); 
			if (!this.isAnOwnedVar(current))
				result.add(current);
		}
		return result;
	}
	
	
	public LinkedList<String> getLocalVarsNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.localVars.size(); i++){
			result.add(this.localVars.get(i).getName());
		}
		return result;
	}
	
	public LinkedList<String> getLocalVarsNamesByType(Type t){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.localVars.size(); i++){
			if (this.localVars.get(i).getType()==t)
				result.add(this.localVars.get(i).getName());
		}
		return result; 
	}
	
	
	/**
	 * 
	 * @return	The names of the boolean parameters, EXCEPTING those that are in the owns clause or are of boolean primitive
	 */
	public LinkedList<String> getBoolParNamesWithLock(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.BOOL && !this.pars.get(i).isPrimType() && !this.isAnOwnedVar(this.pars.get(i).getName()) ){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	public LinkedList<String> getLockParNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.LOCK){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	public LinkedList<Lock> getLockPars(){
		LinkedList<Lock> result = new LinkedList<Lock>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.LOCK){
				result.add((Lock) this.pars.get(i));
			}
		}
		return result;	
	}
	
	public LinkedList<String> getParNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (Var v:pars){
			result.add(v.getName());
		}
		return result;
	}
	
	public LinkedList<String> getOwnedBoolParNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.BOOL && this.isAnOwnedVar(this.pars.get(i).getName()) ){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	/**
	 * 
	 * @return all the boolean par names
	 */
	public LinkedList<String> getBoolParNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.BOOL){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	/**
	 * 
	 * @return	The names of the primitive boolean parameters, EXCEPTING those that are in the owns clause 
	 */
	public LinkedList<String> getBoolPrimParNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.PRIMBOOL && !this.isAnOwnedVar(this.pars.get(i).getName())){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	/**
	 * 
	 * @param i
	 * @return	the ith formal parameter of the process
	 */
	public Var getIthFormalPar(int i){
		if (i > this.pars.size()-1)
			throw new RuntimeException("Wrong number of Formal Parameter");
		else{
			return this.pars.get(i);
		}
	}
	
	/**
	 * A method to check whether a process mention a global var o nor
	 * @param var
	 * @return	true when the global variable is mentioned in the process
	 */
	public boolean usesSharedVar(String var){
		for (int i=0; i<actions.size();i++){
			if (actions.get(i).usesVar(var))
				return true;
		}
		for (int i=0; i< invs.size();i++){
			if (invs.get(i).usesVar(var))
				return true;
		}
		return init.usesVar(var);
	}
	
	public boolean isAnOwnedVar(String name){
		for (int i=0; i< this.ownedVars.size(); i++){
			if (this.ownedVars.get(i).equals(name))
				return true;
		}
		return false;
	}
	
	
	/**
	 * 
	 * @return	the names of non-primitive Int parameters, excepting those that are in the owns clause
	 */
	public LinkedList<String> getIntParNamesWithLock(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.INT && !this.pars.get(i).isPrimType() && !this.isAnOwnedVar(this.pars.get(i).getName())){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	/**
	 * 
	 * @return	the names of non-primitive Enum parameters, excepting those that are in the owns clause
	 */
	public LinkedList<String> getEnumParNamesWithLock(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.ENUM && !this.pars.get(i).isPrimType() && !this.isAnOwnedVar(this.pars.get(i).getName())){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	public LinkedList<String> getOwnedIntParNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.INT && this.isAnOwnedVar(this.pars.get(i).getName())){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	
	public LinkedList<String> getOwnedEnumParNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.ENUM && this.isAnOwnedVar(this.pars.get(i).getName())){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	
	/**
	 * 
	 * @return all the int par names
	 */
	public LinkedList<String> getIntParNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.INT){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	/**
	 * 
	 * @return	the names of the pimitive-one paramaeter names, excepting those that are in the owns clause
	 */
	public LinkedList<String> getIntPrimParNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.INT && this.pars.get(i).isPrimType() && !this.isAnOwnedVar(this.pars.get(i).getName())){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	/**
	 * @return	the names of the primitive-one parameter names, excepting those that are in the owns clause
	 */
	public LinkedList<String> getEnumPrimParNames(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.pars.size();i++){
			if (this.pars.get(i).getType() == Type.ENUM&& this.pars.get(i).isPrimType() && !this.isAnOwnedVar(this.pars.get(i).getName())){
				result.add(this.pars.get(i).getName());
			}
		}
		return result;	
	}
	
	public String metamodelToString(String templateDir, int scope){
		
		// we save the local bool propositions
		List<String> localBoolProps = new ArrayList<String>();
		for (int i = 0; i < localVars.size(); i++){
			if (localVars.get(i).getType() == Type.BOOL)
				localBoolProps.add(localVars.get(i).getName());
				
		}
		
		
		
		localBoolProps.addAll(this.getOwnedSharedVarsNamesbyType(Type.BOOL)); // the owned vars are considered local for efficiency reasons
		localBoolProps.addAll(this.getOwnedSharedVarsNamesbyType(Type.PRIMBOOL));
		
		// we save the local int vars
		List<String> localIntVars = new ArrayList<String>();
		for (int i = 0; i < localVars.size(); i++){
			if (localVars.get(i).getType() == Type.INT)
				localIntVars.add(localVars.get(i).getName());
		}
		
		localIntVars.addAll(this.getOwnedSharedVarsNamesbyType(Type.INT));
		localIntVars.addAll(this.getOwnedSharedVarsNamesbyType(Type.PRIMINT));
		
		// we save the enum local vars
		List<String> localEnumVars = new ArrayList<String>();
		// a list to save the possible enum values
		List<String> enumValues = new ArrayList<String>();
		for (int i = 0; i < localVars.size(); i++){
			if (localVars.get(i).getType() == Type.ENUM){
				localEnumVars.add(localVars.get(i).getName());
				// we add the values of the variables to the enum values
				for(String v:((EnumVar) localVars.get(i)).getValues()){
					if (!enumValues.contains(v))
						enumValues.add(v);
				}
			}
		}
	
		localEnumVars.addAll(this.getOwnedSharedVarsNamesbyType(Type.ENUM));
		localEnumVars.addAll(this.getOwnedSharedVarsNamesbyType(Type.ENUMPRIM));
		
		// we set the actions
		List<Action> localActions = new ArrayList<Action>();
		List<Action> envActions = new ArrayList<Action>();
		for (int i = 0; i < actions.size(); i++){
			if (actions.get(i).getIsLocal())
				localActions.add(actions.get(i));
			else
				envActions.add(actions.get(i));
		}
		
		List<String> invariants = new ArrayList<String>(); // the invariants of the specification
		List<String> auxVars = new ArrayList<String>();    // the auxiliar vars needed for translating CTL to Alloy
		List<String> auxAxioms = new ArrayList<String>();  // the auxiliar axioms needed for translating CTL to Alloy
		List<String> auxPreds = new ArrayList<String>();   // the auxiliar axioms needed for translating CTL to Alloy
		for (int i=0; i<this.invs.size(); i++){
			invariants.add(invs.get(i).toAlloy(name+"Meta", "s"));
			auxVars.addAll(invs.get(i).generateAuxProps(name+"Meta"));
			auxAxioms.addAll(invs.get(i).generateAxioms());
			auxPreds.addAll(invs.get(i).generatePreds(name+"Meta"));
		}		
		
		List<Action> actions = new ArrayList<Action>();
		actions.addAll(localActions);
		actions.addAll(envActions);
		
		STGroup group = new STGroupDir(templateDir);
		ST st = mySpec.isTokenRing() ? group.getInstanceOf("TokenRingMetamodel") : group.getInstanceOf("Metamodel");
		if (st == null){ // linux uses uppercases for the metamodel!
			throw new RuntimeException("Template Folder Not Found");				
		}
		
		st.add("name", this.name);
		if (mySpec.isTokenRing()){
			// if it is a token ring then we remove hasToken, sendi, sendi+1
			for (int i=0; i< localBoolProps.size(); i++){
				if (localBoolProps.get(i).contains("hasToken"))
					localBoolProps.remove(i);
			}
		}
		st.add("boolProps", localBoolProps); // we add local boolean variables
		st.add("intVars", localIntVars); // we add the local int variables
		st.add("enumVars", localEnumVars); // we add the local enum vars
		
		LinkedList<String> usedBooleanGlobalVars = new LinkedList<String>(); // a list for the boolean non-primitive global vars	
																			
		// we add just the boolean global variables used in this process
		for (int i=0; i< mySpec.getGlobalVarsNames().size(); i++){
			String currentVar = mySpec.getGlobalVarsNames().get(i);
			if (this.usesSharedVar(currentVar) && !mySpec.isPrimVar(currentVar) && !this.isAnOwnedVar(currentVar) && mySpec.getGlobalVarsTypes().get(currentVar) == "BOOL"){
				usedBooleanGlobalVars.add(mySpec.getGlobalVarsNames().get(i));
			}
		}
		
		LinkedList<String> usedIntGlobalVars = new LinkedList<String>(); // a list for the integer global vars	
		// we add the int global vars used in this process
		for (int i=0; i< mySpec.getGlobalVarsNames().size(); i++){
			String currentVar = mySpec.getGlobalVarsNames().get(i);
			if (this.usesSharedVar(currentVar) && !mySpec.isPrimVar(currentVar)  && !this.isAnOwnedVar(currentVar) && mySpec.getGlobalVarsTypes().get(currentVar) == "INT"){
				usedIntGlobalVars.add(mySpec.getGlobalVarsNames().get(i));
			}
		}
		
		LinkedList<String> usedEnumGlobalVars = new LinkedList<String>(); // a list for the integer global vars	
		// we add the enum global vars used in this process
		for (int i=0; i< mySpec.getGlobalVarsNames().size(); i++){
			String currentVar = mySpec.getGlobalVarsNames().get(i);
			if (this.usesSharedVar(currentVar) && !mySpec.isPrimVar(currentVar)  && !this.isAnOwnedVar(currentVar) && mySpec.getGlobalVarsTypes().get(currentVar) == "ENUM"){
				usedEnumGlobalVars.add(mySpec.getGlobalVarsNames().get(i));
				for(String v:((EnumVar) mySpec.getGlobalVarByName(mySpec.getGlobalVarsNames().get(i))).getValues()){
					if (!enumValues.contains(v))
						enumValues.add(v);
				}
			}
		}
		
		// parameters are considered global vars, those parameters in the owns clause are not added
		usedBooleanGlobalVars.addAll(this.getBoolParNamesWithLock());
		usedIntGlobalVars.addAll(this.getIntParNamesWithLock());
		usedEnumGlobalVars.addAll(this.getEnumParNamesWithLock());
		
		
		// define UsedGlobalVars
		LinkedList<String> usedGlobalVars = new LinkedList<String>();
		for (int i=0; i<this.mySpec.getGlobalVarsNames().size();i++){
			if (this.usesSharedVar(this.mySpec.getGlobalVarsNames().get(i)) && !mySpec.isPrimVar(this.mySpec.getGlobalVarsNames().get(i)) && !this.isAnOwnedVar(this.mySpec.getGlobalVarsNames().get(i)) ){
				usedGlobalVars.add(this.mySpec.getGlobalVarsNames().get(i));  // those variables that are only locks are not here
			}
		}
		// and the parameters are added 
		usedGlobalVars.addAll(this.getBoolParNamesWithLock()); // we add the parameters that are not prim types adn not owned
		usedGlobalVars.addAll(this.getIntParNamesWithLock()); // 
		usedGlobalVars.addAll(this.getEnumParNamesWithLock());
		
		// define UsedGlobalVars with primitive types
		LinkedList<String> usedPrimGlobalVars = new LinkedList<String>();
		for (int i=0; i<this.mySpec.getGlobalVarsNames().size();i++){
			if (this.usesSharedVar(this.mySpec.getGlobalVarsNames().get(i)) && mySpec.isPrimVar(this.mySpec.getGlobalVarsNames().get(i)) && !this.isAnOwnedVar(this.mySpec.getGlobalVarsNames().get(i)) ){
				usedPrimGlobalVars.add(this.mySpec.getGlobalVarsNames().get(i));
			}
		}
		// and the parameters are added 
		usedGlobalVars.addAll(this.getBoolPrimParNames()); // we add the parameters that are not prim types
		usedGlobalVars.addAll(this.getIntPrimParNames()); // 
		usedGlobalVars.addAll(this.getEnumPrimParNames()); // 
		
		
		// we set the volatile or primitive boolean and int used in the specification
		LinkedList<String> usedPrimBoolVars = new LinkedList<String>();
		for (int i=0; i< mySpec.getGlobalVarsNames().size(); i++){
			String currentVar = mySpec.getGlobalVarsNames().get(i);
			if (this.usesSharedVar(currentVar) && mySpec.isPrimVar(currentVar) && mySpec.getGlobalVarsTypes().get(currentVar).equals("PRIMBOOL") && !this.isAnOwnedVar(currentVar)){
				usedPrimBoolVars.add(mySpec.getGlobalVarsNames().get(i));
			}
		}
		
		usedPrimBoolVars.addAll(this.getBoolPrimParNames());
		//we set the volatile or primitive int vars
		LinkedList<String> usedPrimIntVars = new LinkedList<String>(); // a list for the integer global vars	
		
		// we add the int global vars used in this process
		for (int i=0; i< mySpec.getGlobalVarsNames().size(); i++){
			String currentVar = mySpec.getGlobalVarsNames().get(i);
			if (this.usesSharedVar(currentVar) && mySpec.isPrimVar(currentVar)  && mySpec.getGlobalVarsTypes().get(currentVar).equals("PRIMINT") && !this.isAnOwnedVar(currentVar)){
				usedPrimIntVars.add(mySpec.getGlobalVarsNames().get(i));
			}
		}
		// and the int primitive parameters
		usedPrimIntVars.addAll(this.getIntPrimParNames());
		
		LinkedList<String> usedPrimEnumVars = new LinkedList<String>(); // a list for the enumglobal vars	
		
		// we add the int global vars used in this process
		for (int i=0; i< mySpec.getGlobalVarsNames().size(); i++){
			String currentVar = mySpec.getGlobalVarsNames().get(i);
			if (this.usesSharedVar(currentVar) && mySpec.isPrimVar(currentVar)  && mySpec.getGlobalVarsTypes().get(currentVar).equals("PRIMENUM") && !this.isAnOwnedVar(currentVar)){
				usedPrimEnumVars.add(mySpec.getGlobalVarsNames().get(i));
			}
		}
		// and the int primitive parameters
		usedPrimEnumVars.addAll(this.getEnumPrimParNames());
		

		LinkedList<Lock> usedLocks= new LinkedList<Lock>();
		LinkedList<Lock> onlyLocks = new LinkedList<Lock>(); // those locks that do not have variables associated to them 
		LinkedList<String> onlyLocksNames = new LinkedList<String>();
		for (int i=0;i<this.mySpec.getLocks().size();i++){			
			//if (usedGlobalVars.contains(this.mySpec.getLocks().get(i).getVarName())) //TBD: ADD SIMPLE LOCKS HERE
			this.mySpec.getLocks().get(i).resetUsedVars();
			if (this.usesSharedVar(this.mySpec.getLocks().get(i).getName())){
				usedLocks.add(this.mySpec.getLocks().get(i)); //CHECK THIS!
				if (this.mySpec.getLocks().get(i).isOnlyLock()){
					onlyLocks.add(this.mySpec.getLocks().get(i));
					onlyLocksNames.add(this.mySpec.getLocks().get(i).getName());
				}
			}
		}
				
		usedLocks.addAll(this.getLockPars());
		onlyLocks.addAll(this.getLockPars());
		onlyLocksNames.addAll(this.getLockParNames());
		
		// we set the important global vars for the locks, those variables in the owns clause are skipped
		for (int i=0; i<usedLocks.size();i++){
			Lock currentLock = usedLocks.get(i);
			currentLock.addAllUsedGlobalVars(usedGlobalVars);
			currentLock.addAllUsedGlobalVars(usedPrimGlobalVars);	
			currentLock.addAllUsedBooleanGlobalVars(usedPrimBoolVars);
			currentLock.addAllUsedBooleanGlobalVars(usedBooleanGlobalVars);
			currentLock.addAllUsedIntGlobalVars(usedIntGlobalVars);
			currentLock.addAllUsedIntGlobalVars(usedPrimIntVars);
			currentLock.addAllUsedEnumGlobalVars(usedEnumGlobalVars);
			currentLock.addAllUsedEnumGlobalVars(usedPrimEnumVars);
			currentLock.addAllUsedGlobalVarsWithLocks(usedGlobalVars);
			currentLock.addAllUsedGlobalVarsWithLocks(onlyLocksNames); 	
		}
		
		for (int i=0; i<this.getLockPars().size();i++){
			Lock currentLock = this.getLockPars().get(i);
			currentLock.addAllUsedGlobalVars(usedGlobalVars);
			currentLock.addAllUsedGlobalVars(usedPrimGlobalVars);	
			currentLock.addAllUsedBooleanGlobalVars(usedPrimBoolVars);
			currentLock.addAllUsedBooleanGlobalVars(usedBooleanGlobalVars);
			currentLock.addAllUsedIntGlobalVars(usedIntGlobalVars);
			currentLock.addAllUsedIntGlobalVars(usedPrimIntVars);
			currentLock.addAllUsedEnumGlobalVars(usedEnumGlobalVars);
			currentLock.addAllUsedEnumGlobalVars(usedPrimEnumVars);
			currentLock.addAllUsedGlobalVarsWithLocks(usedGlobalVars);
			currentLock.addAllUsedGlobalVarsWithLocks(onlyLocksNames); 	
		}
		
		// Non-primitive Boolean parameters are also considered locks 
		for (int i=0; i<this.getBoolParNamesWithLock().size();i++){
			Lock parLock = new Lock(this.getBoolParNamesWithLock().get(i), this.mySpec);
			//parLock.setUsedGlobalVars(usedGlobalVars);
			parLock.addAllUsedGlobalVars(usedGlobalVars);
			parLock.addAllUsedGlobalVars(usedPrimGlobalVars);	
			parLock.addAllUsedBooleanGlobalVars(usedPrimBoolVars);
			parLock.addAllUsedBooleanGlobalVars(usedBooleanGlobalVars);
			parLock.addAllUsedIntGlobalVars(usedIntGlobalVars);
			parLock.addAllUsedIntGlobalVars(usedPrimIntVars);
			parLock.addAllUsedEnumGlobalVars(usedEnumGlobalVars);
			parLock.addAllUsedEnumGlobalVars(usedPrimEnumVars);
			parLock.addAllUsedGlobalVarsWithLocks(usedGlobalVars);
			parLock.addAllUsedGlobalVarsWithLocks(onlyLocksNames); 	
			usedLocks.add(parLock);
		}
		
		// Non-primitive int parameters are also considered locks 
		for (int i=0; i<this.getIntParNamesWithLock().size();i++){
			Lock parLock = new Lock(this.getIntParNamesWithLock().get(i), this.mySpec);
			parLock.setUsedGlobalVars(usedGlobalVars);
			usedLocks.add(parLock);
		}
		
		// Non-primitive int parameters are also considered locks 
		for (int i=0; i<this.getEnumParNamesWithLock().size();i++){
			Lock parLock = new Lock(this.getEnumParNamesWithLock().get(i), this.mySpec);
			parLock.setUsedGlobalVars(usedGlobalVars);
			usedLocks.add(parLock);
		}
		
		for (int i=0; i<usedLocks.size(); i++){
			usedLocks.get(i).getOtherGlobalVars();
		}
		
		
		// we calculate the sets of integers used by the program
		// for now, we only consider positive integers, 
		LinkedList<String> intSet = new LinkedList<String>();
		for (int i=0; i<this.intSize; i++){
			intSet.add(String.valueOf(i));
			i++;
		}
		
		
		
		// a ugly solution to produce the complement of each primvar..
		// and anonimous class
		class VarContainer{
			String name;
			LinkedList<String> rest;
			
			public VarContainer(String name, LinkedList<String> rest){
				this.name = name;
				this.rest = rest;
			}
			public String getName(){
				return this.name;
			}
			public LinkedList<String> getRest(){
				LinkedList<String> result = new LinkedList<String>();
				for (String v:rest){
					if (!this.name.equals(v))
						result.add(v);
				}
				return result;
			}
		}
		
		LinkedList<VarContainer> primContainer = new LinkedList<VarContainer>();
		for (String v:usedPrimBoolVars){
			VarContainer vc = new VarContainer(v, usedPrimBoolVars);		
			primContainer.add(vc);
		}
		
		st.add("sharedBoolProps", usedBooleanGlobalVars); // we take the parameters as a global variables
		st.add("sharedIntVars", usedIntGlobalVars);
		st.add("sharedEnumVars", usedEnumGlobalVars);
		if (mySpec.isTokenRing()){
			// if it is a token ring then we remove hasToken, sendi, sendi+1
			for (int i=0; i< usedPrimBoolVars.size(); i++){
				if (usedPrimBoolVars.get(i).contains("send"))
					usedPrimBoolVars.remove(i);
			}
			for (int i=0; i< primContainer.size(); i++){
				if (primContainer.get(i).getName().contains("send"))
					primContainer.remove(i);
			}
			
		}
		st.add("sharedPrimBoolProps", usedPrimBoolVars); // the primitive/volatile shared bool vars
		st.add("sharedPrimIntVars", usedPrimIntVars); // the primitive/volatile shared int vars
		st.add("sharedPrimEnumVars", usedPrimEnumVars); // the primitive/volatile shared enum vars
		st.add("locks", usedLocks); //for now the global vars are locks
		//System.out.println(usedLocks);
		st.add("onlyLocks", onlyLocksNames); // those locks that do not have any variables associated to them
		//System.out.println(usedLocks);
		st.add("enumTypes", enumValues);
		st.add("primContainer", primContainer);
		
		
		// we create a collection for all the shared variables
		LinkedList<String> allSharedVars = new LinkedList<String>();
		allSharedVars.addAll(usedBooleanGlobalVars);
		allSharedVars.addAll(usedIntGlobalVars);
		allSharedVars.addAll(usedPrimBoolVars);
		allSharedVars.addAll(usedPrimIntVars);
		allSharedVars.addAll(onlyLocksNames);
		allSharedVars.addAll(usedEnumGlobalVars);
		allSharedVars.addAll(usedPrimEnumVars);
		st.add("allSharedVars", allSharedVars);
		
		st.add("localActions", localActions);
		st.add("envActions", envActions);
		st.add("actions", actions);
		st.add("auxVars", auxVars);
		st.add("auxAxioms", auxAxioms);
		st.add("auxPreds", auxPreds);
		st.add("invariants", invariants);
		st.add("init", this.init.toAlloy(this.name+"Meta", "s"));
		st.add("scope", scope);
		st.add("intSet", intSet); // the set of integers considered by the synthesis algorithm, this is important for 
								  // specifying the behavior of the environment, .e.g., to state that the environment can
								  // set any possible integer to a shared int variable.
		
		boolean containsEnum = !localEnumVars.isEmpty() || !usedEnumGlobalVars.isEmpty() || !usedPrimEnumVars.isEmpty();
		boolean containsInt = !localIntVars.isEmpty() || !usedIntGlobalVars.isEmpty() || !usedPrimIntVars.isEmpty();
		st.add("containsEnums", containsEnum);
		st.add("containsInts", containsInt);
		if (mySpec.isTokenRing()){
			int id = mySpec.getProcessId(this.name);
			int size = mySpec.getNumberOfProcs();
			st.add("idProcess", id);
			st.add("nextIdProcess", (id%size)+1);
			st.add("firstProcess", id==1);
		}
		
		String result = st.render();
		return result;
	}
	
	public LinkedList<String> getInvsAsStrings(String name){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.invs.size(); i++){
			result.add(invs.get(i).toAlloy(name, "s"));
		}
		return result;
	}
	
	public LinkedList<String> getAuxVars(String name){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.invs.size(); i++){
			result.addAll(this.invs.get(i).generateAuxProps(name));
		}
		return result;
	}
	
	public LinkedList<String> getAuxAxioms(){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.invs.size(); i++){
			result.addAll(this.invs.get(i).generateAxioms());
		}
		return result;
	}
	
	public LinkedList<String> getAuxPreds(String name){
		LinkedList<String> result = new LinkedList<String>();
		for (int i=0; i<this.invs.size(); i++){
			result.addAll(this.invs.get(i).generatePreds(name));
		}
		return result;
	}
	
	/**
	 * It generates the metamodel of the process  in alloy
	 * DEPRECATED it will be replace for he methods above
	 * @param file	where the metamodel will be written
	 */
	public void generateMetamodel(FileWriter file, String templateDir, int scope){
		// we set the propositions
		//List<String> sharedBoolProps = new ArrayList<String>();
		//for (int i = 0; i < sharedVars.size(); i++){
		//		if (sharedVars.get(i).getType() == Type.BOOL)
		//			sharedBoolProps.add(sharedVars.get(i).getName());
		//			
		//}		
		
		List<String> localBoolProps = new ArrayList<String>();
		for (int i = 0; i < localVars.size(); i++){
			if (localVars.get(i).getType() == Type.BOOL)
				localBoolProps.add(localVars.get(i).getName());
		}
		
		// we set the actions
		List<Action> localActions = new ArrayList<Action>();
		List<Action> envActions = new ArrayList<Action>();
		for (int i = 0; i < actions.size(); i++){
			if (actions.get(i).getIsLocal())
				localActions.add(actions.get(i));
			else
				envActions.add(actions.get(i));
		}
		
		List<String> invariants = new ArrayList<String>();
		List<String> auxVars = new ArrayList<String>(); // the auxiliar vars needed for translating CTL to Alloy
		List<String> auxAxioms = new ArrayList<String>(); // the auxiliar axioms needed for translating CTL to Alloy
		List<String> auxPreds = new ArrayList<String>(); // the auxiliar axioms needed for translating CTL to Alloy
		for (int i=0; i<this.invs.size(); i++){
			invariants.add(invs.get(i).toAlloy(name+"Meta", "s"));
			auxVars.addAll(invs.get(i).generateAuxProps(name+"Meta"));
			auxAxioms.addAll(invs.get(i).generateAxioms());
			auxPreds.addAll(invs.get(i).generatePreds(name+"Meta"));
			
		}		
		List<Action> actions = new ArrayList<Action>();
		actions.addAll(localActions);
		actions.addAll(envActions);
		
		STGroup group = new STGroupDir(templateDir);
		ST st = group.getInstanceOf("metamodel");
		
		//System.out.println(localActions);
		
		
		
		st.add("name", this.name);
		st.add("boolProps", localBoolProps);
		//st.add("sharedBoolProps", sharedBoolProps);
		st.add("sharedBoolProps", mySpec.getGlobalVarsNames());
		st.add("localActions", localActions);
		st.add("envActions", envActions);
		st.add("actions", actions);
		st.add("auxVars", auxVars);
		st.add("auxAxioms", auxAxioms);
		st.add("auxPred", auxPreds);
		st.add("invariants", invariants);
		st.add("init", this.init.toAlloy(this.name+"Meta", "s"));
		st.add("scope", scope);
		//List<String> values = new ArrayList<String>();
		//values.add("one");
		//values.add("two");
		//st.add("values", values);
		
		String result = st.render();
		try{
		    PrintWriter writer = new PrintWriter("/Users/Pablo/University/my-papers/drafts/Alloy.Synt/Tool/local/output/"+name+"Template.als", "UTF-8");
		    writer.print(result);
		    writer.close();
		} catch (IOException e) {
			System.out.println("Input-Output Error trying to write the metamodel.");
		}
		//System.out.println(result);
	}
	
	public String toString(){
		String result = "";
		result += "Process " + name + "(){\n";
		result += "vars: ";
		for (int i=0; i<localVars.size(); i++){
			result += localVars.get(i).toString()+",";
		}
		result += "\n";
		for (int i=0; i<actions.size(); i++){
			result += actions.get(i).toString();
		}
		for (int i=0; i<invs.size(); i++){
			result += "inv: " + invs.get(i).toString()+"\n" ;
		}
		result += "}\n";
		return result;		
	}
	
	
}
