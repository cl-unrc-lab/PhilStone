package PS;
import java.util.*;

/**
 * This class is used for saving counterexamples, it implements the basic methods to manage counterexamples
 * @author Pablo
 */

public class CounterExample{
	HashMap<String, LinkedList<String>> runs; // maps for each instance process the run (the list of nodes) corresponding to the counter example, the order
											  // is not important to us  since the backtracking inspects every possibility
	HashMap<String, LinkedList<HashMap<String, String>>> props; // It stores the propositions holding in each state for each instance
	
	public CounterExample(){
		this.runs = new HashMap<String, LinkedList<String>>();
		this.props = new HashMap<String, LinkedList<HashMap<String, String>>>();
	}
	
	public void addRun(String process, LinkedList<String> run){
		runs.put(process, run);
	}
	
	public LinkedList<String> getRuns(String process){
		return runs.get(process);
	}
	
	public LinkedList<HashMap<String, String>> getProps(String process){
		return props.get(process);
	}
	
	public int size(String instance){
		return runs.get(instance).size();
	}
	
	
	/**
	 * 
	 * @param cex A counterexample represented by a HashMap, for each step of the CEX there is a mapping
	 * 			  assigning to each instance a state  
	 * @param props The list of propositions true in each state, this is useful since nuSMV works 
	 * 		  with equivalence classes	
	 */
	public void addRuns(LinkedList<HashMap<String, String>> cex, LinkedList<HashMap<String, HashMap<String, String>>> props){
		//System.out.println(cex);
		for (int i=0; i< cex.size(); i++){
			if (i==0){ // if it is the first state
				HashMap<String, String> currentMap = cex.get(i);
				Iterator<String> it = currentMap.keySet().iterator();
				while (it.hasNext()){
					String currentProcess = it.next();
					LinkedList<String> listStates = new LinkedList<String>();
					LinkedList<HashMap<String, String>> listProps = new LinkedList<HashMap<String, String>>();
					listStates.add(cex.get(i).get(currentProcess));
					listProps.add(props.get(i).get(currentProcess));
					runs.put(currentProcess, listStates);
					this.props.put(currentProcess, listProps);
				}
			}
			else{ // otherwise it is another run
				HashMap<String, String> currentMap = cex.get(i);
				Iterator<String> it = currentMap.keySet().iterator();
				while (it.hasNext()){
					String currentProcess = it.next();
					//if (!runs.get(currentProcess).getLast().equals(cex.get(i).get(currentProcess))) { // avoid repeated elements
					runs.get(currentProcess).addLast(cex.get(i).get(currentProcess));
					this.props.get(currentProcess).addLast(props.get(i).get(currentProcess));
					//}
				}
			}
		}
	}
	
	/**
	 * This version does not have the propositions, it must be replaced for the version above
	 * but still needed for other search: herSearch etc, must be fixed....
	 * @param cex	The counterexamples to be processed
	 */
	public void addRuns(LinkedList<HashMap<String, String>> cex){
		//System.out.println(cex);
		for (int i=0; i< cex.size(); i++){
			if (i==0){ // if it is the first state
				HashMap<String, String> currentMap = cex.get(i);
				Iterator<String> it = currentMap.keySet().iterator();
				while (it.hasNext()){
					String currentProcess = it.next();
					LinkedList<String> listStates = new LinkedList<String>();
					listStates.add(cex.get(i).get(currentProcess));
					runs.put(currentProcess, listStates);
				}
			}
			else{ // otherwise it is another run
				HashMap<String, String> currentMap = cex.get(i);
				Iterator<String> it = currentMap.keySet().iterator();
				while (it.hasNext()){
					String currentProcess = it.next();
					if (!runs.get(currentProcess).getLast().equals(cex.get(i).get(currentProcess))) { // avoid repeated elements
						runs.get(currentProcess).addLast(cex.get(i).get(currentProcess));
						//this.props.get(currentProcess).addLast(props.get(i).get(currentProcess));
					}
				}
			}
		}
	}
	
	/**
	 * An implementation of equals for Counterexample
	 */
	public boolean equals(Object obj){
		if (obj == null || obj instanceof CounterExample)
			return false;
		else{
			CounterExample another = (CounterExample) obj;
			Iterator<String> it = runs.keySet().iterator();
			while (it.hasNext()){
				String currentProcess = it.next();
				LinkedList<String> anotherRun = another.getRuns(currentProcess);
				LinkedList<String> myRun = runs.get(currentProcess);
				if (anotherRun.size() == myRun.size()){
					for (int j = 0; j <  anotherRun.size(); j++){
						if (!anotherRun.get(j).equals(myRun.get(j)))
							return false;
					}
					LinkedList<HashMap<String, String>> anotherProps = another.getProps(currentProcess);
					LinkedList<HashMap<String, String>> myProps = props.get(currentProcess);
					for (int j = 0; j <  anotherProps.size(); j++){
						if (!anotherProps.get(j).equals(myProps.get(j)))
							return false;
					}
					
				}
				else
					return false;
			}
		}
		return true;
	}
	
	/**
	 * this <= c (this refines c)
	 * @param c	another counterexample
	 * @return	check if this refines c 
	 */
	public boolean lInclusion(CounterExample c, String instance) {
		if (this.size(instance)>1){
			if (c.size(instance) >= this.size(instance)){ // the length of c has to be less than the length of this
				int i=0;
				int j=0;	
				while (j<c.size(instance)-1){
					if (this.getRuns(instance).get(i).equals(c.getRuns(instance).get(j)) 
						&& this.getRuns(instance).get(i+1).equals(c.getRuns(instance).get(j+1))
						&& this.getProps(instance).get(i).equals(c.getProps(instance).get(j))
						&& this.getProps(instance).get(i+1).equals(c.getProps(instance).get(j+1)))		
					{
						i++; // if found we search the next element
						j++;
						if (i == this.size(instance)-1) // if we have traversed all the sequence of this then true
							break;
					}
					else{
						j++; // otherwise we continue searching
						//i=0; // and reset the position in the first sequence
					}
				}
				return (i == this.size(instance)-1);
			}
			else{
				return false;
			}
		}
		else{
			return true;
		}
	}
	
	/**
	 * Checks if c refines the current instance: c <= this for the given inctance
	 * @param c	Another counterexample
	 * @param instance	
	 * @return
	 */
	public boolean rInclusion(CounterExample c, String instance){
		return c.lInclusion(this, instance);
	}	
	
	public String toString(){
		String result = " ";
		Iterator<String> it = runs.keySet().iterator();
		while (it.hasNext()){
			String current = it.next();
			result += "["+current +" : "+ runs.get(current) + "]";
		}
		for (String ins : this.props.keySet()) {
			result += "["+ins+":"+props.get(ins).toString()+"]";
		}
		return result;
	}

}
