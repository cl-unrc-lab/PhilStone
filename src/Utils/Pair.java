package Utils;
/**
 * A simple generic class to model pairs of objects
 * @author Pablo
 *
 */
public class Pair<F, S> {
	private F first; //first member of pair
    private S second; //second member of pair

    /**
     * Basic constructor
     */
    public Pair(){
    	
    }
    
    /**
     * A Simple Constructor
     * @param first	the first argument
     * @param second	the second argument
     */
    public Pair(F first, S second) {
        this.first = first;
        this.second = second;
    }

    /**
     * Setter for first
     * @param first
     */
    public void setFirst(F first) {
        this.first = first;
    }

    /**
     * Setter for second
     * @param second
     */
    public void setSecond(S second) {
        this.second = second;
    }

    /**
     * Getter for First
     * @return
     */
    public F getFirst() {
        return first;
    }

    /**
     * Getter for second
     * @return
     */
    public S getSecond() {
        return second;
    }
    
    public boolean equals(Object o) {
    	if (o instanceof Pair<?,?>) {
    		Pair<F,S> anotherObject = (Pair<F,S>) o;
    		return this.first.equals(anotherObject.getFirst()) && this.second.equals(anotherObject.getSecond());
    		
    	}
    	else {
    		return false;
    	}
    	
    }
    
    public String toString() {
    	return "("+this.first.toString()+" , "+this.second.toString()+" )";
    }
    
    
}
