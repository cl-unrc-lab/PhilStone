package PS;
import java.util.*;

/**
 * To keep track a specific step of a counterexample,
 * A CEX step has an abstract state and the values of the attributes
 * @author Pablo
 */

public class CexState {
	private String state;
	private HashMap<String, String> vals;
	
	public CexState() {
		state = "";
		vals = new HashMap<String,String>();
	}
	
	public void setState(String state) {
		this.state = state;
	}
	
	public void setVal(String att, String val) {
		vals.put(att, val);
	}
	
	public String getState() {
		return state;
	}
	
	public String getVal(String att) {
		String result = vals.get(att);
		if (result == null)
			throw new RuntimeException("Attribite does not exists");
		return result;
	}
	
	public HashMap<String, String> getVals(){
		return vals;
	}
	
	@Override
	public int hashCode() {
		return Objects.hash(state, vals);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		CexState other = (CexState) obj;
		return Objects.equals(state, other.state) && Objects.equals(vals, other.vals);
	}

}
