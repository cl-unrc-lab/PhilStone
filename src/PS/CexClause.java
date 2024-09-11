package PS;
import java.util.Objects;

/**
 * A Simple class to keep track of a state of a counterexample: A target state and a source state
 * @author pablo
 *
 */

public class CexClause {
	CexState originState;
	CexState targetState;
	
	public CexState getOriginState() {
		return originState;
	}
	public void setOriginState(CexState originState) {
		this.originState = originState;
	}
	public CexState getTargetState() {
		return targetState;
	}
	public void setTargetState(CexState targetState) {
		this.targetState = targetState;
	}
	
	@Override
	public int hashCode() {
		return Objects.hash(originState, targetState);
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		CexClause other = (CexClause) obj;
		return Objects.equals(originState, other.originState) && Objects.equals(targetState, other.targetState);
	}
	
	
	
}
