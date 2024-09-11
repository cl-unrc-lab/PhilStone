package PS;
import java.util.*;

/**
 * An abstract CEX contains a sequence of CexClauses for each instance
 * @author pablo
 *
 */

public class AbstractCEX {
	private LinkedList<CexClause> cex; // for each instance it has the runs
	
	public AbstractCEX(LinkedList<CexClause> cex) {
		super();
		this.cex = cex;
	}

	public  LinkedList<CexClause> getCex() {
		return cex;
	}

	public void setCex(LinkedList<CexClause> cex) {
		this.cex = cex;
	}

	@Override
	public int hashCode() {
		return Objects.hash(cex);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		AbstractCEX other = (AbstractCEX) obj;
		return Objects.equals(cex, other.cex);
	}
	
	
	

}
