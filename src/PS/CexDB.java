package PS;
import java.util.*;
/**
 * This class provides basic logic for managing a set of Counterexamples for a given instance
 * @author pablo
 *
 */

public class CexDB {
	private HashSet<HashSet<CexClause>> cexs; // the collections of CEXs 
	private HashMap<CexClause, Integer> rank; // it ranks each clause following its number of 

	public CexDB() {
		super();
		this.cexs = new HashSet<HashSet<CexClause>>();
		this.rank = new HashMap<CexClause, Integer>();		
	}

	public HashSet<HashSet<CexClause>> getCexs() {
		return cexs;
	}

	public void setCexs(HashSet<HashSet<CexClause>> cexs) {
		this.cexs = cexs;
	}

	public HashMap<CexClause, Integer> getRank() {
		return rank;
	}

	public void setRank(HashMap<CexClause, Integer> rank) {
		this.rank = rank;
	}

	/**
	 * @return	the minimum cover set of the CEX database, emptyset, no cover set
	 */
	public HashSet<CexClause> getMinCoverSet(){
		HashSet<HashSet<CexClause>> toCover = (HashSet<HashSet<CexClause>>) cexs.clone(); // the cexs to be covered
		HashSet<CexClause> clauses = new HashSet<CexClause>(); // all the clauses in the cexs: a clause contains two states
		HashMap<CexClause, HashSet<HashSet<CexClause>>> covered = new HashMap<CexClause, HashSet<HashSet<CexClause>>>(); // we to keep track of the cexs covered for each clause
		HashSet<CexClause> result = new HashSet<CexClause>(); // the result
		
		// we add all the sets in the DB
		for (HashSet<CexClause> s : cexs) {
			clauses.addAll(s);
		}
		
		// we initialise the covered variable
		for (CexClause c: clauses) {
			covered.put(c, new HashSet<HashSet<CexClause>>());
		}
		
		// we compute the cexs covered for each clause
		for (CexClause c : clauses) {
			for (HashSet<CexClause> s : cexs ) {
				if (s.contains(c))
					covered.get(c).add(s);
			}
		}
		
		while (!toCover.isEmpty() && !clauses.isEmpty()) {
			HashMap<CexClause, Integer> coverNumber = new HashMap<CexClause, Integer>();
			
			// we initilize the number of covered cexs for each clause
			for (CexClause c : clauses) {
				coverNumber.put(c, 0);
			}
			
			// we calculate for each clause the number of covered cexs
			for (CexClause c : clauses) {
				for (HashSet<CexClause> s : toCover) {
					if (s.contains(c))
						coverNumber.put(c, coverNumber.get(c)+1);
				}
			}
			
			// we get the max 
			CexClause max = null;
			for (CexClause c: clauses) {
				if (max == null) // first time
					max = c;
				else {
					if (coverNumber.get(c) > coverNumber.get(max))
						max = c;
				}
			}
			
			// the max is removed
			clauses.remove(max);
			result.add(max);
			
			// the clauses covered by max are removed
			for (HashSet<CexClause> c : toCover) {
				if (covered.get(max).contains(c))
					toCover.remove(c);
			}
			
		}
		
		if (toCover.isEmpty())  // a cover was found
			return result;
		else
			return new HashSet<CexClause>(); // empty set, no cover found!
		
	}

	
	@Override
	public int hashCode() {
		return Objects.hash(cexs, rank);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		CexDB other = (CexDB) obj;
		return Objects.equals(cexs, other.cexs) && Objects.equals(rank, other.rank);
	}
	
	
	
	
}
