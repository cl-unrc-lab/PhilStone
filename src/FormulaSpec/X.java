package FormulaSpec;

import java.util.LinkedList;

public class X extends TemporalFormula {


	public X(Formula e1){
        super(e1,null);		
	}
	
	@Override
	public void accept(FormulaVisitor v){
	     v.visit(this);			
	}	
	
	public String toAlloy(String metaName, String state){
		String result = "Form"+this.getId()+"["+metaName+","+state+"]";
		return result;
	}
	
	public boolean usesVar(String name){
		return this.getExpr1().usesVar(name);
	}
	
	public String toString(){
		return "X( "+ this.getExpr1().toString() + ")";
	}
	
	public String getAuxPred(String modelName){
		String result = "No Alloy for LTL yet";
		//String f = this.getExpr1().toAlloy(modelName, "s'");
		//String result = "pred Form"+this.getId()+"[i:"+modelName+", s:Node]{\n some s':(*("+modelName+".succs)[s]) | " + f + "}";
		return result;
	}
	
	public LinkedList<String> generatePreds(String modelName){
		LinkedList<String> result = new LinkedList<String>();
		result.add(this.getAuxPred(modelName));
		if (this.getExpr1() instanceof TemporalFormula)
			result.addAll(((TemporalFormula)this.getExpr1()).generatePreds(modelName));
		return result;
	}
	
	public Formula removeVarOwnedBy(LinkedList<String> instances){
		return new F(this.getExpr1().removeVarOwnedBy(instances));
	}
	
	public boolean containsVarOwnedBy(LinkedList<String> instances){
		return this.getExpr1().containsVarOwnedBy(instances);
	}
}
