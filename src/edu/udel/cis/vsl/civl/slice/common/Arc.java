package edu.udel.cis.vsl.civl.slice.common;

import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.State;

/**
 * Wrapper class for CIVL Statements.
 * 
 * @author mgerrard
 *
 */

public class Arc {
	
	protected Statement statement;
	protected Vertex source;
	protected Vertex target;
	protected Vertex originalTarget;
	protected Map<Variable,Set<Variable>> formalToActualMap;
	
	protected State state;
	protected int pid;
	
	protected Arc (Statement s) {
		this.statement = s;
	}

	public String toString() {
		return this.statement.toString();
	}
}
