package edu.udel.cis.vsl.civl.util.IF;

import java.util.Map;

import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

public class BranchConstraints {
	
	/* The map values are a pair of <firstGuard, notFirstGuard> inserted
	 * in CommonEnabler's method enabledTransitionsAtBinaryBranchingLocation */
	public static Map<State,Pair<BooleanExpression,BooleanExpression>> map;

}
