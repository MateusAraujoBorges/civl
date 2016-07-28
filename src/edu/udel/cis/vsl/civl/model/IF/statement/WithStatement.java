package edu.udel.cis.vsl.civl.model.IF.statement;

import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;

public interface WithStatement extends Statement {
	boolean isEnter();

	boolean isExit();

	LHSExpression collateState();
}
