package edu.udel.cis.vsl.civl.model.IF.expression;

public interface PointerSetExpression extends Expression {
	LHSExpression getBasePointer();

	Expression getRange();
}
