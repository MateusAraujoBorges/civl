package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.StateExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonStateExpression extends CommonExpression
		implements StateExpression {

	private int id;

	public CommonStateExpression(CIVLSource source, Scope scope, CIVLType type,
			int id) {
		super(source, scope, scope, type);
		this.id = id;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.STATE_REF;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return null;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof StateExpression) {
			return ((StateExpression) expression).id() == this.id;
		}
		return false;
	}

	@Override
	public int id() {
		return this.id;
	}

	@Override
	public String toString() {
		return "STATE(" + id + ")";
	}
}
