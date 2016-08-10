package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.ValueAtExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonValueAtExpression extends CommonExpression
		implements
			ValueAtExpression {
	private Expression state;
	private Expression expression;

	public CommonValueAtExpression(CIVLSource source, Expression state,
			Expression expression) {
		super(source, null, null, expression.getExpressionType());
		this.state = state;
		this.expression = expression;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.VALUE_AT;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return state.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return state.variableAddressedOf();
	}

	@Override
	public Expression state() {
		return state;
	}

	@Override
	public Expression expression() {
		return expression;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof ValueAtExpression) {
			ValueAtExpression that = (ValueAtExpression) expression;

			return state.equals(that.state())
					&& expression.equals(that.expression());
		}
		return false;
	}

}
