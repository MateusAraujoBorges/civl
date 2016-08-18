package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.OriginalExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonOriginalExpression extends CommonExpression
		implements
			OriginalExpression {
	private Expression expression;

	public CommonOriginalExpression(CIVLSource source, Expression expression) {
		super(source, null, null, expression.getExpressionType());
		this.expression = expression;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ORIGINAL;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return expression.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return expression.variableAddressedOf();
	}

	@Override
	public Expression expression() {
		return expression;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof OriginalExpression) {
			OriginalExpression that = (OriginalExpression) expression;

			return this.expression.equals(that.expression());
		}
		return false;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer("$original (");

		result.append(expression);
		result.append(")");
		return result.toString();
	}

}
