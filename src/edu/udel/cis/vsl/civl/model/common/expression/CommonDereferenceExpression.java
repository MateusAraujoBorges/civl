package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.DereferenceExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.VariableExpression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonDereferenceExpression extends CommonExpression implements
		DereferenceExpression {

	private Expression pointer;

	public CommonDereferenceExpression(CIVLSource source, Expression pointer) {
		super(source);
		this.pointer = pointer;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DEREFERENCE;
	}

	@Override
	public Expression pointer() {
		return pointer;
	}

	@Override
	public String toString() {
		return "*(" + pointer + ")";
	}

	@Override
	public void calculateDerefs() {
		this.hasDerefs = true;
	}

	@Override
	public void setPurelyLocal(boolean pl) {
		this.purelyLocal = pl;
	}

	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		this.pointer.purelyLocalAnalysisOfVariables(funcScope);
	}

	@Override
	public void purelyLocalAnalysis() {
		this.purelyLocal = false;
	}

	@Override
	public void replaceWith(ConditionalExpression oldExpression,
			VariableExpression newExpression) {
		if (pointer == oldExpression) {
			pointer = newExpression;
			return;
		}
		pointer.replaceWith(oldExpression, newExpression);
	}

	@Override
	public Expression replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newPointer = pointer.replaceWith(oldExpression,
				newExpression);
		CommonDereferenceExpression result = null;

		if (newPointer != null) {
			result = new CommonDereferenceExpression(this.getSource(),
					newPointer);
		}

		if (result != null)
			result.setExpressionType(expressionType);

		return result;
	}

	@Override
	public Variable variableWritten(Scope scope, CIVLHeapType heapType) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope, CIVLHeapType heapType) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = pointer.variableAddressedOf(scope, heapType);

		if (operandResult != null)
			variableSet.addAll(operandResult);
		return variableSet;
	}
}
