package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.Arrays;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.ACSLPredicate;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ACSLPredicateCall;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonACSLPredicateCall extends CommonExpression
		implements
			ACSLPredicateCall {

	/**
	 * {@linkplain ACSLPredicateCall#predicate()}
	 */
	private final ACSLPredicate predicate;

	/**
	 * {@linkplain ACSLPredicateCall#actualArguments()}
	 */
	private Expression[] actualArguments;

	private int hashCode = 0;

	public CommonACSLPredicateCall(CIVLSource source, Scope hscope,
			Scope lscope, CIVLType type, ACSLPredicate predicate,
			List<Expression> actualArguments) {
		super(source, hscope, lscope, type);
		this.predicate = predicate;
		this.actualArguments = new Expression[actualArguments.size()];
		actualArguments.toArray(this.actualArguments);
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.ACSL_PREDICATE_CALL;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		ACSLPredicate predicate = predicate();
		Expression definition = predicate.definition();
		Set<Variable> varAddrSet = definition.variableAddressedOf(scope);

		for (Expression actualArg : actualArguments()) {
			Set<Variable> set = actualArg.variableAddressedOf();

			if (set != null)
				varAddrSet.addAll(actualArg.variableAddressedOf());
		}
		return varAddrSet;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		ACSLPredicate predicate = predicate();
		Expression definition = predicate.definition();
		Set<Variable> varAddrSet = definition.variableAddressedOf();

		for (Expression actualArg : actualArguments()) {
			Set<Variable> set = actualArg.variableAddressedOf();

			if (set != null)
				varAddrSet.addAll(actualArg.variableAddressedOf());
		}
		return varAddrSet;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (this == expression)
			return true;
		if (expression.hashCode() == hashCode())
			return true;
		if (expression instanceof CommonACSLPredicateCall) {
			CommonACSLPredicateCall other = (CommonACSLPredicateCall) expression;

			if (other.predicate().equals(this.predicate()))
				return Arrays.equals(actualArguments(),
						other.actualArguments());
		}
		return false;
	}

	@Override
	public ACSLPredicate predicate() {
		return predicate;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = 1768763 ^ predicate.hashCode()
					^ Arrays.hashCode(actualArguments);
		}
		return hashCode;
	}

	@Override
	public String toString() {
		String ret = "predicate " + predicate().name() + " (";
		Expression[] actualParams = actualArguments();

		for (int i = 0; i < actualParams.length - 1; i++)
			ret += actualParams[i].toString() + ", ";
		if (actualParams.length > 0)
			ret += actualParams[actualParams.length - 1];
		return ret += ") = " + predicate().definition();
	}

	@Override
	public Expression[] actualArguments() {
		return actualArguments;
	}
}
