package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.DomainGuardExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLDomainType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonDomainGuardExpression extends CommonExpression implements
		DomainGuardExpression {

	private Expression[] variables;

	private Expression domain;

	public CommonDomainGuardExpression(CIVLSource source, CIVLType type,
			Expression dom, List<Expression> vars) {
		super(source);
		this.variables = new Expression[vars.size()];
		vars.toArray(this.variables);
		this.expressionType = type;
		this.domain = dom;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.DOMAIN_GUARD;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = domain.variableAddressedOf(scope);

		if (operandResult != null)
			variableSet.addAll(operandResult);
		for (int i = 0; i < variables.length; i++) {
			operandResult = variables[i].variableAddressedOf(scope);
			if (operandResult != null)
				variableSet.addAll(operandResult);
		}
		return variableSet;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> operandResult = domain.variableAddressedOf();

		if (operandResult != null)
			variableSet.addAll(operandResult);
		for (int i = 0; i < variables.length; i++) {
			operandResult = variables[i].variableAddressedOf();
			if (operandResult != null)
				variableSet.addAll(operandResult);
		}
		return variableSet;
	}

	@Override
	public Expression domain() {
		return this.domain;
	}

	@Override
	public int dimension() {
		return ((CIVLDomainType) this.domain.getExpressionType()).dimension();
	}

	@Override
	public Expression variableAt(int index) {
		return this.variables[index];
	}

}
