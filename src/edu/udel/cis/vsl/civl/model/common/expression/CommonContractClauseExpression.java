package edu.udel.cis.vsl.civl.model.common.expression;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ContractClauseExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonContractClauseExpression extends CommonExpression implements
		ContractClauseExpression {
	private Expression collectiveGroup;

	private Expression body;

	private boolean isCollective;

	public CommonContractClauseExpression(CIVLSource source, Scope hscope,
			Scope lscope, CIVLType type, Expression collectiveGroup,
			Expression body) {
		super(source, hscope, lscope, type);
		if (collectiveGroup == null)
			this.isCollective = false;
		else
			this.isCollective = true;
		this.collectiveGroup = collectiveGroup;
		this.body = body;
	}

	@Override
	public Expression getCollectiveGroup() {
		return this.collectiveGroup;
	}

	@Override
	public Expression getBody() {
		return body;
	}

	@Override
	public boolean isCollectiveClause() {
		return isCollective;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.CONTRACT_CLAUSE;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> componentResult = collectiveGroup
				.variableAddressedOf(scope);

		if (componentResult != null)
			variableSet.addAll(componentResult);
		componentResult = body.variableAddressedOf(scope);
		if (componentResult != null)
			variableSet.addAll(componentResult);
		return variableSet;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> variableSet = new HashSet<>();
		Set<Variable> componentResult = collectiveGroup.variableAddressedOf();

		if (componentResult != null)
			variableSet.addAll(componentResult);
		componentResult = body.variableAddressedOf();
		if (componentResult != null)
			variableSet.addAll(componentResult);
		return variableSet;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof CommonContractClauseExpression) {
			CommonContractClauseExpression clause = ((CommonContractClauseExpression) expression);

			if (clause.getCollectiveGroup().equals(collectiveGroup))
				if (clause.getBody().equals(body))
					return true;
		}
		return false;
	}

	@Override
	public String toString() {
		StringBuffer message = new StringBuffer();

		if (isCollective)
			message.append("collective(" + collectiveGroup.toString() + ") ");
		message.append(this.body);
		return message.toString();
	}
}
