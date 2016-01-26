package edu.udel.cis.vsl.civl.model.common.expression.contracts;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ObligationClause;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonObligationClause extends CommonContractClause implements
		ObligationClause {
	private Expression body;

	public CommonObligationClause(CIVLSource source, Scope hscope,
			Scope lscope, CIVLType type, ContractClauseKind kind,
			Expression body) {
		super(source, hscope, lscope, type, kind);
		this.body = body;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return body.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return body.variableAddressedOf();
	}

	@Override
	public Expression getBody() {
		return body;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof ObligationClause) {
			if (((ObligationClause) expression).contractKind().equals(kind))
				if (((ObligationClause) expression).getBody().equals(body)) {
					return true;
				}
		}
		return false;
	}
}
