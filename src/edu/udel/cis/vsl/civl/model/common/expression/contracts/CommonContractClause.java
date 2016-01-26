package edu.udel.cis.vsl.civl.model.common.expression.contracts;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ContractClause;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.common.expression.CommonExpression;

public abstract class CommonContractClause extends CommonExpression implements
		ContractClause {
	protected ContractClauseKind kind;

	public CommonContractClause(CIVLSource source, Scope hscope, Scope lscope,
			CIVLType type, ContractClauseKind kind) {
		super(source, hscope, lscope, type);
		this.kind = kind;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.CONTRACT_CLAUSE;
	}

	@Override
	public ContractClauseKind contractKind() {
		return kind;
	}

	@Override
	public ContractClause replaceWith(ConditionalExpression oldExpr,
			Expression newExpr) {
		return this;
	}
}
