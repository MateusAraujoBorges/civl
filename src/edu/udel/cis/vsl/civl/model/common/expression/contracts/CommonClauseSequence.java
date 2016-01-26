package edu.udel.cis.vsl.civl.model.common.expression.contracts;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ClauseSequence;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ContractClause;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.expression.CommonExpression;

public class CommonClauseSequence extends CommonExpression implements
		ClauseSequence {
	private List<ContractClause> body;

	public CommonClauseSequence(CIVLSource source, Scope scope, CIVLType type,
			List<ContractClause> body) {
		super(source, scope, scope, type);
		this.body = body;
	}

	@Override
	public ExpressionKind expressionKind() {
		return ExpressionKind.CONTRACT_CLAUSE;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> result = new HashSet<>();

		for (ContractClause clause : body) {
			result.addAll(clause.variableAddressedOf(scope));
		}
		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> result = new HashSet<>();

		for (ContractClause clause : body) {
			result.addAll(clause.variableAddressedOf());
		}
		return result;
	}

	@Override
	public Iterator<ContractClause> getIterator() {
		return body.iterator();
	}

	@Override
	public void toArray(ContractClause[] receiver) {
		body.toArray(receiver);
	}

	@Override
	public int length() {
		return body.size();
	}

	@Override
	public ClauseSequence replaceWith(ConditionalExpression oldExpr,
			Expression newExpr) {
		List<ContractClause> newBody = new LinkedList<>();

		for (ContractClause clause : body) {
			newBody.add(clause.replaceWith(oldExpr, newExpr));
		}
		this.body = newBody;
		return this;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof ClauseSequence) {
			ClauseSequence cast = (ClauseSequence) expression;

			if (this.body.size() == cast.length()) {
				Iterator<ContractClause> bodyIter, exprIter;

				bodyIter = getIterator();
				exprIter = cast.getIterator();
				while (bodyIter.hasNext()) {
					if (!bodyIter.next().equals(exprIter.next()))
						return false;
				}
				return true;
			}
		}
		return false;
	}
}