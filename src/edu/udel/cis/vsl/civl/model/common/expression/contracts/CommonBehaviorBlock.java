package edu.udel.cis.vsl.civl.model.common.expression.contracts;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.BehaviorBlock;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ClauseSequence;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.util.IF.Pair;

public class CommonBehaviorBlock extends CommonContractClause implements
		BehaviorBlock {
	private String name;

	private Pair<Expression, ClauseSequence> subBlock;

	public CommonBehaviorBlock(CIVLSource source, Scope hscope, Scope lscope,
			CIVLType type, Expression assumption, ClauseSequence body,
			String name) {
		super(source, hscope, lscope, type, ContractClauseKind.BEHAVIOR);
		this.subBlock = new Pair<>(assumption, body);
		this.name = name;
	}

	@Override
	public String behaviorName() {
		return name;
	}

	@Override
	public Pair<Expression, ClauseSequence> getSubBlock() {
		return subBlock;
	}

	@Override
	public BehaviorBlock replaceWith(ConditionalExpression oldExpr,
			Expression newExpr) {
		subBlock.left = subBlock.left.replaceWith(oldExpr, newExpr);
		subBlock.right = subBlock.right.replaceWith(oldExpr, newExpr);
		return this;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression.expressionKind().equals(ExpressionKind.CONTRACT_CLAUSE)) {
			BehaviorBlock clause = (BehaviorBlock) expression;

			if (clause.contractKind().equals(kind)) {
				if (clause.getSubBlock().equals(subBlock))
					return true;
			}
		}
		return false;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> vars = new HashSet<>();

		vars = subBlock.left.variableAddressedOf(scope);
		vars.addAll(subBlock.right.variableAddressedOf(scope));
		return vars;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> vars = new HashSet<>();

		vars = subBlock.left.variableAddressedOf();
		vars.addAll(subBlock.right.variableAddressedOf());
		return vars;
	}

}
