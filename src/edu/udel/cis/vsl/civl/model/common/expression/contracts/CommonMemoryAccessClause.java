package edu.udel.cis.vsl.civl.model.common.expression.contracts;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.MemoryAccessClause;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonMemoryAccessClause extends CommonContractClause implements
		MemoryAccessClause {

	private Expression[] expressions;

	private boolean isReads;

	public CommonMemoryAccessClause(CIVLSource source, Scope hscope,
			Scope lscope, CIVLType type, Expression[] body, boolean isReads) {
		super(source, hscope, lscope, type, ContractClauseKind.ASSIGNS_READS);
		this.expressions = body.clone();
		this.isReads = isReads;
	}

	@Override
	public boolean isAssigns() {
		return !isReads;
	}

	@Override
	public boolean isReads() {
		return isReads;
	}

	@Override
	public Expression[] memoryLocations() {
		return expressions;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> result = new HashSet<>();

		for (int i = 0; i < expressions.length; i++)
			result.addAll(expressions[i].variableAddressedOf(scope));
		return result;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> result = new HashSet<>();

		for (int i = 0; i < expressions.length; i++)
			result.addAll(expressions[i].variableAddressedOf());
		return result;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof MemoryAccessClause) {
			Expression[] objExprs = ((MemoryAccessClause) expression)
					.memoryLocations();
			if (((MemoryAccessClause) expression).isReads() == isReads)
				if (objExprs.length == expressions.length) {
					for (int i = 0; i < expressions.length; i++)
						if (!expressions[i].equals(objExprs[i]))
							return false;
					return true;
				}
		}
		return false;
	}
}
