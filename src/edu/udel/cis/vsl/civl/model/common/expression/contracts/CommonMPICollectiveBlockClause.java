package edu.udel.cis.vsl.civl.model.common.expression.contracts;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ClauseSequence;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.ContractClause;
import edu.udel.cis.vsl.civl.model.IF.expression.contracts.MPICollectiveBlockClause;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonMPICollectiveBlockClause extends CommonContractClause
		implements MPICollectiveBlockClause {
	private Expression MPIComm;

	private COLLECTIVE_KIND colKind;

	private ClauseSequence body;

	public CommonMPICollectiveBlockClause(CIVLSource source, Scope hscope,
			Scope lscope, CIVLType type, ClauseSequence body,
			Expression MPIComm, COLLECTIVE_KIND colKind) {
		super(source, hscope, lscope, type, ContractClauseKind.MPI_COLLECTIVE);
		this.MPIComm = MPIComm;
		this.colKind = colKind;
		this.body = body;
	}

	@Override
	public Expression getMPIComm() {
		return MPIComm;
	}

	@Override
	public COLLECTIVE_KIND getCollectiveKind() {
		return colKind;
	}

	@Override
	public ClauseSequence getBody() {
		return body;
	}

	@Override
	public ContractClause replaceWith(ConditionalExpression oldExpr,
			Expression newExpr) {
		body = body.replaceWith(oldExpr, newExpr);
		MPIComm = MPIComm.replaceWith(oldExpr, newExpr);
		return this;
	}

	@Override
	protected boolean expressionEquals(Expression expression) {
		if (expression instanceof MPICollectiveBlockClause) {
			MPICollectiveBlockClause cast = (MPICollectiveBlockClause) expression;

			if (cast.getCollectiveKind().equals(colKind))
				if (cast.getMPIComm().equals(MPIComm))
					if (cast.getBody().equals(body))
						return true;
		}
		return false;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> set = body.variableAddressedOf(scope);

		set.addAll(this.MPIComm.variableAddressedOf(scope));
		return set;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> set = body.variableAddressedOf();

		set.addAll(MPIComm.variableAddressedOf());
		return set;
	}
}
