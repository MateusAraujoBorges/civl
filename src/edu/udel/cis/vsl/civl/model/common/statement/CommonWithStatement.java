package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.WithStatement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

public class CommonWithStatement extends CommonStatement
		implements WithStatement {

	private LHSExpression colStateExpr;

	private boolean isEnter;

	public CommonWithStatement(CIVLSource source, Location srcLoc,
			Expression guard, LHSExpression colState, boolean isEnter) {
		super(source, colState.expressionScope(), colState.lowestScope(),
				srcLoc, guard);
		this.colStateExpr = colState;
		this.isEnter = isEnter;
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return colStateExpr.variableAddressedOf(scope);
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return this.colStateExpr.variableAddressedOf();
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.WITH;
	}

	@Override
	public boolean isEnter() {
		return this.isEnter;
	}

	@Override
	public boolean isExit() {
		return !this.isEnter;
	}

	@Override
	public LHSExpression collateState() {
		return this.colStateExpr;
	}

	@Override
	protected void calculateConstantValueWork(SymbolicUniverse universe) {
		this.colStateExpr.calculateConstantValue(universe);
	}

	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();

		sb.append("$with_");
		if (this.isEnter)
			sb.append("enter");
		else
			sb.append("exit");
		sb.append(" (");
		sb.append(this.colStateExpr);
		sb.append(")");
		return sb.toString();
	}
}
