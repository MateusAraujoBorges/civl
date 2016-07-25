package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.UpdateStatement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

public class CommonUpdateStatement extends CommonStatement
		implements UpdateStatement {

	private Expression collator;

	private CallOrSpawnStatement call;

	public CommonUpdateStatement(CIVLSource source, Location sourceLoc,
			Expression guard, Expression collator, CallOrSpawnStatement call) {
		super(source, collator.expressionScope(), collator.lowestScope(),
				sourceLoc, guard);
		this.collator = collator;
		this.call = call;
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		Expression newGuard = this.guard().replaceWith(oldExpression,
				newExpression), newCollator = collator;
		CallOrSpawnStatement newCall = call;
		boolean hasNew = false;

		if (newGuard != null)
			hasNew = true;
		else
			newGuard = this.guard();
		if (!hasNew) {
			newCollator = collator.replaceWith(oldExpression, newExpression);
			if (newCollator != null)
				hasNew = true;
			else
				newCollator = collator;
		}
		if (!hasNew) {
			newCall = call.replaceWith(oldExpression, newExpression);
			if (newCall != null)
				hasNew = true;
		}
		if (hasNew)
			return new CommonUpdateStatement(this.getSource(), this.source(),
					this.guard(), newCollator, newCall);
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> result = new HashSet<>();
		Set<Variable> subResult = collator.variableAddressedOf();

		if (subResult != null)
			result.addAll(subResult);
		subResult = call.variableAddressedOf(scope);
		result.addAll(call.variableAddressedOf(scope));
		if (result.size() > 0)
			return result;
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> result = new HashSet<>();
		Set<Variable> subResult = collator.variableAddressedOf();

		if (subResult != null)
			result.addAll(subResult);
		subResult = call.variableAddressedOf();
		result.addAll(call.variableAddressedOf());
		if (result.size() > 0)
			return result;
		return null;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.UPDATE;
	}

	@Override
	public Expression collator() {
		return collator;
	}

	@Override
	public CallOrSpawnStatement call() {
		return call;
	}

	@Override
	protected void calculateConstantValueWork(SymbolicUniverse universe) {
		this.collator.calculateConstantValue(universe);
		this.call.calculateConstantValue(universe);
	}

}
