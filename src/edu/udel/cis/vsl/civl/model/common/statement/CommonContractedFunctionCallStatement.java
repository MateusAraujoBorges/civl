package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.ConditionalExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.FunctionIdentifierExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.ContractedFunctionCallStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

/**
 * <p>
 * This class is same as a {@link FunctionCallStatement} but with a different
 * statement kind. This special function call statement can represent two
 * sub-statements : contracted function call enter statement and contracted
 * function call exit statement. In contracts system mode, a function call on a
 * contracted function will be break into two steps: enter and exit. Since in
 * contracts system, such a call doesn't depends on the function body but on
 * function contracts, this two-steps structure helps implementing
 * synchronizations. Why it helps ?
 * <ol>
 * <li>Without a special kind of statement, it's hard for enabler to decide
 * whether a function call is a regular function call or a contracted function
 * call.</li>
 * <li>Evaluation on contracts requires that a call stack entry being pushed
 * into the call stack. So the enter statement can be responsible for pushing
 * the call stack and the exit is responsible for pop the call stack. The
 * evaluation intuitively happens in between of them.</li>
 * <li><b>The most important reason is</b></li>
 * </ol>
 * </p>
 * 
 * @author ziqingluo
 *
 */
public class CommonContractedFunctionCallStatement extends CommonStatement
		implements ContractedFunctionCallStatement {

	private CONTRACTED_FUNCTION_CALL_KIND contractedCallKind;

	private List<Expression> arguments;

	private FunctionIdentifierExpression functionExpression;

	private LHSExpression lhs;

	public CommonContractedFunctionCallStatement(CIVLSource civlSource,
			Scope hscope, Scope lscope, Location source,
			FunctionIdentifierExpression functionExpression,
			List<Expression> arguments, Expression guard,
			CONTRACTED_FUNCTION_CALL_KIND kind) {
		super(civlSource, hscope, lscope, source, guard);
		this.contractedCallKind = kind;
		this.arguments = arguments;
		this.functionExpression = functionExpression;
	}

	@Override
	public Statement replaceWith(ConditionalExpression oldExpression,
			Expression newExpression) {
		List<Expression> newArguments = new LinkedList<>();

		if (arguments != null) {
			for (Expression arg : arguments) {
				newArguments.add(arg.replaceWith(oldExpression, newExpression));
			}
			this.arguments = newArguments;
		}
		return new CommonContractedFunctionCallStatement(this.getSource(),
				this.statementScope, this.lowestScope, this.source(),
				functionExpression, arguments, guard(), contractedCallKind);
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		Set<Variable> vars = new HashSet<Variable>();

		vars.addAll(functionExpression.variableAddressedOf(scope));
		for (Expression arg : arguments) {
			Set<Variable> argResults = arg.variableAddressedOf(scope);
			if (argResults != null)
				vars.addAll(argResults);
		}
		return vars;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		Set<Variable> vars = new HashSet<Variable>();

		vars.addAll(functionExpression.variableAddressedOf());
		for (Expression arg : arguments) {
			Set<Variable> argResults = arg.variableAddressedOf();
			if (argResults != null)
				vars.addAll(argResults);
		}
		return vars;
	}

	@Override
	public StatementKind statementKind() {
		return StatementKind.CONTRACTED_CALL;
	}

	@Override
	public LHSExpression lhs() {
		return lhs;
	}

	@Override
	public CIVLFunction function() {
		return functionExpression.function();
	}

	@Override
	public List<Expression> arguments() {
		return arguments;
	}

	@Override
	public void setLhs(LHSExpression lhs) {
		this.lhs = lhs;
	}

	@Override
	public void setFunction(FunctionIdentifierExpression function) {
		this.functionExpression = function;
	}

	@Override
	public void setArguments(List<Expression> arguments) {
		this.arguments = arguments;
	}

	@Override
	public Expression functionExpression() {
		return functionExpression;
	}

	@Override
	public CONTRACTED_FUNCTION_CALL_KIND getContractedFunctionCallKind() {
		return contractedCallKind;
	}

	@Override
	protected void calculateConstantValueWork(SymbolicUniverse universe) {
		functionExpression.calculateConstantValue(universe);
		for (Expression arg : arguments) {
			arg.calculateConstantValue(universe);
		}
	}

	@Override
	public String toString() {
		String kind = this.contractedCallKind == CONTRACTED_FUNCTION_CALL_KIND.ENTER ? "enter"
				: "exit";

		return this.functionExpression.function().name() + "_CONTRACT_" + kind;
	}
}
