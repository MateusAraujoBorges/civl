package edu.udel.cis.vsl.civl.library.civlc;

import java.util.Arrays;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.LogicFunction;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.prove.IF.ProverPredicate;

/**
 * 
 * @author ziqing
 *
 */
public class LogicFunctionInterpretor {

	/**
	 * Translates (evaluates) a set of {@link ACSLPredicate}s to P
	 * {@link ProverPredicate}s on the given state.
	 * 
	 */
	static public ProverPredicate[] evaluateLogicFunctions(
			List<LogicFunction> logicFunctions, State state, int pid,
			Evaluator evaluator) throws UnsatisfiablePathConditionException {
		ProverPredicate why3Preds[] = new ProverPredicate[logicFunctions
				.size()];
		int i = 0;

		for (LogicFunction pred : logicFunctions)
			why3Preds[i++] = evaluateLogicFunctionWorker(pred, state, pid,
					evaluator);
		return why3Preds;
	}

	static private ProverPredicate evaluateLogicFunctionWorker(
			LogicFunction acslPredicate, State state, int pid,
			Evaluator evaluator) throws UnsatisfiablePathConditionException {
		String name = acslPredicate.name().name();
		SymbolicConstant[] parameters = new SymbolicConstant[acslPredicate
				.parameters().size()];
		ModelFactory mf = evaluator.modelFactory();
		CIVLTypeFactory tf = mf.typeFactory();
		Evaluation eval;
		CIVLSource source = acslPredicate.definition().getSource();
		Expression asLambda = acslPredicate.definition();

		// For easily evaluating the predicate definition, evaluate the
		// predicate definition as a lambda expression. NOTICE: that the
		// parameters must be encoded in Lambda Expression in a inverse order:
		Variable[] inverseParams = new Variable[acslPredicate.parameters()
				.size()];
		int i = inverseParams.length - 1;

		for (Variable param : acslPredicate.parameters())
			inverseParams[i--] = param;
		for (Variable param : inverseParams) {
			CIVLType inputType[] = {param.type()};

			asLambda = mf.lambdaExpression(source,
					tf.functionType(tf.booleanType(), inputType), param,
					asLambda);
		}
		eval = evaluator.evaluate(state, pid, asLambda);
		assert state == eval.state;

		SymbolicExpression definitionValue = eval.value;

		i = 0;
		while (definitionValue.operator() == SymbolicOperator.LAMBDA) {
			SymbolicConstant paramVal = (SymbolicConstant) definitionValue
					.argument(0);

			parameters[i++] = paramVal;
			definitionValue = (SymbolicExpression) definitionValue.argument(1);
		}
		assert definitionValue.type().isBoolean();
		if (i < parameters.length)
			parameters = Arrays.copyOfRange(parameters, 0, i);
		return ProverPredicate.newProverPredicate(name, parameters,
				(BooleanExpression) definitionValue);
	}

}
