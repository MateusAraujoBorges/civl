package edu.udel.cis.vsl.civl.library.civlc;

import java.util.Arrays;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.LogicFunction;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.prove.IF.ProverFunctionInterpretation;

/**
 * Evaluates {@link LogicFunction}s to their interpretations which can be fed to
 * SARL. Since logic functions are stateless, the evaluation of each logic
 * function is only need to be done once.
 * 
 * @author ziqing
 */
public class LogicFunctionInterpretor {

	/**
	 * Translates (evaluates) a set of {@link ACSLPredicate}s to P
	 * {@link ProverFunctionInterpretation}s. This evaluation is
	 * state-independent.
	 * 
	 */
	static public ProverFunctionInterpretation[] evaluateLogicFunctions(
			List<LogicFunction> logicFunctions, State state, int pid,
			Evaluator evaluator) throws UnsatisfiablePathConditionException {
		ProverFunctionInterpretation why3Preds[] = new ProverFunctionInterpretation[logicFunctions
				.size()];
		int i = 0;

		for (LogicFunction pred : logicFunctions) {
			if (pred.definition() != null)
				why3Preds[i++] = evaluateLogicFunction(pred, state, pid,
						evaluator);
		}
		return Arrays.copyOf(why3Preds, i);
	}

	/**
	 * 
	 * @throws UnsatisfiablePathConditionException
	 *             if the definition of the logic function is unsatisfiable.
	 */
	static private ProverFunctionInterpretation evaluateLogicFunction(
			LogicFunction pred, State state, int pid, Evaluator evaluator)
			throws UnsatisfiablePathConditionException {
		ProverFunctionInterpretation result = pred.getConstantValue();
		SymbolicUniverse su = evaluator.universe();
		StateFactory sf = evaluator.stateFactory();

		if (result != null)
			return result;

		// evaluate arguments:
		SymbolicConstant[] actualArg = new SymbolicConstant[pred.parameters()
				.size()];
		int i = 0;

		// TODO: check pointer restriction:
		for (Variable var : pred.parameters()) {
			if (var.type().isPointerType())
				actualArg[i++] = null; // will be set later
			else
				actualArg[i++] = su.symbolicConstant(
						su.stringObject(var.name().name()),
						var.type().getDynamicType(su));
		}
		state = sf.pushCallStack(state, pid, pred, actualArg);

		// the parameter dynamic scope
		int dyscopeId = state.getProcessState(pid).getDyscopeId();
		// the parameter lexical scope, note that if there is any pointer type
		// argument, this scope will contain dummy "heap" variable for it.
		// This is the way of achieving the state-independent. The pointer type
		// argument will be set to point to its unique dummy heap.
		Scope lexScope = state.getDyscope(dyscopeId).lexicalScope();

		i = 0;
		// set pointer to dummy heap; set heap to arbitrary arrayof T:
		for (Variable var : pred.parameters()) {
			if (var.type().isPointerType()) {
				int heapVid = pred.pointerToHeapVidMap()[i];
				Variable heapVar = lexScope.variable(heapVid);
				SymbolicConstant heapVal = su.symbolicConstant(
						su.stringObject(heapVar.name().name()),
						heapVar.type().getDynamicType(su));

				state = sf.setVariable(state, var.vid(), dyscopeId,
						evaluator.symbolicUtility().makePointer(dyscopeId,
								heapVid, su.arrayElementReference(
										su.identityReference(), su.zeroInt())));
				state = sf.setVariable(state, heapVid, dyscopeId, heapVal);
				actualArg[i] = heapVal;
			}
			i++;
		}

		Evaluation eval = evaluator.evaluate(state, pid, pred.definition());

		result = ProverFunctionInterpretation
				.newProverPredicate(pred.name().name(), actualArg, eval.value);
		pred.setConstantValue(result);
		return result;
	}
}
