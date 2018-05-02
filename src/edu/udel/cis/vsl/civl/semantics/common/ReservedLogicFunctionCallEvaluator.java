package edu.udel.cis.vsl.civl.semantics.common;

import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.LogicFunction;
import edu.udel.cis.vsl.civl.semantics.IF.ArrayToolBox;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
/**
 * This evaluator focuses on evaluating logic function calls.
 * 
 * @author ziqing
 *
 */
public class ReservedLogicFunctionCallEvaluator {

	/**
	 * <p>
	 * <b>pre-condition:</b> {@link LogicFunction#isReservedFunction()} returns
	 * true.
	 * </p>
	 * 
	 * <p>
	 * Applying actual arguments to a reserved logic function.
	 * </p>
	 * 
	 * @param Evaluator
	 *            a reference to a {@link Evaluator}
	 * @param function
	 *            the {@link LogicFunction} that gets called
	 * @param arguments
	 *            an array of actual parameters
	 * @param source
	 *            the {@link CIVLSource} that is associated with this function
	 *            call
	 * @return the logic function call expression
	 */
	static SymbolicExpression applyReservedFunction(Evaluator evaluator,
			LogicFunction function, SymbolicExpression arguments[],
			CIVLSource source) {
		switch (function.name().name()) {
			case LogicFunction.RESERVED_PERMUT :
				return applyPermut(evaluator, arguments, source);
			default :
				throw new CIVLInternalException(
						"unknown reserved function " + function.name().name(),
						source);
		}
	}

	static private SymbolicExpression applyPermut(Evaluator evaluator,
			SymbolicExpression arguments[], CIVLSource source) {
		SymbolicUniverse su = evaluator.universe();
		ArrayToolBox arrayToolBox = evaluator.newArrayToolBox(su);
		NumericExpression sliceLength0 = su.subtract(su.length(arguments[0]),
				(NumericExpression) arguments[1]);
		SymbolicExpression slice0 = arrayToolBox.arraySliceRead(arguments[0],
				new NumericExpression[]{(NumericExpression) arguments[1]},
				sliceLength0);
		NumericExpression sliceLength1 = su.subtract(su.length(arguments[2]),
				(NumericExpression) arguments[1]);
		SymbolicExpression slice1 = arrayToolBox.arraySliceRead(arguments[2],
				new NumericExpression[]{(NumericExpression) arguments[3]},
				sliceLength1);
		BooleanExpression sliceLengthEq = su.equals(sliceLength0, sliceLength1);
		BooleanExpression permut = su.permut(slice0, slice1,
				(NumericExpression) arguments[4],
				(NumericExpression) arguments[5]);

		return su.and(sliceLengthEq, permut);
	}
}
