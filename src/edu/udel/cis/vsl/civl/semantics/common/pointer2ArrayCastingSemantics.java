package edu.udel.cis.vsl.civl.semantics.common;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType.TypeKind;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * This class implements a subset of the semantics of a casted pointer q, where
 * q is defined as <code>q := (T)p</code>. There are some constraints on q, p
 * and T respectively thus it is only a subset of the semantics of the C
 * language.
 * 
 * <p>
 * Constraints:
 * <ol>
 * <li>T must be a pointer type. Thus, pointer type T can be written as
 * <code>pointer-to- (array-of-)* T'</code> where T' is a derived type</li>
 * <li>Both q and p must have pointer types : t<sub>q</sub>, t<sub>p</sub>.<br>
 * t<sub>q</sub> is same as T. <br>
 * T, t<sub>q</sub> and t<sub>p</sub> must have the same T' when they are
 * written in the form specified in constraint 1.</li>
 * </ol>
 * </p>
 * 
 * 
 * <p>
 * The subset of the semantics of <code>q := (T)p</code>:
 * <ol>
 * <li>A function f that maps a pointer p and a casted type T to q. see
 * {@link #castingPointer(State, int, Expression, CIVLType)}</li>
 * <li>A function g that maps a casted pointer q to the original p, where
 * "original p" can be defined as the referenced type of type of p is exactly
 * same as the type of the object pointed by p. see
 * {@link #isCastedPointer(SymbolicExpression)}</li>
 * <li>Semantics of a subscript operation on a casted pointer q</li>
 * <li>Semantics of a dereference operation on a casted pointer q</li>
 * <li>Semantics of a pointer addition on a casted pointer q</li>
 * <li>Semantics of a pointer subtraction on a casted pointer q</li>
 * </ol>
 * </p>
 * 
 * @author ziqingluo
 *
 */
class pointer2ArrayCastingSemantics {

	private SymbolicUniverse universe;

	private Evaluator evaluator;

	private final NumericExpression noExtent;

	private final SymbolicConstant castFunc;

	private static final String castFuncName = "_cast";

	pointer2ArrayCastingSemantics(Evaluator evaluator) {
		this.evaluator = evaluator;
		this.universe = evaluator.universe();
		noExtent = universe.zeroInt();

		SymbolicType intArrayType = universe.arrayType(universe.integerType());
		SymbolicType pointerType = evaluator.modelFactory().typeFactory()
				.pointerSymbolicType();

		castFunc = universe.symbolicConstant(
				universe.stringObject(castFuncName),
				universe.functionType(
						Arrays.asList(intArrayType, intArrayType, pointerType),
						pointerType));
	}

	Evaluation castingPointer(State state, int pid, Expression pointer,
			CIVLType castedType, CIVLSource castingSource)
			throws UnsatisfiablePathConditionException {
		CIVLType originType = pointer.getExpressionType();
		SymbolicExpression pointerVal;
		Evaluation eval;

		assert originType.isPointerType() && castedType.isPointerType();
		eval = evaluator.evaluate(state, pid, pointer);
		pointerVal = eval.value;
		eval = makeCastedPointer(eval.state, pid, (CIVLPointerType) castedType,
				(CIVLPointerType) originType, pointerVal, castingSource);
		return eval;
	}

	boolean isCastedPointer(SymbolicExpression pointer) {
		if (pointer.operator() == SymbolicOperator.APPLY) {
			SymbolicConstant symConst = (SymbolicConstant) pointer.argument(0);

			return symConst.name().equals(castFunc.name());
		}
		return false;
	}

	Evaluation pointerAdd(State state, int pid, String process,
			Expression pointerAddExpression, SymbolicExpression pointer,
			NumericExpression offset) {
		assert isCastedPointer(pointer);
		SymbolicExpression originPointer = getOriginPointer(pointer);
		SymbolicExpression castedDimArray = getCastedDimArray(pointer);
		NumericExpression originExtsProd = getOriginExtProd(pointer);
		NumericExpression step, castedExtsProd;
		SymbolicArrayType dimArrayType = (SymbolicArrayType) castedDimArray
				.type();
		int dim = dimArrayType.dimensions();

		castedExtsProd = universe.oneInt();
		for (int i = 0; i < dim; i++)
			castedExtsProd = universe.multiply(castedExtsProd,
					(NumericExpression) universe.arrayRead(castedDimArray,
							universe.integer(i)));
		// cannot do pointer addition on a pointer which has incomplete type:
		assert !castedExtsProd.isZero();
		// TODO: If originExtsProd is normalized to one, then castedExtsProd is
		// the step:
		return null;
	}

	/* ******************** private helper methods *********************/
	private Evaluation makeCastedPointer(State state, int pid,
			CIVLPointerType castedType, CIVLPointerType originType,
			SymbolicExpression pointer, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		CIVLType originSuffixType, castedSuffixType;
		List<Expression> originExts, castedExts;
		SymbolicExpression castedDimArray, originDimArray, originExtsProd;
		Evaluation eval;

		originExts = new LinkedList<>();
		castedExts = new LinkedList<>();
		originSuffixType = getPointer2ArrayReferedType(originType, originExts);
		castedSuffixType = getPointer2ArrayReferedType(castedType, castedExts);
		// Constraint 2 checking:
		if (!originSuffixType.equals(castedSuffixType))
			throw new CIVLUnimplementedFeatureException(
					"Casting a pointer-to-(array-of)*-T1 to a pointer-to-(array-of)*-T2,"
							+ " where T1 and T2 are not lexically equivalent.",
					source);
		eval = valueOfExtents(state, pid, castedExts);
		castedDimArray = eval.value;
		// If the given pointer was casted before, then it contains the original
		// array dimensions and original pointer values:
		if (isCastedPointer(pointer)) {
			originExtsProd = getOriginExtProd(pointer);
			pointer = getOriginPointer(pointer);
			eval.value = universe.apply(castFunc,
					Arrays.asList(castedDimArray, originExtsProd, pointer));
		} else {
			eval = valueOfExtents(state, pid, originExts);
			originDimArray = eval.value;
			eval.value = this.normalize(castedDimArray, originDimArray,
					pointer);
		}
		return eval;
	}

	// invariants:
	// isCastedPointer(pointer) ==>
	// originExtsProd <= castedExtsProd && castedExtsProd % originExtsProd == 0;
	private SymbolicExpression normalize(SymbolicExpression castedDimArray,
			SymbolicExpression originDimArray, SymbolicExpression pointer) {
		NumericExpression castedExtsProd, originExtsProd;
		NumericExpression factor;
		SymbolicArrayType originDimArrayType = (SymbolicArrayType) originDimArray
				.type();
		int dim = originDimArrayType.dimensions();
		ReferenceExpression reference = evaluator.symbolicUtility()
				.getSymRef(pointer);

		for (int i = 0; i < dim; i++)
			reference = universe.arrayElementReference(reference,
					universe.zeroInt());
		pointer = evaluator.symbolicUtility().makePointer(pointer, reference);
		return universe.apply(castFunc, Arrays.asList(castedDimArray, pointer));
	}

	private CIVLType getPointer2ArrayReferedType(CIVLPointerType type,
			List<Expression> extents) {
		CIVLType referedType = type.baseType();
		TypeKind kind = referedType.typeKind();

		while (kind == TypeKind.ARRAY) {
			CIVLArrayType arrayType = (CIVLArrayType) referedType;

			referedType = (arrayType).elementType();
			if (arrayType.isComplete()) {
				extents.add(((CIVLCompleteArrayType) arrayType).extent());
			} else
				extents.add(null);
			kind = referedType.typeKind();
		}
		return referedType;
	}

	private Evaluation valueOfExtents(State state, int pid,
			List<Expression> extents)
			throws UnsatisfiablePathConditionException {
		List<NumericExpression> valueComponents = new LinkedList<>();
		Evaluation eval = null;

		for (Expression extent : extents) {
			if (extent == null) {
				// Only first extent can be absent, e.g. a[][N];
				// Front-end should guarantee this:
				assert valueComponents.isEmpty();
				valueComponents.add(noExtent);
			} else {
				eval = evaluator.evaluate(state, pid, extent);
				state = eval.state;
				valueComponents.add((NumericExpression) eval.value);
			}
		}
		if (eval == null)
			eval = new Evaluation(state, null);
		eval.value = universe.array(universe.integerType(), valueComponents);
		return eval;
	}

	private NumericExpression product(SymbolicExpression array) {
		NumericExpression product = universe.oneInt();
		SymbolicArrayType arrayType = (SymbolicArrayType) array.type();
		int dim = arrayType.dimensions();

		for (int i = 0; i < dim; i++)
			product = universe.multiply(product, (NumericExpression) universe
					.arrayRead(array, universe.integer(i)));
		return product;
	}

	private SymbolicExpression getCastedDimArray(
			SymbolicExpression castedPointer) {
		SymbolicExpression args = (SymbolicExpression) castedPointer
				.argument(1);

		return (SymbolicExpression) args.argument(0);
	}

	private NumericExpression getOriginExtProd(
			SymbolicExpression castedPointer) {
		SymbolicExpression args = (SymbolicExpression) castedPointer
				.argument(1);

		return (NumericExpression) args.argument(1);
	}

	private SymbolicExpression getOriginPointer(
			SymbolicExpression castedPointer) {
		SymbolicExpression args = (SymbolicExpression) castedPointer
				.argument(1);

		return (SymbolicExpression) args.argument(2);
	}
}
