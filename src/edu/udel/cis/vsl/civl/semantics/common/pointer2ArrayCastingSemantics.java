package edu.udel.cis.vsl.civl.semantics.common;

import java.util.LinkedList;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType.TypeKind;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.TypeEvaluation;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

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
 * <code>pointer-to- (pointer-to | array-of-)* T'</code> where T' is a derived
 * type</li>
 * <li>Both q and p must have pointer types : t<sub>q</sub>, t<sub>p</sub>.<br>
 * 
 * t<sub>q</sub> is same as T. <br>
 * 
 * T, t<sub>q</sub> and t<sub>p</sub> must have the same T' when they are
 * written in the form specified in constraint 1.</li>
 * <li>t<sub>q</sub> and t<sub>p</sub> can be written in the following forms:
 * <code>
 * Common-Prefix-T := pointer-to- (pointer-to | array-of-)*
 * t<sub>q</sub> :=  Common-Prefix-T  (array-of-)*  T'
 * t<sub>p</sub> :=  Common-Prefix-T  (array-of-)*  T'
 * </code></li>
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

	Evaluation castingPointer(State state, int pid, Expression pointer,
			CIVLType castedType) {
		// TODO:
		return null;
	}

	boolean isCastedPointer(SymbolicExpression pointer) {
		// TODO:
		return false;
	}

	/* ******************** private helper methods *********************/
	private void getTypeDifference(State state, int pid,
			CIVLPointerType castedType, CIVLPointerType originType,
			CIVLSource castedTypeSource, CIVLSource originTypeSource)
			throws UnsatisfiablePathConditionException {
		Pair<CIVLType, Pair<TypeKind, Expression>> derivedRet0, derivedRet1;
		LinkedList<Pair<TypeKind, Expression>> typeRefs0, typeRefs1;
		CIVLType derivedType0, derivedType1;
		TypeEvaluation teval;

		typeRefs0 = new LinkedList<>();
		typeRefs1 = new LinkedList<>();
		derivedRet0 = derivedType(castedType);
		derivedRet1 = derivedType(originType);
		while (derivedRet0 != null && derivedRet1 != null) {
			typeRefs0.add(derivedRet0.right);
			typeRefs1.add(derivedRet1.right);
			derivedRet0 = derivedType(derivedRet0.left);
			derivedRet1 = derivedType(derivedRet1.left);
		}

		// check then remove the common prefix and suffix:
		while (!typeRefs0.isEmpty() && !typeRefs1.isEmpty()) {
			Pair<TypeKind, Expression> typeRef0, typeRef1;

			typeRef0 = typeRefs0.removeFirst();
			typeRef1 = typeRefs1.removeFirst();
		}
	}

	private Pair<CIVLType, Pair<TypeKind, Expression>> derivedType(
			CIVLType type) {
		TypeKind kind = type.typeKind();

		switch (kind) {
			case ARRAY :
				CIVLArrayType arrayType = (CIVLArrayType) type;
				Expression extent = null;
				if (arrayType.isComplete())
					extent = ((CIVLCompleteArrayType) arrayType).extent();
				return new Pair<>(arrayType.elementType(),
						new Pair<>(TypeKind.ARRAY, extent));
			case POINTER :
				CIVLPointerType ptrType = (CIVLPointerType) type;
				return new Pair<>(ptrType.baseType(),
						new Pair<>(TypeKind.POINTER, null));
			default :
				return null;
		}
	}

	private boolean typeAbstEquals(State state, int pid,
			Pair<TypeKind, Expression> typeAbst0,
			Pair<TypeKind, Expression> typeAbst1)
			throws UnsatisfiablePathConditionException {
		// If both are null, true
		if (typeAbst0 == null && typeAbst1 == null)
			return true;
		// If both are pointers, true
		if (typeAbst0.left == TypeKind.POINTER
				&& typeAbst1.left == TypeKind.POINTER)
			return true;
		// If both are array, check extent
		if (typeAbst0.left == TypeKind.ARRAY
				&& typeAbst1.left == TypeKind.ARRAY) {
			Expression ext0, ext1;

			ext0 = typeAbst0.right;
			ext1 = typeAbst1.right;
			if (ext0 != null && ext1 != null) {
				if (ext0.equals(ext1))
					return true;

				Evaluation eval;
				SymbolicExpression ext0val, ext1val;

				eval = evaluator.evaluate(state, pid, ext0);
				ext0val = eval.value;
				eval = evaluator.evaluate(eval.state, pid, ext1);
				ext1val = eval.value;

			}
		}
		// Else false
		return false;
	}
}
